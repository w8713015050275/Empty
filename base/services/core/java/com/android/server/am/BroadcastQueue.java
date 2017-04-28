/*
 * Copyright (C) 2012 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.android.server.am;

import java.io.FileDescriptor;
import java.io.PrintWriter;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
// [+LEUI][FERRARI-3400][chenxu1] added:update receiver after app died.
import java.util.Iterator;
//[-LEUI]
import java.util.Set;

import android.app.ActivityManager;
import android.app.AppGlobals;
import android.app.AppOpsManager;
import android.app.BroadcastOptions;
import android.content.ComponentName;
import android.content.IIntentReceiver;
import android.content.Intent;
import android.content.pm.ActivityInfo;
import android.content.pm.ApplicationInfo;
import android.content.pm.PackageManager;
import android.content.pm.ResolveInfo;
import android.os.Bundle;
import android.os.Handler;
import android.os.IBinder;
import android.os.Looper;
import android.os.Message;
import android.os.Process;
import android.os.RemoteException;
import android.os.SystemClock;
import android.os.UserHandle;
import android.util.EventLog;
import android.util.Slog;
import android.util.TimeUtils;
import com.android.internal.util.ArrayUtils;
import com.android.server.DeviceIdleController;
import com.android.server.am.LetvDebugManager;

import static com.android.server.am.ActivityManagerDebugConfig.*;

/**
 * BROADCASTS
 *
 * We keep two broadcast queues and associated bookkeeping, one for those at
 * foreground priority, and one for normal (background-priority) broadcasts.
 */
public final class BroadcastQueue {
    private static final String TAG = "BroadcastQueue";
    private static final String TAG_MU = TAG + POSTFIX_MU;
    private static final String TAG_BROADCAST = TAG + POSTFIX_BROADCAST;

    static final int MAX_BROADCAST_HISTORY = ActivityManager.isLowRamDeviceStatic() ? 10 : 50;
    static final int MAX_BROADCAST_SUMMARY_HISTORY
            = ActivityManager.isLowRamDeviceStatic() ? 25 : 300;

    final ActivityManagerService mService;

    /**
     * Recognizable moniker for this queue
     */
    final String mQueueName;

    /**
     * Timeout period for this queue's broadcasts
     */
    final long mTimeoutPeriod;

    /**
     * If true, we can delay broadcasts while waiting services to finish in the previous
     * receiver's process.
     */
    final boolean mDelayBehindServices;

    /**
     * Lists of all active broadcasts that are to be executed immediately
     * (without waiting for another broadcast to finish).  Currently this only
     * contains broadcasts to registered receivers, to avoid spinning up
     * a bunch of processes to execute IntentReceiver components.  Background-
     * and foreground-priority broadcasts are queued separately.
     */
    final ArrayList<BroadcastRecord> mParallelBroadcasts = new ArrayList<>();

    /**
     * List of all active broadcasts that are to be executed one at a time.
     * The object at the top of the list is the currently activity broadcasts;
     * those after it are waiting for the top to finish.  As with parallel
     * broadcasts, separate background- and foreground-priority queues are
     * maintained.
     */
    final ArrayList<BroadcastRecord> mOrderedBroadcasts = new ArrayList<>();

    /**
     * Historical data of past broadcasts, for debugging.  This is a ring buffer
     * whose last element is at mHistoryNext.
     */
    final BroadcastRecord[] mBroadcastHistory = new BroadcastRecord[MAX_BROADCAST_HISTORY];
    int mHistoryNext = 0;

    /**
     * Summary of historical data of past broadcasts, for debugging.  This is a
     * ring buffer whose last element is at mSummaryHistoryNext.
     */
    final Intent[] mBroadcastSummaryHistory = new Intent[MAX_BROADCAST_SUMMARY_HISTORY];
    int mSummaryHistoryNext = 0;

    /**
     * Various milestone timestamps of entries in the mBroadcastSummaryHistory ring
     * buffer, also tracked via the mSummaryHistoryNext index.  These are all in wall
     * clock time, not elapsed.
     */
    final long[] mSummaryHistoryEnqueueTime = new  long[MAX_BROADCAST_SUMMARY_HISTORY];
    final long[] mSummaryHistoryDispatchTime = new  long[MAX_BROADCAST_SUMMARY_HISTORY];
    final long[] mSummaryHistoryFinishTime = new  long[MAX_BROADCAST_SUMMARY_HISTORY];

    /**
     * Set when we current have a BROADCAST_INTENT_MSG in flight.
     */
    boolean mBroadcastsScheduled = false;

    /**
     * True if we have a pending unexpired BROADCAST_TIMEOUT_MSG posted to our handler.
     */
    boolean mPendingBroadcastTimeoutMessage;

    /**
     * Intent broadcasts that we have tried to start, but are
     * waiting for the application's process to be created.  We only
     * need one per scheduling class (instead of a list) because we always
     * process broadcasts one at a time, so no others can be started while
     * waiting for this one.
     */
    BroadcastRecord mPendingBroadcast = null;

    /**
     * The receiver index that is pending, to restart the broadcast if needed.
     */
    int mPendingBroadcastRecvIndex;

    static final int BROADCAST_INTENT_MSG = ActivityManagerService.FIRST_BROADCAST_QUEUE_MSG;
    static final int BROADCAST_TIMEOUT_MSG = ActivityManagerService.FIRST_BROADCAST_QUEUE_MSG + 1;
    static final int SCHEDULE_TEMP_WHITELIST_MSG
            = ActivityManagerService.FIRST_BROADCAST_QUEUE_MSG + 2;

    final BroadcastHandler mHandler;

    private final class BroadcastHandler extends Handler {
        public BroadcastHandler(Looper looper) {
            super(looper, null, true);
        }

        @Override
        public void handleMessage(Message msg) {
            switch (msg.what) {
                case BROADCAST_INTENT_MSG: {
                    if (DEBUG_BROADCAST) Slog.v(
                            TAG_BROADCAST, "Received BROADCAST_INTENT_MSG");
                    //处理广播
                    processNextBroadcast(true);
                } break;
                case BROADCAST_TIMEOUT_MSG: {
                    synchronized (mService) {
                        broadcastTimeoutLocked(true);
                    }
                } break;
                case SCHEDULE_TEMP_WHITELIST_MSG: {
                    DeviceIdleController.LocalService dic = mService.mLocalDeviceIdleController;
                    if (dic != null) {
                        dic.addPowerSaveTempWhitelistAppDirect(UserHandle.getAppId(msg.arg1),
                                msg.arg2, true, (String)msg.obj);
                    }
                } break;
            }
        }
    };

    private final class AppNotResponding implements Runnable {
        private final ProcessRecord mApp;
        private final String mAnnotation;

        public AppNotResponding(ProcessRecord app, String annotation) {
            mApp = app;
            mAnnotation = annotation;
        }

        @Override
        public void run() {
            mService.appNotResponding(mApp, null, null, false, mAnnotation);
        }
    }

    BroadcastQueue(ActivityManagerService service, Handler handler,
            String name, long timeoutPeriod, boolean allowDelayBehindServices) {
        mService = service;
        //handler 默认主线程
        mHandler = new BroadcastHandler(handler.getLooper());
        mQueueName = name;
        mTimeoutPeriod = timeoutPeriod;
        mDelayBehindServices = allowDelayBehindServices;
    }

    public boolean isPendingBroadcastProcessLocked(int pid) {
        return mPendingBroadcast != null && mPendingBroadcast.curApp.pid == pid;
    }

    public void enqueueParallelBroadcastLocked(BroadcastRecord r) {
        mParallelBroadcasts.add(r);
        r.enqueueClockTime = System.currentTimeMillis();
    }

    public void enqueueOrderedBroadcastLocked(BroadcastRecord r) {
        mOrderedBroadcasts.add(r);
        r.enqueueClockTime = System.currentTimeMillis();
    }

    public final boolean replaceParallelBroadcastLocked(BroadcastRecord r) {
        for (int i = mParallelBroadcasts.size() - 1; i >= 0; i--) {
            if (r.intent.filterEquals(mParallelBroadcasts.get(i).intent)) {
                if (DEBUG_BROADCAST) Slog.v(TAG_BROADCAST,
                        "***** DROPPING PARALLEL ["
                + mQueueName + "]: " + r.intent);
                mParallelBroadcasts.set(i, r);
                return true;
            }
        }
        return false;
    }

    public final boolean replaceOrderedBroadcastLocked(BroadcastRecord r) {
        for (int i = mOrderedBroadcasts.size() - 1; i > 0; i--) {
            if (r.intent.filterEquals(mOrderedBroadcasts.get(i).intent)) {
                if (DEBUG_BROADCAST) Slog.v(TAG_BROADCAST,
                        "***** DROPPING ORDERED ["
                        + mQueueName + "]: " + r.intent);
                mOrderedBroadcasts.set(i, r);
                return true;
            }
        }
        return false;
    }

    private final void processCurBroadcastLocked(BroadcastRecord r,
            ProcessRecord app) throws RemoteException {
        if (DEBUG_BROADCAST)  Slog.v(TAG_BROADCAST,
                "Process cur broadcast " + r + " for app " + app);
        if (app.thread == null) {
            throw new RemoteException();
        }
        r.receiver = app.thread.asBinder();
        r.curApp = app;
        app.curReceiver = r;
        app.forceProcessStateUpTo(ActivityManager.PROCESS_STATE_RECEIVER);
        mService.updateLruProcessLocked(app, false, null);
        mService.updateOomAdjLocked();

        // Tell the application to launch this receiver.
        r.intent.setComponent(r.curComponent);

        boolean started = false;
        try {
            if (DEBUG_BROADCAST_LIGHT) Slog.v(TAG_BROADCAST,
                    "Delivering to component " + r.curComponent
                    + ": " + r);
            mService.ensurePackageDexOpt(r.intent.getComponent().getPackageName());
            app.thread.scheduleReceiver(new Intent(r.intent), r.curReceiver,
                    mService.compatibilityInfoForPackageLocked(r.curReceiver.applicationInfo),
                    r.resultCode, r.resultData, r.resultExtras, r.ordered, r.userId,
                    app.repProcState);
            if (DEBUG_BROADCAST)  Slog.v(TAG_BROADCAST,
                    "Process cur broadcast " + r + " DELIVERED for app " + app);
            started = true;
        } finally {
            if (!started) {
                if (DEBUG_BROADCAST)  Slog.v(TAG_BROADCAST,
                        "Process cur broadcast " + r + ": NOT STARTED!");
                r.receiver = null;
                r.curApp = null;
                app.curReceiver = null;
            }
        }
    }

    public boolean sendPendingBroadcastsLocked(ProcessRecord app) {
        boolean didSomething = false;
        final BroadcastRecord br = mPendingBroadcast;
        if (br != null && br.curApp.pid == app.pid) {
            if (br.curApp != app) {
                Slog.e(TAG, "App mismatch when sending pending broadcast to "
                        + app.processName + ", intended target is " + br.curApp.processName);
                return false;
            }
            try {
                mPendingBroadcast = null;
                processCurBroadcastLocked(br, app);
                didSomething = true;
            } catch (Exception e) {
                Slog.w(TAG, "Exception in new application when starting receiver "
                        + br.curComponent.flattenToShortString(), e);
                logBroadcastReceiverDiscardLocked(br);
                finishReceiverLocked(br, br.resultCode, br.resultData,
                        br.resultExtras, br.resultAbort, false);
                scheduleBroadcastsLocked();
                // We need to reset the state if we failed to start the receiver.
                br.state = BroadcastRecord.IDLE;
                throw new RuntimeException(e.getMessage());
            }
        }
        return didSomething;
    }

    public void skipPendingBroadcastLocked(int pid) {
        final BroadcastRecord br = mPendingBroadcast;
        if (br != null && br.curApp.pid == pid) {
            br.state = BroadcastRecord.IDLE;
            br.nextReceiver = mPendingBroadcastRecvIndex;
            mPendingBroadcast = null;
            scheduleBroadcastsLocked();
        }
    }

    public void skipCurrentReceiverLocked(ProcessRecord app) {
        BroadcastRecord r = null;
        if (mOrderedBroadcasts.size() > 0) {
            BroadcastRecord br = mOrderedBroadcasts.get(0);
            if (br.curApp == app) {
                r = br;
            }
        }
        if (r == null && mPendingBroadcast != null && mPendingBroadcast.curApp == app) {
            if (DEBUG_BROADCAST) Slog.v(TAG_BROADCAST,
                    "[" + mQueueName + "] skip & discard pending app " + r);
            r = mPendingBroadcast;
        }

        if (r != null) {
            logBroadcastReceiverDiscardLocked(r);
            finishReceiverLocked(r, r.resultCode, r.resultData,
                    r.resultExtras, r.resultAbort, false);
            scheduleBroadcastsLocked();
        }
    }

    // [+LEUI][FERRARI-3400][chenxu1] added:update receiver after app died.
    //remove unused or died BroadcastFilter
    public void updateReceiverListLocked(ProcessRecord app) {
        for (BroadcastRecord r : mOrderedBroadcasts) {
            //[+LEUI][FERRARI-3898][chenxu1] NPE at r.receivers will block ordered broadcast
            if (null == r.receivers) {
                continue;
            }
            //[-LEUI]
            // [+LEUI][RUBY-30954][chenxu1] added:update nextReceiver after remove receivers.
            Object o;
            for (int i = r.receivers.size() - 1; i >= 0; i--) {
                o = r.receivers.get(i);
                if (o instanceof BroadcastFilter) {
                    BroadcastFilter bf = (BroadcastFilter)o;
                    if (bf.receiverList != null && bf.receiverList.app == app) {
                        Slog.d(TAG, "remove BroadcastFilter bf = " + bf);
                        r.receivers.remove(i);
                        if (i < r.nextReceiver) {
                            r.nextReceiver--;
                            Slog.d(TAG, "after remove change r.nextReceiver = " + r.nextReceiver);
                        }
                    }
                }
            }
            r.nextReceiver = Math.min(r.nextReceiver, r.receivers.size());
        }
        Slog.d(TAG, "removeReceiverListLocked app = " + app);
        //[-LEUI]
    }
    //[-LEUI]

    public void scheduleBroadcastsLocked() {
        if (DEBUG_BROADCAST) Slog.v(TAG_BROADCAST, "Schedule broadcasts ["
                + mQueueName + "]: current="
                + mBroadcastsScheduled);

        if (mBroadcastsScheduled) {
            return;
        }
        //mHandler默认主线程: AMS所在的进程的主线程
        mHandler.sendMessage(mHandler.obtainMessage(BROADCAST_INTENT_MSG, this));
        mBroadcastsScheduled = true;
    }

    public BroadcastRecord getMatchingOrderedReceiver(IBinder receiver) {
        if (mOrderedBroadcasts.size() > 0) {
            final BroadcastRecord r = mOrderedBroadcasts.get(0);
            if (r != null && r.receiver == receiver) {
                return r;
            }
        }
        return null;
    }

    public boolean finishReceiverLocked(BroadcastRecord r, int resultCode,
            String resultData, Bundle resultExtras, boolean resultAbort, boolean waitForServices) {
        final int state = r.state;
        final ActivityInfo receiver = r.curReceiver;
        r.state = BroadcastRecord.IDLE;
        if (state == BroadcastRecord.IDLE) {
            Slog.w(TAG, "finishReceiver [" + mQueueName + "] called but state is IDLE");
        }
        r.receiver = null;
        r.intent.setComponent(null);
        if (r.curApp != null && r.curApp.curReceiver == r) {
            r.curApp.curReceiver = null;
        }
        if (r.curFilter != null) {
            r.curFilter.receiverList.curBroadcast = null;
        }
        r.curFilter = null;
        r.curReceiver = null;
        r.curApp = null;
        mPendingBroadcast = null;

        r.resultCode = resultCode;
        r.resultData = resultData;
        r.resultExtras = resultExtras;
        if (resultAbort && (r.intent.getFlags()&Intent.FLAG_RECEIVER_NO_ABORT) == 0) {
            r.resultAbort = resultAbort;
        } else {
            r.resultAbort = false;
        }

        if (waitForServices && r.curComponent != null && r.queue.mDelayBehindServices
                && r.queue.mOrderedBroadcasts.size() > 0
                && r.queue.mOrderedBroadcasts.get(0) == r) {
            ActivityInfo nextReceiver;
            if (r.nextReceiver < r.receivers.size()) {
                Object obj = r.receivers.get(r.nextReceiver);
                nextReceiver = (obj instanceof ActivityInfo) ? (ActivityInfo)obj : null;
            } else {
                nextReceiver = null;
            }
            // Don't do this if the next receive is in the same process as the current one.
            if (receiver == null || nextReceiver == null
                    || receiver.applicationInfo.uid != nextReceiver.applicationInfo.uid
                    || !receiver.processName.equals(nextReceiver.processName)) {
                // In this case, we are ready to process the next receiver for the current broadcast,
                // but are on a queue that would like to wait for services to finish before moving
                // on.  If there are background services currently starting, then we will go into a
                // special state where we hold off on continuing this broadcast until they are done.
                if (mService.mServices.hasBackgroundServices(r.userId)) {
                    Slog.i(TAG, "Delay finish: " + r.curComponent.flattenToShortString());
                    r.state = BroadcastRecord.WAITING_SERVICES;
                    return false;
                }
            }
        }

        r.curComponent = null;

        // We will process the next receiver right now if this is finishing
        // an app receiver (which is always asynchronous) or after we have
        // come back from calling a receiver.
        return state == BroadcastRecord.APP_RECEIVE
                || state == BroadcastRecord.CALL_DONE_RECEIVE;
    }

    public void backgroundServicesFinishedLocked(int userId) {
        if (mOrderedBroadcasts.size() > 0) {
            BroadcastRecord br = mOrderedBroadcasts.get(0);
            if (br.userId == userId && br.state == BroadcastRecord.WAITING_SERVICES) {
                Slog.i(TAG, "Resuming delayed broadcast");
                br.curComponent = null;
                br.state = BroadcastRecord.IDLE;
                processNextBroadcast(false);
            }
        }
    }

    //重要!!!
    private static void performReceiveLocked(ProcessRecord app, IIntentReceiver receiver,
            Intent intent, int resultCode, String data, Bundle extras,
            boolean ordered, boolean sticky, int sendingUser) throws RemoteException {
        // Send the intent to the receiver asynchronously using one-way binder calls.
        if (app != null) {
            if (app.thread != null) {
                // If we have an app thread, do the call through that so it is
                // correctly ordered with other one-way calls.
                app.thread.scheduleRegisteredReceiver(receiver, intent, resultCode,
                        data, extras, ordered, sticky, sendingUser, app.repProcState);
            } else {
                // Application has died. Receiver doesn't exist.
                throw new RemoteException("app.thread must not be null");
            }
        } else {

            receiver.performReceive(intent, resultCode, data, extras, ordered,
                    sticky, sendingUser);
        }
    }

    //发送给动态注册的BR
    private void deliverToRegisteredReceiverLocked(BroadcastRecord r,
            BroadcastFilter filter, boolean ordered) {
        boolean skip = false;
        if (filter.requiredPermission != null) {
            int perm = mService.checkComponentPermission(filter.requiredPermission,
                    r.callingPid, r.callingUid, -1, true);
            if (perm != PackageManager.PERMISSION_GRANTED) {
                Slog.w(TAG, "Permission Denial: broadcasting "
                        + r.intent.toString()
                        + " from " + r.callerPackage + " (pid="
                        + r.callingPid + ", uid=" + r.callingUid + ")"
                        + " requires " + filter.requiredPermission
                        + " due to registered receiver " + filter);
                skip = true;
            } else {
                final int opCode = AppOpsManager.permissionToOpCode(filter.requiredPermission);
                if (opCode != AppOpsManager.OP_NONE
                        && mService.mAppOpsService.noteOperationFB(opCode, r.callingUid,
                                r.callerPackage,true) != AppOpsManager.MODE_ALLOWED) {
                    Slog.w(TAG, "Appop Denial: broadcasting "
                            + r.intent.toString()
                            + " from " + r.callerPackage + " (pid="
                            + r.callingPid + ", uid=" + r.callingUid + ")"
                            + " requires appop " + AppOpsManager.permissionToOp(
                                    filter.requiredPermission)
                            + " due to registered receiver " + filter);
                    skip = true;
                }
            }
        }
        if (!skip && r.requiredPermissions != null && r.requiredPermissions.length > 0) {
            for (int i = 0; i < r.requiredPermissions.length; i++) {
                String requiredPermission = r.requiredPermissions[i];
                int perm = mService.checkComponentPermission(requiredPermission,
                        filter.receiverList.pid, filter.receiverList.uid, -1, true);
                if (perm != PackageManager.PERMISSION_GRANTED) {
                    Slog.w(TAG, "Permission Denial: receiving "
                            + r.intent.toString()
                            + " to " + filter.receiverList.app
                            + " (pid=" + filter.receiverList.pid
                            + ", uid=" + filter.receiverList.uid + ")"
                            + " requires " + requiredPermission
                            + " due to sender " + r.callerPackage
                            + " (uid " + r.callingUid + ")");
                    skip = true;
                    break;
                }
                int appOp = AppOpsManager.permissionToOpCode(requiredPermission);
                if (appOp != AppOpsManager.OP_NONE && appOp != r.appOp
                        && mService.mAppOpsService.noteOperationFB(appOp,
                        filter.receiverList.uid, filter.packageName,true)
                        != AppOpsManager.MODE_ALLOWED) {
                    Slog.w(TAG, "Appop Denial: receiving "
                            + r.intent.toString()
                            + " to " + filter.receiverList.app
                            + " (pid=" + filter.receiverList.pid
                            + ", uid=" + filter.receiverList.uid + ")"
                            + " requires appop " + AppOpsManager.permissionToOp(
                            requiredPermission)
                            + " due to sender " + r.callerPackage
                            + " (uid " + r.callingUid + ")");
                    skip = true;
                    break;
                }
            }
        }
        if (!skip && (r.requiredPermissions == null || r.requiredPermissions.length == 0)) {
            int perm = mService.checkComponentPermission(null,
                    filter.receiverList.pid, filter.receiverList.uid, -1, true);
            if (perm != PackageManager.PERMISSION_GRANTED) {
                Slog.w(TAG, "Permission Denial: security check failed when receiving "
                        + r.intent.toString()
                        + " to " + filter.receiverList.app
                        + " (pid=" + filter.receiverList.pid
                        + ", uid=" + filter.receiverList.uid + ")"
                        + " due to sender " + r.callerPackage
                        + " (uid " + r.callingUid + ")");
                skip = true;
            }
        }
        if (!skip && r.appOp != AppOpsManager.OP_NONE
                && mService.mAppOpsService.noteOperation(r.appOp,
                filter.receiverList.uid, filter.packageName)
                != AppOpsManager.MODE_ALLOWED) {
            Slog.w(TAG, "Appop Denial: receiving "
                    + r.intent.toString()
                    + " to " + filter.receiverList.app
                    + " (pid=" + filter.receiverList.pid
                    + ", uid=" + filter.receiverList.uid + ")"
                    + " requires appop " + AppOpsManager.opToName(r.appOp)
                    + " due to sender " + r.callerPackage
                    + " (uid " + r.callingUid + ")");
            skip = true;
        }

        if (!mService.mIntentFirewall.checkBroadcast(r.intent, r.callingUid,
                r.callingPid, r.resolvedType, filter.receiverList.uid)) {
            return;
        }

        if (filter.receiverList.app == null || filter.receiverList.app.crashing) {
            Slog.w(TAG, "Skipping deliver [" + mQueueName + "] " + r
                    + " to " + filter.receiverList + ": process crashing");
            skip = true;
        }
        // [+LEUI] [REQ] [LEUI-13225] [quqixuan] added:feature for limit background apps.
        if(!skip && filter.receiverList.app != null && filter.receiverList.app.info != null) {
            skip = mService.isAllowAcquireResource(r.intent.getAction(), filter.receiverList.app.info.packageName, filter.receiverList.app.info.uid, filter.receiverList.app.pid, 1) == 0;
        }
        // [-LEUI]
        if (!skip) {
            // If this is not being sent as an ordered broadcast, then we
            // don't want to touch the fields that keep track of the current
            // state of ordered broadcasts.
            if (ordered) {
                r.receiver = filter.receiverList.receiver.asBinder();
                r.curFilter = filter;
                filter.receiverList.curBroadcast = r;
                r.state = BroadcastRecord.CALL_IN_RECEIVE;
                if (filter.receiverList.app != null) {
                    // Bump hosting application to no longer be in background
                    // scheduling class.  Note that we can't do that if there
                    // isn't an app...  but we can only be in that case for
                    // things that directly call the IActivityManager API, which
                    // are already core system stuff so don't matter for this.
                    r.curApp = filter.receiverList.app;
                    filter.receiverList.app.curReceiver = r;
                    mService.updateOomAdjLocked(r.curApp);
                }
            }
            try {
                if (DEBUG_BROADCAST_LIGHT) Slog.i(TAG_BROADCAST,
                        "Delivering to " + filter + " : " + r);
                if (ordered) checkTime(r.receiverTime,"before performReceiveLocked "+r+" "+r.receiver ,getTimeoutToCheck());
                //接收到广播
                performReceiveLocked(filter.receiverList.app, filter.receiverList.receiver,
                        new Intent(r.intent), r.resultCode, r.resultData,
                        r.resultExtras, r.ordered, r.initialSticky, r.userId);
                if (ordered) {
                    r.state = BroadcastRecord.CALL_DONE_RECEIVE;
                }
            } catch (RemoteException e) {
                Slog.w(TAG, "Failure sending broadcast " + r.intent, e);
                if (ordered) {
                    r.receiver = null;
                    r.curFilter = null;
                    filter.receiverList.curBroadcast = null;
                    if (filter.receiverList.app != null) {
                        filter.receiverList.app.curReceiver = null;
                    }
                }
            }
        }
    }

    final void scheduleTempWhitelistLocked(int uid, long duration, BroadcastRecord r) {
        if (duration > Integer.MAX_VALUE) {
            duration = Integer.MAX_VALUE;
        }
        // XXX ideally we should pause the broadcast until everything behind this is done,
        // or else we will likely start dispatching the broadcast before we have opened
        // access to the app (there is a lot of asynchronicity behind this).  It is probably
        // not that big a deal, however, because the main purpose here is to allow apps
        // to hold wake locks, and they will be able to acquire their wake lock immediately
        // it just won't be enabled until we get through this work.
        StringBuilder b = new StringBuilder();
        b.append("broadcast:");
        UserHandle.formatUid(b, r.callingUid);
        b.append(":");
        if (r.intent.getAction() != null) {
            b.append(r.intent.getAction());
        } else if (r.intent.getComponent() != null) {
            b.append(r.intent.getComponent().flattenToShortString());
        } else if (r.intent.getData() != null) {
            b.append(r.intent.getData());
        }
        mHandler.obtainMessage(SCHEDULE_TEMP_WHITELIST_MSG, uid, (int)duration, b.toString())
                .sendToTarget();
    }

    final void processNextBroadcast(boolean fromMsg) {
        synchronized(mService) {
            BroadcastRecord r;

            if (DEBUG_BROADCAST) Slog.v(TAG_BROADCAST, "processNextBroadcast ["
                    + mQueueName + "]: "
                    + mParallelBroadcasts.size() + " broadcasts, "
                    + mOrderedBroadcasts.size() + " ordered broadcasts");

            mService.updateCpuStats();

            if (fromMsg) {
                mBroadcastsScheduled = false;
            }

            // First, deliver any non-serialized broadcasts right away.
            while (mParallelBroadcasts.size() > 0) {
                r = mParallelBroadcasts.remove(0);
                r.dispatchTime = SystemClock.uptimeMillis();
                r.dispatchClockTime = System.currentTimeMillis();
                final int N = r.receivers.size();
                if (DEBUG_BROADCAST_LIGHT) Slog.v(TAG_BROADCAST, "Processing parallel broadcast ["
                        + mQueueName + "] " + r);
                for (int i=0; i<N; i++) {
                    Object target = r.receivers.get(i);
                    if (DEBUG_BROADCAST) Slog.v(TAG_BROADCAST,
                            "Delivering non-ordered on [" + mQueueName + "] to registered "
                            + target + ": " + r);
                    //处理动态注册的BR
                    deliverToRegisteredReceiverLocked(r, (BroadcastFilter)target, false);
                }
                addBroadcastToHistoryLocked(r);
                if (DEBUG_BROADCAST_LIGHT) Slog.v(TAG_BROADCAST, "Done with parallel broadcast ["
                        + mQueueName + "] " + r);
            }

            // Now take care of the next serialized one...

            // If we are waiting for a process to come up to handle the next
            // broadcast, then do nothing at this point.  Just in case, we
            // check that the process we're waiting for still exists.
            if (mPendingBroadcast != null) {
                if (DEBUG_BROADCAST_LIGHT) Slog.v(TAG_BROADCAST,
                        "processNextBroadcast [" + mQueueName + "]: waiting for "
                        + mPendingBroadcast.curApp);

                boolean isDead;
                synchronized (mService.mPidsSelfLocked) {
                    ProcessRecord proc = mService.mPidsSelfLocked.get(mPendingBroadcast.curApp.pid);
                    isDead = proc == null || proc.crashing;
                }
                if (!isDead) {
                    // It's still alive, so keep waiting
                    return;
                } else {
                    Slog.w(TAG, "pending app  ["
                            + mQueueName + "]" + mPendingBroadcast.curApp
                            + " died before responding to broadcast");
                    mPendingBroadcast.state = BroadcastRecord.IDLE;
                    mPendingBroadcast.nextReceiver = mPendingBroadcastRecvIndex;
                    mPendingBroadcast = null;
                }
            }

            boolean looped = false;
            
            do {
                if (mOrderedBroadcasts.size() == 0) {
                    // No more broadcasts pending, so all done!
                    mService.scheduleAppGcsLocked();
                    if (looped) {
                        // If we had finished the last ordered broadcast, then
                        // make sure all processes have correct oom and sched
                        // adjustments.
                        mService.updateOomAdjLocked();
                    }
                    return;
                }
                r = mOrderedBroadcasts.get(0);
                boolean forceReceive = false;

                // Ensure that even if something goes awry with the timeout
                // detection, we catch "hung" broadcasts here, discard them,
                // and continue to make progress.
                //
                // This is only done if the system is ready so that PRE_BOOT_COMPLETED
                // receivers don't get executed with timeouts. They're intended for
                // one time heavy lifting after system upgrades and can take
                // significant amounts of time.
                int numReceivers = (r.receivers != null) ? r.receivers.size() : 0;
                if (mService.mProcessesReady && r.dispatchTime > 0) {
                    long now = SystemClock.uptimeMillis();
                    //[+LEUI][RUBY-12263][zhangp]add for anr debug mechanism at 20160401
                    if ((numReceivers > 0) &&
                            (now > r.dispatchTime + (2*mTimeoutPeriod*numReceivers)) &&
                            !mService.isDidDexOpt(r.dispatchTime)) {
                        Slog.w(TAG, "Hung broadcast ["
                                + mQueueName + "] discarded after timeout failure:"
                                + " now=" + now
                                + " dispatchTime=" + r.dispatchTime
                                + " startTime=" + r.receiverTime
                                + " intent=" + r.intent
                                + " numReceivers=" + numReceivers
                                + " nextReceiver=" + r.nextReceiver
                                + " state=" + r.state);
                        broadcastTimeoutLocked(false); // forcibly finish this broadcast
                        forceReceive = true;
                        r.state = BroadcastRecord.IDLE;
                    }
                    //[+LEUI][RUBY-12263][zhangp]end
                }

                if (r.state != BroadcastRecord.IDLE) {
                    if (DEBUG_BROADCAST) Slog.d(TAG_BROADCAST,
                            "processNextBroadcast("
                            + mQueueName + ") called when not idle (state="
                            + r.state + ")");
                    return;
                }

                if (r.receivers == null || r.nextReceiver >= numReceivers
                        || r.resultAbort || forceReceive) {
                    // No more receivers for this broadcast!  Send the final
                    // result if requested...
                    if (r.resultTo != null) {
                        try {
                            if (DEBUG_BROADCAST) Slog.i(TAG_BROADCAST,
                                    "Finishing broadcast [" + mQueueName + "] "
                                    + r.intent.getAction() + " app=" + r.callerApp);
                            performReceiveLocked(r.callerApp, r.resultTo,
                                new Intent(r.intent), r.resultCode,
                                r.resultData, r.resultExtras, false, false, r.userId);
                            // Set this to null so that the reference
                            // (local and remote) isn't kept in the mBroadcastHistory.
                            r.resultTo = null;
                        } catch (RemoteException e) {
                            r.resultTo = null;
                            Slog.w(TAG, "Failure ["
                                    + mQueueName + "] sending broadcast result of "
                                    + r.intent, e);
                        }
                    }

                    if (DEBUG_BROADCAST) Slog.v(TAG_BROADCAST, "Cancelling BROADCAST_TIMEOUT_MSG");
                    cancelBroadcastTimeoutLocked();

                    if (DEBUG_BROADCAST_LIGHT) Slog.v(TAG_BROADCAST,
                            "Finished with ordered broadcast " + r);

                    // ... and on to the next...
                    addBroadcastToHistoryLocked(r);
                    mOrderedBroadcasts.remove(0);
                    r = null;
                    looped = true;
                    continue;
                }
            } while (r == null);

            // Get the next receiver...
            int recIdx = r.nextReceiver++;

            // Keep track of when this receiver started, and make sure there
            // is a timeout message pending to kill it if need be.
            r.receiverTime = SystemClock.uptimeMillis();
            //[+LEUI-24824]
            r.intent.setArg1(r.receiverTime);
            r.intent.setArg2(this.mQueueName.equals("foreground")?1:0);
            //[-LEUI-24824]
            if (recIdx == 0) {
                r.dispatchTime = r.receiverTime;
                r.dispatchClockTime = System.currentTimeMillis();
                if (DEBUG_BROADCAST_LIGHT) Slog.v(TAG_BROADCAST, "Processing ordered broadcast ["
                        + mQueueName + "] " + r);
            }
            if (! mPendingBroadcastTimeoutMessage) {
                long timeoutTime = r.receiverTime + mTimeoutPeriod;
                if (DEBUG_BROADCAST) Slog.v(TAG_BROADCAST,
                        "Submitting BROADCAST_TIMEOUT_MSG ["
                        + mQueueName + "] for " + r + " at " + timeoutTime);
                setBroadcastTimeoutLocked(timeoutTime);
            }

            final BroadcastOptions brOptions = r.options;
            final Object nextReceiver = r.receivers.get(recIdx);

            if (nextReceiver instanceof BroadcastFilter) {
                // Simple case: this is a registered receiver who gets
                // a direct call.
                BroadcastFilter filter = (BroadcastFilter)nextReceiver;
                if (DEBUG_BROADCAST)  Slog.v(TAG_BROADCAST,
                        "Delivering ordered ["
                        + mQueueName + "] to registered "
                        + filter + ": " + r);
                deliverToRegisteredReceiverLocked(r, filter, r.ordered);
                if (r.receiver == null || !r.ordered) {
                    // The receiver has already finished, so schedule to
                    // process the next one.
                    if (DEBUG_BROADCAST) Slog.v(TAG_BROADCAST, "Quick finishing ["
                            + mQueueName + "]: ordered="
                            + r.ordered + " receiver=" + r.receiver);
                    r.state = BroadcastRecord.IDLE;
                    scheduleBroadcastsLocked();
                } else {
                    if (brOptions != null && brOptions.getTemporaryAppWhitelistDuration() > 0) {
                        scheduleTempWhitelistLocked(filter.owningUid,
                                brOptions.getTemporaryAppWhitelistDuration(), r);
                    }
                }
                return;
            }

            // Hard case: need to instantiate the receiver, possibly
            // starting its application process to host it.

            ResolveInfo info =
                (ResolveInfo)nextReceiver;
            ComponentName component = new ComponentName(
                    info.activityInfo.applicationInfo.packageName,
                    info.activityInfo.name);

            boolean skip = false;
            int perm = mService.checkComponentPermission(info.activityInfo.permission,
                    r.callingPid, r.callingUid, info.activityInfo.applicationInfo.uid,
                    info.activityInfo.exported);
            if (perm != PackageManager.PERMISSION_GRANTED) {
                if (!info.activityInfo.exported) {
                    Slog.w(TAG, "Permission Denial: broadcasting "
                            + r.intent.toString()
                            + " from " + r.callerPackage + " (pid=" + r.callingPid
                            + ", uid=" + r.callingUid + ")"
                            + " is not exported from uid " + info.activityInfo.applicationInfo.uid
                            + " due to receiver " + component.flattenToShortString());
                } else {
                    Slog.w(TAG, "Permission Denial: broadcasting "
                            + r.intent.toString()
                            + " from " + r.callerPackage + " (pid=" + r.callingPid
                            + ", uid=" + r.callingUid + ")"
                            + " requires " + info.activityInfo.permission
                            + " due to receiver " + component.flattenToShortString());
                }
                skip = true;
            } else if (info.activityInfo.permission != null) {
                final int opCode = AppOpsManager.permissionToOpCode(info.activityInfo.permission);
                if (opCode != AppOpsManager.OP_NONE
                        && mService.mAppOpsService.noteOperationFB(opCode, r.callingUid,
                                r.callerPackage,true) != AppOpsManager.MODE_ALLOWED) {
                    Slog.w(TAG, "Appop Denial: broadcasting "
                            + r.intent.toString()
                            + " from " + r.callerPackage + " (pid="
                            + r.callingPid + ", uid=" + r.callingUid + ")"
                            + " requires appop " + AppOpsManager.permissionToOp(
                                    info.activityInfo.permission)
                            + " due to registered receiver "
                            + component.flattenToShortString());
                    skip = true;
                }
            }
            if (!skip && info.activityInfo.applicationInfo.uid != Process.SYSTEM_UID &&
                r.requiredPermissions != null && r.requiredPermissions.length > 0) {
                for (int i = 0; i < r.requiredPermissions.length; i++) {
                    String requiredPermission = r.requiredPermissions[i];
                    try {
                        perm = AppGlobals.getPackageManager().
                                checkPermission(requiredPermission,
                                        info.activityInfo.applicationInfo.packageName,
                                        UserHandle
                                                .getUserId(info.activityInfo.applicationInfo.uid));
                    } catch (RemoteException e) {
                        perm = PackageManager.PERMISSION_DENIED;
                    }
                    if (perm != PackageManager.PERMISSION_GRANTED) {
                        Slog.w(TAG, "Permission Denial: receiving "
                                + r.intent + " to "
                                + component.flattenToShortString()
                                + " requires " + requiredPermission
                                + " due to sender " + r.callerPackage
                                + " (uid " + r.callingUid + ")");
                        skip = true;
                        break;
                    }
                    int appOp = AppOpsManager.permissionToOpCode(requiredPermission);
                    if (appOp != AppOpsManager.OP_NONE && appOp != r.appOp
                            && mService.mAppOpsService.noteOperationFB(appOp,
                            info.activityInfo.applicationInfo.uid, info.activityInfo.packageName,true)
                            != AppOpsManager.MODE_ALLOWED) {
                        Slog.w(TAG, "Appop Denial: receiving "
                                + r.intent + " to "
                                + component.flattenToShortString()
                                + " requires appop " + AppOpsManager.permissionToOp(
                                requiredPermission)
                                + " due to sender " + r.callerPackage
                                + " (uid " + r.callingUid + ")");
                        skip = true;
                        break;
                    }
                }
            }
            if (!skip && r.appOp != AppOpsManager.OP_NONE
                    && mService.mAppOpsService.noteOperation(r.appOp,
                    info.activityInfo.applicationInfo.uid, info.activityInfo.packageName)
                    != AppOpsManager.MODE_ALLOWED) {
                Slog.w(TAG, "Appop Denial: receiving "
                        + r.intent + " to "
                        + component.flattenToShortString()
                        + " requires appop " + AppOpsManager.opToName(r.appOp)
                        + " due to sender " + r.callerPackage
                        + " (uid " + r.callingUid + ")");
                skip = true;
            }
            if (!skip) {
                skip = !mService.mIntentFirewall.checkBroadcast(r.intent, r.callingUid,
                        r.callingPid, r.resolvedType, info.activityInfo.applicationInfo.uid);
            }
            boolean isSingleton = false;
            try {
                isSingleton = mService.isSingleton(info.activityInfo.processName,
                        info.activityInfo.applicationInfo,
                        info.activityInfo.name, info.activityInfo.flags);
            } catch (SecurityException e) {
                Slog.w(TAG, e.getMessage());
                skip = true;
            }
            if ((info.activityInfo.flags&ActivityInfo.FLAG_SINGLE_USER) != 0) {
                if (ActivityManager.checkUidPermission(
                        android.Manifest.permission.INTERACT_ACROSS_USERS,
                        info.activityInfo.applicationInfo.uid)
                                != PackageManager.PERMISSION_GRANTED) {
                    Slog.w(TAG, "Permission Denial: Receiver " + component.flattenToShortString()
                            + " requests FLAG_SINGLE_USER, but app does not hold "
                            + android.Manifest.permission.INTERACT_ACROSS_USERS);
                    skip = true;
                }
            }
            if (r.curApp != null && r.curApp.crashing) {
                // If the target process is crashing, just skip it.
                Slog.w(TAG, "Skipping deliver ordered [" + mQueueName + "] " + r
                        + " to " + r.curApp + ": process crashing");
                skip = true;
            }
            if (!skip) {
                boolean isAvailable = false;
                try {
                    isAvailable = AppGlobals.getPackageManager().isPackageAvailable(
                            info.activityInfo.packageName,
                            UserHandle.getUserId(info.activityInfo.applicationInfo.uid));
                } catch (Exception e) {
                    // all such failures mean we skip this receiver
                    Slog.w(TAG, "Exception getting recipient info for "
                            + info.activityInfo.packageName, e);
                }
                if (!isAvailable) {
                    if (DEBUG_BROADCAST) Slog.v(TAG_BROADCAST,
                            "Skipping delivery to " + info.activityInfo.packageName + " / "
                            + info.activityInfo.applicationInfo.uid
                            + " : package no longer available");
                    skip = true;
                }
            }

            if (skip) {
                if (DEBUG_BROADCAST)  Slog.v(TAG_BROADCAST,
                        "Skipping delivery of ordered [" + mQueueName + "] "
                        + r + " for whatever reason");
                r.receiver = null;
                r.curFilter = null;
                r.state = BroadcastRecord.IDLE;
                scheduleBroadcastsLocked();
                return;
            }

            r.state = BroadcastRecord.APP_RECEIVE;
            String targetProcess = info.activityInfo.processName;
            r.curComponent = component;
            final int receiverUid = info.activityInfo.applicationInfo.uid;
            // If it's a singleton, it needs to be the same app or a special app
            if (r.callingUid != Process.SYSTEM_UID && isSingleton
                    && mService.isValidSingletonCall(r.callingUid, receiverUid)) {
                info.activityInfo = mService.getActivityInfoForUser(info.activityInfo, 0);
            }
            r.curReceiver = info.activityInfo;
            if (DEBUG_MU && r.callingUid > UserHandle.PER_USER_RANGE) {
                Slog.v(TAG_MU, "Updated broadcast record activity info for secondary user, "
                        + info.activityInfo + ", callingUid = " + r.callingUid + ", uid = "
                        + info.activityInfo.applicationInfo.uid);
            }

            if (brOptions != null && brOptions.getTemporaryAppWhitelistDuration() > 0) {
                scheduleTempWhitelistLocked(receiverUid,
                        brOptions.getTemporaryAppWhitelistDuration(), r);
            }

            // Broadcast is being executed, its package can't be stopped.
            try {
                AppGlobals.getPackageManager().setPackageStoppedState(
                        r.curComponent.getPackageName(), false, UserHandle.getUserId(r.callingUid));
            } catch (RemoteException e) {
            } catch (IllegalArgumentException e) {
                Slog.w(TAG, "Failed trying to unstop package "
                        + r.curComponent.getPackageName() + ": " + e);
            }

            ProcessRecord app = null;
            // Is this receiver's application already running?

            //[+LEUI] [REQ][LEUI-8957] [xulei] add 
            //for support double app
            boolean isDouble = false;

            try {
                    isDouble = AppGlobals.getPackageManager().isAppDouble(info.activityInfo.packageName);

                    if(isDouble && r.isShadow && (info.activityInfo.isShadow == false || info.activityInfo.applicationInfo.isShadow == false)){
                        info = AppGlobals.getPackageManager().getCloneResolveInfo(info);
                        if(DEBUG_DOUBLE_APP)
                        Slog.w(TAG, "double app after getCloneResolveInfo  r:"+r+",r.intent:"+r.intent+", Info:"+info.activityInfo+", targetProcess:"+targetProcess);
                    }
            } catch (RemoteException ex) {
                // pm is in same process, this will never happen.
            }

            if(info.activityInfo != null && info.activityInfo.isShadow && isDouble){
                app = mService.getProcessRecordLocked(targetProcess,
                        info.activityInfo.applicationInfo.uid + info.activityInfo.applicationInfo.uidOffset, false);
                if(DEBUG_DOUBLE_APP)
                 Slog.w(TAG, "double app info.activityInfo is clone r:"+r+", callerApp:"+r.callerApp+", targetProcess:"+targetProcess+"app:"+app);
            }else{
               //[+LEUI]end
                app = mService.getProcessRecordLocked(targetProcess,
                        info.activityInfo.applicationInfo.uid, false);
            }
            
            if (app != null && app.thread != null) {
                // [+LEUI] [REQ] [LEUI-13225] [quqixuan] added:feature for limit background apps.
                if(mService.isAllowAcquireResource(r.intent.getAction(), r.curComponent.getPackageName(), app.uid, app.pid, 1) == 0){
                    r.receiver = null;
                    r.curFilter = null;
                    r.curComponent = null;
                    r.curReceiver = null;
                    r.state = BroadcastRecord.IDLE;
                    scheduleBroadcastsLocked();
                    return;
                }
                // [-LEUI]
                try {
                    app.addPackage(info.activityInfo.packageName,
                            info.activityInfo.applicationInfo.versionCode, mService.mProcessStats);
                    processCurBroadcastLocked(r, app);
                    return;
                } catch (RemoteException e) {
                    Slog.w(TAG, "Exception when sending broadcast to "
                          + r.curComponent, e);
                } catch (RuntimeException e) {
                    Slog.wtf(TAG, "Failed sending broadcast to "
                            + r.curComponent + " with " + r.intent, e);
                    // If some unexpected exception happened, just skip
                    // this broadcast.  At this point we are not in the call
                    // from a client, so throwing an exception out from here
                    // will crash the entire system instead of just whoever
                    // sent the broadcast.
                    logBroadcastReceiverDiscardLocked(r);
                    finishReceiverLocked(r, r.resultCode, r.resultData,
                            r.resultExtras, r.resultAbort, false);
                    scheduleBroadcastsLocked();
                    // We need to reset the state if we failed to start the receiver.
                    r.state = BroadcastRecord.IDLE;
                    return;
                }

                // If a dead object exception was thrown -- fall through to
                // restart the application.
            }

            //[add start 20151110][yuanguohong][LEUI-10523]
            /* The application that has the current receiver hasn't been started.
             * Then check whether the application has the authority of auto-launch.
             * Execute the original logic when has the authority, otherwise skip the
             * current receiver, update status of broadcast record and then continue
             * to schedule.
             */
            boolean limit = isLimitSend(r, info);
            if(limit) {
                Slog.w(TAG, "don't launch " + info.activityInfo.applicationInfo.packageName + "/"
                        + info.activityInfo.applicationInfo.uid + " for broadcast " + r.intent);
                logBroadcastReceiverDiscardLocked(r);
                finishReceiverLocked(r, r.resultCode, r.resultData,
                        r.resultExtras, r.resultAbort, true);
                scheduleBroadcastsLocked();
                r.state = BroadcastRecord.IDLE;
                return;
            }
            //[add end 20151110]

            // Not running -- get it started, to be executed when the app comes up.
            if (DEBUG_BROADCAST)  Slog.v(TAG_BROADCAST,
                    "Need to start app ["
                    + mQueueName + "] " + targetProcess + " for broadcast " + r);
            if ((r.curApp=mService.startProcessLocked(targetProcess,
                    info.activityInfo.applicationInfo, true,
                    r.intent.getFlags() | Intent.FLAG_FROM_BACKGROUND,
                    "broadcast", r.curComponent,
                    (r.intent.getFlags()&Intent.FLAG_RECEIVER_BOOT_UPGRADE) != 0, false, false))
                            == null) {
                // Ah, this recipient is unavailable.  Finish it if necessary,
                // and mark the broadcast record as ready for the next.
                Slog.w(TAG, "Unable to launch app "
                        + info.activityInfo.applicationInfo.packageName + "/"
                        + info.activityInfo.applicationInfo.uid + " for broadcast "
                        + r.intent + ": process is bad");
                logBroadcastReceiverDiscardLocked(r);
                finishReceiverLocked(r, r.resultCode, r.resultData,
                        r.resultExtras, r.resultAbort, false);
                scheduleBroadcastsLocked();
                r.state = BroadcastRecord.IDLE;
                return;
            }

            mPendingBroadcast = r;
            mPendingBroadcastRecvIndex = recIdx;
        }
    }

    final void setBroadcastTimeoutLocked(long timeoutTime) {
        if (! mPendingBroadcastTimeoutMessage) {
            Message msg = mHandler.obtainMessage(BROADCAST_TIMEOUT_MSG, this);
            mHandler.sendMessageAtTime(msg, timeoutTime);
            mPendingBroadcastTimeoutMessage = true;
            LetvDebugManager.getInstance().sendEventAtTime(
                LetvDebugManager.START_MONITOR_BROADCAST_TIMEOUT_MSG,getCurrentOrderedBroadcastsPid(),
                timeoutTime - mTimeoutPeriod / 4,getCurrentOrderedBroadcastsProcessRecored());//when 3/4 timeout elapsed, predump debug info.
        }
    }

    final void cancelBroadcastTimeoutLocked() {
        if (mPendingBroadcastTimeoutMessage) {
            mHandler.removeMessages(BROADCAST_TIMEOUT_MSG, this);
            mPendingBroadcastTimeoutMessage = false;
            LetvDebugManager.getInstance().removeEvent(LetvDebugManager.START_MONITOR_BROADCAST_TIMEOUT_MSG,
                            getCurrentOrderedBroadcastsProcessRecored());
        }
    }

    final void broadcastTimeoutLocked(boolean fromMsg) {
        if (fromMsg) {
            mPendingBroadcastTimeoutMessage = false;
        }

        if (mOrderedBroadcasts.size() == 0) {
            return;
        }

        long now = SystemClock.uptimeMillis();
        BroadcastRecord r = mOrderedBroadcasts.get(0);
        if (fromMsg) {
            //[+LEUI][RUBY-12263][zhangp]add for anr debug mechanism at 20160401
            if (mService.mProcessesReady && mService.isDidDexOpt(SystemClock.uptimeMillis() - mTimeoutPeriod)) {
                Slog.d(TAG, "Skip BROADCAST_TIMEOUT ANR due to DexOpt performing: " + r);
                mService.mDidDexOpt = true;
            }
            //[+LEUI]end
            if (mService.mDidDexOpt) {
                // Delay timeouts until dexopt finishes.
                mService.mDidDexOpt = false;
                long timeoutTime = SystemClock.uptimeMillis() + mTimeoutPeriod;
                setBroadcastTimeoutLocked(timeoutTime);
                return;
            }
            if (!mService.mProcessesReady) {
                // Only process broadcast timeouts if the system is ready. That way
                // PRE_BOOT_COMPLETED broadcasts can't timeout as they are intended
                // to do heavy lifting for system up.
                return;
            }

            long timeoutTime = r.receiverTime + mTimeoutPeriod;
            if (timeoutTime > now) {
                // We can observe premature timeouts because we do not cancel and reset the
                // broadcast timeout message after each receiver finishes.  Instead, we set up
                // an initial timeout then kick it down the road a little further as needed
                // when it expires.
                if (DEBUG_BROADCAST) Slog.v(TAG_BROADCAST,
                        "Premature timeout ["
                        + mQueueName + "] @ " + now + ": resetting BROADCAST_TIMEOUT_MSG for "
                        + timeoutTime);
                setBroadcastTimeoutLocked(timeoutTime);
                return;
            }
        }

        BroadcastRecord br = mOrderedBroadcasts.get(0);
        if (br.state == BroadcastRecord.WAITING_SERVICES) {
            // In this case the broadcast had already finished, but we had decided to wait
            // for started services to finish as well before going on.  So if we have actually
            // waited long enough time timeout the broadcast, let's give up on the whole thing
            // and just move on to the next.
            Slog.i(TAG, "Waited long enough for: " + (br.curComponent != null
                    ? br.curComponent.flattenToShortString() : "(null)"));
            br.curComponent = null;
            br.state = BroadcastRecord.IDLE;
            processNextBroadcast(false);
            return;
        }

        Slog.w(TAG, "Timeout of broadcast " + r + " - receiver=" + r. receiver
                + ", started " + (now - r.receiverTime) + "ms ago");
        r.receiverTime = now;
        r.anrCount++;

        // Current receiver has passed its expiration date.
        if (r.nextReceiver <= 0) {
            Slog.w(TAG, "Timeout on receiver with nextReceiver <= 0");
            return;
        }

        ProcessRecord app = null;
        String anrMessage = null;

        Object curReceiver = r.receivers.get(r.nextReceiver-1);
        Slog.w(TAG, "Receiver during timeout: " + curReceiver);
        logBroadcastReceiverDiscardLocked(r);
        if (curReceiver instanceof BroadcastFilter) {
            BroadcastFilter bf = (BroadcastFilter)curReceiver;
            if (bf.receiverList.pid != 0
                    && bf.receiverList.pid != ActivityManagerService.MY_PID) {
                synchronized (mService.mPidsSelfLocked) {
                    app = mService.mPidsSelfLocked.get(
                            bf.receiverList.pid);
                }
            }
        } else {
            app = r.curApp;
        }

        if (app != null) {
            anrMessage = "Broadcast of " + r.intent.toString();
        }

        if (mPendingBroadcast == r) {
            mPendingBroadcast = null;
        }

        // Move on to the next receiver.
        finishReceiverLocked(r, r.resultCode, r.resultData,
                r.resultExtras, r.resultAbort, false);
        scheduleBroadcastsLocked();

        if (anrMessage != null) {
            // Post the ANR to the handler since we do not want to process ANRs while
            // potentially holding our lock.
            mHandler.post(new AppNotResponding(app, anrMessage));
        }
    }

    private final int ringAdvance(int x, final int increment, final int ringSize) {
        x += increment;
        if (x < 0) return (ringSize - 1);
        else if (x >= ringSize) return 0;
        else return x;
    }

    private final void addBroadcastToHistoryLocked(BroadcastRecord r) {
        if (r.callingUid < 0) {
            // This was from a registerReceiver() call; ignore it.
            return;
        }
        r.finishTime = SystemClock.uptimeMillis();

        mBroadcastHistory[mHistoryNext] = r;
        mHistoryNext = ringAdvance(mHistoryNext, 1, MAX_BROADCAST_HISTORY);

        mBroadcastSummaryHistory[mSummaryHistoryNext] = r.intent;
        mSummaryHistoryEnqueueTime[mSummaryHistoryNext] = r.enqueueClockTime;
        mSummaryHistoryDispatchTime[mSummaryHistoryNext] = r.dispatchClockTime;
        mSummaryHistoryFinishTime[mSummaryHistoryNext] = System.currentTimeMillis();
        mSummaryHistoryNext = ringAdvance(mSummaryHistoryNext, 1, MAX_BROADCAST_SUMMARY_HISTORY);
    }

    boolean cleanupDisabledPackageReceiversLocked(
            String packageName, Set<String> filterByClasses, int userId, boolean doit) {
        boolean didSomething = false;
        for (int i = mParallelBroadcasts.size() - 1; i >= 0; i--) {
            didSomething |= mParallelBroadcasts.get(i).cleanupDisabledPackageReceiversLocked(
                    packageName, filterByClasses, userId, doit);
            if (!doit && didSomething) {
                return true;
            }
        }

        for (int i = mOrderedBroadcasts.size() - 1; i >= 0; i--) {
            didSomething |= mOrderedBroadcasts.get(i).cleanupDisabledPackageReceiversLocked(
                    packageName, filterByClasses, userId, doit);
            if (!doit && didSomething) {
                return true;
            }
        }

        return didSomething;
    }

    final void logBroadcastReceiverDiscardLocked(BroadcastRecord r) {
        final int logIndex = r.nextReceiver - 1;
        if (logIndex >= 0 && logIndex < r.receivers.size()) {
            Object curReceiver = r.receivers.get(logIndex);
            if (curReceiver instanceof BroadcastFilter) {
                BroadcastFilter bf = (BroadcastFilter) curReceiver;
                EventLog.writeEvent(EventLogTags.AM_BROADCAST_DISCARD_FILTER,
                        bf.owningUserId, System.identityHashCode(r),
                        r.intent.getAction(), logIndex, System.identityHashCode(bf));
            } else {
                ResolveInfo ri = (ResolveInfo) curReceiver;
                EventLog.writeEvent(EventLogTags.AM_BROADCAST_DISCARD_APP,
                        UserHandle.getUserId(ri.activityInfo.applicationInfo.uid),
                        System.identityHashCode(r), r.intent.getAction(), logIndex, ri.toString());
            }
        } else {
            if (logIndex < 0) Slog.w(TAG,
                    "Discarding broadcast before first receiver is invoked: " + r);
            EventLog.writeEvent(EventLogTags.AM_BROADCAST_DISCARD_APP,
                    -1, System.identityHashCode(r),
                    r.intent.getAction(),
                    r.nextReceiver,
                    "NONE");
        }
    }

    final boolean dumpLocked(FileDescriptor fd, PrintWriter pw, String[] args,
            int opti, boolean dumpAll, String dumpPackage, boolean needSep) {
        SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");
        if (mParallelBroadcasts.size() > 0 || mOrderedBroadcasts.size() > 0
                || mPendingBroadcast != null) {
            boolean printed = false;
            for (int i = mParallelBroadcasts.size() - 1; i >= 0; i--) {
                BroadcastRecord br = mParallelBroadcasts.get(i);
                if (dumpPackage != null && !dumpPackage.equals(br.callerPackage)) {
                    continue;
                }
                if (!printed) {
                    if (needSep) {
                        pw.println();
                    }
                    needSep = true;
                    printed = true;
                    pw.println("  Active broadcasts [" + mQueueName + "]:");
                }
                pw.println("  Active Broadcast " + mQueueName + " #" + i + ":");
                br.dump(pw, "    ", sdf);
            }
            printed = false;
            needSep = true;
            for (int i = mOrderedBroadcasts.size() - 1; i >= 0; i--) {
                BroadcastRecord br = mOrderedBroadcasts.get(i);
                if (dumpPackage != null && !dumpPackage.equals(br.callerPackage)) {
                    continue;
                }
                if (!printed) {
                    if (needSep) {
                        pw.println();
                    }
                    needSep = true;
                    printed = true;
                    pw.println("  Active ordered broadcasts [" + mQueueName + "]:");
                }
                pw.println("  Active Ordered Broadcast " + mQueueName + " #" + i + ":");
                mOrderedBroadcasts.get(i).dump(pw, "    ", sdf);
            }
            if (dumpPackage == null || (mPendingBroadcast != null
                    && dumpPackage.equals(mPendingBroadcast.callerPackage))) {
                if (needSep) {
                    pw.println();
                }
                pw.println("  Pending broadcast [" + mQueueName + "]:");
                if (mPendingBroadcast != null) {
                    mPendingBroadcast.dump(pw, "    ", sdf);
                } else {
                    pw.println("    (null)");
                }
                needSep = true;
            }
        }

        int i;
        boolean printed = false;

        i = -1;
        int lastIndex = mHistoryNext;
        int ringIndex = lastIndex;
        do {
            // increasing index = more recent entry, and we want to print the most
            // recent first and work backwards, so we roll through the ring backwards.
            ringIndex = ringAdvance(ringIndex, -1, MAX_BROADCAST_HISTORY);
            BroadcastRecord r = mBroadcastHistory[ringIndex];
            if (r == null) {
                continue;
            }

            i++; // genuine record of some sort even if we're filtering it out
            if (dumpPackage != null && !dumpPackage.equals(r.callerPackage)) {
                continue;
            }
            if (!printed) {
                if (needSep) {
                    pw.println();
                }
                needSep = true;
                pw.println("  Historical broadcasts [" + mQueueName + "]:");
                printed = true;
            }
            if (dumpAll) {
                pw.print("  Historical Broadcast " + mQueueName + " #");
                        pw.print(i); pw.println(":");
                r.dump(pw, "    ", sdf);
            } else {
                pw.print("  #"); pw.print(i); pw.print(": "); pw.println(r);
                pw.print("    ");
                pw.println(r.intent.toShortString(false, true, true, false));
                if (r.targetComp != null && r.targetComp != r.intent.getComponent()) {
                    pw.print("    targetComp: "); pw.println(r.targetComp.toShortString());
                }
                Bundle bundle = r.intent.getExtras();
                if (bundle != null) {
                    pw.print("    extras: "); pw.println(bundle.toString());
                }
            }
        } while (ringIndex != lastIndex);

        if (dumpPackage == null) {
            lastIndex = ringIndex = mSummaryHistoryNext;
            if (dumpAll) {
                printed = false;
                i = -1;
            } else {
                // roll over the 'i' full dumps that have already been issued
                for (int j = i;
                        j > 0 && ringIndex != lastIndex;) {
                    ringIndex = ringAdvance(ringIndex, -1, MAX_BROADCAST_SUMMARY_HISTORY);
                    BroadcastRecord r = mBroadcastHistory[ringIndex];
                    if (r == null) {
                        continue;
                    }
                    j--;
                }
            }
            // done skipping; dump the remainder of the ring. 'i' is still the ordinal within
            // the overall broadcast history.
            do {
                ringIndex = ringAdvance(ringIndex, -1, MAX_BROADCAST_SUMMARY_HISTORY);
                Intent intent = mBroadcastSummaryHistory[ringIndex];
                if (intent == null) {
                    continue;
                }
                if (!printed) {
                    if (needSep) {
                        pw.println();
                    }
                    needSep = true;
                    pw.println("  Historical broadcasts summary [" + mQueueName + "]:");
                    printed = true;
                }
                if (!dumpAll && i >= 50) {
                    pw.println("  ...");
                    break;
                }
                i++;
                pw.print("  #"); pw.print(i); pw.print(": ");
                pw.println(intent.toShortString(false, true, true, false));
                pw.print("    ");
                TimeUtils.formatDuration(mSummaryHistoryDispatchTime[ringIndex]
                        - mSummaryHistoryEnqueueTime[ringIndex], pw);
                pw.print(" dispatch ");
                TimeUtils.formatDuration(mSummaryHistoryFinishTime[ringIndex]
                        - mSummaryHistoryDispatchTime[ringIndex], pw);
                pw.println(" finish");
                pw.print("    enq=");
                pw.print(sdf.format(new Date(mSummaryHistoryEnqueueTime[ringIndex])));
                pw.print(" disp=");
                pw.print(sdf.format(new Date(mSummaryHistoryDispatchTime[ringIndex])));
                pw.print(" fin=");
                pw.println(sdf.format(new Date(mSummaryHistoryFinishTime[ringIndex])));
                Bundle bundle = intent.getExtras();
                if (bundle != null) {
                    pw.print("    extras: "); pw.println(bundle.toString());
                }
            } while (ringIndex != lastIndex);
        }

        return needSep;
    }

    //[add start 20160808][yuanguohong][LEUI-19856]
    private final String[] mSourcePkgs = new String[] {
        "com.stv.stvpush"
    };

    private final String[] mTargetPkgs = new String[] {
        "com.sina.weibo"
    };

    private boolean isNeedCheck(BroadcastRecord r, ResolveInfo info) {
        String sourcePkg = r.callerPackage;
        if (sourcePkg != null && !ArrayUtils.isEmpty(mSourcePkgs)
                && ArrayUtils.contains(mSourcePkgs, sourcePkg)) {
            String targetPkg = info.activityInfo.applicationInfo.packageName;
            if(DEBUG_BROADCAST) Slog.w(TAG, "isNeedCheck: sourcePkg = " + sourcePkg + ", targetPkg = " + targetPkg);
            if (targetPkg != null && !ArrayUtils.isEmpty(mTargetPkgs)
                    && ArrayUtils.contains(mTargetPkgs, targetPkg)) {
                return true;
            }

            boolean hasSystemFlag = (info.activityInfo.applicationInfo.flags & ApplicationInfo.FLAG_SYSTEM) != 0;
            boolean hasExOpFlag = (info.activityInfo.applicationInfo.flagsEx & ApplicationInfo.FLAG_EX_OPERATOR) != 0;
            if(DEBUG_BROADCAST) Slog.w(TAG, "isNeedCheck: hasSystemFlag = " + hasSystemFlag + ", hasExOpFlag = " + hasExOpFlag);
            int infoUid = info.activityInfo.applicationInfo.uid;
            if (infoUid >= Process.FIRST_APPLICATION_UID
                    && infoUid <= Process.LAST_APPLICATION_UID
                    && !hasSystemFlag && !hasExOpFlag) {
                return true;
            }

            boolean hasCheckFlag = (r.intent.getEuiFlags() & Intent.EUI_FLAG_NEED_CHECK_AUTO_LAUNCH_PERMISSION) != 0;
            if (DEBUG_BROADCAST) Slog.w(TAG, "need check auto launch permission for "
                    + r.intent.getAction()  + ": " + (hasCheckFlag ? "true" : "false"));
            if (hasCheckFlag)
                return true;
            else
                return false;
        }

        return true;
    }

    private boolean isLimitSend(BroadcastRecord r, ResolveInfo info) {
        boolean limit = false;
        boolean isNeedCheck = isNeedCheck(r, info);
        try {
            if (isNeedCheck) {
                int infoUid = info.activityInfo.applicationInfo.uid;
                int curUid = r.curReceiver.applicationInfo.uid;
                String infoPkg = info.activityInfo.applicationInfo.packageName;
                int check = mService.mAppOpsService.checkOperation(AppOpsManager.OP_BOOT_COMPLETED, infoUid, infoPkg);
                if (DEBUG_BROADCAST) {
                    Slog.w(TAG, "check = " + check
                            + ", curUid = " + curUid
                            + ", infoUid = " + infoUid
                            + ", r.callingUid = " + r.callingUid
                            + ", r.callingPid = " + r.callingPid
                            + ", r.callerApp = " + r.callerApp);
                }
                if (check != AppOpsManager.MODE_ALLOWED) {
                    if (DEBUG_BROADCAST) {
                        boolean isWidgetAction = r.intent.toString().contains("android.appwidget.action");
                        boolean isFromAlarmMS = r.callingPid == -1 && r.callerApp == null && curUid == r.callingUid
                                && infoPkg.equals(r.callerPackage) && mService.isAlarmWhiteApp(infoPkg);
                        boolean hasAppStarted = mService.hasAppStarted(infoPkg, null);
                        Slog.w(TAG, "isWidgetAction = " + isWidgetAction
                                + ", isFromAlarmMS = " + isFromAlarmMS
                                + ", hasAppStarted = " + hasAppStarted);
                    }
                    if (!r.intent.toString().contains("android.appwidget.action")
                           && !(r.callingPid == -1 && r.callerApp == null && curUid == r.callingUid
                           && infoPkg.equals(r.callerPackage) && mService.isAlarmWhiteApp(infoPkg))
                           && !mService.hasAppStarted(infoPkg, null)) {
                        limit = true;
                    }
                }
            }
        } catch (Exception e) {
            Slog.e(TAG, e + "");
        }

        return limit;
    }
    //[add end 20160808]

	int getCurrentOrderedBroadcastsPid() {
        int pid = -1;
        synchronized(mService) {
            if (mOrderedBroadcasts.size() > 0) {
                BroadcastRecord  br = mOrderedBroadcasts.get(0);
                if (br != null && br.curApp != null) {
                    pid = br.curApp.pid;
                }
                if(br != null && pid<=0)
                    pid = br.callingPid;
            }
        }
        return pid;
    }

    ProcessRecord getCurrentOrderedBroadcastsProcessRecored() {
        int pid = -1;
        ProcessRecord proc= null;
        synchronized(mService) {
            if (mOrderedBroadcasts.size() > 0) {
                BroadcastRecord  br = mOrderedBroadcasts.get(0);
                if (br != null && br.curApp != null) {
                    pid = br.curApp.pid;
                    proc = br.curApp;
                }
                if(br != null && pid<=0)
                    pid = br.callingPid;
                    proc = br.callerApp;
            }
        }
        return proc;
     }
    //[LEUI] [TASK] checktime to log slow operation in app
    private void checkTime(long startTime, String where,long checkTimeout) {
        long now = SystemClock.uptimeMillis();
        if ((now-startTime) > checkTimeout) {
            // If we are taking more than checkpoint time, log about it.
            Slog.w(TAG, this.mQueueName+ " Slow operation: " + (now-startTime) + "ms so far, now at " + where);
        }
    }

    private int getTimeoutToCheck(){
        if(this.mQueueName.equals("foreground"))
            return 2000;//2000ms mService.BROADCAST_FG_TIMEOUT;
        else //if(this.mQueueName.equals("background")) // same as innerbackground
            return 5000;// 5s
    }
}
