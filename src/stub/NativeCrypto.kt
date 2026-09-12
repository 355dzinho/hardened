package com.anon.stub

import android.app.Activity

object NativeCrypto {
    init { System.loadLibrary("anoncrypto") }
    external fun boot(activity: Activity)
}
