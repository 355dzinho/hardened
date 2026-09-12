package com.anon.stub

import android.app.Activity
import android.os.Bundle

class StubActivity : Activity() {
    override fun onCreate(b: Bundle?) {
        super.onCreate(b)
        NativeCrypto.boot(this)
    }
}
