package com.anon.real;
import android.app.Activity;
import android.graphics.Color;
import android.view.Gravity;
import android.widget.Button;
import android.widget.LinearLayout;
import android.widget.ScrollView;
import android.widget.TextView;
import android.widget.Toast;
public class RealApp {
    private Activity activity;
    private TextView output;
    public RealApp() {}
    public void start(Activity a) {
        this.activity = a;
        LinearLayout root = new LinearLayout(a);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setPadding(40, 80, 40, 40);
        root.setBackgroundColor(0xFF0E0C0C);
        TextView t = new TextView(a);
        t.setText("app real");
        t.setTextSize(22f); t.setTextColor(Color.WHITE); t.setGravity(Gravity.CENTER);
        root.addView(t);
        TextView sub = new TextView(a);
        sub.setText("gate 100% nativo · anti-tamper");
        sub.setTextSize(12f); sub.setTextColor(0xFF888888);
        sub.setPadding(0,10,0,40); sub.setGravity(Gravity.CENTER);
        root.addView(sub);
        Button b1 = new Button(a); b1.setText("logica secreta");
        b1.setOnClickListener(v -> runSecret()); root.addView(b1);
        Button b2 = new Button(a); b2.setText("calculo interno");
        b2.setOnClickListener(v -> runCalc()); root.addView(b2);
        output = new TextView(a); output.setTextSize(12f); output.setTextColor(0xFFCCCCCC);
        output.setPadding(0,40,0,0); root.addView(output);
        ScrollView sc = new ScrollView(a); sc.addView(root); a.setContentView(sc);
    }
    private void runSecret() { log("token: " + deriveToken()); Toast.makeText(activity,"ok",Toast.LENGTH_SHORT).show(); }
    private void runCalc() { int[] d={3,7,11,19,23,31}; int s=0; for(int x:d) s+=transform(x); log("calculo: "+s); }
    private int transform(int x){ return (x*7+13)^0x5A; }
    private String deriveToken() {
        long h = System.currentTimeMillis()/1000L;
        for(int i=0;i<5;i++) h=(h*6364136223846793005L+1442695040888963407L);
        return Long.toHexString(h).substring(0,16);
    }
    private void log(String s){ output.append(s+"\n"); }
}
