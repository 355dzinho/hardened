#define _GNU_SOURCE
#include <jni.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <time.h>
#include <sys/syscall.h>
#include <link.h>
#include <dlfcn.h>
#include <pthread.h>
#include <signal.h>
#include <android/log.h>

#define LOGE(...) __android_log_print(ANDROID_LOG_ERROR, "vmp", __VA_ARGS__)

// ---------- constantes ----------
static const uint8_t KEY_A[16] = {0x61,0x6E,0x6F,0x6E,0x2D,0x73,0x65,0x63,0x72,0x65,0x74,0x2D,0x6B,0x65,0x79,0x2D};
static const uint8_t KEY_B[16] = {0x32,0x30,0x32,0x36,0x2D,0x78,0x6F,0x72,0x2D,0x6D,0x69,0x78,0x2D,0x76,0x31,0x21};
static const uint8_t SALT_A[8] = {0x61,0x6E,0x6F,0x6E,0x2D,0x73,0x61,0x6C};
static const uint8_t SALT_B[8] = {0x74,0x2D,0x68,0x6D,0x61,0x63,0x2D,0x76};

// preenchidos no build
static uint8_t DEX_EXPECTED_HASH[32] = { 0 };
static uint8_t STUB_EXPECTED_HASH[32] = { 0 };

// ---------- SHA-256 ----------
typedef struct { uint32_t state[8]; uint64_t bitlen; uint8_t buffer[64]; size_t buflen; } sha256_ctx;
static const uint32_t K256[64] = {
0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
#define ROTR(x,n) (((x)>>(n))|((x)<<(32-(n))))
static void sha256_init(sha256_ctx* c){c->state[0]=0x6a09e667;c->state[1]=0xbb67ae85;c->state[2]=0x3c6ef372;c->state[3]=0xa54ff53a;c->state[4]=0x510e527f;c->state[5]=0x9b05688c;c->state[6]=0x1f83d9ab;c->state[7]=0x5be0cd19;c->bitlen=0;c->buflen=0;}
static void sha256_transform(sha256_ctx* c,const uint8_t* d){
uint32_t w[64];
for(int i=0;i<16;i++)w[i]=(d[i*4]<<24)|(d[i*4+1]<<16)|(d[i*4+2]<<8)|d[i*4+3];
for(int i=16;i<64;i++){uint32_t s0=ROTR(w[i-15],7)^ROTR(w[i-15],18)^(w[i-15]>>3);uint32_t s1=ROTR(w[i-2],17)^ROTR(w[i-2],19)^(w[i-2]>>10);w[i]=w[i-16]+s0+w[i-7]+s1;}
uint32_t a=c->state[0],b=c->state[1],cc=c->state[2],dd=c->state[3],e=c->state[4],f=c->state[5],g=c->state[6],h=c->state[7];
for(int i=0;i<64;i++){uint32_t S1=ROTR(e,6)^ROTR(e,11)^ROTR(e,25);uint32_t ch=(e&f)^((~e)&g);uint32_t t1=h+S1+ch+K256[i]+w[i];uint32_t S0=ROTR(a,2)^ROTR(a,13)^ROTR(a,22);uint32_t maj=(a&b)^(a&cc)^(b&cc);uint32_t t2=S0+maj;h=g;g=f;f=e;e=dd+t1;dd=cc;cc=b;b=a;a=t1+t2;}
c->state[0]+=a;c->state[1]+=b;c->state[2]+=cc;c->state[3]+=dd;c->state[4]+=e;c->state[5]+=f;c->state[6]+=g;c->state[7]+=h;}
static void sha256_update(sha256_ctx* c,const uint8_t* d,size_t len){for(size_t i=0;i<len;i++){c->buffer[c->buflen++]=d[i];if(c->buflen==64){sha256_transform(c,c->buffer);c->bitlen+=512;c->buflen=0;}}}
static void sha256_final(sha256_ctx* c,uint8_t* out){
uint64_t bl=c->bitlen+c->buflen*8;
c->buffer[c->buflen++]=0x80;
if(c->buflen>56){while(c->buflen<64)c->buffer[c->buflen++]=0;sha256_transform(c,c->buffer);c->buflen=0;}
while(c->buflen<56)c->buffer[c->buflen++]=0;
for(int i=7;i>=0;i--)c->buffer[c->buflen++]=(bl>>(i*8))&0xFF;
sha256_transform(c,c->buffer);
for(int i=0;i<8;i++){out[i*4]=(c->state[i]>>24)&0xFF;out[i*4+1]=(c->state[i]>>16)&0xFF;out[i*4+2]=(c->state[i]>>8)&0xFF;out[i*4+3]=c->state[i]&0xFF;}}
static void sha256(const uint8_t* d, size_t len, uint8_t* out){
  sha256_ctx c; sha256_init(&c); sha256_update(&c, d, len); sha256_final(&c, out);
}

// ---------- HMAC ----------
static void hmac_sha256(const uint8_t* key,size_t klen,const uint8_t* data,size_t dlen,uint8_t* out){
uint8_t k[64]={0};
if(klen>64){sha256(key,klen,k);}else memcpy(k,key,klen);
uint8_t ipad[64],opad[64];
for(int i=0;i<64;i++){ipad[i]=k[i]^0x36;opad[i]=k[i]^0x5c;}
sha256_ctx c;uint8_t inner[32];
sha256_init(&c);sha256_update(&c,ipad,64);sha256_update(&c,data,dlen);sha256_final(&c,inner);
sha256_init(&c);sha256_update(&c,opad,64);sha256_update(&c,inner,32);sha256_final(&c,out);}

// ---------- PBKDF2 ----------
static void pbkdf2(const uint8_t* pw,size_t pwlen,const uint8_t* salt,size_t saltlen,uint32_t iters,uint8_t* out,size_t outlen){
uint32_t blocks=(outlen+31)/32;
for(uint32_t b=1;b<=blocks;b++){
uint8_t salt_block[256];memcpy(salt_block,salt,saltlen);
salt_block[saltlen]=(b>>24)&0xFF;salt_block[saltlen+1]=(b>>16)&0xFF;salt_block[saltlen+2]=(b>>8)&0xFF;salt_block[saltlen+3]=b&0xFF;
uint8_t u[32],t[32];hmac_sha256(pw,pwlen,salt_block,saltlen+4,u);memcpy(t,u,32);
for(uint32_t i=1;i<iters;i++){hmac_sha256(pw,pwlen,u,32,u);for(int j=0;j<32;j++)t[j]^=u[j];}
size_t off=(b-1)*32;size_t n=(outlen-off<32)?(outlen-off):32;memcpy(out+off,t,n);}}

// ---------- AES-256 ----------
static const uint8_t sbox[256]={0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16};
static const uint8_t inv_sbox[256]={0x52,0x09,0x6a,0xd5,0x30,0x36,0xa5,0x38,0xbf,0x40,0xa3,0x9e,0x81,0xf3,0xd7,0xfb,0x7c,0xe3,0x39,0x82,0x9b,0x2f,0xff,0x87,0x34,0x8e,0x43,0x44,0xc4,0xde,0xe9,0xcb,0x54,0x7b,0x94,0x32,0xa6,0xc2,0x23,0x3d,0xee,0x4c,0x95,0x0b,0x42,0xfa,0xc3,0x4e,0x08,0x2e,0xa1,0x66,0x28,0xd9,0x24,0xb2,0x76,0x5b,0xa2,0x49,0x6d,0x8b,0xd1,0x25,0x72,0xf8,0xf6,0x64,0x86,0x68,0x98,0x16,0xd4,0xa4,0x5c,0xcc,0x5d,0x65,0xb6,0x92,0x6c,0x70,0x48,0x50,0xfd,0xed,0xb9,0xda,0x5e,0x15,0x46,0x57,0xa7,0x8d,0x9d,0x84,0x90,0xd8,0xab,0x00,0x8c,0xbc,0xd3,0x0a,0xf7,0xe4,0x58,0x05,0xb8,0xb3,0x45,0x06,0xd0,0x2c,0x1e,0x8f,0xca,0x3f,0x0f,0x02,0xc1,0xaf,0xbd,0x03,0x01,0x13,0x8a,0x6b,0x3a,0x91,0x11,0x41,0x4f,0x67,0xdc,0xea,0x97,0xf2,0xcf,0xce,0xf0,0xb4,0xe6,0x73,0x96,0xac,0x74,0x22,0xe7,0xad,0x35,0x85,0xe2,0xf9,0x37,0xe8,0x1c,0x75,0xdf,0x6e,0x47,0xf1,0x1a,0x71,0x1d,0x29,0xc5,0x89,0x6f,0xb7,0x62,0x0e,0xaa,0x18,0xbe,0x1b,0xfc,0x56,0x3e,0x4b,0xc6,0xd2,0x79,0x20,0x9a,0xdb,0xc0,0xfe,0x78,0xcd,0x5a,0xf4,0x1f,0xdd,0xa8,0x33,0x88,0x07,0xc7,0x31,0xb1,0x12,0x10,0x59,0x27,0x80,0xec,0x5f,0x60,0x51,0x7f,0xa9,0x19,0xb5,0x4a,0x0d,0x2d,0xe5,0x7a,0x9f,0x93,0xc9,0x9c,0xef,0xa0,0xe0,0x3b,0x4d,0xae,0x2a,0xf5,0xb0,0xc8,0xeb,0xbb,0x3c,0x83,0x53,0x99,0x61,0x17,0x2b,0x04,0x7e,0xba,0x77,0xd6,0x26,0xe1,0x69,0x14,0x63,0x55,0x21,0x0c,0x7d};
static uint8_t xtime(uint8_t x){return (x<<1)^((x>>7)*0x1b);}
static uint8_t mul(uint8_t a,uint8_t b){uint8_t p=0;for(int i=0;i<8;i++){if(b&1)p^=a;uint8_t hi=a&0x80;a<<=1;if(hi)a^=0x1b;b>>=1;}return p;}
typedef struct{uint8_t rk[240];int rounds;}aes_ctx;
static void aes_expand_key(aes_ctx* ctx,const uint8_t* key,int keylen){
int nk=keylen/4;ctx->rounds=nk+6;memcpy(ctx->rk,key,keylen);uint8_t rcon=1;
for(int i=nk;i<4*(ctx->rounds+1);i++){uint8_t t[4];memcpy(t,ctx->rk+(i-1)*4,4);
if(i%nk==0){uint8_t tmp=t[0];t[0]=sbox[t[1]]^rcon;t[1]=sbox[t[2]];t[2]=sbox[t[3]];t[3]=sbox[tmp];rcon=xtime(rcon);}
else if(nk>6&&i%nk==4){t[0]=sbox[t[0]];t[1]=sbox[t[1]];t[2]=sbox[t[2]];t[3]=sbox[t[3]];}
for(int j=0;j<4;j++)ctx->rk[i*4+j]=ctx->rk[(i-nk)*4+j]^t[j];}}
static void aes_decrypt_block(aes_ctx* ctx,const uint8_t* in,uint8_t* out){
uint8_t s[16];memcpy(s,in,16);
for(int i=0;i<16;i++)s[i]^=ctx->rk[ctx->rounds*16+i];
for(int r=ctx->rounds-1;r>=1;r--){
uint8_t t[16];t[0]=s[0];t[1]=s[13];t[2]=s[10];t[3]=s[7];t[4]=s[4];t[5]=s[1];t[6]=s[14];t[7]=s[11];t[8]=s[8];t[9]=s[5];t[10]=s[2];t[11]=s[15];t[12]=s[12];t[13]=s[9];t[14]=s[6];t[15]=s[3];
for(int i=0;i<16;i++)s[i]=inv_sbox[t[i]];
for(int i=0;i<16;i++)s[i]^=ctx->rk[r*16+i];
for(int c=0;c<4;c++){uint8_t a0=s[c*4],a1=s[c*4+1],a2=s[c*4+2],a3=s[c*4+3];
s[c*4]=mul(a0,14)^mul(a1,11)^mul(a2,13)^mul(a3,9);s[c*4+1]=mul(a0,9)^mul(a1,14)^mul(a2,11)^mul(a3,13);
s[c*4+2]=mul(a0,13)^mul(a1,9)^mul(a2,14)^mul(a3,11);s[c*4+3]=mul(a0,11)^mul(a1,13)^mul(a2,9)^mul(a3,14);}}
uint8_t t[16];t[0]=s[0];t[1]=s[13];t[2]=s[10];t[3]=s[7];t[4]=s[4];t[5]=s[1];t[6]=s[14];t[7]=s[11];t[8]=s[8];t[9]=s[5];t[10]=s[2];t[11]=s[15];t[12]=s[12];t[13]=s[9];t[14]=s[6];t[15]=s[3];
for(int i=0;i<16;i++)s[i]=inv_sbox[t[i]];
for(int i=0;i<16;i++)s[i]^=ctx->rk[i];
memcpy(out,s,16);}
static void aes_cbc_decrypt(const uint8_t* key,int keylen,const uint8_t* iv,const uint8_t* in,size_t len,uint8_t* out){
aes_ctx ctx;aes_expand_key(&ctx,key,keylen);uint8_t prev[16];memcpy(prev,iv,16);
for(size_t off=0;off<len;off+=16){uint8_t block[16];aes_decrypt_block(&ctx,in+off,block);
for(int i=0;i<16;i++)out[off+i]=block[i]^prev[i];memcpy(prev,in+off,16);}}
static size_t strip_pkcs7(const uint8_t* data,size_t len){
if(len==0)return 0;uint8_t pad=data[len-1];
if(pad==0||pad>16||pad>len)return len;
for(size_t i=len-pad;i<len;i++)if(data[i]!=pad)return len;
return len-pad;}

// ---------- anti-frida nativo ----------
static const char* _p1="frid"; static const char* _p2="a";
static const char* _q1="gadg"; static const char* _q2="et";
static int contains_case(const char* hay,size_t hay_len,const char* needle){
size_t nlen=strlen(needle);if(nlen==0||nlen>hay_len)return 0;
for(size_t i=0;i+nlen<=hay_len;i++){size_t j=0;
while(j<nlen){char a=hay[i+j],b=needle[j];
if(a>='A'&&a<='Z')a+=32;if(b>='A'&&b<='Z')b+=32;
if(a!=b)break;j++;}
if(j==nlen)return 1;}
return 0;}
static long read_file_syscall(const char* path,char* buf,size_t cap){
long fd=syscall(SYS_openat,AT_FDCWD,path,O_RDONLY,0);
if(fd<0)return -1;long total=0;
while(total<(long)cap-1){long n=syscall(SYS_read,fd,buf+total,cap-1-total);if(n<=0)break;total+=n;}
buf[total]=0;syscall(SYS_close,fd);return total;}

// ---------- JNI helpers ----------
static int cmp_hash(const uint8_t* a, const uint8_t* b) {
  uint8_t d = 0;
  for (int i = 0; i < 32; i++) d |= (a[i] ^ b[i]);
  return d == 0;
}

// lê classes.dex de dentro do próprio APK e compara com STUB_EXPECTED_HASH
static int verify_stub_integrity(JNIEnv* env, jobject activity) {
  // pega getPackageCodePath()
  jclass ctxCls = (*env)->GetObjectClass(env, activity);
  jmethodID getCodePath = (*env)->GetMethodID(env, ctxCls, "getPackageCodePath", "()Ljava/lang/String;");
  jstring jpath = (jstring)(*env)->CallObjectMethod(env, activity, getCodePath);
  const char* apkPath = (*env)->GetStringUTFChars(env, jpath, NULL);

  // abre o zip via minizip simplificado: usa zlib do Android (libz)
  // como não linkamos libz, usa open + parse manual do diretório central
  // simplificação: procura pela entry "classes.dex" no buffer do APK
  FILE* f = fopen(apkPath, "rb");
  if (!f) { (*env)->ReleaseStringUTFChars(env, jpath, apkPath); return 0; }
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  uint8_t* apk = (uint8_t*)malloc(sz);
  if (!apk) { fclose(f); (*env)->ReleaseStringUTFChars(env, jpath, apkPath); return 0; }
  fread(apk, 1, sz, f); fclose(f);
  (*env)->ReleaseStringUTFChars(env, jpath, apkPath);

  // parse ZIP central directory — procura por "classes.dex"
  // ... simplificado: procura pela string "classes.dex" no diretório
  // depois lê compressed_size e uncompressed_size pra extrair
  // (implementação real precisa inflate, mas o dex do stub é pequeno e
  //  frequentemente stored — se for deflated, precisa libz)

  // POC: hash do APK inteiro (não do classes.dex). Funciona pq qualquer
  // edição no smali altera o APK, e o hash do APK inteiro muda.
  // Se editar o smali, o APK tem que ser reassinado, e o hash do APK muda.
  uint8_t actual[32];
  sha256(apk, sz, actual);
  free(apk);

  if (!cmp_hash(actual, STUB_EXPECTED_HASH)) {
    LOGE("stub tampered");
    return 0;
  }
  return 1;
}

// signature check via JNI
static int verify_signature(JNIEnv* env, jobject activity) {
  // getPackageManager()
  jclass ctxCls = (*env)->GetObjectClass(env, activity);
  jmethodID getPM = (*env)->GetMethodID(env, ctxCls, "getPackageManager", "()Landroid/content/pm/PackageManager;");
  jobject pm = (*env)->CallObjectMethod(env, activity, getPM);
  if (!pm) return 0;

  // getPackageName()
  jmethodID getPkgName = (*env)->GetMethodID(env, ctxCls, "getPackageName", "()Ljava/lang/String;");
  jstring jpkg = (jstring)(*env)->CallObjectMethod(env, activity, getPkgName);

  // getPackageInfo(String, int) com GET_SIGNATURES = 64
  jclass pmCls = (*env)->GetObjectClass(env, pm);
  jmethodID getInfo = (*env)->GetMethodID(env, pmCls, "getPackageInfo",
    "(Ljava/lang/String;I)Landroid/content/pm/PackageInfo;");
  jobject info = (*env)->CallObjectMethod(env, pm, getInfo, jpkg, 64);
  if (!info) return 0;

  // info.signatures[0]
  jclass infoCls = (*env)->GetObjectClass(env, info);
  jfieldID sigsField = (*env)->GetFieldID(env, infoCls, "signatures", "[Landroid/content/pm/Signature;");
  jobjectArray sigs = (jobjectArray)(*env)->GetObjectField(env, info, sigsField);
  if (!sigs || (*env)->GetArrayLength(env, sigs) == 0) return 0;
  jobject sig = (*env)->GetObjectArrayElement(env, sigs, 0);

  // sig.toByteArray()
  jclass sigCls = (*env)->GetObjectClass(env, sig);
  jmethodID toBytes = (*env)->GetMethodID(env, sigCls, "toByteArray", "()[B");
  jbyteArray sigBytes = (jbyteArray)(*env)->CallObjectMethod(env, sig, toBytes);
  if (!sigBytes) return 0;

  jsize n = (*env)->GetArrayLength(env, sigBytes);
  jbyte* b = (*env)->GetByteArrayElements(env, sigBytes, NULL);

  uint8_t computed[32];
  sha256((const uint8_t*)b, n, computed);

  (*env)->ReleaseByteArrayElements(env, sigBytes, b, JNI_ABORT);

  // compara com CERT_SHA (que está no .so, não no Java)
  static const uint8_t CERT[32] = { 0 };  // injetado no build
  return cmp_hash(computed, CERT);
}

// ---------- boot: gate inteiro ----------
static uint8_t* g_dex_buf = NULL;
static size_t   g_dex_len = 0;

__attribute__((visibility("default")))
JNIEXPORT void JNICALL Java_com_anon_stub_NativeCrypto_boot(JNIEnv* env, jclass clazz, jobject activity) {
  LOGE("boot");

  int tampered = 0;

  // 1. anti-frida
  char maps[65536];
  if (read_file_syscall("/proc/self/maps", maps, sizeof(maps)) > 0) {
    if (contains_case(maps, strlen(maps), _p1) && contains_case(maps, strlen(maps), _p2)) tampered = 1;
    if (contains_case(maps, strlen(maps), _q1) && contains_case(maps, strlen(maps), _q2)) tampered = 1;
  }
  char status[4096];
  if (read_file_syscall("/proc/self/status", status, sizeof(status)) > 0) {
    for (long i = 0; i + 10 < (long)strlen(status); i++) {
      if (memcmp(status + i, "TracerPid:", 10) == 0) {
        long pid = atol(status + i + 10);
        if (pid != 0) tampered = 1;
      }
    }
  }

  // 2. stub integrity via signature (cobre edição de smali)
  // hash do APK tem problema de auto-referência (o .so está dentro do APK),
  // então confiamos na assinatura — editar smali exige reassinar.
  // (verificação de assinatura está no passo 3, abaixo)

  // 3. signature check
  if (!verify_signature(env, activity)) tampered = 1;

  // 4. carrega o dex apropriado
  jclass cls = NULL;
  const char* targetClass = "com.anon.real.RealApp";

  // pega Context pra ler recursos
  jclass ctxCls = (*env)->GetObjectClass(env, activity);
  jmethodID getRes = (*env)->GetMethodID(env, ctxCls, "getResources", "()Landroid/content/res/Resources;");
  jobject res = (*env)->CallObjectMethod(env, activity, getRes);
  jmethodID getRawId = (*env)->GetMethodID(env, (*env)->GetObjectClass(env, res),
    "getIdentifier", "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)I");
  jmethodID getPkgName = (*env)->GetMethodID(env, ctxCls, "getPackageName", "()Ljava/lang/String;");
  jstring pkg = (jstring)(*env)->CallObjectMethod(env, activity, getPkgName);
  jstring vStr = (*env)->NewStringUTF(env, "v");
  jstring rawStr = (*env)->NewStringUTF(env, "raw");
  jint rid = (*env)->CallIntMethod(env, res, getRawId, vStr, rawStr, pkg);

  if (rid == 0) { LOGE("raw/v not found"); return; }

  // openRawResource
  jmethodID openRaw = (*env)->GetMethodID(env, (*env)->GetObjectClass(env, res),
    "openRawResource", "(I)Ljava/io/InputStream;");
  jobject is = (*env)->CallObjectMethod(env, res, openRaw, rid);

  // lê tudo via readAllBytes (API 33+? — usa read loop)
  jclass isCls = (*env)->GetObjectClass(env, is);
  jmethodID read = (*env)->GetMethodID(env, isCls, "read", "([B)I");
  jbyteArray buf = (*env)->NewByteArray(env, 65536);
  uint8_t* blob = NULL;
  size_t blob_len = 0;
  while (1) {
    jint n = (*env)->CallIntMethod(env, is, read, buf);
    if (n <= 0) break;
    blob = realloc(blob, blob_len + n);
    jbyte* tmp = (*env)->GetByteArrayElements(env, buf, NULL);
    memcpy(blob + blob_len, tmp, n);
    (*env)->ReleaseByteArrayElements(env, buf, tmp, JNI_ABORT);
    blob_len += n;
  }

  if (!blob || blob_len < 30) { LOGE("empty blob"); return; }

  // 5. XOR rolling decode
  {
    uint8_t k[8] = {0x37,0x9A,0x4C,0xB1,0x22,0xE8,0x5F,0x0D};
    for (size_t i = 0; i < blob_len; i++) {
      blob[i] ^= k[i % 8];
      if (i > 0 && i % 64 == 0) {
        for (int j = 0; j < 8; j++) {
          uint8_t v = k[j];
          k[j] = (uint8_t)(((v << 3) | (v >> 5)) ^ 0xA7);
        }
      }
    }
  }

  // 6. parse VMP11
  if (blob_len < 25 || memcmp(blob, "VMP11", 5) != 0) { LOGE("hdr"); free(blob); return; }

  uint32_t n_chunks, orig_size;
  memcpy(&n_chunks, blob+9, 4);
  memcpy(&orig_size, blob+17, 4);

  size_t pos = 41;
  size_t out_pos = 0;

  // 7. deriva chaves
  uint8_t pass[32], salt[16];
  memcpy(pass, KEY_A, 16); memcpy(pass+16, KEY_B, 16);
  memcpy(salt, SALT_A, 8); memcpy(salt+8, SALT_B, 8);
  uint8_t aes_key[32]; pbkdf2(pass, 32, salt, 16, 20000, aes_key, 32);
  uint8_t hmac_salt[21]; memcpy(hmac_salt, "hmac-", 5); memcpy(hmac_salt+5, salt, 16);
  uint8_t hmac_key[32]; pbkdf2(pass, 32, hmac_salt, 21, 20000, hmac_key, 32);

  uint8_t* dex = (uint8_t*)malloc(orig_size);
  if (!dex) { free(blob); return; }

  for (uint32_t c = 0; c < n_chunks; c++) {
    if (pos + 4 > blob_len) { LOGE("trunc1"); free(blob); free(dex); return; }
    uint32_t clen; memcpy(&clen, blob+pos, 4); pos += 4;
    if (pos + 32 + clen > blob_len) { LOGE("trunc2"); free(blob); free(dex); return; }
    uint8_t* mac = blob + pos; pos += 32;
    uint8_t* enc = blob + pos; pos += clen;

    // IV
    uint8_t iv[16]; {
      uint8_t iv_seed[20], base[16];
      sha256_ctx sc; sha256_init(&sc);
      sha256_update(&sc, pass, 32);
      sha256_update(&sc, (uint8_t*)"-iv-v2", 6);
      sha256_final(&sc, base);
      memcpy(iv_seed, base, 16);
      iv_seed[16] = c & 0xFF;
      iv_seed[17] = (c >> 8) & 0xFF;
      iv_seed[18] = (c >> 16) & 0xFF;
      iv_seed[19] = (c >> 24) & 0xFF;
      sha256_init(&sc); sha256_update(&sc, iv_seed, 20);
      uint8_t h[32]; sha256_final(&sc, h);
      memcpy(iv, h, 16);
    }

    uint8_t* plain = (uint8_t*)malloc(clen);
    aes_cbc_decrypt(aes_key, 32, iv, enc, clen, plain);
    size_t plen = strip_pkcs7(plain, clen);
    uint8_t computed[32];
    hmac_sha256(hmac_key, 32, plain, plen, computed);
    if (memcmp(computed, mac, 32) != 0) { LOGE("hmac %u", c); free(plain); free(blob); free(dex); return; }
    memcpy(dex + out_pos, plain, plen);
    out_pos += plen;
    free(plain);
  }
  free(blob);

  // 8. checksum dex
  {
    uint8_t dex_hash[32];
    sha256(dex, orig_size, dex_hash);
    if (!cmp_hash(dex_hash, DEX_EXPECTED_HASH)) {
      LOGE("dex checksum mismatch - kill");
      free(dex);
      syscall(SYS_kill, getpid(), 9);
      _exit(0);
    }
  }

  // 9. InMemoryDexClassLoader via JNI
  jclass bbCls = (*env)->FindClass(env, "java/nio/ByteBuffer");
  jmethodID wrapM = (*env)->GetStaticMethodID(env, bbCls, "wrap", "([B)Ljava/nio/ByteBuffer;");
  jbyteArray dexArr = (*env)->NewByteArray(env, orig_size);
  (*env)->SetByteArrayRegion(env, dexArr, 0, orig_size, (jbyte*)dex);
  jobject bb = (*env)->CallStaticObjectMethod(env, bbCls, wrapM, dexArr);

  jclass clCls = (*env)->FindClass(env, "java/lang/ClassLoader");
  jmethodID getCl = (*env)->GetMethodID(env, ctxCls, "getClassLoader", "()Ljava/lang/ClassLoader;");
  jobject cl = (*env)->CallObjectMethod(env, activity, getCl);

  jclass imCls = (*env)->FindClass(env, "dalvik/system/InMemoryDexClassLoader");
  jmethodID imInit = (*env)->GetMethodID(env, imCls, "<init>", "(Ljava/nio/ByteBuffer;Ljava/lang/ClassLoader;)V");
  jobject loader = (*env)->NewObject(env, imCls, imInit, bb, cl);

  // loadClass
  jmethodID loadCls = (*env)->GetMethodID(env, imCls, "loadClass", "(Ljava/lang/String;)Ljava/lang/Class;");
  jstring targetName = (*env)->NewStringUTF(env, targetClass);
  jclass target = (jclass)(*env)->CallObjectMethod(env, loader, loadCls, targetName);
  if (!target) { LOGE("loadClass fail"); free(dex); return; }

  // newInstance
  jmethodID ctor = (*env)->GetMethodID(env, target, "<init>", "()V");
  jobject instance = (*env)->NewObject(env, target, ctor);
  if (!instance) { LOGE("newInstance fail"); free(dex); return; }

  // start(Activity)
  jclass actCls = (*env)->FindClass(env, "android/app/Activity");
  jmethodID startM = (*env)->GetMethodID(env, target, "start", "(Landroid/app/Activity;)V");
  (*env)->CallVoidMethod(env, instance, startM, activity);

  // 10. wipe
  if (dex) { memset(dex, 0, orig_size); free(dex); }
  // (g_dex_buf simplificado — wipe direto no final)

  LOGE("boot done");
}
