
// ysearch.c : search y z (y+z) = 6x^3 + x^2 + K, UMIN <= |x| <= UMAX
// w = -(y+z), y+z+w=0, yzw = -N(x); d=|w| (smallest), sign(w)=sign(N)
// test: d | N(x), Delta = d^2 + 4|N|/d is a square t^2, t = d mod 2.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <time.h>

typedef unsigned __int128 u128;
typedef __int128 i128;
typedef uint64_t u64;
typedef int64_t i64;
typedef uint32_t u32;

static i64 KC = 1;
static u64 UMIN = 4, UMAX = 1000;
static u64 DMAX, SB;
static int NTH = 8;
static u64 LTH = 2048;
static u64 CH = (1ull<<24);
static u64 DS = 0; static u64 SLABW = 0; static long nC = 0; static int WID=0, NW=1;
static u64 SLO=0, SHI=0;
static FILE* OUT;
static pthread_mutex_t outmu = PTHREAD_MUTEX_INITIALIZER;
static double T0;
static double now(){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }

static inline u64 mulmod(u64 a, u64 b, u64 m){ return (u64)((u128)a*b % m); }
static i64 invmod_i(i64 a, i64 m){
  if(m==1) return 0;
  i64 t=0, nt=1, r=m, nr=a % m;
  while(nr){ i64 q=r/nr; i64 tmp=t-q*nt; t=nt; nt=tmp; tmp=r-q*nr; r=nr; nr=tmp; }
  if(r!=1) return -1;
  if(t<0) t+=m; return t;
}
static u64 kmod(u64 m){ i64 k = KC % (i64)m; if(k<0) k+=m; return (u64)k; }
static inline u64 fmodm(u64 x, u64 m){ // f(x) mod m, 0<=x<m
  u64 x2 = mulmod(x,x,m); u64 x3 = mulmod(x2,x,m);
  u128 v = (u128)6*x3 + x2 + kmod(m); return (u64)(v % m);
}
static inline u64 fpmodm(u64 x, u64 m){ // f'(x)=18x^2+2x
  u64 x2 = mulmod(x,x,m); u128 v=(u128)18*x2 + 2*(u128)x; return (u64)(v%m);
}

// ---------------- Montgomery ----------------
typedef struct { u64 n, ni, r2; } Mont;
static inline u64 m_redc(u128 T, const Mont* M){ u64 m = (u64)T * M->ni; u128 t = (T + (u128)m*M->n) >> 64; u64 r=(u64)t; if(r>=M->n) r-=M->n; return r; }
static inline u64 m_mul(u64 a, u64 b, const Mont* M){ return m_redc((u128)a*b, M); }
static inline u64 m_add(u64 a, u64 b, u64 n){ u64 s=a+b; return s>=n? s-n : s; }
static inline u64 m_sub(u64 a, u64 b, u64 n){ return a>=b? a-b : a+n-b; }
static void m_init(Mont* M, u64 n){ M->n=n; u64 inv=n; for(int i=0;i<6;i++) inv*=2-n*inv; M->ni = (u64)0-inv; u64 R = (u64)((((u128)1)<<64) % n); M->r2 = mulmod(R,R,n); }
static inline u64 to_m(u64 a, const Mont* M){ return m_mul(a % M->n, M->r2, M); }
static inline u64 from_m(u64 a, const Mont* M){ return m_redc((u128)a, M); }
static u64 m_pow(u64 a, u64 e, const Mont* M){ u64 r = to_m(1,M); while(e){ if(e&1) r=m_mul(r,a,M); a=m_mul(a,a,M); e>>=1; } return r; }

typedef struct { u64 a0,a1,a2; } P3;
static inline P3 reduce5(u64 c0,u64 c1,u64 c2,u64 c3,u64 c4,u64 c,const Mont* M){
  u64 n=M->n; P3 R; u64 d43=m_sub(c4,c3,n);
  R.a0 = m_add(c0, m_mul(c,d43,M), n);
  R.a1 = m_sub(c1, m_mul(c,c4,M), n);
  R.a2 = m_add(c2, d43, n); return R;
}
static inline P3 psqr(P3 A, u64 c, const Mont* M){
  u64 n=M->n;
  u64 c0=m_mul(A.a0,A.a0,M);
  u64 t01=m_mul(A.a0,A.a1,M); u64 c1=m_add(t01,t01,n);
  u64 t02=m_mul(A.a0,A.a2,M); u64 c2=m_add(m_mul(A.a1,A.a1,M), m_add(t02,t02,n), n);
  u64 t12=m_mul(A.a1,A.a2,M); u64 c3=m_add(t12,t12,n);
  u64 c4=m_mul(A.a2,A.a2,M);
  return reduce5(c0,c1,c2,c3,c4,c,M);
}
static inline P3 pmul(P3 A, P3 B, u64 c, const Mont* M){
  u64 n=M->n;
  u64 c0=m_mul(A.a0,B.a0,M);
  u64 c1=m_add(m_mul(A.a0,B.a1,M), m_mul(A.a1,B.a0,M), n);
  u64 c2=m_add(m_add(m_mul(A.a0,B.a2,M), m_mul(A.a1,B.a1,M), n), m_mul(A.a2,B.a0,M), n);
  u64 c3=m_add(m_mul(A.a1,B.a2,M), m_mul(A.a2,B.a1,M), n);
  u64 c4=m_mul(A.a2,B.a2,M);
  return reduce5(c0,c1,c2,c3,c4,c,M);
}
static inline P3 pmulx(P3 A, u64 c, const Mont* M){ P3 R; u64 n=M->n; R.a0 = m_sub(0, m_mul(c,A.a2,M), n); R.a1=A.a0; R.a2=m_sub(A.a1,A.a2,n); return R; }
static P3 ppow(P3 B, u64 e, u64 c, const Mont* M){ P3 R = {to_m(1,M),0,0}; while(e){ if(e&1) R=pmul(R,B,c,M); B=psqr(B,c,M); e>>=1;} return R; }

// g(phi)=phi^3+phi^2+c (normal form values), linear-gcd root extraction from H (normal form deg<=2)
static int lin_root(u64 p, u64 c, u64 h0, u64 h1, u64 h2, u64* r){
  u64 l0,l1;
  if(h2){
    u64 iv = (u64)invmod_i((i64)h2,(i64)p);
    u64 e1 = mulmod(h1,iv,p), e0 = mulmod(h0,iv,p);
    // l1 = e1^2 - e0 - e1 ; l0 = e1 e0 - e0 + c
    l1 = (mulmod(e1,e1,p) + 2*p - e0 - e1) % p;
    l0 = (mulmod(e1,e0,p) + p - e0 + c) % p;
  } else { l1=h1; l0=h0; }
  if(!l1) return 0;
  u64 rr = mulmod(p - l0 % p, (u64)invmod_i((i64)l1,(i64)p), p); if(rr>=p) rr-=p;
  // verify g(rr)=0
  u64 r2 = mulmod(rr,rr,p); u64 v = (mulmod(r2,rr,p) + r2 + c) % p;
  if(v) return 0;
  *r = rr; return 1;
}
static u64 sqrt_mod(u64 a, u64 p){ // p odd prime, a QR
  if(a==0) return 0;
  Mont M; m_init(&M,p);
  u64 am = to_m(a,&M);
  if((p&3)==3){ return from_m(m_pow(am,(p+1)/4,&M),&M); }
  u64 q=p-1; int s=0; while(!(q&1)){q>>=1;s++;}
  u64 z=2; u64 one=to_m(1,&M), mone=to_m(p-1,&M);
  while(m_pow(to_m(z,&M),(p-1)/2,&M)!=mone) z++;
  u64 cc=m_pow(to_m(z,&M),q,&M), x=m_pow(am,(q+1)/2,&M), t=m_pow(am,q,&M); int m=s;
  while(t!=one){ int i=0; u64 tt=t; while(tt!=one){ tt=m_mul(tt,tt,&M); i++; if(i==m) return (u64)-1; }
    u64 b=cc; for(int j=0;j<m-i-1;j++) b=m_mul(b,b,&M);
    x=m_mul(x,b,&M); cc=m_mul(b,b,&M); t=m_mul(t,cc,&M); m=i; }
  return from_m(x,&M);
}
static int brute_roots(u64 p, u64* out){ int n=0; for(u64 x=0;x<p;x++) if(fmodm(x,p)==0) out[n++]=x; return n; }

// roots of f mod prime p (x-values), returns count
static i64 DISC;
static int cubic_roots_x(u64 p, u64* out){
  if(p<=97 || (DISC % (i64)p)==0) return brute_roots(p,out);
  Mont M; m_init(&M,p);
  u64 cn = mulmod(36 % p, kmod(p), p);
  u64 c = to_m(cn,&M); u64 one=to_m(1,&M);
  P3 R = {0, one, 0};
  int top = 63 - __builtin_clzll(p);
  for(int i=top-1;i>=0;i--){ R = psqr(R,c,&M); if((p>>i)&1) R = pmulx(R,c,&M); }
  u64 h0 = from_m(R.a0,&M), h1 = from_m(m_sub(R.a1, one, p),&M), h2 = from_m(R.a2,&M);
  u64 phis[3]; int nphi=0;
  if(h0==0 && h1==0 && h2==0){
    // three roots: Cantor-Zassenhaus
    u64 r1=0; int got=0;
    for(u64 a=1; a<200 && !got; a++){
      P3 B = {to_m(a,&M), one, 0};
      P3 T = ppow(B,(p-1)/2,c,&M);
      u64 t0=from_m(T.a0,&M), t1=from_m(T.a1,&M), t2=from_m(T.a2,&M);
      if(lin_root(p,cn,(t0+p-1)%p,t1,t2,&r1)) got=1;
      else if(lin_root(p,cn,(t0+1)%p,t1,t2,&r1)) got=1;
    }
    if(!got) return brute_roots(p,out);
    // quadratic phi^2 + (1+r1) phi + (r1 + r1^2)
    u64 b = (1+r1)%p, cq = (r1 + mulmod(r1,r1,p))%p;
    u64 disc = (mulmod(b,b,p) + 4*p - mulmod(4,cq,p)) % p;
    u64 s = sqrt_mod(disc,p);
    if(s==(u64)-1) return brute_roots(p,out);
    u64 inv2=(p+1)/2;
    phis[0]=r1; phis[1]=mulmod((p - b + s)%p, inv2, p); phis[2]=mulmod((2*p - b - s)%p, inv2, p); nphi=3;
  } else {
    u64 r; if(lin_root(p,cn,h0,h1,h2,&r)){ phis[0]=r; nphi=1; }
  }
  u64 inv6 = (u64)invmod_i(6 % (i64)p,(i64)p);
  for(int i=0;i<nphi;i++) out[i]=mulmod(phis[i],inv6,p);
  // verify
  int n=0; for(int i=0;i<nphi;i++) if(fmodm(out[i],p)==0) out[n++]=out[i];
  if(n!=nphi){ return brute_roots(p,out); }
  return n;
}


// finish root extraction for one lane given phi^p (Montgomery)
static int finish_roots(u64 p, const Mont* Mp, u64 cn, u64 c, u64 one, P3 R, u64* out){
  Mont M=*Mp;
  u64 h0 = from_m(R.a0,&M), h1 = from_m(m_sub(R.a1, one, p),&M), h2 = from_m(R.a2,&M);
  u64 phis[3]; int nphi=0;
  if(h0==0 && h1==0 && h2==0){
    return cubic_roots_x(p,out); // rare: 3 roots, scalar path
  } else {
    u64 r; if(lin_root(p,cn,h0,h1,h2,&r)){ phis[0]=r; nphi=1; }
  }
  if(!nphi) return 0;
  u64 inv6 = (u64)invmod_i(6 % (i64)p,(i64)p);
  out[0]=mulmod(phis[0],inv6,p);
  if(fmodm(out[0],p)!=0) return cubic_roots_x(p,out);
  return 1;
}
#define NL 4
static void roots_batch(const u64* P, int* nr, u64 (*out)[3]){
  Mont M[NL]; u64 c[NL], one[NL], cn[NL]; P3 R[NL];
  for(int l=0;l<NL;l++){ m_init(&M[l],P[l]); one[l]=to_m(1,&M[l]); cn[l]=mulmod(36%P[l],kmod(P[l]),P[l]); c[l]=to_m(cn[l],&M[l]); R[l].a0=0; R[l].a1=one[l]; R[l].a2=0; }
  int top = 63 - __builtin_clzll(P[0]);
  for(int i=top-1;i>=0;i--){
    for(int l=0;l<NL;l++) R[l]=psqr(R[l],c[l],&M[l]);
    for(int l=0;l<NL;l++) if((P[l]>>i)&1) R[l]=pmulx(R[l],c[l],&M[l]);
  }
  for(int l=0;l<NL;l++) nr[l]=finish_roots(P[l],&M[l],cn[l],c[l],one[l],R[l],out[l]);
}


// ---------- fast roots via Cardano + Lucas sequences ----------
static int jacobi_u64(u64 a, u64 n){ // n odd positive
  int t=1; a%=n;
  while(a){ while(!(a&1)){ a>>=1; u64 r=n&7; if(r==3||r==5) t=-t; }
    u64 tmp=a; a=n; n=tmp; if((a&3)==3 && (n&3)==3) t=-t; a%=n; }
  return n==1? t : 0;
}
static i64 DISCG_ABS; static int DISCG_NEG; static int8_t* CHITAB; static u64 CHIMOD;
static inline int chi_disc(u64 p){ // Legendre (discg/p), discg = -c(4+27c) with c=36K -> same class as disc(f) * square
  u64 r = p % CHIMOD; int v = CHITAB[r];
  if(v) return v;
  u64 a = (u64)(DISCG_ABS % (i64)p); if(DISCG_NEG) a = (p - a) % p;
  int j = jacobi_u64(a,p); CHITAB[r] = (int8_t)j; return j;
}
// V_k(P) mod p in Montgomery form; two, P given in Montgomery form
static inline u64 lucasV(u64 k, u64 Pm, u64 twom, const Mont* M){
  u64 n=M->n; u64 a=twom, b=Pm; // (V_0, V_1)
  int top = 63 - __builtin_clzll(k);
  for(int i=top;i>=0;i--){
    u64 ab = m_sub(m_mul(a,b,M), Pm, n);
    if((k>>i)&1){ a = ab; b = m_sub(m_mul(b,b,M), twom, n); }
    else { b = ab; a = m_sub(m_mul(a,a,M), twom, n); }
  }
  return a;
}
static u64 NFAST=0, NFALL=0;
static int fast_roots_x(u64 p, u64* out){
  if(p<=97 || (DISC % (i64)p)==0) return brute_roots(p,out);
  int chi = chi_disc(p);
  if(chi==0) return cubic_roots_x(p,out);
  Mont M; m_init(&M,p);
  u64 c = mulmod(36 % p, kmod(p), p);
  u64 inv3 = (p%3==1)? (2*p+1)/3 : (p+1)/3;          // 3*inv3 = 1 mod p
  u64 inv27 = mulmod(mulmod(inv3,inv3,p),inv3,p);
  u64 Q = (c + 2*inv27) % p;
  u64 PL = (p - mulmod(27,Q,p)) % p;               // -27Q
  u64 Pm = to_m(PL,&M), twom = to_m(2,&M);
  u64 t;
  if(chi<0){
    u64 k = (p%3==2)? (2*p-1)/3 : (p+2)/3;
    t = mulmod(from_m(lucasV(k,Pm,twom,&M),&M), inv3, p);
    u64 phi = (t + p - inv3) % p;
    u64 inv6 = mulmod(inv3, (p+1)/2, p);
    u64 x = mulmod(phi, inv6, p);
    if(fmodm(x,p)!=0){ NFALL++; return cubic_roots_x(p,out); }
    out[0]=x; return 1;
  } else {
    int pm1 = (p%3==1);
    u64 nord = pm1? p-1 : p+1;  // group order containing beta
    u64 e = nord/3;
    u64 Ve = from_m(lucasV(e,Pm,twom,&M),&M);
    if(Ve!=2) return 0;
    u64 m = e; // nord = 3m
    if(m%3==0){ NFALL++; return cubic_roots_x(p,out); }
    u64 k = (m%3==2)? (m+1)/3 : (2*m+1)/3;
    t = mulmod(from_m(lucasV(k,Pm,twom,&M),&M), inv3, p);
    u64 phi1 = (t + p - inv3) % p;
    // deflate: phi^2 + (1+phi1) phi + (phi1 + phi1^2)
    u64 b = (1+phi1)%p, cq = (phi1 + mulmod(phi1,phi1,p))%p;
    u64 dsc = (mulmod(b,b,p) + 4*p - mulmod(4,cq,p)) % p;
    u64 s = sqrt_mod(dsc,p);
    if(s==(u64)-1){ NFALL++; return cubic_roots_x(p,out); }
    u64 inv2=(p+1)/2;
    u64 ph[3] = { phi1, mulmod((p - b + s)%p, inv2, p), mulmod((2*p - b - s)%p, inv2, p) };
    u64 inv6 = mulmod(inv3, (p+1)/2, p);
    for(int i=0;i<3;i++){ out[i]=mulmod(ph[i],inv6,p); if(fmodm(out[i],p)!=0){ NFALL++; return cubic_roots_x(p,out);} }
    return 3;
  }
}
static void init_chi(){
  // discg = -c(4+27c), c=36K  -> use disc(f) = -4K(1+243K) (same square class since discg = 36^2 * 27 * ... ) -- use discg directly
  i64 c = 36*KC; i128 dg = -(i128)c*(4+27*(i128)c);
  DISCG_NEG = dg<0; i128 ad = dg<0? -dg: dg;
  // squarefree-ish reduction: strip square factors of small primes to keep table small
  for(i64 q=2;q<100000;q++){ while(ad % ((i128)q*q)==0) ad/= (i128)q*q; }
  DISCG_ABS=(i64)ad; CHIMOD = 4*(u64)ad; CHITAB = calloc(CHIMOD,1);
}

// ---------------- filters ----------------
#define NSQ 16
static const int SQL[NSQ] = {64,27,7,5,11,13,17,19,23,29,31,37,41,43,47,53};
static uint8_t LOCT[NSQ][64];       // local solvability of x mod q
static uint8_t SQT[NSQ][64];        // squares mod q
static int INVT[NSQ][64];           // inverse mod q or -1
static int NAT[NSQ][2][64];         // |N| mod q for u mod q, sigma=+1 (0), -1 (1)
static uint8_t F3NZ[2][3];          // N(x) mod 3 != 0 for x = sigma*u, u mod 3
#define LM 12096
static uint8_t LOCM[2][LM];         // local filter on u mod LM for sigma

static int Fyz_has(int q, int v){ for(int y=0;y<q;y++) for(int z=0;z<q;z++){ if(((y*y*z + y*z*z) % q)==v) return 1; } return 0; }
static void init_filters(){
  for(int qi=0;qi<NSQ;qi++){
    int q=SQL[qi];
    uint8_t has[64]; for(int v=0;v<q;v++) has[v]=Fyz_has(q,v);
    for(int x=0;x<q;x++){ i64 N = 6LL*x*x*x + (i64)x*x + KC; i64 v = ((N % q)+q)%q; LOCT[qi][x]=has[v]; }
    for(int v=0;v<q;v++) SQT[qi][v]=0; for(int t=0;t<q;t++) SQT[qi][(t*t)%q]=1;
    for(int a=0;a<q;a++){ INVT[qi][a]=-1; for(int b=0;b<q;b++) if((a*b)%q==1%q){ INVT[qi][a]=b; break; } }
    for(int s=0;s<q;s++){
      for(int sg=0;sg<2;sg++){
        i64 sig = sg?-1:1; i64 v = 6LL*s*s*s + sig*((i64)s*s + KC); v%=q; if(v<0) v+=q; NAT[qi][sg][s]=(int)v;
      }
    }
  }
  for(int sg=0;sg<2;sg++) for(int s=0;s<3;s++){ i64 x = sg? (3-s)%3 : s; i64 N=6*x*x*x+x*x+KC; F3NZ[sg][s] = ((N%3)+3)%3 != 0; }
  for(int sg=0;sg<2;sg++) for(int u=0;u<LM;u++){
    int ok=1; int qs[3]={64,27,7}; int qis[3]={0,1,2};
    for(int j=0;j<3;j++){ int q=qs[j]; int s=u%q; int x = sg? (q-s)%q : s; if(!LOCT[qis[j]][x]) ok=0; }
    LOCM[sg][u]=ok;
  }
}

// ---------------- thread state ----------------
typedef struct { u64 *buf; size_t cap; } RB;
typedef struct { RB lev[40]; u64 nroots, nsieve_k, ndirect_k, nexact, nsol, nprimes; u64 *bx; uint8_t* sv; } TS;
static void rb_need(RB* r, size_t n){ if(r->cap<n){ r->cap = n*2+16; r->buf = realloc(r->buf, r->cap*sizeof(u64)); } }

static u64 isqrt128(u128 v){
  if(v==0) return 0;
  u64 s = (u64)sqrt((double)v);
  // newton refine
  for(int it=0; it<4; it++){ if(s==0) s=1; u128 q = v / s; s = (u64)(((u128)s + q) >> 1); }
  while((u128)s*s > v) s--;
  while((u128)(s+1)*(s+1) <= v) s++;
  return s;
}


typedef struct { u64 w[4]; } U256;
static inline U256 u256_from128(u128 a){ U256 r={{(u64)a,(u64)(a>>64),0,0}}; return r; }
static inline U256 u256_mul64(U256 a, u64 b){ U256 r; u128 c=0; for(int i=0;i<4;i++){ c += (u128)a.w[i]*b; r.w[i]=(u64)c; c>>=64; } return r; }
static inline U256 u256_add(U256 a, U256 b){ U256 r; u128 c=0; for(int i=0;i<4;i++){ c += (u128)a.w[i] + b.w[i]; r.w[i]=(u64)c; c>>=64; } return r; }
static inline U256 u256_sub(U256 a, U256 b){ U256 r; u64 br=0; for(int i=0;i<4;i++){ u64 t=a.w[i]-b.w[i]; u64 b1 = a.w[i]<b.w[i]; u64 t2=t-br; u64 b2 = t<br; r.w[i]=t2; br=b1|b2; } return r; }
static inline int u256_cmp(U256 a, U256 b){ for(int i=3;i>=0;i--){ if(a.w[i]!=b.w[i]) return a.w[i]<b.w[i]?-1:1; } return 0; }
static inline U256 u256_divmod64(U256 a, u64 d, u64* rem){ U256 q; u128 r=0; for(int i=3;i>=0;i--){ r = (r<<64) | a.w[i]; q.w[i]=(u64)(r/d); r%=d; } *rem=(u64)r; return q; }
static inline U256 u256_sq128(u128 t){ u64 a0=(u64)t, a1=(u64)(t>>64); u128 p00=(u128)a0*a0, p01=(u128)a0*a1, p11=(u128)a1*a1;
  U256 r={{0,0,0,0}}; U256 x=u256_from128(p00); r=u256_add(r,x);
  U256 m={{0,(u64)p01,(u64)(p01>>64),0}}; r=u256_add(r,m); r=u256_add(r,m);
  U256 h={{0,0,(u64)p11,(u64)(p11>>64)}}; r=u256_add(r,h); return r; }
static u128 u256_isqrt(U256 v){ // floor sqrt, result < 2^128
  int top=3; while(top>0 && v.w[top]==0) top--;
  int bits = top*64 + (v.w[top]? 64-__builtin_clzll(v.w[top]) : 0);
  int sb = (bits+1)/2 + 1; if(sb>127) sb=127;
  u128 lo=0, hi=((u128)1)<<sb;
  while(hi-lo>1){ u128 mid=lo+((hi-lo)>>1); if(u256_cmp(u256_sq128(mid),v)<=0) lo=mid; else hi=mid; }
  return lo;
}
static void print_i128(char* b, i128 v){ int neg=v<0; u128 a = neg? (u128)(-v):(u128)v; char tmp[64]; int k=0; if(a==0) tmp[k++]='0'; while(a){ tmp[k++]='0'+(int)(a%10); a/=10;} int j=0; if(neg) b[j++]='-'; while(k) b[j++]=tmp[--k]; b[j]=0; }
static void exact_test(TS* ts, u64 d, u64 u, int sg){
  ts->nexact++;
  U256 u2 = u256_from128((u128)u*u);
  U256 u3 = u256_mul64(u2,u);
  U256 N6 = u256_mul64(u3,6);
  U256 kk = u256_add(u2, u256_from128((u128)KC));
  U256 Nabs = sg==0 ? u256_add(N6,kk) : u256_sub(N6,kk);
  u64 rem; U256 Q = u256_divmod64(Nabs,d,&rem);
  if(rem){ pthread_mutex_lock(&outmu); fprintf(stderr,"BUG: d=%llu does not divide N at u=%llu sg=%d\n",(unsigned long long)d,(unsigned long long)u,sg); pthread_mutex_unlock(&outmu); return; }
  U256 Dl = u256_add(u256_mul64(Q,4), u256_from128((u128)d*d));
  u128 t = u256_isqrt(Dl);
  if(u256_cmp(u256_sq128(t),Dl)!=0) return;
  if(((u64)t ^ d) & 1) return;
  ts->nsol++;
  i64 sig = sg?-1:1;
  i128 w = (i128)sig*(i128)d; i128 y = (-w + (i128)t)/2, z = (-w - (i128)t)/2; i128 x = (i128)sig*(i128)u;
  char bx[64],by[64],bz[64]; print_i128(bx,x); print_i128(by,y); print_i128(bz,z);
  pthread_mutex_lock(&outmu); fprintf(OUT,"SOL x=%s y=%s z=%s d=%llu\n",bx,by,bz,(unsigned long long)d); fflush(OUT); pthread_mutex_unlock(&outmu);
}
#define QT(QI, Q) do{ u64 dq = d % Q; int iv = INVT[QI][dq]; if(iv>=0){ u64 s = u % Q; int D2 = (int)((dq*dq + 4*(u64)NAT[QI][sg][s]*iv) % Q); if(!SQT[QI][D2]) return 0; if(Q==27 && F3NZ[sg][s%3] && (D2%9)) return 0; } }while(0)
static inline int quick_ok(u64 d, u64 u, int sg){
  QT(1,27); QT(0,64); QT(2,7); QT(3,5); QT(4,11); QT(5,13); QT(6,17); QT(7,19); QT(8,23); QT(9,29); QT(10,31);
  return 1;
}

static void direct_mode(TS* ts, u64 d, u64 u0, u64 L, int sg){
  u64 dm = d % LM, rm = u0 % LM; const uint8_t* loc = LOCM[sg];
  u64 u = u0;
  for(u64 k=0;k<L;k++){
    if(loc[rm]){ if(quick_ok(d,u,sg)) exact_test(ts,d,u,sg); }
    rm += dm; if(rm>=LM) rm-=LM; u += d;
  }
  ts->ndirect_k += L;
}

static u64 allowed_mask(int qi, u64 d, int sg){
  int q=SQL[qi]; int dq=(int)(d % q); int iv=INVT[qi][dq]; int d2=(dq*dq)%q; u64 m=0;
  for(int s=0;s<q;s++){
    int x = sg? (q-s)%q : s; if(!LOCT[qi][x]) continue;
    if(iv>=0){ int D2 = (int)((d2 + 4LL*NAT[qi][sg][s]*iv) % q); if(!SQT[qi][D2]) continue; if(q==27 && F3NZ[sg][s%3] && (D2%9)) continue; }
    m |= 1ull<<s;
  }
  return m;
}

static void sieve_mode(TS* ts, u64 d, u64 u0, u64 L, int sg){
  u64 rep0[NSQ], rep1[NSQ]; int ph[NSQ], inc[NSQ];
  for(int qi=0;qi<NSQ;qi++){
    int q=SQL[qi]; u64 am = allowed_mask(qi,d,sg);
    int dq=(int)(d%q), s=(int)(u0%q); uint8_t pk[64];
    for(int j=0;j<q;j++){ pk[j]=(am>>s)&1; s+=dq; if(s>=q) s-=q; }
    u64 r0=0,r1=0; int j=0;
    for(int b=0;b<64;b++){ if(pk[j]) r0|=1ull<<b; j++; if(j==q) j=0; }
    for(int b=0;b<64;b++){ if(pk[j]) r1|=1ull<<b; j++; if(j==q) j=0; }
    rep0[qi]=r0; rep1[qi]=r1; ph[qi]=0; inc[qi]=64%q;
  }
  u64 nw=(L+63)/64;
  for(u64 i=0;i<nw;i++){
    u64 w=~0ull;
    for(int qi=0;qi<NSQ;qi++){
      int s=ph[qi];
      if(qi<6 || w){ u64 e = s? ((rep0[qi]>>s)|(rep1[qi]<<(64-s))) : rep0[qi]; w&=e; }
      s+=inc[qi]; if(s>=SQL[qi]) s-=SQL[qi]; ph[qi]=s;
    }
    if(w){
      if(i==nw-1 && (L&63)) w &= (1ull<<(L&63))-1;
      while(w){ int b=__builtin_ctzll(w); w&=w-1; u64 k=i*64+b; exact_test(ts,d,u0+k*d,sg); }
    }
  }
  ts->nsieve_k += L;
}

static inline void process_root_rng(TS* ts, u64 d, u64 r, u64 lo, u64 hi){
  ts->nroots++;
  u64 ulo = d>1000 ? (u64)(0.69*(double)d) - 2 : 0;
  if(ulo<lo) ulo=lo;
  for(int sg=0;sg<2;sg++){
    u64 res = sg==0 ? r : (r? d-r : 0);
    u64 u0 = ulo + ((res + d - (ulo % d)) % d);
    if(u0>hi) continue;
    u64 L = (hi - u0)/d + 1;
    if(L>=LTH) sieve_mode(ts,d,u0,L,sg); else direct_mode(ts,d,u0,L,sg);
  }
}
static inline void process_root(TS* ts, u64 d, u64 r){ if(d<=DS) return; process_root_rng(ts,d,r,UMIN,UMAX); }
// ---------------- small primes & root tables ----------------
typedef struct { u64 pk; int nr; u64 *r; } PP;
typedef struct { u64 p; int npp; PP *pp; } SPrime;
static u32* allp; static int nallp;    // all primes <= SB
static SPrime* SPR; static int nSPR;   // good primes <= SB
static u32 *mt_off, *mt_r; static u32* goodm; static int ngoodm; // m-table m < SB

static void build_small(){
  uint8_t* comp = calloc(SB+1,1); nallp=0; allp=malloc(sizeof(u32)*(SB/2+10));
  for(u64 i=2;i<=SB;i++){ if(!comp[i]){ allp[nallp++]=(u32)i; for(u64 j=i*i;j<=SB;j+=i) comp[j]=1; } }
  free(comp);
  SPR = malloc(sizeof(SPrime)*nallp); nSPR=0;
  u64* tmp = malloc(sizeof(u64)*1024);
  for(int i=0;i<nallp;i++){
    u64 p=allp[i]; u64 rr[3]; int nr = (p<=97 || DISC%(i64)p==0)? 0 : -1;
    u64* R; int n;
    if(nr==0){ R = malloc(sizeof(u64)*p); n = brute_roots(p,R); } else { R=malloc(sizeof(u64)*3); n = cubic_roots_x(p,rr); for(int j=0;j<n;j++) R[j]=rr[j]; }
    if(n==0){ free(R); continue; }
    SPrime sp; sp.p=p; sp.npp=0; sp.pp=malloc(sizeof(PP)*64);
    u64 pk=p; 
    while(1){
      sp.pp[sp.npp].pk=pk; sp.pp[sp.npp].nr=n; sp.pp[sp.npp].r=R; sp.npp++;
      if(pk > DMAX / p) break;
      u64 npk = pk*p;
      // lift
      static u64 R2buf[4096]; u64* R2 = R2buf; int n2=0;
      for(int j=0;j<n;j++){
        u64 r=R[j];
        u64 fp = fpmodm(r % p, p);
        if(fp){ // Hensel
          u64 fr = fmodm(r % npk, npk); // divisible by pk
          u64 a = (fr / pk) % p;
          u64 t = mulmod((p - a)%p, (u64)invmod_i((i64)fp,(i64)p), p);
          u64 nr2 = r + t*pk; if(fmodm(nr2,npk)==0){ R2[n2++]=nr2; }
        } else {
          for(u64 t=0;t<p;t++){ u64 c=r+t*pk; if(fmodm(c,npk)==0){ if(n2<4096) R2[n2++]=c; } }
        }
      }
      if(n2==0){ break; }
      pk=npk; R=malloc(sizeof(u64)*n2); memcpy(R,R2buf,sizeof(u64)*n2); n=n2;
    }
    sp.pp = realloc(sp.pp, sizeof(PP)*(sp.npp>0?sp.npp:1));
    SPR[nSPR++]=sp;
  }
  free(tmp);
  // m-table for m < SB
  u32* spf = calloc(SB+1,sizeof(u32));
  for(int i=0;i<nallp;i++){ u64 p=allp[i]; for(u64 j=p;j<=SB;j+=p) if(!spf[j]) spf[j]=(u32)p; }
  // map prime -> SPR index
  int* sidx = malloc(sizeof(int)*(SB+1)); for(u64 i=0;i<=SB;i++) sidx[i]=-1; for(int i=0;i<nSPR;i++) sidx[SPR[i].p]=i;
  mt_off = malloc(sizeof(u32)*(SB+2));
  size_t cap = SB*2+16, used=0; mt_r = malloc(sizeof(u32)*cap);
  mt_off[0]=0; mt_off[1]=0; // m=0 empty
  mt_r[used++]=0; mt_off[2]=(u32)used; // m=1 -> {0}
  for(u64 m=2;m<SB;m++){
    u64 p=spf[m]; u64 pk=1; u64 mm=m; int e=0; while(mm%p==0){ mm/=p; pk*=p; e++; }
    int si = sidx[p];
    if(si<0 || e>SPR[si].npp || mt_off[mm+1]==mt_off[mm]){ mt_off[m+1]=(u32)used; continue; }
    PP* pp=&SPR[si].pp[e-1];
    u32 a0=mt_off[mm], a1=mt_off[mm+1];
    size_t need = (size_t)(a1-a0)*pp->nr; if(used+need>cap){ cap=(used+need)*2; mt_r=realloc(mt_r,sizeof(u32)*cap); }
    u64 inv = (u64)invmod_i((i64)(mm % pk),(i64)pk);
    for(u32 ia=a0; ia<a1; ia++){ u64 a=mt_r[ia]; for(int jb=0;jb<pp->nr;jb++){ u64 b=pp->r[jb]; u64 t = mulmod((b + pk - a%pk)%pk, inv, pk); mt_r[used++]=(u32)(a + mm*t); } }
    mt_off[m+1]=(u32)used;
  }
  goodm = malloc(sizeof(u32)*SB); ngoodm=0; for(u64 m=1;m<SB;m++) if(mt_off[m+1]>mt_off[m]) goodm[ngoodm++]=(u32)m;
  free(spf); free(sidx);
}

// ---------------- Case 2 DFS ----------------
static void dfs(TS* ts, int depth, u64 d, const u64* roots, int nr, int imax){
  for(int j=0;j<nr;j++) process_root(ts,d,roots[j]);
  for(int i=0;i<imax;i++){
    SPrime* sp=&SPR[i];
    if(sp->p > DMAX / d) break;
    for(int j=0;j<sp->npp;j++){
      PP* pp=&sp->pp[j];
      if(pp->pk > DMAX / d) break;
      u64 nd=d*pp->pk; RB* rb=&ts->lev[depth+1]; rb_need(rb,(size_t)nr*pp->nr);
      u64 pk=pp->pk; u64 inv=(u64)invmod_i((i64)(d % pk),(i64)pk); int no=0;
      for(int a=0;a<nr;a++){ u64 ra=roots[a]; for(int b=0;b<pp->nr;b++){ u64 t = mulmod((pp->r[b] + pk - ra%pk)%pk, inv, pk); rb->buf[no++] = ra + d*t; } }
      dfs(ts,depth+1,nd,rb->buf,no,i);
    }
  }
}

// ---------------- Case 1 chunk ----------------
static void case1_chunk(TS* ts, u64 lo, u64 hi){
  if(lo<=SB) lo=SB+1;
  if(hi>DMAX+1) hi=DMAX+1;
  if(lo>=hi) return;
  if(!(lo&1)) lo++;
  u64 n = (hi - lo + 1)/2; // odd numbers lo, lo+2, ...
  uint8_t* sv = ts->sv; memset(sv,1,n);
  for(int i=1;i<nallp;i++){ u64 p=allp[i]; if(p*p>=hi) break;
    u64 st = ((lo + p - 1)/p)*p; if(st < p*p) st=p*p; if(!(st&1)) st+=p;
    for(u64 j=(st-lo)/2;j<n;j+=p) sv[j]=0; }
  u64 bx[3];
  u64 PB[NL]; int nbq=0; u64 OB[NL][3]; int NB[NL];
  #define HANDLE_P(Pv, nbv, bxv) do{ u64 P_=(Pv); int nb_=(nbv); const u64* bx_=(bxv); if(nb_){ u64 Mlim = DMAX / P_; \
      for(int gi=0; gi<ngoodm && goodm[gi]<=Mlim; gi++){ u64 m=goodm[gi]; \
        if(m==1){ for(int b=0;b<nb_;b++) process_root(ts,P_,bx_[b]); continue; } \
        u64 iv=(u64)invmod_i((i64)(P_ % m),(i64)m); u64 d=P_*m; \
        for(u32 ia=mt_off[m]; ia<mt_off[m+1]; ia++){ u64 a=mt_r[ia]; \
          for(int b=0;b<nb_;b++){ u64 t = ((a + m - bx_[b]%m)%m) * iv % m; process_root(ts,d,bx_[b] + P_*t); } } } } }while(0)
  for(u64 j=0;j<n;j++){ if(!sv[j]) continue; u64 P=lo+2*j; if(P>=hi) break;
    ts->nprimes++;
    int nb=fast_roots_x(P,bx); HANDLE_P(P,nb,bx);
  }
}

// ---------------- tasks ----------------
static atomic_long next_task;
static u64 *BLO, *BHI;
static long nA, nB;
static void run_task(TS* ts, long t){
  if(t<nC){ u64 lo = UMIN + (u64)t*SLABW; u64 hi = lo + SLABW - 1; if(hi>UMAX || hi<lo) hi=UMAX;
    for(u64 d=1; d<=DS; d++){ for(u32 ia=mt_off[d]; ia<mt_off[d+1]; ia++) process_root_rng(ts,d,mt_r[ia],lo,hi); }
    return; }
  t -= nC;
  if(t<nA){ int i=(int)t; SPrime* sp=&SPR[i];
    for(int j=0;j<sp->npp;j++){ PP* pp=&sp->pp[j]; if(pp->pk>DMAX) break; dfs(ts,0,pp->pk,pp->r,pp->nr,i); }
    return; }
  long c=t-nA; case1_chunk(ts,BLO[c],BHI[c]);
}
static TS* TSS;
static long TOTAL;
static void* worker(void* arg){
  TS* ts=(TS*)arg;
  while(1){ long t=atomic_fetch_add(&next_task,1); if(t>=TOTAL) break; if(t % NW != WID) continue; run_task(ts,t);
    if((t % 4096)==WID){ pthread_mutex_lock(&outmu); fprintf(stderr,"[%.1fs] task %ld/%ld\n",now()-T0,t,TOTAL); pthread_mutex_unlock(&outmu);} }
  return NULL;
}
int main(int argc, char** argv){
  if(argc<4){ fprintf(stderr,"usage: K UMIN UMAX [NTH] [LTH]\n"); return 1; }
  KC=atoll(argv[1]); UMIN=strtoull(argv[2],0,10); UMAX=strtoull(argv[3],0,10);
  if(argc>4) NTH=atoi(argv[4]); if(argc>5) LTH=strtoull(argv[5],0,10); if(argc>7){ WID=atoi(argv[6]); NW=atoi(argv[7]); }
  OUT=stdout; T0=now();
  DISC = -4*KC*(1+243*KC);
  DMAX = (u64)(1.44225*(double)UMAX) + 3;
  SB = (u64)sqrt((double)DMAX)+2;
  init_filters(); init_chi();
  build_small();
  fprintf(stderr,"K=%lld UMIN=%llu UMAX=%llu DMAX=%llu SB=%llu nSPR=%d ngoodm=%d  [%.1fs]\n",(long long)KC,(unsigned long long)UMIN,(unsigned long long)UMAX,(unsigned long long)DMAX,(unsigned long long)SB,nSPR,ngoodm,now()-T0);
  nA=nSPR;
  { // adaptive chunks: work per prime ~ c1*(DMAX/P)*goodfrac + c2 ; target bounded work per chunk
    size_t cap=1024; BLO=malloc(cap*8); BHI=malloc(cap*8); nB=0;
    u64 lo=SB+1; double Pth = (double)DMAX/64.0;
    while(lo<=DMAX){ u64 len = CH; if((double)lo < Pth){ double f=(double)lo/Pth; len = (u64)((double)CH*f); if(len<2048) len=2048; }
      len &= ~1ull; u64 hi=lo+len; if(hi>DMAX+1) hi=DMAX+1;
      if((size_t)nB==cap){ cap*=2; BLO=realloc(BLO,cap*8); BHI=realloc(BHI,cap*8); }
      BLO[nB]=lo; BHI[nB]=hi; nB++; lo=hi; }
  }
  DS = SB-1 < 65536 ? SB-1 : 65536; SLABW = (u64)1<<32; if(UMAX-UMIN < SLABW*64) SLABW = (UMAX-UMIN)/64 + 1; nC = (long)((UMAX-UMIN)/SLABW + 1);
  TOTAL = nC + nA + nB;
  fprintf(stderr,"tasks: slabs=%ld (DS=%llu, W=%llu) A=%ld B=%ld  worker %d/%d\n",nC,(unsigned long long)DS,(unsigned long long)SLABW,nA,nB,WID,NW);
  atomic_store(&next_task,0);
  pthread_t th[64]; TSS=calloc(NTH,sizeof(TS));
  for(int i=0;i<NTH;i++){ TSS[i].sv=malloc(CH/2+16); pthread_create(&th[i],0,worker,&TSS[i]); }
  u64 a=0,b=0,c=0,e=0,s=0,pr=0;
  for(int i=0;i<NTH;i++){ pthread_join(th[i],0); a+=TSS[i].nroots; b+=TSS[i].nsieve_k; c+=TSS[i].ndirect_k; e+=TSS[i].nexact; s+=TSS[i].nsol; pr+=TSS[i].nprimes; }
  fprintf(stderr,"DONE roots=%llu sieve_k=%llu direct_k=%llu exact=%llu sols=%llu bigprimes=%llu time=%.1fs\n",(unsigned long long)a,(unsigned long long)b,(unsigned long long)c,(unsigned long long)e,(unsigned long long)s,(unsigned long long)pr,now()-T0);
  printf("DONE K=%lld UMIN=%llu UMAX=%llu sols=%llu time=%.1f\n",(long long)KC,(unsigned long long)UMIN,(unsigned long long)UMAX,(unsigned long long)s,now()-T0);
  return 0;
}
