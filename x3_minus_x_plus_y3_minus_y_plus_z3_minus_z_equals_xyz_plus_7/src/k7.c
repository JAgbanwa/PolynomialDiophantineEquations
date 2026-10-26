/*
 * k7.c -- complete search for integer solutions of
 *
 *        x^3 - x + y^3 - y + z^3 - z = x*y*z + K          (default K = 7)
 *
 * Reduction (validated against brute force for many K):
 *   - every solution has a pair with d = x + y == R (mod 10)            (R = 2 for K = 7)
 *   - e = z + 3d divides N(d) = 26 d^3 - 2 d + K, sign(e) = sign(d), |e| <= 2.3|d| + 50
 *   - x*y = e^2 - 9 e d + 27 d^2 - 1 - N/e  and  d^2 - 4xy = (x - y)^2 must be a square
 *
 * Work units (scheduled dynamically over threads, in order of the smallest |d| they touch):
 *   A [t0,t1)       d = 10 t + R; all divisors e of N(d) built from primes <= T
 *                   (roots of N mod p tabulated for p <= T, sieve over t)
 *   B (q0,q1]       primes q > T; divisors e = m*q with m <= 2.3|d|/q <= 10000 (CRT over the roots of N mod m)
 *                   for DB0 <= |d| <= DB1.  Requires T^2 > 2.3*DB1+50 and 2.3*DB1+50 <= 10000*q0.
 *   Exact test in 192-bit arithmetic: valid for |d| < 2^44 (~1.7e13).
 *
 * Every finished unit is appended to the progress file; on restart, finished units are skipped.
 *
 * Usage: k7 [-j threads] [-T T] [-R R] [-a t0 t1]... [[-bu log2unit] -b q0 q1 DB0 DB1]... [-bm 0|1|2]
 *           [-p progress.txt] [-s solutions.txt] [-l log.txt] [-ua log2unitA] [-ub log2unitB]
 *        k7 -roots q0 q1 out.txt        (dump roots of 26t^3-2t+K mod primes in (q0,q1], for testing)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <pthread.h>
#include <unistd.h>
#include <time.h>
#include <sys/time.h>

typedef uint64_t u64; typedef int64_t i64; typedef uint32_t u32;
typedef unsigned __int128 u128; typedef __int128 i128;
#ifndef K
#define K 7
#endif
#define MSTEP 10

static double now(void){ struct timeval tv; gettimeofday(&tv,0); return tv.tv_sec+tv.tv_usec*1e-6; }

/* ===================== Montgomery arithmetic mod odd q < 2^62 (thread-local) ===================== */
static __thread u64 Q, QINV, R2, ONE, GA, GB, INV26;
static inline u64 mm(u64 a,u64 b,u64 q,u64 qi){ u128 t=(u128)a*b; u64 m=(u64)t*qi; u64 r=(u64)((t+(u128)m*q)>>64); return r>=q? r-q : r; }
static inline u64 mmul(u64 a,u64 b){ return mm(a,b,Q,QINV); }
static inline u64 madd(u64 a,u64 b){ u64 r=a+b; return r>=Q? r-Q: r; }
static inline u64 msub(u64 a,u64 b){ return a>=b? a-b : a+Q-b; }
static inline u64 tom(u64 a){ return mmul(a%Q, R2); }
static inline u64 fromm(u64 a){ return mmul(a,1); }
static void mont_init(u64 q){ Q=q; u64 x=q; for(int i=0;i<6;i++) x*=2-q*x; QINV=-x; u64 r=(u64)(((u128)1<<64)%q); R2=(u64)((u128)r*r%q); ONE=r; }
static inline u64 mpow(u64 a, u64 e){ u64 r=ONE; while(e){ if(e&1) r=mmul(r,a); a=mmul(a,a); e>>=1; } return r; }
static inline u64 minv(u64 a){ return mpow(a,Q-2); }
static i64 inv_mod(i64 a, i64 m){ i64 t=0,nt=1,r=m,nr=((a%m)+m)%m; while(nr){ i64 q=r/nr,tmp=t-q*nt; t=nt; nt=tmp; tmp=r-q*nr; r=nr; nr=tmp; } return ((t%m)+m)%m; }

/* ===================== polynomials over F_q (Montgomery coefficients), degree <= 5 ===================== */
typedef struct { int n; u64 c[6]; } poly;
static void pnorm(poly*p){ while(p->n>=0 && p->c[p->n]==0) p->n--; }
static poly pmod(poly a, const poly*b){
  u64 il=minv(b->c[b->n]); pnorm(&a);
  while(a.n>=b->n){ u64 f=mmul(a.c[a.n],il); int sh=a.n-b->n; for(int i=0;i<=b->n;i++) a.c[i+sh]=msub(a.c[i+sh],mmul(f,b->c[i])); a.c[a.n]=0; pnorm(&a); }
  return a;
}
static poly pdiv(poly a, const poly*b){
  poly qo; qo.n=a.n-b->n; for(int i=0;i<6;i++) qo.c[i]=0;
  u64 il=minv(b->c[b->n]);
  while(a.n>=b->n){ u64 f=mmul(a.c[a.n],il); int sh=a.n-b->n; qo.c[sh]=f; for(int i=0;i<=b->n;i++) a.c[i+sh]=msub(a.c[i+sh],mmul(f,b->c[i])); a.c[a.n]=0; pnorm(&a); }
  pnorm(&qo); return qo;
}
static poly pmonic(poly a){ u64 il=minv(a.c[a.n]); for(int i=0;i<=a.n;i++) a.c[i]=mmul(a.c[i],il); return a; }
static poly pgcd(poly a, poly b){ pnorm(&a); pnorm(&b); while(b.n>=0){ poly r=pmod(a,&b); a=b; b=r; } return pmonic(a); }
static poly pmulmod(const poly*a,const poly*b,const poly*g){
  poly r; r.n=-1; for(int i=0;i<6;i++) r.c[i]=0;
  if(a->n<0||b->n<0) return r;
  for(int i=0;i<=a->n;i++) for(int j=0;j<=b->n;j++) r.c[i+j]=madd(r.c[i+j],mmul(a->c[i],b->c[j]));
  r.n=a->n+b->n;
  for(int k=r.n;k>=g->n;k--){ u64 f=r.c[k]; if(!f) continue; int sh=k-g->n; for(int i=0;i<g->n;i++) r.c[i+sh]=msub(r.c[i+sh],mmul(f,g->c[i])); r.c[k]=0; }
  r.n = r.n<g->n-1? r.n : g->n-1; pnorm(&r); return r;
}
static poly ppow(poly base, u64 e, const poly*g){
  poly r; r.n=0; for(int i=0;i<6;i++) r.c[i]=0; r.c[0]=ONE;
  int top=63; while(top>=0 && !((e>>top)&1)) top--;
  for(int b=top;b>=0;b--){ r=pmulmod(&r,&r,g); if((e>>b)&1) r=pmulmod(&r,&base,g); }
  return r;
}
static int msqrt(u64 a, u64*out){
  if(a==0){*out=0;return 1;}
  if(mpow(a,(Q-1)/2)!=ONE) return 0;
  if((Q&3)==3){ *out=mpow(a,(Q+1)/4); return 1; }
  u64 sq=Q-1; int v=0; while(!(sq&1)){sq>>=1;v++;}
  u64 z=tom(2); while(mpow(z,(Q-1)/2)==ONE) z=madd(z,ONE);
  u64 c=mpow(z,sq), x=mpow(a,(sq+1)/2), t=mpow(a,sq); int m=v;
  while(t!=ONE){ int i=0; u64 tt=t; while(tt!=ONE){ tt=mmul(tt,tt); i++; }
    u64 b=c; for(int j=0;j<m-i-1;j++) b=mmul(b,b);
    x=mmul(x,b); c=mmul(b,b); t=mmul(t,c); m=i; }
  *out=x; return 1;
}

/* ===================== roots of 26 t^3 - 2 t + K mod prime q ===================== */
/* work with g(u) = u^3 - 52 u + 676 K, u = 26 t */
static __thread int nroots; static __thread u64 roots[3]; static __thread u64 gdelta=1;
static void split(poly g){
  if(g.n<=0) return;
  if(g.n==1){ roots[nroots++]=fromm(msub(0,g.c[0])); return; }
  for(;;){ u64 delta=gdelta++; if(gdelta>1000000) gdelta=1;
    poly base; base.n=1; for(int i=0;i<6;i++) base.c[i]=0; base.c[0]=tom(delta); base.c[1]=ONE;
    poly w=ppow(base,(Q-1)/2,&g);
    if(w.n<0){ w.n=0; w.c[0]=0; }
    w.c[0]=msub(w.c[0],ONE); pnorm(&w);
    if(w.n<0) continue;
    poly d=pgcd(g,w);
    if(d.n>0 && d.n<g.n){ poly o=pdiv(g,&d); split(d); split(pmonic(o)); return; }
  }
}
static void push_u(u64 u){ roots[nroots++]=fromm(mmul(u,INV26)); }
static void quad_roots(u64 b, u64 c){
  u64 disc=msub(mmul(b,b),mmul(tom(4),c)); u64 sr; if(!msqrt(disc,&sr)) return;
  u64 i2=tom((Q+1)/2);
  push_u(mmul(msub(sr,b),i2)); if(sr) push_u(mmul(msub(0,madd(sr,b)),i2));
}
static void roots_setup(u64 q){
  mont_init(q); nroots=0;
  u64 qm=q%26, k; for(k=0;k<26;k++) if((qm*k+1)%26==0) break; INV26=tom((u64)(((u128)q*k+1)/26));
  i64 kk=676L*K; GA=tom(q-52); GB=tom((u64)(((kk%(i64)q)+(i64)q)%(i64)q));
}
/* t^q mod (t^3 + GA t + GB), Montgomery form, explicit constants (for lane batching) */
#if defined(__AVX512IFMA__) && !defined(NO_IFMA)
#define USE_IFMA 1
#define LANES 8
#else
#define LANES 4
#endif
static void tq_batch(int n, const u64*q, const u64*qi, const u64*one, const u64*ga, const u64*gb, u64 (*out)[3]){
  u64 c0[LANES],c1[LANES],c2[LANES]; int top[LANES]; int maxtop=0;
  for(int l=0;l<n;l++){ c0[l]=0; c1[l]=one[l]; c2[l]=0; top[l]=63-__builtin_clzll(q[l]); if(top[l]>maxtop) maxtop=top[l]; }
  for(int b=maxtop-1;b>=0;b--){
    for(int l=0;l<n;l++){
      if(b>=top[l]) continue;
      u64 Ql=q[l], Il=qi[l];
      #define MM(a,b_) mm(a,b_,Ql,Il)
      #define AD(a,b_) ({u64 _r=(a)+(b_); _r>=Ql?_r-Ql:_r;})
      #define SB(a,b_) ({u64 _a=(a),_b=(b_); _a>=_b?_a-_b:_a+Ql-_b;})
      u64 x0=c0[l],x1=c1[l],x2=c2[l];
      u64 s0=MM(x0,x0), s1=MM(x0,x1); s1=AD(s1,s1);
      u64 s2=MM(x0,x2); s2=AD(s2,s2); s2=AD(s2,MM(x1,x1));
      u64 s3=MM(x1,x2); s3=AD(s3,s3); u64 s4=MM(x2,x2);
      u64 n2=SB(s2,MM(ga[l],s4)), n1=SB(SB(s1,MM(gb[l],s4)),MM(ga[l],s3)), n0=SB(s0,MM(gb[l],s3));
      if((Ql>>b)&1){ u64 m0=SB(0,MM(gb[l],n2)), m1=SB(n0,MM(ga[l],n2)), m2=n1; n0=m0; n1=m1; n2=m2; }
      c0[l]=n0; c1[l]=n1; c2[l]=n2;
      #undef MM
      #undef AD
      #undef SB
    }
  }
  for(int l=0;l<n;l++){ out[l][0]=c0[l]; out[l][1]=c1[l]; out[l][2]=c2[l]; }
}
static void roots_finish(u64 hc0, u64 hc1, u64 hc2){
  u64 h0=hc0, h1=msub(hc1,ONE), h2=hc2;
  if(h0==0&&h1==0&&h2==0){ /* splits completely */
    int top=63-__builtin_clzll((Q-1)/2); u64 E=(Q-1)/2;
    for(int tries=0;tries<200;tries++){
      u64 dl=tom(gdelta++); if(gdelta>1000000) gdelta=1;
      u64 c0=dl,c1=ONE,c2=0;
      for(int b=top-1;b>=0;b--){
        u64 s0=mmul(c0,c0), s1=mmul(c0,c1); s1=madd(s1,s1);
        u64 s2=mmul(c0,c2); s2=madd(s2,s2); s2=madd(s2,mmul(c1,c1));
        u64 s3=mmul(c1,c2); s3=madd(s3,s3); u64 s4=mmul(c2,c2);
        c2=msub(s2,mmul(GA,s4)); c1=msub(msub(s1,mmul(GB,s4)),mmul(GA,s3)); c0=msub(s0,mmul(GB,s3));
        if((E>>b)&1){ u64 n0=msub(mmul(dl,c0),mmul(GB,c2)), n1=madd(msub(c0,mmul(GA,c2)),mmul(dl,c1)), n2=madd(c1,mmul(dl,c2)); c0=n0;c1=n1;c2=n2; }
      }
      u64 w0=msub(c0,ONE), w1=c1, w2=c2;
      if(w2!=0){
        u64 w22=mmul(w2,w2);
        u64 r1=madd(msub(mmul(w22,GA),mmul(w2,w0)),mmul(w1,w1));
        u64 r0=madd(mmul(w22,GB),mmul(w1,w0));
        if(r1==0 && r0==0){
          u64 iw=minv(w2); u64 bq=mmul(w1,iw), cq=mmul(w0,iw);
          u64 disc=msub(mmul(bq,bq),mmul(tom(4),cq)), sr; if(!msqrt(disc,&sr)) continue;
          u64 i2=tom((Q+1)/2); u64 ua=mmul(msub(sr,bq),i2), ub=mmul(msub(0,madd(sr,bq)),i2);
          push_u(ua); push_u(ub); push_u(msub(0,madd(ua,ub))); return; }
        if(r1==0) continue;
        u64 test=madd(msub(mmul(w2,mmul(r0,r0)),mmul(w1,mmul(r0,r1))),mmul(w0,mmul(r1,r1)));
        if(test!=0) continue;
        u64 ur=mmul(msub(0,r0),minv(r1)); push_u(ur); quad_roots(ur, madd(GA,mmul(ur,ur))); return;
      }
      if(w1!=0){
        u64 ur=mmul(msub(0,w0),minv(w1));
        u64 gv=madd(madd(mmul(ur,mmul(ur,ur)),mmul(GA,ur)),GB);
        if(gv!=0) continue;
        push_u(ur); quad_roots(ur, madd(GA,mmul(ur,ur))); return;
      }
    }
    goto generic;
  }
  if(h2!=0){
    u64 r1=madd(msub(mmul(mmul(h2,h2),GA),mmul(h2,h0)),mmul(h1,h1));
    u64 r0=madd(mmul(mmul(h2,h2),GB),mmul(h1,h0));
    if(r1==0){ if(r0==0) goto generic; return; }
    u64 test=madd(msub(mmul(h2,mmul(r0,r0)),mmul(h1,mmul(r0,r1))),mmul(h0,mmul(r1,r1)));
    if(test!=0) return;
    push_u(mmul(msub(0,r0),minv(r1))); return;
  }
  if(h1!=0){
    u64 test=msub(msub(mmul(GB,mmul(h1,mmul(h1,h1))),mmul(h0,mmul(h0,h0))),mmul(GA,mmul(h0,mmul(h1,h1))));
    if(test!=0) return;
    push_u(mmul(msub(0,h0),minv(h1))); return;
  }
  return;
generic: {
    poly g; g.n=3; for(int i=0;i<6;i++) g.c[i]=0; g.c[0]=GB; g.c[1]=GA; g.c[3]=ONE;
    poly H; H.n=2; for(int i=0;i<6;i++) H.c[i]=0; H.c[0]=h0; H.c[1]=h1; H.c[2]=h2; pnorm(&H);
    poly G=pgcd(g,H); int n0=nroots; split(G); for(int i=n0;i<nroots;i++) roots[i]=fromm(mmul(tom(roots[i]),INV26));
  }
}
/* batch root finding: calls cb(q, r) for every root r of 26t^3-2t+K mod q, q in qs[0..n) (q >= 64, odd primes) */
typedef void (*root_cb)(void*ctx, u64 q, u64 r);
static void roots_batch(int n, const u64*qs, root_cb cb, void*ctx);
static void roots_batch_scalar(int n, const u64*qs, root_cb cb, void*ctx){
  u64 qi[LANES],one[LANES],r2[LANES],ga[LANES],gb[LANES],i26[LANES]; u64 h[LANES][3];
  for(int l=0;l<n;l++){ roots_setup(qs[l]); qi[l]=QINV; one[l]=ONE; r2[l]=R2; ga[l]=GA; gb[l]=GB; i26[l]=INV26; }
  tq_batch(n,qs,qi,one,ga,gb,h);
  for(int l=0;l<n;l++){
    Q=qs[l]; QINV=qi[l]; ONE=one[l]; R2=r2[l]; GA=ga[l]; GB=gb[l]; INV26=i26[l]; nroots=0;
    roots_finish(h[l][0],h[l][1],h[l][2]);
    for(int k=0;k<nroots;k++) cb(ctx,qs[l],roots[k]);
  }
}
static void find_roots_scalar(u64 q){ roots_setup(q); u64 h[1][3]; tq_batch(1,&q,&QINV,&ONE,&GA,&GB,h); roots_finish(h[0][0],h[0][1],h[0][2]); }
#ifdef USE_IFMA
/* ================= AVX-512 IFMA batch root finder (8 primes) ================= */
#include <immintrin.h>
typedef __m512i V;
static inline V mm52(V a, V b, V q, V qinv){
  const V z=_mm512_setzero_si512();
  V lo=_mm512_madd52lo_epu64(z,a,b);
  V hi=_mm512_madd52hi_epu64(z,a,b);
  V m =_mm512_madd52lo_epu64(z,lo,qinv);
  hi=_mm512_madd52hi_epu64(hi,m,q);
  __mmask8 c=_mm512_cmpneq_epu64_mask(lo,z);
  hi=_mm512_mask_add_epi64(hi,c,hi,_mm512_set1_epi64(1));
  return _mm512_min_epu64(hi,_mm512_sub_epi64(hi,q));
}
static inline V vadd(V a,V b,V q){ V t=_mm512_add_epi64(a,b); return _mm512_min_epu64(t,_mm512_sub_epi64(t,q)); }
static inline V vsub(V a,V b,V q){ V t=_mm512_sub_epi64(_mm512_add_epi64(a,q),b); return _mm512_min_epu64(t,_mm512_sub_epi64(t,q)); }
static __thread int bnroots[8]; static __thread u64 broots[8][3];
static void find_roots8(const u64 *qs){
  u64 qa[8],qi[8],r2[8],one[8],ga[8],gb[8],i26[8],tl[8],em2[8];
  int maxtop=0;
  for(int l=0;l<8;l++){ u64 q=qs[l]; qa[l]=q; u64 x=q; for(int i=0;i<6;i++) x*=2-q*x; qi[l]=(-x)&((1ULL<<52)-1);
    u64 R=(1ULL<<52)%q; one[l]=R; r2[l]=(u64)((u128)R*R%q);
    ga[l]=q-52; long kk=676L*K; gb[l]=(u64)(((kk%(long)q)+(long)q)%(long)q);
    u64 qm=q%26,k; for(k=0;k<26;k++) if((qm*k+1)%26==0) break; i26[l]=(u64)(((u128)q*k+1)/26);
    int t=63-__builtin_clzll(q); tl[l]=t; if(t>maxtop) maxtop=t; em2[l]=q-2; }
  V Q=_mm512_loadu_si512(qa), QI=_mm512_loadu_si512(qi), R2=_mm512_loadu_si512(r2), ONEV=_mm512_loadu_si512(one);
  V A=mm52(_mm512_loadu_si512(ga),R2,Q,QI), B=mm52(_mm512_loadu_si512(gb),R2,Q,QI);
  V I26=mm52(_mm512_loadu_si512(i26),R2,Q,QI);
  V TL=_mm512_loadu_si512(tl);
  V c0=_mm512_setzero_si512(), c1=ONEV, c2=_mm512_setzero_si512();
  for(int bpos=maxtop-1;bpos>=0;bpos--){
    __mmask8 act=_mm512_cmpgt_epu64_mask(TL,_mm512_set1_epi64(bpos));
    V s0=mm52(c0,c0,Q,QI), s1=mm52(c0,c1,Q,QI); s1=vadd(s1,s1,Q);
    V s2=mm52(c0,c2,Q,QI); s2=vadd(s2,s2,Q); s2=vadd(s2,mm52(c1,c1,Q,QI),Q);
    V s3=mm52(c1,c2,Q,QI); s3=vadd(s3,s3,Q); V s4=mm52(c2,c2,Q,QI);
    V n2=vsub(s2,mm52(A,s4,Q,QI),Q);
    V n1=vsub(vsub(s1,mm52(B,s4,Q,QI),Q),mm52(A,s3,Q,QI),Q);
    V n0=vsub(s0,mm52(B,s3,Q,QI),Q);
    c0=_mm512_mask_mov_epi64(c0,act,n0); c1=_mm512_mask_mov_epi64(c1,act,n1); c2=_mm512_mask_mov_epi64(c2,act,n2);
    __mmask8 bit=act & _mm512_test_epi64_mask(_mm512_srli_epi64(Q,bpos),_mm512_set1_epi64(1));
    V z=_mm512_setzero_si512();
    V m0=vsub(z,mm52(B,c2,Q,QI),Q), m1=vsub(c0,mm52(A,c2,Q,QI),Q), m2=c1;
    c0=_mm512_mask_mov_epi64(c0,bit,m0); c1=_mm512_mask_mov_epi64(c1,bit,m1); c2=_mm512_mask_mov_epi64(c2,bit,m2);
  }
  V h0=c0, h1=vsub(c1,ONEV,Q), h2=c2;
  // pseudo-remainder (h2 != 0 case)
  V h22=mm52(h2,h2,Q,QI);
  V r1=vadd(vsub(mm52(h22,A,Q,QI),mm52(h2,h0,Q,QI),Q),mm52(h1,h1,Q,QI),Q);
  V r0=vadd(mm52(h22,B,Q,QI),mm52(h1,h0,Q,QI),Q);
  V test=vadd(vsub(mm52(h2,mm52(r0,r0,Q,QI),Q,QI),mm52(h1,mm52(r0,r1,Q,QI),Q,QI),Q),mm52(h0,mm52(r1,r1,Q,QI),Q,QI),Q);
  // linear case (h2 == 0, h1 != 0)
  V h12=mm52(h1,h1,Q,QI);
  V test2=vsub(vsub(mm52(B,mm52(h1,h12,Q,QI),Q,QI),mm52(h0,mm52(h0,h0,Q,QI),Q,QI),Q),mm52(A,mm52(h0,h12,Q,QI),Q,QI),Q);
  V z=_mm512_setzero_si512();
  __mmask8 h2nz=_mm512_cmpneq_epu64_mask(h2,z), h1nz=_mm512_cmpneq_epu64_mask(h1,z), h0nz=_mm512_cmpneq_epu64_mask(h0,z);
  V num=_mm512_mask_mov_epi64(h0,h2nz,r0), den=_mm512_mask_mov_epi64(h1,h2nz,r1);
  // Fermat inverse den^(q-2), right-to-left with per-lane exponent
  V E=_mm512_loadu_si512(em2), res=ONEV, base=den;
  for(int bpos=0;bpos<=maxtop;bpos++){
    __mmask8 bit=_mm512_test_epi64_mask(_mm512_srli_epi64(E,bpos),_mm512_set1_epi64(1));
    res=_mm512_mask_mov_epi64(res,bit,mm52(res,base,Q,QI)); base=mm52(base,base,Q,QI); }
  V u=vsub(z,mm52(num,res,Q,QI),Q);
  V t=mm52(mm52(u,I26,Q,QI),_mm512_set1_epi64(1),Q,QI); // plain t
  u64 H0[8],H1[8],H2[8],R1[8],R0[8],T1[8],T2[8],TT[8];
  _mm512_storeu_si512(H0,h0); _mm512_storeu_si512(H1,h1); _mm512_storeu_si512(H2,h2);
  _mm512_storeu_si512(R1,r1); _mm512_storeu_si512(R0,r0); _mm512_storeu_si512(T1,test); _mm512_storeu_si512(T2,test2); _mm512_storeu_si512(TT,t);
  (void)h2nz; (void)h1nz; (void)h0nz;
  for(int l=0;l<8;l++){
    bnroots[l]=0;
    int fallback=0;
    if(H0[l]==0&&H1[l]==0&&H2[l]==0) fallback=1;
    else if(H2[l]!=0){ if(R1[l]==0){ if(R0[l]==0) fallback=1; } else if(T1[l]==0){ broots[l][0]=TT[l]; bnroots[l]=1; } }
    else if(H1[l]!=0){ if(T2[l]==0){ broots[l][0]=TT[l]; bnroots[l]=1; } }
    if(fallback){ find_roots_scalar(qs[l]); bnroots[l]=nroots; for(int i=0;i<nroots;i++) broots[l][i]=roots[i]; }
  }
}
#endif
static void roots_small(u64 p, root_cb cb, void*ctx){ /* brute force for p < 64 */
  for(u64 t=0;t<p;t++){ i64 v=((26*(i64)t%(i64)p*(i64)t%(i64)p*(i64)t - 2*(i64)t + K)%(i64)p); if(v<0) v+=p; if(v==0) cb(ctx,p,t); }
}
static void roots_batch(int n, const u64*qs, root_cb cb, void*ctx){
#ifdef USE_IFMA
  if(n==8){ find_roots8(qs); for(int l=0;l<8;l++) for(int k=0;k<bnroots[l];k++) cb(ctx,qs[l],broots[l][k]); return; }
#endif
  roots_batch_scalar(n,qs,cb,ctx);
}

/* ===================== base primes & segmented odd sieve ===================== */
static u32 *basep; static long nbasep;
static void make_base(u64 lim){
  uint8_t*s=calloc(lim+1,1); basep=malloc(4*(lim/2+16)); nbasep=0;
  for(u64 i=2;i<=lim;i++) if(!s[i]){ basep[nbasep++]=(u32)i; for(u64 j=i*i;j<=lim;j+=i) s[j]=1; }
  free(s);
}
/* calls f(ctx, q) for each prime q in (lo, hi], q odd >= 3; seg buffer of SEGN odd numbers */
#define SEGN (1u<<23)
typedef void (*prime_cb)(void*ctx, u64 q);
static void for_primes(u64 lo, u64 hi, uint8_t*buf, void (*batch)(void*ctx,u64*qs,int n), void*ctx){
  u64 start=lo+1; if(start<3) start=3; if(start%2==0) start++;
  u64 qs[LANES]; int nq=0;
  for(u64 s0=start; s0<=hi; s0+=2*(u64)SEGN){
    u64 s1=s0+2*(u64)SEGN; if(s1>hi+1) s1=hi+1;  /* odd numbers s0, s0+2, ..., < s1 */
    u64 cnt=(s1-s0+1)/2; memset(buf,0,cnt);
    for(long j=1;j<nbasep;j++){ u64 p=basep[j]; if(p*p>=s1) break;
      u64 st=p*p; if(st<s0){ st=((s0+p-1)/p)*p; } if(st%2==0) st+=p;
      for(u64 v=st; v<s1; v+=2*p) buf[(v-s0)/2]=1; }
    for(u64 i=0;i<cnt;i++) if(!buf[i]){ u64 q=s0+2*i; if(q<3) continue;
      qs[nq++]=q; if(nq==LANES){ batch(ctx,qs,nq); nq=0; } }
  }
  if(nq) batch(ctx,qs,nq);
}

/* ===================== candidate test ===================== */
static void pr128(FILE*f, i128 v){ char buf[64]; int i=63; buf[i]=0; int neg=v<0; u128 u=neg?(u128)(-v):(u128)v; if(u==0)buf[--i]='0'; while(u){buf[--i]='0'+(int)(u%10); u/=10;} if(neg)buf[--i]='-'; fputs(&buf[i],f); }
static FILE *solf, *logfp; static pthread_mutex_t outlock=PTHREAD_MUTEX_INITIALIZER;
typedef struct { long cand, pass, pass2, sols, ovf, events, primes; } stats;
static void report_solution(i128 x,i128 y,i128 z,i64 d,i64 e){
  pthread_mutex_lock(&outlock);
  FILE* fs[3]={solf,logfp,stdout};
  for(int k=0;k<3;k++){ FILE*f=fs[k]; if(!f) continue; fprintf(f,"SOLUTION x="); pr128(f,x); fprintf(f," y="); pr128(f,y); fprintf(f," z="); pr128(f,z); fprintf(f,"  (d=%lld e=%lld K=%d)\n",(long long)d,(long long)e,K); fflush(f); }
  pthread_mutex_unlock(&outlock);
}
static void report_bug(i64 d,i64 e){
  pthread_mutex_lock(&outlock);
  fprintf(stderr,"BUG d=%lld e=%lld\n",(long long)d,(long long)e); if(logfp){fprintf(logfp,"BUG d=%lld e=%lld\n",(long long)d,(long long)e); fflush(logfp);}
  pthread_mutex_unlock(&outlock);
}
/* N(d) = 26 d^3 - 2 d + K  reduced mod M  (1 <= M < 2^62), no overflow for any 64-bit d */
static inline u64 Nmod(i64 d, u64 M){
  i64 dm_=d%(i64)M; if(dm_<0) dm_+=(i64)M; u64 dm=(u64)dm_;
  u64 d2=(u64)((u128)dm*dm%M), d3=(u64)((u128)d2*dm%M);
  u64 Km=(u64)(((i64)K%(i64)M+(i64)M)%(i64)M);
  u128 v=(u128)26*d3 + (u128)2*(M-dm) + Km; return (u64)(v%M);
}
/* quadratic-character filters: P = e*disc = -4e^3+36e^2 d-107 d^2 e+4e+4N must be e*(square) mod p */
typedef struct { u64 M; int np; int p[8]; } fgroup;
static fgroup FG[3]={ {111546435ULL,8,{3,5,7,11,13,17,19,23}}, {58642669ULL,5,{29,31,37,41,43}}, {600662303ULL,5,{47,53,59,61,67}} };
static int8_t LEGT[68][68];
static void init_leg(void){
  for(int g=0;g<3;g++) for(int i=0;i<FG[g].np;i++){ int p=FG[g].p[i]; for(int a=0;a<p;a++) LEGT[p][a]=-1; LEGT[p][0]=0; for(int a=1;a<p;a++) LEGT[p][(a*a)%p]=1; }
}
/* specialized with compile-time moduli so every % is a multiply-high */
#define FGBODY(MC) \
  const u64 M=(MC); \
  i64 dm_=d%(i64)M; if(dm_<0) dm_+=(i64)M; i64 em_=e%(i64)M; if(em_<0) em_+=(i64)M; \
  u64 dm=(u64)dm_, em=(u64)em_; \
  u64 d2=(dm*dm)%M, e2=(em*em)%M; \
  u64 Km=(u64)(((i64)K%(i64)M+(i64)M)%(i64)M); \
  u64 Nm=((((26%M)*((d2*dm)%M))%M) + 2*(M-dm) + Km)%M; \
  u64 Pm=( 4*(M-(e2*em)%M) + ((36%M)*((e2*dm)%M))%M + (M-((107%M)*((d2*em)%M))%M) + 4*em + 4*Nm )%M;
#define LT(P) { u64 ep=em%(P); if(ep){ u64 pp=Pm%(P); if(pp && LEGT[P][pp]!=LEGT[P][ep]) return 0; } }
static inline int fg0(i64 d,i64 e){ FGBODY(111546435ULL) LT(3) LT(5) LT(7) LT(11) LT(13) LT(17) LT(19) LT(23) return 1; }
static inline int fg1(i64 d,i64 e){ FGBODY(58642669ULL) LT(29) LT(31) LT(37) LT(41) LT(43) return 1; }
static inline int fg2(i64 d,i64 e){ FGBODY(600662303ULL) LT(47) LT(53) LT(59) LT(61) LT(67) return 1; }
#undef LT
/* ---- minimal unsigned 192-bit arithmetic for the exact test ---- */
typedef struct { u64 w[3]; } u192;
static inline u192 U(u128 x){ u192 r={{(u64)x,(u64)(x>>64),0}}; return r; }
static inline u192 u192_mul64(u192 a,u64 m){ u128 c=0; u192 r; for(int i=0;i<3;i++){ u128 t=(u128)a.w[i]*m+c; r.w[i]=(u64)t; c=t>>64; } return r; }
static inline u192 u192_add(u192 a,u192 b){ u128 c=0; u192 r; for(int i=0;i<3;i++){ u128 t=(u128)a.w[i]+b.w[i]+c; r.w[i]=(u64)t; c=t>>64; } return r; }
static inline u192 u192_sub(u192 a,u192 b){ u64 br=0; u192 r; for(int i=0;i<3;i++){ u64 t=a.w[i]-b.w[i]; u64 b1=a.w[i]<b.w[i]; u64 t2=t-br; u64 b2=t<br; r.w[i]=t2; br=b1|b2; } return r; }
static inline int u192_cmp(u192 a,u192 b){ for(int i=2;i>=0;i--) if(a.w[i]!=b.w[i]) return a.w[i]<b.w[i]?-1:1; return 0; }
static inline u192 u192_div64(u192 a,u64 e,u64*rem){ u192 q; u128 r=0; for(int i=2;i>=0;i--){ u128 cur=(r<<64)|a.w[i]; q.w[i]=(u64)(cur/e); r=cur%e; } *rem=(u64)r; return q; }
static inline u192 u192_sq(u128 s){ /* s < 2^96 */
  u64 lo=(u64)s, hi=(u64)(s>>64); u128 ll=(u128)lo*lo, lh=(u128)lo*hi, hh=(u128)hi*hi;
  u192 r=U(ll); u192 a=u192_mul64(U(lh),2); u192 as={{0,a.w[0],a.w[1]}}; r=u192_add(r,as); u192 h={{0,(u64)hh,(u64)(hh>>64)}}; u192 hs={{0,0,h.w[1]}}; r=u192_add(r,hs); return r; }
static inline double u192_d(u192 a){ return ldexp((double)a.w[2],128)+ldexp((double)a.w[1],64)+(double)a.w[0]; }
static int isqrt192(u192 D, u128*out){
  double sd=sqrt(u192_d(D)); u128 s0=(u128)sd; u128 W=(u128)1<<24;
  u128 lo = s0>W? s0-W : 0, hi = s0+W;
  while(lo>0 && u192_cmp(u192_sq(lo),D)>0){ lo = lo>W? lo-W : 0; W<<=1; }
  W=(u128)1<<24; while(u192_cmp(u192_sq(hi),D)<=0){ hi+=W; W<<=1; }
  /* invariant: lo^2 <= D < hi^2 */
  while(hi-lo>1){ u128 mid=lo+(hi-lo)/2; if(u192_cmp(u192_sq(mid),D)<=0) lo=mid; else hi=mid; }
  *out=lo; return u192_cmp(u192_sq(lo),D)==0;
}
/* exact test, valid for |d| < 2^44, |e| <= 2.3|d|+50 */
static void exact_check(i64 d, i64 e, stats*st, int verbose){
  i64 ad=d<0?-d:d, ae=e<0?-e:e; i64 sk=(d>0?1:-1)*(i64)K;
  u192 N=u192_mul64(u192_mul64(U((u128)ad*(u128)ad),(u64)ad),26);      /* |N| = 26 ad^3 - 2 ad + sgn(d) K */
  N=u192_sub(N,U((u128)2*(u128)ad));
  if(sk>=0) N=u192_add(N,U((u128)sk)); else N=u192_sub(N,U((u128)(-sk)));
  u64 rem; u192 f=u192_div64(N,(u64)ae,&rem);
  if(verbose) printf("N=%016llx%016llx%016llx rem=%llu f=%016llx%016llx%016llx\n",(unsigned long long)N.w[2],(unsigned long long)N.w[1],(unsigned long long)N.w[0],(unsigned long long)rem,(unsigned long long)f.w[2],(unsigned long long)f.w[1],(unsigned long long)f.w[0]);
  if(rem) return;
  i128 small = -107*(i128)d*d - 4*(i128)e*e + 36*(i128)e*d + 4;      /* disc = 4f + small */
  u192 D=u192_mul64(f,4);
  if(small>=0) D=u192_add(D,U((u128)small)); else { u192 sm=U((u128)(-small)); if(u192_cmp(D,sm)<0){ if(verbose) printf("disc<0\n"); return; } D=u192_sub(D,sm); }
  u128 s; int sq=isqrt192(D,&s);
  if(verbose) printf("D=%016llx%016llx%016llx s=%016llx%016llx sq=%d\n",(unsigned long long)D.w[2],(unsigned long long)D.w[1],(unsigned long long)D.w[0],(unsigned long long)(u64)(s>>64),(unsigned long long)(u64)s,sq);
  if(!sq) return;
  if((((u64)d)+((u64)s))&1) return;
  i128 x=((i128)d+(i128)s)/2, y=(i128)d-x, z=(i128)e-3*(i128)d;
  u128 X=(u128)x, Y=(u128)y, Z=(u128)z;
  u128 F=X*X*X-X+Y*Y*Y-Y+Z*Z*Z-Z-X*Y*Z-(u128)(i128)K;     /* identity checked mod 2^128 */
  if(F!=0){ report_bug(d,e); return; }
  st->sols++; report_solution(x,y,z,d,e);
}
static void check(i64 d, i64 e, stats*st){
  st->cand++;
  if(e&1){ u64 ud=(u64)d, ue=(u64)e;
    u64 inv=ue; for(int i=0;i<5;i++) inv*=2-ue*inv;
    u64 N64=26*ud*ud*ud-2*ud+(u64)(i64)K;
    u64 f64=N64*inv;
    u64 xy=ue*ue-9*ue*ud+27*ud*ud-1-f64;
    u64 D=ud*ud-4*xy;
    if(D){ int tz=__builtin_ctzll(D); if(tz&1) return; if(tz<=61 && ((D>>tz)&7)!=1) return; } }
  if(!fg0(d,e)) return;
  st->pass++;
  if(!fg1(d,e) || !fg2(d,e)) return;
  st->pass2++;
  exact_check(d,e,st,0);
}
static inline i64 bound_e(i64 ad){ return (i64)(2.3*(double)ad)+50; }

/* ===================== root table for A units ===================== */
static u64 TT=2300001000ULL; static i64 RR=2;
static u32 *TP, *TR; static long NT; static long JSMALL;   /* TP prime, TR t-residue: t == TR (mod p)  <=>  d=10t+R == root */
typedef struct { u32*p; u32*r; long n, cap; } rvec;
static void rvec_push(rvec*v,u32 p,u32 r){ if(v->n==v->cap){ v->cap=v->cap?2*v->cap:1<<16; v->p=realloc(v->p,4*v->cap); v->r=realloc(v->r,4*v->cap); } v->p[v->n]=p; v->r[v->n]=r; v->n++; }
static void table_cb(void*ctx,u64 q,u64 r){
  if(MSTEP%q==0) return;
  i64 tr=(i64)(((((i64)r-RR)%(i64)q+(i64)q)%(i64)q) * (u128)inv_mod(MSTEP,(i64)q) % q);
  rvec_push((rvec*)ctx,(u32)q,(u32)tr);
}
static void table_batch(void*ctx,u64*qs,int n){
  int m=0; u64 big[LANES];
  for(int i=0;i<n;i++){ if(qs[i]<64) roots_small(qs[i],table_cb,ctx); else big[m++]=qs[i]; }
  if(m) roots_batch(m,big,table_cb,ctx);
}
#define TCH (1ULL<<27)
static rvec *tparts; static long ntparts; static long tnext=0; static pthread_mutex_t tlock=PTHREAD_MUTEX_INITIALIZER;
static void* table_worker(void*arg){
  uint8_t*buf=malloc(SEGN);
  for(;;){ pthread_mutex_lock(&tlock); long i=tnext++; pthread_mutex_unlock(&tlock); if(i>=ntparts) break;
    u64 lo=(u64)i*TCH, hi=lo+TCH; if(hi>TT) hi=TT;
    for_primes(lo,hi,buf,table_batch,&tparts[i]); }
  free(buf); return 0;
}
static u32 lastp(void){ for(long i=ntparts-1;i>=0;i--) if(tparts[i].n) return tparts[i].p[tparts[i].n-1]; return 0; }
static void build_table(int nth){
  double t0=now();
  ntparts=(long)((TT+TCH-1)/TCH); tparts=calloc(ntparts,sizeof(rvec));
  pthread_t th[256]; for(int i=0;i<nth;i++) pthread_create(&th[i],0,table_worker,0); for(int i=0;i<nth;i++) pthread_join(th[i],0);
  /* keep the parts (no merged copy): peak memory = table size (~0.9 GB for T = 2.3e9) */
  NT=0; for(long i=0;i<ntparts;i++){ NT+=tparts[i].n; if(tparts[i].n){ tparts[i].p=realloc(tparts[i].p,4*tparts[i].n); tparts[i].r=realloc(tparts[i].r,4*tparts[i].n); } tparts[i].cap=tparts[i].n; }
  TP=tparts[0].p; TR=tparts[0].r;
  JSMALL=0; while(JSMALL<tparts[0].n && TP[JSMALL]<(1u<<21)) JSMALL++;
  fprintf(stderr,"root table: primes <= %llu, %ld (p,root) pairs, last p=%u, built in %.1f s\n",(unsigned long long)TT,NT,lastp(),now()-t0);
  if(logfp){ fprintf(logfp,"root table: primes <= %llu, %ld (p,root) pairs, last p=%u, built in %.1f s\n",(unsigned long long)TT,NT,lastp(),now()-t0); fflush(logfp); }
}

/* ===================== A unit: sieve over t ===================== */
#define SA (1<<20)
#define MAXF 12
typedef struct { u32 off; u32 p; } hit;
typedef struct { hit*h; long n,cap; } hvec;
static inline void hpush(hvec*v,u32 off,u32 p){ if(v->n==v->cap){ v->cap=v->cap?2*v->cap:1<<16; v->h=realloc(v->h,sizeof(hit)*v->cap); } v->h[v->n].off=off; v->h[v->n].p=p; v->n++; }
typedef struct { u32*fac; uint8_t*nf; hvec*bk; int nbk; hvec ov; } abuf;
/* exponent of p in N(d) (p | N(d) known), capped where p^k > B */
static inline int pexp(i64 d, u64 p, i64 B){ int ex=1; if((i64)p>B/(i64)p) return 1; u64 pk=p*p; for(;;){ if(Nmod(d,pk)!=0) break; ex++; if((i64)pk>B/(i64)p) break; pk*=p; } return ex; }
static void rec(int i,int np,const u32*P,const int*E,i64 cur,i64 B,i64 d,stats*st){
  if(i==np){ check(d, d>0? cur : -cur, st); return; }
  i128 c=cur;
  for(int j=0;j<=E[i];j++){ if(c>B) break; rec(i+1,np,P,E,(i64)c,B,d,st); c*=P[i]; }
}
static int cmp_hit(const void*a,const void*b){ u32 x=((hit*)a)->off, y=((hit*)b)->off; return x<y?-1:x>y; }
static void do_unitA(i64 t0, i64 t1, abuf*ab, stats*st){
  i64 U=t1-t0; int nseg=(int)((U+SA-1)/SA);
  if(!ab->fac){ ab->fac=malloc(4L*SA*MAXF); ab->nf=malloc(SA); ab->nbk=0; ab->bk=0; ab->ov.h=0; ab->ov.n=ab->ov.cap=0; }
  if(nseg>ab->nbk){ ab->bk=realloc(ab->bk,sizeof(hvec)*nseg); for(int i=ab->nbk;i<nseg;i++){ ab->bk[i].h=0; ab->bk[i].n=ab->bk[i].cap=0; } ab->nbk=nseg; }
  for(int i=0;i<nseg;i++) ab->bk[i].n=0;
  /* large primes: hits for the whole unit, bucketed by segment */
  for(long pi=0;pi<ntparts;pi++){ const u32*PPp=tparts[pi].p, *PRr=tparts[pi].r; long n=tparts[pi].n;
    for(long j=(pi==0?JSMALL:0);j<n;j++){ i64 p=PPp[j]; i64 x=((i64)PRr[j]-t0)%p; if(x<0) x+=p;
      for(; x<U; x+=p) hpush(&ab->bk[x>>20],(u32)x,(u32)p); } }
  for(int sg=0;sg<nseg;sg++){
    i64 s0=t0+(i64)sg*SA; long len=(long)((t1-s0<SA)?t1-s0:SA);
    memset(ab->nf,0,len); ab->ov.n=0;
    u32*fac=ab->fac; uint8_t*nf=ab->nf;
    #define ADDF(i_,p_) { long _i=(i_); if(nf[_i]<MAXF){ fac[_i*MAXF+nf[_i]]=(p_); nf[_i]++; } else { hpush(&ab->ov,(u32)_i,(p_)); } }
    for(long j=0;j<JSMALL;j++){ i64 p=TP[j]; i64 x=((i64)TR[j]-s0)%p; if(x<0) x+=p; for(;x<len;x+=p) ADDF(x,(u32)p) }
    hvec*b=&ab->bk[sg]; u32 base=(u32)((i64)sg*SA);
    for(long k=0;k<b->n;k++) ADDF((long)(b->h[k].off-base), b->h[k].p)
    #undef ADDF
    if(ab->ov.n){ st->ovf+=ab->ov.n; qsort(ab->ov.h,ab->ov.n,sizeof(hit),cmp_hit); }
    long ovp=0;
    for(long i=0;i<len;i++){
      i64 d=MSTEP*(s0+i)+RR; if(d==0) continue;
      i64 ad=d<0?-d:d; i64 B=bound_e(ad);
      u32 P[64]; int E[64]; int np=0;
      int cnt=nf[i];
      for(int k=0;k<cnt+1;k++){
        /* iterate tabled factors, then overflow entries for this i */
        if(k==cnt){ while(ovp<ab->ov.n && ab->ov.h[ovp].off<(u32)i) ovp++;
          while(ovp<ab->ov.n && ab->ov.h[ovp].off==(u32)i){ u32 p=ab->ov.h[ovp].p; ovp++; if((i64)p>B) continue;
            int ex=pexp(d,p,B); if(np<64){P[np]=p;E[np]=ex;np++;} }
          break; }
        u32 p=fac[i*MAXF+k]; if((i64)p>B) continue;
        int ex=pexp(d,p,B);
        P[np]=p; E[np]=ex; np++;
      }
      { static const int sp[2]={2,5}; for(int q=0;q<2;q++){ int p=sp[q]; if(MSTEP%p) continue; int ex=0; u64 pk=p; while((i64)pk<=B && Nmod(d,pk)==0){ ex++; pk*=p; } if(ex&&np<64){P[np]=p;E[np]=ex;np++;} } }
      rec(0,np,P,E,1,B,d,st);
    }
  }
}

/* ===================== B unit: large prime q, small cofactor m (CRT enumeration) ===================== */
#define MMAXG 10000
typedef struct { i64 m; int ns; i64*s10; } admm;      /* residues s10 mod 10m with m | N(s10) and s10 == R (mod 10) */
static admm*AM; static int nAM;
static void init_adm(void){
  AM=malloc(sizeof(admm)*(MMAXG/2+2)); nAM=0;
  for(i64 m=1;m<=MMAXG;m+=2){ if(m%5==0) continue;
    i64 inv10=inv_mod(m%10,10); int cnt=0;
    for(i64 s=0;s<m;s++) if(Nmod(s,(u64)m)==0) cnt++;
    if(!cnt) continue;
    admm A; A.m=m; A.ns=cnt; A.s10=malloc(sizeof(i64)*cnt); int k=0;
    for(i64 s=0;s<m;s++) if(Nmod(s,(u64)m)==0){ i64 j=((((RR-s)%10)+10)%10)*inv10%10; A.s10[k++]=s+m*j; }
    AM[nAM++]=A; }
}
typedef struct { i64 DB0, DB1; stats*st; } bctx;
static void bq_cb(void*vc, u64 q_, u64 r_){
  bctx*c=(bctx*)vc; stats*st=c->st; i64 q=(i64)q_, r=(i64)r_;
  i64 Bmax=bound_e(c->DB1);
  for(int a=0;a<nAM;a++){
    i64 m=AM[a].m; if(m*q>Bmax) break;
    i64 L10=10*m, qinv=inv_mod(q%L10,L10), L=L10*q, e=m*q;
    double dmd=((double)e-50.0)/2.3; i64 dmin=(i64)floor(dmd)-2; if(dmin<c->DB0) dmin=c->DB0; if(dmin<1) dmin=1;
    if(dmin>c->DB1) continue;
    i64 rmod=r%L10;
    for(int k=0;k<AM[a].ns;k++){
      i64 kk=((((AM[a].s10[k]-rmod)%L10)+L10)%L10)*qinv%L10;
      i64 D0=r+q*kk;                         /* d == D0 (mod L): d == r (q), d == s (m), d == R (10) */
      st->events++;
      i64 first=dmin+(((D0-dmin)%L)+L)%L;
      for(i64 d=first; d<=c->DB1; d+=L) if(e<=bound_e(d)) check(d,e,st);
      i64 lo=-c->DB1; first=lo+(((D0-lo)%L)+L)%L;
      for(i64 d=first; d<=-dmin; d+=L) if(e<=bound_e(-d)) check(d,-e,st);
    }
  }
}
/* per-d scan (good when the d-progression is short): residues of d mod small primes updated incrementally */
static int nsp; static int spp[1300]; static uint8_t *spr[1300];
static int *nsp_le;     /* nsp_le[x] = number of tabled small primes <= x */
static i64 *nm_le, *np_le;  /* admissible m <= x : count, and total residues */
static int BMODE=0; static double FROMKEY=-1;     /* 0 auto, 1 per-d scan, 2 CRT */
static void init_sp(void){
  nsp=0;
  for(int p=3;p<=MMAXG;p+=2){ int isp=1; for(int a=3;a*a<=p;a+=2) if(p%a==0){isp=0;break;} if(!isp) continue;
    if(MSTEP%p==0) continue;
    uint8_t*t=calloc(p,1); int any=0;
    for(int r=0;r<p;r++) if(Nmod(r,(u64)p)==0){ t[r]=1; any=1; }
    if(!any){free(t);continue;} spp[nsp]=p; spr[nsp]=t; nsp++; }
  nsp_le=calloc(MMAXG+2,sizeof(int)); nm_le=calloc(MMAXG+2,sizeof(i64)); np_le=calloc(MMAXG+2,sizeof(i64));
  { int k=0; for(int x=0;x<=MMAXG+1;x++){ while(k<nsp && spp[k]<=x) k++; nsp_le[x]=k; } }
  { int k=0; i64 c=0,t=0; for(int x=0;x<=MMAXG+1;x++){ while(k<nAM && AM[k].m<=x){ c++; t+=AM[k].ns; k++; } nm_le[x]=c; np_le[x]=t; } }
}
static void scan_cb(void*vc, u64 q_, u64 r_){
  bctx*c=(bctx*)vc; stats*st=c->st; i64 q=(i64)q_, r=(i64)r_;
  i64 Mq=(i64)MSTEP*q;
  i64 j0=((((RR-r)%MSTEP)+MSTEP)%MSTEP) * inv_mod(q%MSTEP,MSTEP) % MSTEP;
  i64 s=r+q*j0;
  double dm=((double)q-50.0)/2.3; i64 dmin=(i64)floor(dm)-2; if(dmin<c->DB0) dmin=c->DB0; if(dmin<1) dmin=1;
  i64 mmaxall=bound_e(c->DB1)/q; if(mmaxall>MMAXG) mmaxall=MMAXG;
  int ns=nsp_le[mmaxall];
  i64 res[1300], stp[1300];
  for(int sg=0;sg<2;sg++){
    i64 lo = sg==0? dmin : -c->DB1, hi = sg==0? c->DB1 : -dmin;
    if(lo>hi) continue;
    i64 first = lo + ((((s-lo)%Mq)+Mq)%Mq);
    if(first>hi) continue;
    for(int i=0;i<ns;i++){ i64 p=spp[i]; i64 x=first%p; if(x<0)x+=p; res[i]=x; stp[i]=Mq%p; }
    for(i64 d=first; d<=hi; d+=Mq){
      st->events++;
      i64 ad=d<0?-d:d; i64 B=bound_e(ad); i64 mmax=B/q;
      if(mmax>=1){
        int pp[64], pe[64]; int np=0;
        for(int i=0;i<ns && spp[i]<=mmax;i++) if(spr[i][res[i]] && np<64){ pp[np]=spp[i]; pe[np]=pexp(d,(u64)spp[i],mmax); np++; }
        i64 ms[4096]; int nm=1; ms[0]=1;
        for(int i=0;i<np;i++){ int cur=nm; for(int j=0;j<cur;j++){ i64 m=ms[j]; for(int k=1;k<=pe[i];k++){ m*=pp[i]; if(m>mmax) break; if(nm<4096) ms[nm++]=m; } } }
        for(int j=0;j<nm;j++){ i64 e=ms[j]*q; check(d, d>0? e : -e, st); }
      }
      for(int i=0;i<ns;i++){ i64 x=res[i]+stp[i]; if(x>=spp[i]) x-=spp[i]; res[i]=x; }
    }
  }
}
static void b_dispatch(void*vc, u64 q_, u64 r_){
  bctx*c=(bctx*)vc; i64 q=(i64)q_;
  if(BMODE==1){ scan_cb(vc,q_,r_); return; } if(BMODE==2){ bq_cb(vc,q_,r_); return; }
  i64 mmaxall=bound_e(c->DB1)/q; if(mmaxall>MMAXG) mmaxall=MMAXG; if(mmaxall<0) mmaxall=0;
  double dmin=((double)q-50.0)/2.3; if(dmin<(double)c->DB0) dmin=(double)c->DB0;
  double nev=2.0*((double)c->DB1-dmin)/(10.0*(double)q); if(nev<0) nev=0;
  double cost_scan = nev*(nsp_le[mmaxall]*1.0+12.0) + 2.0*nsp_le[mmaxall];
  double cost_crt  = nm_le[mmaxall]*45.0 + np_le[mmaxall]*25.0;
  if(cost_scan<=cost_crt) scan_cb(vc,q_,r_); else bq_cb(vc,q_,r_);
}
static void bq_batch(void*ctx,u64*qs,int n){
  bctx*c=(bctx*)ctx; c->st->primes+=n;
  int m=0; u64 big[LANES];
  for(int i=0;i<n;i++){ if(qs[i]<64) roots_small(qs[i],b_dispatch,ctx); else big[m++]=qs[i]; }
  if(m) roots_batch(m,big,b_dispatch,ctx);
}
static void do_unitB(u64 q0,u64 q1,i64 DB0,i64 DB1,uint8_t**buf,stats*st){
  if(!*buf) *buf=malloc(SEGN);
  bctx c={DB0,DB1,st};
  for_primes(q0,q1,*buf,bq_batch,&c);
}

/* ===================== units, scheduling, progress ===================== */
typedef struct { char type; i64 a0,a1; i64 db0,db1; double key; int done; } unit;
static unit*units; static long nunits, ucap;
static long *order; static long nextu=0; static pthread_mutex_t qlock=PTHREAD_MUTEX_INITIALIZER;
static FILE*progf; static double tstart; static long ndone_run=0, ndone_total=0;
static stats gtot; static int log2UA=24; static int log2UB=30;
static void add_unit(unit u){ if(nunits==ucap){ ucap=ucap?2*ucap:1024; units=realloc(units,sizeof(unit)*ucap);} units[nunits++]=u; }
static int ukey_cmp(const unit*x,const unit*y){
  if(x->type!=y->type) return x->type<y->type?-1:1;
  if(x->a0!=y->a0) return x->a0<y->a0?-1:1;
  if(x->a1!=y->a1) return x->a1<y->a1?-1:1;
  if(x->type=='B'){ if(x->db0!=y->db0) return x->db0<y->db0?-1:1; if(x->db1!=y->db1) return x->db1<y->db1?-1:1; }
  return 0; }
static int cmp_ukey(const void*a,const void*b){ return ukey_cmp(&units[*(long*)a],&units[*(long*)b]); }
static int cmp_order(const void*a,const void*b){ double x=units[*(long*)a].key, y=units[*(long*)b].key; return x<y?-1:x>y; }
static void frontier_report(void){
  /* smallest key among unfinished units */
  double fr=-1; for(long k=0;k<nunits;k++){ unit*u=&units[order[k]]; if(!u->done){ fr=u->key; break; } }
  double el=now()-tstart;
  char buf[512];
  if(fr<0) snprintf(buf,sizeof buf,"[%.0fs] ALL %ld units done. candidates=%ld passed=%ld passed2=%ld solutions=%ld overflow=%ld primes=%ld progressions=%ld\n",el,nunits,gtot.cand,gtot.pass,gtot.pass2,gtot.sols,gtot.ovf,gtot.primes,gtot.events);
  else snprintf(buf,sizeof buf,"[%.0fs] units done %ld/%ld (this run %ld); job complete for |d| < %.6g; solutions so far (this run): %ld\n",el,ndone_total,nunits,ndone_run,fr,gtot.sols);
  fputs(buf,stderr); if(logfp){ fputs(buf,logfp); fflush(logfp); }
}
static void* worker(void*arg){
  (void)arg; abuf ab; memset(&ab,0,sizeof ab); uint8_t*bbuf=0;
  for(;;){
    pthread_mutex_lock(&qlock);
    long k; unit*u=0;
    while(nextu<nunits){ k=order[nextu++]; if(!units[k].done){ u=&units[k]; break; } }
    pthread_mutex_unlock(&qlock);
    if(!u) break;
    stats st; memset(&st,0,sizeof st); double t0=now();
    if(u->type=='A') do_unitA(u->a0,u->a1,&ab,&st);
    else do_unitB((u64)u->a0,(u64)u->a1,u->db0,u->db1,&bbuf,&st);
    double dt=now()-t0;
    pthread_mutex_lock(&qlock);
    u->done=1; ndone_run++; ndone_total++;
    gtot.cand+=st.cand; gtot.pass+=st.pass; gtot.pass2+=st.pass2; gtot.sols+=st.sols; gtot.ovf+=st.ovf; gtot.primes+=st.primes; gtot.events+=st.events;
    if(u->type=='A') fprintf(progf,"A %lld %lld cand=%ld passed=%ld passed2=%ld sols=%ld ovf=%ld sec=%.1f\n",(long long)u->a0,(long long)u->a1,st.cand,st.pass,st.pass2,st.sols,st.ovf,dt);
    else fprintf(progf,"B %lld %lld %lld %lld primes=%ld progressions=%ld cand=%ld passed=%ld passed2=%ld sols=%ld sec=%.1f\n",(long long)u->a0,(long long)u->a1,(long long)u->db0,(long long)u->db1,st.primes,st.events,st.cand,st.pass,st.pass2,st.sols,dt);
    fflush(progf); fsync(fileno(progf));
    static double lastrep=0; if(now()-lastrep>60 || nextu>=nunits){ lastrep=now(); frontier_report(); }
    pthread_mutex_unlock(&qlock);
  }
  return 0;
}
static void dump_roots(u64 q0,u64 q1,const char*out);
static FILE*dumpf;
static void dump_cb(void*ctx,u64 q,u64 r){ (void)ctx; fprintf(dumpf,"%llu %llu\n",(unsigned long long)q,(unsigned long long)r); }
static void dump_batch(void*ctx,u64*qs,int n){ int m=0; u64 big[LANES]; for(int i=0;i<n;i++){ if(qs[i]<64) roots_small(qs[i],dump_cb,ctx); else big[m++]=qs[i]; } if(m) roots_batch(m,big,dump_cb,ctx); }
static void dump_roots(u64 q0,u64 q1,const char*out){ dumpf=fopen(out,"w"); make_base((u64)sqrt((double)q1)+2); uint8_t*buf=malloc(SEGN); for_primes(q0,q1,buf,dump_batch,0); fclose(dumpf); }

int main(int argc,char**argv){
  if(argc>=4 && !strcmp(argv[1],"-t192")){ stats st; memset(&st,0,sizeof st); exact_check(atoll(argv[2]),atoll(argv[3]),&st,1); return 0; }
  if(argc>=5 && !strcmp(argv[1],"-roots")){ dump_roots(strtoull(argv[2],0,10),strtoull(argv[3],0,10),argv[4]); return 0; }
  int nth=(int)sysconf(_SC_NPROCESSORS_ONLN); const char*pfile="progress.txt",*sfile="solutions.txt",*lfile="log.txt";
  i64 ar[64][2]; int na=0; i64 br[64][5]; int nb=0; int curUB=-1;
  for(int i=1;i<argc;i++){
    if(!strcmp(argv[i],"-j")) nth=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-T")) TT=strtoull(argv[++i],0,10);
    else if(!strcmp(argv[i],"-R")) RR=atoll(argv[++i]);
    else if(!strcmp(argv[i],"-a")){ ar[na][0]=atoll(argv[i+1]); ar[na][1]=atoll(argv[i+2]); na++; i+=2; }
    else if(!strcmp(argv[i],"-b")){ for(int k=0;k<4;k++) br[nb][k]=atoll(argv[i+1+k]); br[nb][4]=curUB; nb++; i+=4; }
    else if(!strcmp(argv[i],"-bu")) curUB=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-p")) pfile=argv[++i];
    else if(!strcmp(argv[i],"-s")) sfile=argv[++i];
    else if(!strcmp(argv[i],"-l")) lfile=argv[++i];
    else if(!strcmp(argv[i],"-ua")) log2UA=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-ub")) log2UB=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-bm")) BMODE=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-from")) FROMKEY=atof(argv[++i]);
    else { fprintf(stderr,"unknown arg %s\n",argv[i]); return 1; }
  }
  init_leg(); init_adm(); init_sp();
  logfp=fopen(lfile,"a"); solf=fopen(sfile,"a");
  /* sanity of B ranges */
  u64 maxq=1000;
  for(int b=0;b<nb;b++){
    i64 q0=br[b][0], q1=br[b][1], DB1=br[b][3];
    if((u64)q0<TT){ fprintf(stderr,"B range must start at q0 >= T\n"); return 1; }
    if((double)TT*(double)TT <= 2.3*(double)DB1+60){ fprintf(stderr,"need T^2 > 2.3*DB1\n"); return 1; }
    if(bound_e(DB1)/q0 > MMAXG){ fprintf(stderr,"cofactor bound 2.3*DB1/q0 exceeds %d\n",MMAXG); return 1; }
    if((u64)q1>maxq) maxq=q1;
  }
  { u64 mx = maxq>TT? maxq : TT; make_base((u64)sqrt((double)mx)+2); }
  /* units */
  i64 UA=1LL<<log2UA, UB=1LL<<log2UB;
  for(int a=0;a<na;a++) for(i64 t=ar[a][0]; t<ar[a][1]; t+=UA){ unit u; memset(&u,0,sizeof u); u.type='A'; u.a0=t; u.a1=t+UA<ar[a][1]?t+UA:ar[a][1];
      i64 d0=MSTEP*u.a0+RR, d1=MSTEP*(u.a1-1)+RR; i64 m0=d0<0?-d0:d0, m1=d1<0?-d1:d1; u.key=(double)(m0<m1?m0:m1); if(d0<=0 && d1>=0) u.key=0; add_unit(u); }
  for(int b=0;b<nb;b++){ i64 UBb = br[b][4]>0 ? (1LL<<br[b][4]) : UB; for(i64 q=br[b][0]; q<br[b][1]; q+=UBb){ unit u; memset(&u,0,sizeof u); u.type='B'; u.a0=q; u.a1=q+UBb<br[b][1]?q+UBb:br[b][1]; u.db0=br[b][2]; u.db1=br[b][3];
      double k=((double)u.a0-50.0)/2.3; if(k<(double)u.db0) k=(double)u.db0; u.key=k; add_unit(u); } }
  /* resume */
  FILE*pf=fopen(pfile,"r"); long resumed=0;
  if(pf){
    long*ix=malloc(sizeof(long)*nunits); for(long k=0;k<nunits;k++) ix[k]=k; qsort(ix,nunits,sizeof(long),cmp_ukey);
    char line[512]; while(fgets(line,sizeof line,pf)){ char ty; long long x0,x1,x2=0,x3=0; int n=sscanf(line,"%c %lld %lld %lld %lld",&ty,&x0,&x1,&x2,&x3);
      if(n<3 || (ty!='A'&&ty!='B') || (ty=='B'&&n<5)) continue;
      unit probe; memset(&probe,0,sizeof probe); probe.type=ty; probe.a0=x0; probe.a1=x1; if(ty=='B'){probe.db0=x2; probe.db1=x3;}
      long lo=0, hi=nunits-1;
      while(lo<=hi){ long mid=(lo+hi)/2; int c=ukey_cmp(&probe,&units[ix[mid]]); if(c==0){ unit*u=&units[ix[mid]]; if(!u->done){u->done=1; resumed++;} break; } if(c<0) hi=mid-1; else lo=mid+1; } }
    fclose(pf); free(ix); }
  if(FROMKEY>0){ long sk=0; for(long k=0;k<nunits;k++) if(!units[k].done && units[k].key<FROMKEY){ units[k].done=1; sk++; } resumed+=sk;
    fprintf(stderr,"-from %.6g: %ld units below it treated as done (checkpoint)\n",FROMKEY,sk); }
  ndone_total=resumed;
  progf=fopen(pfile,"a");
  order=malloc(sizeof(long)*nunits); for(long k=0;k<nunits;k++) order[k]=k; qsort(order,nunits,sizeof(long),cmp_order);
  int needA=0; for(long k=0;k<nunits;k++) if(units[k].type=='A' && !units[k].done) needA=1;
  { char buf[512]; snprintf(buf,sizeof buf,"k7 start: K=%d R=%lld T=%llu threads=%d units=%ld (resumed %ld already done)\n",K,(long long)RR,(unsigned long long)TT,nth,nunits,resumed); fputs(buf,stderr); if(logfp){fputs(buf,logfp); fflush(logfp);} }
  tstart=now();
  if(needA){ if(TT>=(1ULL<<32)){ fprintf(stderr,"T must be < 2^32\n"); return 1; } build_table(nth); }
  pthread_t th[256]; for(int i=0;i<nth;i++) pthread_create(&th[i],0,worker,0); for(int i=0;i<nth;i++) pthread_join(th[i],0);
  frontier_report();
  return 0;
}
