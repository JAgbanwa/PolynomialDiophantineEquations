// search14 (= search13 + lazy-reduction Montgomery square roots; search12 + division-free bucket indexing + AVX2 survivor scan + second pre-sieve pattern 29*31*37;  search10 + compact bucket sieve: p stored in entries, N-root exceptions as a sorted list): complete search for  x^2 y + x y^2 + x z^2 + 2x^2 - z^2 + 3 = 0  over a range of a (x = 2a).
// x = 2a, y = b - a:  2a b^2 + (2a-1) z^2 = N(a) := 2a^3 - 8a^2 - 3.
// Proven necessary: a = 3 (mod 36); primes of a/3 are +-1 mod 12; primes of t=|2a-1| are 19 (once) or QR mod 19;
// z^2 = 3 (mod 2a); b odd.  N-sieve: p || N(a) with (-2a(2a-1)/p) = -1  =>  a impossible.
// a = s*m, m = r + 36 j  (r = 3 if s = +1, r = 33 if s = -1).   Usage: search10 s J0 J1 [S]  (requires nbad.txt)
// Same mathematics as search9 (validated); engineering changes only:
//  * survivors of the exclusion sieves are compacted (bitmap + rank) before factoring m over good primes
//    (no 2MB head memset, cache-friendly random accesses);
//  * q = 1 (mod 8) square roots batched 4-wide, non-residue search with constant moduli;
//  * +-symmetry: only one root of each pair {R, m-R} is built by CRT; both lifts z1, 2m-z1 are tested.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
#include <immintrin.h>
typedef uint64_t u64; typedef int64_t i64; typedef uint32_t u32;
typedef __int128 i128; typedef unsigned __int128 u128;

static inline u64 mulmod(u64 a,u64 b,u64 m){ return (u64)((u128)a*b%m); }
static i64 inv_i64(i64 a,i64 m){ i64 b=((a%m)+m)%m, r0=b,r1=m,s0=1,s1=0; while(r1){ i64 q=r0/r1,t=r0-q*r1; r0=r1; r1=t; t=s0-q*s1; s0=s1; s1=t; } s0%=m; if(s0<0) s0+=m; return s0; }
static inline u64 bmod(u64 x,u64 p,u64 mu){ u64 q=(u64)(((u128)x*mu)>>64); u64 r=x-q*p; return r>=p? r-p : r; }
static inline u32 inv_u32(u32 a,u32 m){ i64 t=0,nt=1; u32 r=m,nr=a%m; while(nr){ u32 q=r/nr; i64 tt=t-(i64)q*nt; t=nt; nt=tt; u32 rr=r-q*nr; r=nr; nr=rr; } if(t<0) t+=m; return (u32)t; }
typedef struct { u64 n, ni, r1; } Mont;
static inline void mont_init(Mont *M,u64 n){ M->n=n; u64 inv=n; for(int i=0;i<6;i++) inv*=2-n*inv; M->ni=0-inv; M->r1=(0-n)%n; }
static inline u64 mmul(u64 a,u64 b,const Mont *M){ u128 t=(u128)a*b; u64 m=(u64)t*M->ni; u128 u=t+(u128)m*M->n; u64 r=(u64)(u>>64); return r>=M->n? r-M->n : r; }
static inline u64 m_small(u64 c,const Mont *M){ return mulmod(c, M->r1, M->n); }   // c*R mod n
static inline u64 from_m(u64 a,const Mont *M){ return mmul(a,1,M); }
static u64 mpow(u64 b,u64 e,const Mont *M){ u64 r=M->r1; while(e){ if(e&1) r=mmul(r,b,M); b=mmul(b,b,M); e>>=1; } return r; }
static int jacobi(u64 a,u64 n){ int s=1; a%=n; while(a){ while(!(a&1)){ a>>=1; u64 r=n&7; if(r==3||r==5) s=-s; } u64 t=a; a=n; n=t; if((a&3)==3&&(n&3)==3) s=-s; a%=n; } return n==1? s:0; }
static u64 sqrt3_prime(u64 q){ // q prime > 3 with (3/q)=1  (used only for the small sieving primes)
    Mont M; mont_init(&M,q); u64 three=m_small(3,&M);
    if((q&3)==3) return from_m(mpow(three,(q+1)/4,&M),&M);
    if((q&7)==5){ u64 two_a=m_small(6,&M); u64 v=mpow(two_a,(q-5)/8,&M); u64 i=mmul(mmul(two_a,v,&M),v,&M);
        u64 one=M.r1; u64 im1 = i>=one ? i-one : i+q-one; return from_m(mmul(mmul(three,v,&M),im1,&M),&M); }
    u64 Q=q-1; int S=0; while(!(Q&1)){ Q>>=1; S++; }
    u64 zn=2; while(jacobi(zn,q)!=-1) zn++;
    u64 c=mpow(m_small(zn,&M),Q,&M), t=mpow(three,Q,&M), R=mpow(three,(Q+1)/2,&M), one=M.r1; int Mx=S;
    while(t!=one){ int i=0; u64 tt=t; while(tt!=one){ tt=mmul(tt,tt,&M); i++; }
        u64 b=c; for(int j=0;j<Mx-i-1;j++) b=mmul(b,b,&M);
        R=mmul(R,b,&M); c=mmul(b,b,&M); t=mmul(t,c,&M); Mx=i; }
    return from_m(R,&M);
}
static inline u64 addm(u64 a,u64 b,u64 n){ u64 s=a+b; return s>=n? s-n : s; }
// 4-lane interleaved: class A (q=3 mod 4): rho = 3^((q+1)/4);  class B (q=5 mod 8): Atkin with base 6
static void sqrt3_batch4(const u64 *q, u64 *rho, int cls){
    Mont M[4]; u64 e[4], r[4]; u64 c = cls==0? 3:6; int top=0;
    for(int l=0;l<4;l++){ mont_init(&M[l],q[l]); e[l]= cls==0? (q[l]+1)/4 : (q[l]-5)/8; int tb=63-__builtin_clzll(e[l]); if(tb>top) top=tb; r[l]=M[l].r1; }
    for(int b=top;b>=0;b--){
        r[0]=mmul(r[0],r[0],&M[0]); r[1]=mmul(r[1],r[1],&M[1]); r[2]=mmul(r[2],r[2],&M[2]); r[3]=mmul(r[3],r[3],&M[3]);
        for(int l=0;l<4;l++){ u64 n=M[l].n, x=r[l]; u64 x2=addm(x,x,n), x3=addm(x2,x,n); u64 y = c==3? x3 : addm(x3,x3,n);
            u64 mask=0-((e[l]>>b)&1); r[l]=(y&mask)|(x&~mask); } }
    for(int l=0;l<4;l++){
        if(cls==0){ rho[l]=from_m(r[l],&M[l]); }
        else { u64 n=M[l].n, v=r[l]; u64 x=mmul(v,v,&M[l]); u64 x2=addm(x,x,n), x3=addm(x2,x,n), i=addm(x3,x3,n); u64 one=M[l].r1; u64 im1= i>=one? i-one : i+n-one;
               u64 v2=addm(v,v,n), v3=addm(v2,v,n); rho[l]=from_m(mmul(v3,im1,&M[l]),&M[l]); } }
}
// non-residue for q = 1 (mod 8): (p/q) = (q/p); constant moduli so the compiler avoids divisions
static unsigned char Q5[5],Q7[7],Q11[11],Q13[13],Q17[17],Q19[19],Q23[23],Q29[29],Q31[31],Q37[37],Q41[41],Q43[43],Q47[47],Q53[53],Q59[59],Q61[61],Q67[67],Q71[71],Q73[73],Q79[79];
static void init_qr(void){
#define IQ(P) for(int x=1;x<P;x++) Q##P[(x*x)%P]=1;
    IQ(5) IQ(7) IQ(11) IQ(13) IQ(17) IQ(19) IQ(23) IQ(29) IQ(31) IQ(37) IQ(41) IQ(43) IQ(47) IQ(53) IQ(59) IQ(61) IQ(67) IQ(71) IQ(73) IQ(79)
}
static inline u64 nonres(u64 q){
#define TQ(P) if(!Q##P[q%P]) return P;
    TQ(5) TQ(7) TQ(11) TQ(13) TQ(17) TQ(19) TQ(23) TQ(29) TQ(31) TQ(37) TQ(41) TQ(43) TQ(47) TQ(53) TQ(59) TQ(61) TQ(67) TQ(71) TQ(73) TQ(79)
    u64 z=83; while(jacobi(z,q)!=-1) z++; return z;
}
// class C (q = 1 mod 8), 4 lanes: c = zn^Q, u = 3^((Q-1)/2) batched, then scalar Tonelli-Shanks finish
static void sqrt3_batchC(const u64 *q, u64 *rho){
    Mont M[4]; u64 Q[4], e2[4], zm[4], c[4], u[4]; int S[4]; int top=0;
    for(int l=0;l<4;l++){ mont_init(&M[l],q[l]); u64 qq=q[l]-1; S[l]=__builtin_ctzll(qq); Q[l]=qq>>S[l]; e2[l]=(Q[l]-1)/2;
        zm[l]=m_small(nonres(q[l]),&M[l]); c[l]=M[l].r1; u[l]=M[l].r1; int tb=63-__builtin_clzll(Q[l]); if(tb>top) top=tb; }
    for(int b=top;b>=0;b--){
        c[0]=mmul(c[0],c[0],&M[0]); c[1]=mmul(c[1],c[1],&M[1]); c[2]=mmul(c[2],c[2],&M[2]); c[3]=mmul(c[3],c[3],&M[3]);
        u[0]=mmul(u[0],u[0],&M[0]); u[1]=mmul(u[1],u[1],&M[1]); u[2]=mmul(u[2],u[2],&M[2]); u[3]=mmul(u[3],u[3],&M[3]);
        u64 y0=mmul(c[0],zm[0],&M[0]), y1=mmul(c[1],zm[1],&M[1]), y2=mmul(c[2],zm[2],&M[2]), y3=mmul(c[3],zm[3],&M[3]);
        u64 ys[4]={y0,y1,y2,y3};
        for(int l=0;l<4;l++){ u64 mask=0-((Q[l]>>b)&1); c[l]=(ys[l]&mask)|(c[l]&~mask);
            u64 n=M[l].n, x=u[l]; u64 x3=addm(addm(x,x,n),x,n); u64 mk2=0-((e2[l]>>b)&1); u[l]=(x3&mk2)|(x&~mk2); } }
    for(int l=0;l<4;l++){ const Mont *Mp=&M[l]; u64 n=Mp->n, one=Mp->r1;
        u64 R=addm(addm(u[l],u[l],n),u[l],n);                // 3^((Q+1)/2)
        u64 uu=mmul(u[l],u[l],Mp); u64 t=addm(addm(uu,uu,n),uu,n); // 3^Q
        u64 cc=c[l]; int Mx=S[l];
        while(t!=one){ int i=0; u64 tt=t; while(tt!=one){ tt=mmul(tt,tt,Mp); i++; if(i>=Mx) break; }
            u64 b=cc; for(int j=0;j<Mx-i-1;j++) b=mmul(b,b,Mp);
            R=mmul(R,b,Mp); cc=mmul(b,b,Mp); t=mmul(t,cc,Mp); Mx=i; }
        rho[l]=from_m(R,Mp); }
}

// Lazy-reduction Montgomery square roots of 3 (requires q < 2^56 so that inputs < 12q keep outputs < 2q).
// mmul_lz(a,b): a*b < q*2^64 required; returns (ab + mq)/2^64 < 2q (no final subtraction).
static inline u64 mmul_lz(u64 a,u64 b,u64 n,u64 ni){ u128 t=(u128)a*b; u64 m=(u64)t*ni; u128 u=t+(u128)m*n; return (u64)(u>>64); }
static inline u64 red1(u64 x,u64 n){ return x>=n? x-n : x; }          // [0,2n) -> [0,n)
// class A (q=3 mod 4): rho = 3^((q+1)/4);  class B (q=5 mod 8): Atkin with base 6
static void sqrt3_batch4_lz(const u64 *q, u64 *rho, int cls){
    u64 n[4], ni[4], e[4], r[4]; int top=0;
    for(int l=0;l<4;l++){ n[l]=q[l]; u64 inv=n[l]; for(int i=0;i<6;i++) inv*=2-n[l]*inv; ni[l]=0-inv;
        e[l]= cls==0? (q[l]+1)/4 : (q[l]-5)/8; int tb=63-__builtin_clzll(e[l]); if(tb>top) top=tb; r[l]=(0-n[l])%n[l]; }
    for(int b=top;b>=0;b--){
        u64 s0=mmul_lz(r[0],r[0],n[0],ni[0]), s1=mmul_lz(r[1],r[1],n[1],ni[1]), s2=mmul_lz(r[2],r[2],n[2],ni[2]), s3=mmul_lz(r[3],r[3],n[3],ni[3]);
        u64 sv[4]={s0,s1,s2,s3};
        for(int l=0;l<4;l++){ u64 x=sv[l]; u64 y = cls==0? 3*x : 6*x; u64 mask=0-((e[l]>>b)&1); r[l]=(y&mask)|(x&~mask); } }
    for(int l=0;l<4;l++){ Mont M; M.n=n[l]; M.ni=ni[l]; M.r1=(0-n[l])%n[l];
        u64 x=r[l]; x%=n[l];                                          // r < 12q -> canonical
        if(cls==0){ rho[l]=from_m(x,&M); }
        else { u64 v=x; u64 vv=mmul(v,v,&M); u64 i=(6*vv)%n[l]; u64 one=M.r1; u64 im1= i>=one? i-one : i+n[l]-one;
               u64 v3=(3*v)%n[l]; rho[l]=from_m(mmul(v3,im1,&M),&M); } }
}
// class C (q = 1 mod 8): c = zn^Q, u = 3^((Q-1)/2) with lazy reduction, then scalar Tonelli-Shanks finish
static void sqrt3_batchC_lz(const u64 *q, u64 *rho){
    u64 n[4], ni[4], Q[4], e2[4], zm[4], c[4], u[4]; int S[4]; int top=0;
    for(int l=0;l<4;l++){ n[l]=q[l]; u64 inv=n[l]; for(int i=0;i<6;i++) inv*=2-n[l]*inv; ni[l]=0-inv;
        u64 qq=q[l]-1; S[l]=__builtin_ctzll(qq); Q[l]=qq>>S[l]; e2[l]=(Q[l]-1)/2;
        u64 r1=(0-n[l])%n[l]; zm[l]=mulmod(nonres(q[l]),r1,n[l]); c[l]=r1; u[l]=r1; int tb=63-__builtin_clzll(Q[l]); if(tb>top) top=tb; }
    for(int b=top;b>=0;b--){
        for(int l=0;l<4;l++){ c[l]=mmul_lz(c[l],c[l],n[l],ni[l]); u[l]=mmul_lz(u[l],u[l],n[l],ni[l]); }
        for(int l=0;l<4;l++){ u64 y=mmul_lz(c[l],zm[l],n[l],ni[l]); u64 mask=0-((Q[l]>>b)&1); c[l]=(y&mask)|(c[l]&~mask);
            u64 x=u[l], x3=3*x; u64 mk2=0-((e2[l]>>b)&1); u[l]=(x3&mk2)|(x&~mk2); } }
    for(int l=0;l<4;l++){ Mont M; M.n=n[l]; M.ni=ni[l]; M.r1=(0-n[l])%n[l]; const Mont *Mp=&M; u64 nn=n[l], one=M.r1;
        u64 uu0=u[l]%nn, cc=c[l]%nn;
        u64 R=(3*uu0)%nn;                                   // 3^((Q+1)/2)
        u64 uu=mmul(uu0,uu0,Mp); u64 t=(3*uu)%nn;           // 3^Q
        int Mx=S[l];
        while(t!=one){ int i=0; u64 tt=t; while(tt!=one){ tt=mmul(tt,tt,Mp); i++; if(i>=Mx) break; }
            u64 bb=cc; for(int j=0;j<Mx-i-1;j++) bb=mmul(bb,bb,Mp);
            R=mmul(R,bb,Mp); cc=mmul(bb,bb,Mp); t=mmul(t,cc,Mp); Mx=i; }
        rho[l]=from_m(R,Mp); }
}

#define MA 45045u   /* 5*7*9*11*13 */
#define MB 7429u    /* 17*19*23 */
static unsigned char sqA[MA], sqB[MB];
static int QR19[19];
static u32 *P; static int NP, NPm; static unsigned char *mtype,*ttype; static u64 *inv36,*inv72,*s3,*pinv,*plim;
static int *Lmb,*Lmg,*Ltb; static int nLmb,nLmg,nLtb;
static unsigned char *pat; static u64 PW=146965; /* 5*7*13*17*19 */
static unsigned char *patB; static u64 PWB=33263; /* 29*31*37 */
static u64 *pmu; static u32 *itoff; static uint16_t *itab;   // Barrett constants; inverse tables for good p < 4096
static int NB; static u64 *bp_,*bj1,*bj2,*bp2; static int CHK=0, DUMP=0;

static void report(int s,u64 m,u64 b,u64 z){
    i128 a=(i128)s*m, x=2*a, y=(i128)b-a, Z=z; u128 X=(u128)x, Y=(u128)y, ZZ=(u128)Z; u128 val=X*X*Y+X*Y*Y+X*ZZ*ZZ+2*X*X-ZZ*ZZ+3;   /* mod 2^128 */
    #pragma omp critical
    { printf("SOLUTION x=%lld y=%lld z=%llu (a=%lld b=%llu) check(mod 2^128)=%s\n",(long long)x,(long long)y,(unsigned long long)z,(long long)a,(unsigned long long)b,val==0?"OK":"FAIL"); fflush(stdout); }
}


// ---------------- search11 main: search10 + bucket sieving for primes >= S (S a power of two) ----------------
#define PSH 20                       /* bucket entry = (item << PSH) | pos,  pos < S <= 2^20 */
typedef struct { u64 *e; u64 cnt, cap; } Bucket;
static inline void bpush(Bucket *B, u64 v){ if(B->cnt>=B->cap){ fprintf(stderr,"bucket overflow (cap %llu)\n",(unsigned long long)B->cap); exit(2);} B->e[B->cnt++]=v; }

int main(int argc,char**argv){
    if(argc<4){ fprintf(stderr,"usage: search14 s J0 J1 [S]\n"); return 1; }
    CHK=getenv("CHECKRES")!=0; DUMP=getenv("DUMP")!=0;
    const char *nbadfn = getenv("NBAD")? getenv("NBAD") : "nbad.txt";
    int s=atoi(argv[1]); u64 J0=strtoull(argv[2],0,10), J1=strtoull(argv[3],0,10);
    u64 S0= argc>4? strtoull(argv[4],0,10) : (1u<<19);
    int LOGS=6; while((1ull<<LOGS)<S0) LOGS++; if(LOGS>PSH){ fprintf(stderr,"S too large\n"); return 1; }
    u64 S=1ull<<LOGS, SMASK=S-1;
    u64 r=(s==1)?3:33;
    for(u64 i=0;i<MA;i++) sqA[(i*i)%MA]=1;
    for(u64 i=0;i<MB;i++) sqB[(i*i)%MB]=1;
    for(int i=1;i<19;i++) QR19[i*i%19]=1;
    init_qr();
    u64 mmax=r+36*J1; if(mmax>=(1ull<<56)){ fprintf(stderr,"range too large for lazy sqrt\n"); return 1; } u64 lim=(u64)sqrtl((long double)(2*mmax+2))+2, limm=(u64)sqrtl((long double)mmax)+2;
    // odd-only sieve of Eratosthenes: comp[i] <-> 2i+1
    u64 half=lim/2+1; char *comp=calloc(half+1,1); P=malloc(sizeof(u32)*(lim/2+100)); NP=0;
    for(u64 i=1;(2*i+1)*(2*i+1)<=lim;i++) if(!comp[i]){ u64 q=2*i+1; for(u64 j=(q*q)/2;j<half;j+=q) comp[j]=1; }
    for(u64 i=2;i<half;i++){ u64 q=2*i+1; if(q>lim) break; if(!comp[i]) P[NP++]=(u32)q; }   // primes >= 5
    free(comp);
    NPm=0; while(NPm<NP && P[NPm]<=limm) NPm++;
    mtype=malloc(NP); ttype=malloc(NP); inv36=malloc(8*NP); inv72=malloc(8*NP); s3=malloc(8*NP); pinv=malloc(8*NP); plim=malloc(8*NP);
    Lmb=malloc(4*NP); Lmg=malloc(4*NP); Ltb=malloc(4*NP); nLmb=nLmg=nLtb=0;
    u64 T36[36]={0}, T72[72]={0}; for(u64 x=1;x<72;x++) if(x%2&&x%3){ for(u64 k=0;k<72;k++){ if(k<36 && (k*x+1)%36==0 && x<36) T36[x]=k; if((k*x+1)%72==0) T72[x]=k; } }
    for(u64 x=1;x<36;x++) if(x%2&&x%3){ for(u64 k=0;k<36;k++) if((k*x+1)%36==0){ T36[x]=k; break; } }
    #pragma omp parallel for schedule(dynamic,8192)
    for(int k=0;k<NP;k++){ u64 p=P[k]; mtype[k]=(p%12==1||p%12==11); ttype[k]=(p==19)||QR19[p%19];
        { u64 k36=T36[p%36], k72=T72[p%72]; inv36[k]=(k36*p+1)/36; inv72[k]=(k72*p+1)/72; } { u64 iv=p; for(int t2=0;t2<6;t2++) iv*=2-p*iv; pinv[k]=iv; plim[k]=UINT64_MAX/p; }
        s3[k]=(mtype[k] && k<NPm)? sqrt3_prime(p):0; }
    for(int k=0;k<NP;k+=97){ u64 p=P[k]; if((36*inv36[k])%p!=1 || (72*inv72[k])%p!=1){ fprintf(stderr,"INV TABLE ERROR p=%llu\n",(unsigned long long)p); return 1; } }
    for(int k=0;k<NP;k++){ u64 p=P[k];
        int pre = (p==5||p==7||p==13||p==17||p==19||p==29||p==31||p==37);
        if(k<NPm){ if(mtype[k]) Lmg[nLmg++]=k; else if(!pre) Lmb[nLmb++]=k; }
        if(!ttype[k] && !pre) Ltb[nLtb++]=k; }
    // split each list into small (p < S, classic loops) and large (p >= S, buckets); lists are in increasing p
    int sLmb=0; while(sLmb<nLmb && P[Lmb[sLmb]]<S) sLmb++;
    int sLtb=0; while(sLtb<nLtb && P[Ltb[sLtb]]<S) sLtb++;
    int sLmg=0; while(sLmg<nLmg && P[Lmg[sLmg]]<S) sLmg++;
    pat=malloc(2*PW+8); for(u64 w=0;w<PW;w++){ u64 mm=r+36*w, tt=2*r-s+72*w;
        pat[w]= (mm%5==0||mm%7==0||mm%17==0||mm%19==0||tt%13==0); }
    memcpy(pat+PW,pat,PW);
    patB=malloc(2*PWB+8); for(u64 w=0;w<PWB;w++){ u64 mm=r+36*w, tt=2*r-s+72*w;
        patB[w]= (mm%29==0||mm%31==0||tt%29==0||tt%31==0||tt%37==0); }
    memcpy(patB+PWB,patB,PWB);
    pmu=malloc(8*NP); itoff=malloc(4*NP); { u64 tot=0; for(int k=0;k<NP;k++){ pmu[k]=~0ull/P[k]; itoff[k]=0xFFFFFFFFu; if(k<NPm && mtype[k] && P[k]<4096){ itoff[k]=(u32)tot; tot+=P[k]; } }
      itab=malloc(2*(tot+1)); for(int k=0;k<NP;k++) if(itoff[k]!=0xFFFFFFFFu){ u32 p=P[k]; for(u32 x=1;x<p;x++) itab[itoff[k]+x]=(uint16_t)inv_u32(x,p); itab[itoff[k]]=0; } }
    { FILE *f=fopen(nbadfn,"r"); if(!f){ fprintf(stderr,"%s missing\n",nbadfn); return 1; }
      u64 cap=1<<16; bp_=malloc(8*cap); bj1=malloc(8*cap); bj2=malloc(8*cap); bp2=malloc(8*cap); NB=0;
      u64 p,th,th2; while(fscanf(f,"%lu %lu %lu",&p,&th,&th2)==3){
        if((u64)NB>=cap){ cap*=2; bp_=realloc(bp_,8*cap); bj1=realloc(bj1,8*cap); bj2=realloc(bj2,8*cap); bp2=realloc(bp2,8*cap); }
        u64 p2=p*p; i64 i1=inv_i64(36,p), i2=inv_i64(36,p2);
        i64 x1=((i64)s*(i64)th-(i64)r)%(i64)p; if(x1<0) x1+=p;
        i128 x2=((i128)s*(i128)th2-(i128)r)%(i128)p2; if(x2<0) x2+=p2;
        bp_[NB]=p; bp2[NB]=p2; bj1[NB]=mulmod((u64)x1,(u64)i1,p); bj2[NB]=mulmod((u64)x2,(u64)i2,p2); NB++; }
      fclose(f); if(getenv("NOKILL")) NB=0; }
    int sNB=0; while(sNB<NB && bp_[sNB]<S) sNB++;          // nbad file is sorted by p
    for(int q=1;q<NB;q++) if(bp_[q]<bp_[q-1]){ fprintf(stderr,"nbad not sorted\n"); return 1; }
    // kofp: prime index of a large good prime p (for survivors hit through buckets)
    u32 *kofp=calloc((limm>>1)+2,sizeof(u32)); for(int a=sLmg;a<nLmg;a++){ int k=Lmg[a]; kofp[P[k]>>1]=(u32)k; }
    double EX=0, EG=0; u64 maxp=S;
    for(int a=sLmb;a<nLmb;a++){ u64 p=P[Lmb[a]]; EX+=(double)S/p; if(p>maxp) maxp=p; }
    for(int a=sLtb;a<nLtb;a++){ u64 p=P[Ltb[a]]; EX+=(double)S/p; if(p>maxp) maxp=p; }
    for(int q=sNB;q<NB;q++){ u64 p=bp_[q]; EX+=(double)S/p; if(p>maxp) maxp=p; }
    for(int a=sLmg;a<nLmg;a++){ EG+=(double)S/P[Lmg[a]]; if(P[Lmg[a]]>maxp) maxp=P[Lmg[a]]; }
    u64 NBK=(maxp>>LOGS)+2;
    u64 capX=(u64)(1.4*EX)+20000, capG=(u64)(1.4*EG)+20000;
    if(maxp>=(1ull<<42)){ fprintf(stderr,"prime too large for entry\n"); return 1; }
    u64 inv72_361=inv_i64(72,361);
    long long tot_kept=0,tot_cand=0,tot_alive=0,tot_sqrt=0,tot_assert=0;
    double t0=omp_get_wtime();
    #pragma omp parallel reduction(+:tot_kept,tot_cand,tot_alive,tot_sqrt,tot_assert)
    {
        int T=omp_get_thread_num(), NT=omp_get_num_threads();
        u64 len=J1-J0; u64 TA=J0+(u64)((u128)len*T/NT), TB=J0+(u64)((u128)len*(T+1)/NT);
        unsigned char *bad=malloc(S+128); u64 NW=S/64; u64 *bm=malloc(8*NW); u32 *pref=malloc(4*(NW+1));
        u64 SC=S/4+64;
        u32 *spos=malloc(4*SC); u64 *srem=malloc(8*SC); u32 *shead=malloc(4*SC);
        u64 CAP=4*SC; u32 *pn=malloc(4*CAP),*pk=malloc(4*CAP); unsigned char *pe=malloc(CAP);
        u64 *roots=malloc(8*16384),*tmp=malloc(8*16384);
        u64 *kq=malloc(8*SC), *krho=malloc(8*SC); u32 *LA=malloc(4*SC),*LB=malloc(4*SC),*LC=malloc(4*SC);
        u32 *om=malloc(4*(NPm+1)), *ot=malloc(4*(NP+1)); u64 *on=malloc(8*(NB+1)), *cun=malloc(8*(NB+1)), *uex=malloc(8*(NB+1));
        Bucket *BX=malloc(sizeof(Bucket)*NBK), *BG=malloc(sizeof(Bucket)*NBK);
        for(u64 b=0;b<NBK;b++){ BX[b].e=malloc(8*capX); BX[b].cnt=0; BX[b].cap=capX; BG[b].e=malloc(8*capG); BG[b].cnt=0; BG[b].cap=capG; }
        for(int k=0;k<NPm;k++){ u64 p=P[k]; u64 c=(r%p+36*(TA%p))%p; om[k]=(u32)((((p-c)%p)*inv36[k])%p); }
        for(int k=0;k<NP;k++){ u64 p=P[k]; u64 c=((2*r-s)%p+72*(TA%p))%p; ot[k]=(u32)((((p-c)%p)*inv72[k])%p); }
        u64 o361; { u64 c=((2*r-s)%361+72*(TA%361))%361; o361=mulmod((361-c)%361,inv72_361,361); }
        for(int q=0;q<NB;q++){ u64 p=bp_[q],p2=bp2[q]; u64 i0=(bj1[q]+p-(TA%p))%p; u64 i2=(bj2[q]+p2-(TA%p2))%p2;
            on[q]=i0; uex[q]=((i2+p2-i0)%p2)/p; cun[q]=0; }
        // initial bucket fill (offsets relative to TA); entry = pos | p<<PSH | type<<63  (type 1 = N-root: counted in ncnt)
        unsigned char *ncnt=calloc(S+128,1);
        for(int a=sLmb;a<nLmb;a++){ int k=Lmb[a]; u64 p=P[k], off=om[k]; bpush(&BX[(off>>LOGS)%NBK], (p<<PSH)|(off&SMASK)); }
        for(int a=sLtb;a<nLtb;a++){ int k=Ltb[a]; u64 p=P[k], off=ot[k]; bpush(&BX[(off>>LOGS)%NBK], (p<<PSH)|(off&SMASK)); }
        for(int q=sNB;q<NB;q++){ u64 p=bp_[q], off=on[q]; bpush(&BX[(off>>LOGS)%NBK], (1ull<<63)|(p<<PSH)|(off&SMASK)); }
        // exceptions: a = th2 (mod p^2) means p^2 | N: such hits must not count (offsets relative to TA, sorted)
        u64 nexc=0, capexc=1024; u64 *exc=malloc(8*capexc);
        for(int q=sNB;q<NB;q++){ u64 p2=bp2[q]; u64 d=(bj2[q]+p2-(TA%p2))%p2; for(;d<TB-TA;d+=p2){ if(nexc>=capexc){ capexc*=2; exc=realloc(exc,8*capexc);} exc[nexc++]=d; } }
        for(u64 x=1;x<nexc;x++){ u64 v=exc[x]; u64 y=x; while(y>0 && exc[y-1]>v){ exc[y]=exc[y-1]; y--; } exc[y]=v; }
        u64 ei=0;
        for(int a=sLmg;a<nLmg;a++){ int k=Lmg[a]; u64 p=P[k], off=om[k]; bpush(&BG[(off>>LOGS)%NBK], (p<<PSH)|(off&SMASK)); }
        u64 g=0;
        for(u64 JL=TA; JL<TB; JL+=S, g++){
            u64 n=TB-JL; if(n>S) n=S;
            { u64 off=JL%PW, done_=0; while(done_<n){ u64 c2=PW-off; if(c2>n-done_) c2=n-done_; memcpy(bad+done_,pat+off,c2); done_+=c2; off=0; } }
            { u64 off=JL%PWB, done_=0; while(done_<n){ u64 c2=PWB-off; if(c2>n-done_) c2=n-done_; unsigned char *dst=bad+done_; const unsigned char *src_=patB+off; for(u64 x=0;x<c2;x++) dst[x]|=src_[x]; done_+=c2; off=0; } }
            // pass 1a: small exclusion primes (classic)
            for(int a=0;a<sLmb;a++){ int k=Lmb[a]; u64 p=P[k], i=om[k]; for(;i<n;i+=p) bad[i]=1; om[k]=(u32)(i-n); }
            for(int a=0;a<sLtb;a++){ int k=Ltb[a]; u64 p=P[k], i=ot[k]; for(;i<n;i+=p) bad[i]=1; ot[k]=(u32)(i-n); }
            { u64 i=o361; for(;i<n;i+=361) bad[i]=1; o361=i-n; }
            for(int q=0;q<sNB;q++){ u64 p=bp_[q], i=on[q], cu=cun[q], ue=uex[q];
                for(;i<n;i+=p){ if(cu!=ue) bad[i]=1; if(++cu==p) cu=0; } on[q]=i-n; cun[q]=cu; }
            // pass 1b: large exclusion items from bucket g
            u64 gm=g%NBK;
            { Bucket *Bk=&BX[gm]; u64 cnt=Bk->cnt; u64 *E=Bk->e; const u64 PM=(1ull<<42)-1;
              for(u64 h=0;h<cnt;h++){ u64 v=E[h]; u64 pos=v&SMASK; u64 p=(v>>PSH)&PM;
                  if(pos<n){ if(v>>63) ncnt[pos]++; else bad[pos]=1; }
                  u64 nx=pos+p; u64 bi=gm+(nx>>LOGS); if(bi>=NBK) bi-=NBK; bpush(&BX[bi], (v&~SMASK)|(nx&SMASK)); }
              Bk->cnt=0; }
            { u64 base=JL-TA; while(ei<nexc && exc[ei]<base+n){ ncnt[exc[ei]-base]--; ei++; } }
            // pass 2: t-cofactor Legendre test, survivor bitmap + rank + compact arrays
            u64 ns=0; u64 nw=(n+63)/64;
            for(u64 i=n;i<64*nw;i++){ bad[i]=1; ncnt[i]=0; }
            { const __m256i Z0=_mm256_setzero_si256();
            for(u64 w=0;w<nw;w++){
                pref[w]=(u32)ns; u64 i0=w*64;
                __m256i b0=_mm256_loadu_si256((const __m256i*)(bad+i0)), b1=_mm256_loadu_si256((const __m256i*)(bad+i0+32));
                __m256i c0=_mm256_loadu_si256((const __m256i*)(ncnt+i0)), c1=_mm256_loadu_si256((const __m256i*)(ncnt+i0+32));
                _mm256_storeu_si256((__m256i*)(ncnt+i0),Z0); _mm256_storeu_si256((__m256i*)(ncnt+i0+32),Z0);
                u64 zm0=(u32)_mm256_movemask_epi8(_mm256_cmpeq_epi8(_mm256_or_si256(b0,c0),Z0));
                u64 zm1=(u32)_mm256_movemask_epi8(_mm256_cmpeq_epi8(_mm256_or_si256(b1,c1),Z0));
                u64 cm=zm0|(zm1<<32), word=0;
                while(cm){ int bit=__builtin_ctzll(cm); cm&=cm-1; u64 i=i0+bit;
                    u64 t=2*(r+36*(JL+i))-s; u64 t19=t%19; if(t19==0) t19=(t/19)%19; if(!QR19[t19]) continue;
                    word|=1ull<<bit; if(ns>=SC){ fprintf(stderr,"survivor overflow\n"); exit(1);} spos[ns]=(u32)i; srem[ns]=r/3+12*(JL+i); shead[ns]=0xFFFFFFFFu; ns++; }
                bm[w]=word; } }
            pref[nw]=(u32)ns;
            // pass 3a: factor m/3 over small good primes, survivors only
            u64 npairs=0;
            for(int a=0;a<sLmg;a++){ int k=Lmg[a]; u64 p=P[k], i=om[k], pv=pinv[k], pl=plim[k];
                for(;i<n;i+=p){ u64 w=i>>6, bit=i&63; u64 word=bm[w]; if(!((word>>bit)&1)) continue;
                    u64 idx=pref[w]+__builtin_popcountll(word&((1ull<<bit)-1));
                    u64 v=srem[idx]; int e=0; while(v*pv<=pl){ v*=pv; e++; } srem[idx]=v;
                    if(npairs>=CAP){ fprintf(stderr,"pair overflow\n"); exit(1);} pk[npairs]=k; pe[npairs]=e; pn[npairs]=shead[idx]; shead[idx]=(u32)npairs; npairs++; }
                om[k]=(u32)(i-n); }
            // pass 3b: large good primes from bucket g
            { Bucket *Bk=&BG[gm]; u64 cnt=Bk->cnt; u64 *E=Bk->e;
              for(u64 h=0;h<cnt;h++){ u64 v0=E[h]; u64 pos=v0&SMASK; u64 p=v0>>PSH;
                  if(pos<n){ u64 w=pos>>6, bit=pos&63; u64 word=bm[w];
                      if((word>>bit)&1){ int k=(int)kofp[p>>1]; u64 idx=pref[w]+__builtin_popcountll(word&((1ull<<bit)-1));
                          u64 pv=pinv[k], pl=plim[k]; u64 v=srem[idx]; int e=0; while(v*pv<=pl){ v*=pv; e++; } srem[idx]=v;
                          if(npairs>=CAP){ fprintf(stderr,"pair overflow\n"); exit(1);} pk[npairs]=k; pe[npairs]=e; pn[npairs]=shead[idx]; shead[idx]=(u32)npairs; npairs++; } }
                  u64 nx=pos+p; u64 bi=gm+(nx>>LOGS); if(bi>=NBK) bi-=NBK; bpush(&BG[bi], (p<<PSH)|(nx&SMASK)); }
              Bk->cnt=0; }
            // pass 4: classify kept entries by the large cofactor
            u64 nA=0,nB=0,nC=0;
            for(u64 idx=0;idx<ns;idx++){ u64 qm=srem[idx]; kq[idx]=qm;
                if(qm>1 && !(qm%12==1||qm%12==11)){ tot_assert++; kq[idx]=0; continue; }
                if(qm>1){ if((qm&3)==3) LA[nA++]=(u32)idx; else if((qm&7)==5) LB[nB++]=(u32)idx; else LC[nC++]=(u32)idx; } }
            tot_kept+=ns;
            // pass 5: batched square roots of 3 modulo the large cofactor
            for(int cls=0;cls<3;cls++){ u32 *L= cls==0? LA : cls==1? LB : LC; u64 nL= cls==0? nA : cls==1? nB : nC;
                for(u64 g4=0; g4<nL; g4+=4){ u64 q4[4], r4[4]; for(int l=0;l<4;l++){ u64 id = g4+l<nL ? L[g4+l] : L[nL-1]; q4[l]=kq[id]; }
                    if(cls<2) sqrt3_batch4_lz(q4,r4,cls); else sqrt3_batchC_lz(q4,r4);
                    for(int l=0;l<4 && g4+l<nL;l++) krho[L[g4+l]]=r4[l]; } }
            // pass 6: CRT (one root per +- pair) + candidates
            for(u64 idx=0; idx<ns; idx++){
                u64 qm=kq[idx]; if(qm==0) continue;
                u64 i=spos[idx]; u64 m=r+36*(JL+i);
                u64 nr, Mod; int first;
                if(qm>1){ roots[0]=krho[idx]; nr=1; Mod=qm; first=0; } else { roots[0]=0; nr=1; Mod=1; first=1; }
                for(u32 q=shead[idx]; q!=0xFFFFFFFFu; q=pn[q]){
                    int k=pk[q]; u64 p=P[k], R0=s3[k]; int e=pe[q]; u64 pe_=p; u64 cnt=0; int ng= first? 1:2; first=0;
                    if(e==1){
                        u64 mu=pmu[k]; u64 invM = itoff[k]!=0xFFFFFFFFu ? itab[itoff[k]+bmod(Mod,p,mu)] : inv_u32((u32)bmod(Mod,p,mu),(u32)p);
                        u64 nR0 = p-R0;
                        for(u64 a1=0;a1<nr;a1++){ u64 r0=roots[a1], r0m=bmod(r0,p,mu);
                            u64 d=R0+p-r0m; if(d>=p) d-=p; tmp[cnt++]=r0+Mod*bmod(d*invM,p,mu);
                            if(ng==2){ d=nR0+p-r0m; if(d>=p) d-=p; tmp[cnt++]=r0+Mod*bmod(d*invM,p,mu); } }
                    } else {
                        for(int ee=1;ee<e;ee++){ u64 pk2=pe_*p;
                            i128 F=(i128)R0*R0-3; i64 Fm=(i64)(F%(i128)pk2); if(Fm<0) Fm+=pk2;
                            u64 iv=(u64)inv_i64((i64)((2*R0)%pk2),(i64)pk2);
                            i128 nr2=(i128)R0-(i128)mulmod((u64)Fm,iv,pk2); nr2%=(i128)pk2; if(nr2<0) nr2+=pk2; R0=(u64)nr2; pe_=pk2; }
                        u64 invM=(u64)inv_i64((i64)(Mod%pe_),(i64)pe_);
                        for(u64 a1=0;a1<nr;a1++) for(int g2=0;g2<ng;g2++){ u64 sr=g2? (pe_-R0)%pe_ : R0; u64 r0=roots[a1];
                            u64 d=(sr+pe_-(r0%pe_))%pe_; tmp[cnt++]=r0+Mod*mulmod(d,invM,pe_); }
                    }
                    Mod*=pe_; nr=cnt; u64 *sw=roots; roots=tmp; tmp=sw;
                }
                { u64 M3=Mod%3; for(u64 a1=0;a1<nr;a1++){ u64 r0=roots[a1]; u64 t3=((3-r0%3)%3)*M3%3; roots[a1]=r0+Mod*t3; } Mod*=3; }
                if(Mod!=m){ fprintf(stderr,"MOD ERROR m=%llu Mod=%llu\n",(unsigned long long)m,(unsigned long long)Mod); exit(1); }
                u64 mi=m; for(int it=0;it<6;it++) mi*=2-m*mi;
                i64 mA=(i64)(m%MA), mB=(i64)(m%MB); i64 baseA=(mA*mA-4*(i64)s*mA)%(i64)MA, baseB=(mB*mB-4*(i64)s*mB)%(i64)MB;
                for(u64 j=0;j<nr;j++){
                    u64 R=roots[j]; u64 z1=(R&1)?R:R+m; u64 zz[2]; int nz=0;
                    if(z1<=m+5) zz[nz++]=z1;
                    { u64 z2=2*m-z1; if(z2<=m+5 && z2!=z1) zz[nz++]=z2; }
                    for(int h=0;h<nz;h++){ u64 z=zz[h];
                        u128 z2=(u128)z*z; u128 w2=(z2-3)>>1; u64 k=(u64)w2*mi;
                        if((u128)k*m!=w2){ fprintf(stderr,"ROOT ERROR m=%llu z=%llu\n",(unsigned long long)m,(unsigned long long)z); exit(1); }
                        i128 B2=(i128)m*m-4*(i128)s*m-(i128)z2+(i128)s*(i128)k;
                        if(B2<=0) continue;
                        tot_cand++;
                        if(((u64)B2&7)!=1) continue;
                        tot_alive++;
                        { i64 zA=(i64)(z%MA), kA=(i64)(k%MA); i64 v=(baseA-zA*zA+(i64)s*kA)%(i64)MA; if(v<0) v+=MA;
                          if(CHK){ i64 vt=(i64)(B2%(i128)MA); if(vt!=v){ fprintf(stderr,"RESA MISMATCH\n"); exit(1);} }
                          if(!sqA[v]) continue; }
                        { i64 zB=(i64)(z%MB), kB=(i64)(k%MB); i64 v=(baseB-zB*zB+(i64)s*kB)%(i64)MB; if(v<0) v+=MB;
                          if(CHK){ i64 vt=(i64)(B2%(i128)MB); if(vt!=v){ fprintf(stderr,"RESB MISMATCH\n"); exit(1);} }
                          if(!sqB[v]) continue; }
                        tot_sqrt++;
                        if(DUMP){
                            #pragma omp critical
                            { printf("CAND %d %llu %llu\n",s,(unsigned long long)m,(unsigned long long)z); }
                        }
                        i128 sq=(i128)sqrtl((long double)B2); while(sq*sq>B2) sq--; while((sq+1)*(sq+1)<=B2) sq++;
                        if(sq*sq==B2) report(s,m,(u64)sq,z);
                    }
                }
            }
        }
    }
    fprintf(stderr,"done14 s=%d j in [%llu,%llu) (|a| up to %llu): kept=%lld cand=%lld alive=%lld sqrt=%lld assert=%lld time=%.1fs nbad=%d\n",
        s,(unsigned long long)J0,(unsigned long long)J1,(unsigned long long)mmax,tot_kept,tot_cand,tot_alive,tot_sqrt,tot_assert,omp_get_wtime()-t0,NB);
    return 0;
}
