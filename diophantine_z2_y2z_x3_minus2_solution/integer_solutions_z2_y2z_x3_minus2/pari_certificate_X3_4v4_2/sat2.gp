
default(parisize,"2G");
K=nfinit(t^3-2); A=Mod(t,t^3-2);
E=ellinit([0,6*A^2,0,-48*A,-256],K);
b=-2*A; c=6*A^2; d=8; e=8*A; cp=c-b^2/4;
Pa=[-4*A^2+8*A-8, -24*A^2+48]; Pb=[-5*A^2,18]; T1=[4*A^2,0]; T2=[-2*A^2,0];
rd(z,mp)=nfmodpr(K,lift(z),mp);
redE(mp)=ellinit(vector(5,i,rd(E[i],mp)));
redP(P,mp)=if(P==[0],[0],[rd(P[1],mp),rd(P[2],mp)]);
{mredq(Er,P,mp)= if(P==[0], return("inf"));
  my(w=-P[1]/2, y=P[2], den=2*(2*w-rd(cp,mp)), num=rd(d,mp)-rd(b,mp)*w+y);
  if(den!=0, return(num/den)); if(num!=0, return("inf")); my(dd=rd(d,mp)-rd(b,mp)*w); if(dd==0,return("?")); return((w^2-rd(e,mp))/dd);}
\\ data for a rational prime q: list over primes above q of [f, Er, ra, rb, rt(4), mp]
{qdata(q)= my(D=idealprimedec(K,q), L=List());
  for(i=1,#D, my(pr=D[i], mp=nfmodprinit(K,pr), Er=redE(mp), t1=redP(T1,mp), t2=redP(T2,mp));
    listput(L,[pr.f, Er, redP(Pa,mp), redP(Pb,mp), [[0],t1,t2,elladd(Er,t1,t2)], mp]));
  Vec(L);}

\\ for odd prime l: test injectivity of G/lG -> prod E(F_q)/l over primes q (all primes above q)
{satcheck(l,qmax)= my(bad=List()); 
  \\ nonzero classes (a,b) in (Z/l)^2 up to scaling
  my(cls=List()); for(a=0,l-1,for(b=0,l-1, if([a,b]!=[0,0], listput(cls,[a,b]))));
  my(alive=Vec(cls));
  forprime(q=5,qmax, if(q==7&&0,next); my(Q=qdata(q));
    for(i=1,#Q, my(Er=Q[i][2], N=ellcard(Er)); if(N%l, next);
      \\ point g=a Pa + b Pb is l-divisible in E(F) iff (N/l^v)*... use: g in l*E(F) test via ellgroup structure
      my(G=ellgroup(Er,,1), cyc=G[2], gens=G[3]);
      alive=select(v-> isldiv(Er,ellmul(Er,Q[i][3],v[1]),ellmul(Er,Q[i][4],v[2]),cyc,gens,l), alive));
    if(#alive==0, return([q,0])));
  [qmax,#alive];}
\\ is P+Q2 in l*E(F)?  via discrete log in the abelian group
{isldiv(Er,P1,P2,cyc,gens,l)= my(P=elladd(Er,P1,P2)); if(P==[0],return(1));
  my(c=ellgroupcoords(Er,P,cyc,gens)); for(k=1,#cyc, if(cyc[k]%l==0 && c[k]%l!=0, return(0))); 1;}
\\ coordinates of P w.r.t. generators (brute force via elllog when cyclic parts)
{ellgroupcoords(Er,P,cyc,gens)= if(#cyc==1, return([elllog(Er,P,gens[1],cyc[1])]));
  my(c1); for(c2=0,cyc[2]-1, my(R=elladd(Er,P,ellmul(Er,gens[2],-c2))); my(t=iferr(elllog(Er,R,gens[1],cyc[1]),E,-1)); if(t>=0 && ellmul(Er,gens[1],t)==R, return([t,c2]))); error("coords");}
Q13=qdata(13); N13=ellcard(Q13[1][2]); print("#E(F_2197)=",N13," ",factor(N13));
L=setminus(Set(concat([43],factor(N13)[,1]~)),Set([2]));
foreach(L, l, print("l=",l," -> ", satcheck(l,3000)));
