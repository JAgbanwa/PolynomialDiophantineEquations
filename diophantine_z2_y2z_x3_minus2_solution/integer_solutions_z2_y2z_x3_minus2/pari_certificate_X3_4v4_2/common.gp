
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
