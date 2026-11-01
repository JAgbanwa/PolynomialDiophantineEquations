
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

{mval(P)= if(P==[0], return("inf"));
  my(w=-P[1]/2, y=P[2], den=2*(2*w-cp), num=d-b*w+y);
  if(den!=0, return(num/den)); if(num!=0, return("inf")); return((w^2-e)/(d-b*w));}
Ts=[[0],T1,T2,elladd(E,T1,T2)];
pt(v)=elladd(E,elladd(E,ellmul(E,Pa,v[1]),ellmul(E,Pb,v[2])),Ts[v[3]]);
goodR=[[0,0,1],[0,1,1],[0,0,2],[0,1,2],[1,0,2],[-1,1,2]];
Ord(Q,k)=lcm(vector(#Q,i,ellorder(Q[i][2],Q[i][k])));
redall(Q,v)=vector(#Q,i, my(Er=Q[i][2]); elladd(Er,elladd(Er,ellmul(Er,Q[i][3],v[1]),ellmul(Er,Q[i][4],v[2])),Q[i][5][v[3]]));
{kernelbasis(p)= my(Q=qdata(p), oa=Ord(Q,3), ob=Ord(Q,4), rel=List(), J=Map());
  for(n1=0,oa-1,for(n2=0,ob-1, for(j=1,4, if(redall(Q,[n1,n2,j])==vector(#Q,i,[0]), listput(rel,[n1,n2]~); mapput(J,Str([n1,n2]),j)))));
  my(H=mathnf(matconcat([Mat(Vec(rel)), [oa,0;0,ob]]))); [H,Q];}
{tidx(Q,v)= for(j=1,4, if(redall(Q,[v[1],v[2],j])==vector(#Q,i,[0]), return(j))); error("no tidx");}
coef(z,i)= polcoef(lift(z),i);
{chab(p)= my(KB=kernelbasis(p), H=KB[1], Q=KB[2], ok=1);
  my(Qv=vector(2,i, my(v=[H[1,i],H[2,i]]); [v[1],v[2],tidx(Q,v)]));
  my(Qp=vector(2,i,pt(Qv[i])));
  for(r=1,#goodR, my(Rv=goodR[r], R=pt(Rv), mR=mval(R), inv=(mR=="inf" || valuation(mR,p)<0), Amat=matrix(2,2));
     for(i=1,2, my(S=elladd(E,R,Qp[i]), g=mval(S)); if(inv, g=if(g=="inf",0,1/g)); for(k=1,2, my(cf=coef(g,k)); if(cf!=0 && valuation(cf,p)<1, ok=0; print("  val<1 at p=",p," R=",Rv)); Amat[k,i]=if(cf==0,0,cf/p)));
     my(dt=matdet(Mod(Amat,p))); if(dt==0, ok=0); );
  print("p=",p," splitting f=",apply(x->x[1],Q)," HNF=",H," all dets nonzero & vals ok: ",ok); ok;}
res=List(); foreach([5,11,17,23,29,31,47,59,71], p, listput(res,[p,chab(p)]));
print(Vec(res));
