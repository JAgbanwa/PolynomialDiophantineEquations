
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

{asint(v,q)= if(v=="inf"||v=="?", return(v)); my(p=v.pol); if(type(p)=="t_INT", return(p%q)); if(poldegree(p)<=0, return(lift(polcoef(p,0))%q)); return("no");}
{condq(Q,q,n1,n2,j)= my(vals=List());
  for(i=1,#Q, my(Er=Q[i][2], P=elladd(Er,elladd(Er,ellmul(Er,Q[i][3],n1),ellmul(Er,Q[i][4],n2)),Q[i][5][j]), v=asint(mredq(Er,P,Q[i][6]),q));
    if(v=="no", return(0)); if(v!="?", listput(vals,v)));
  for(i=2,#vals, if(vals[i]!=vals[1], return(0))); 1;}
Ord(Q,k)=lcm(vector(#Q,i,ellorder(Q[i][2],Q[i][k])));

goodR=[[0,0,1],[0,1,1],[0,0,2],[0,1,2],[1,0,2],[-1,1,2]];
redall(Q,v)=vector(#Q,i, my(Er=Q[i][2]); elladd(Er,elladd(Er,ellmul(Er,Q[i][3],v[1]),ellmul(Er,Q[i][4],v[2])),Q[i][5][v[3]]));
chabP=[5,11,17,29,31,47,59,71]; plainP=[23,107,13,7,43,83,89,101,113,131,137];
S=List([[0,0,1],[0,0,2],[0,0,3],[0,0,4]]); L1=1; L2=1;
{addprime(q,ischab)= my(Q=qdata(q), a=Ord(Q,3), bq=Ord(Q,4), M1=lcm(L1,a), M2=lcm(L2,bq), NS=List(), gset);
  if(ischab, gset=Set(vector(#goodR,i,Str(redall(Q,goodR[i])))));
  for(s=1,#S, for(k1=0,M1/L1-1, for(k2=0,M2/L2-1, my(v=[S[s][1]+k1*L1, S[s][2]+k2*L2, S[s][3]]);
     if(condq(Q,q,v[1],v[2],v[3]) && (!ischab || !setsearch(gset,Str(redall(Q,v)))), listput(NS,v)))));
  S=NS; L1=M1; L2=M2; print("after ",q,if(ischab," (Chabauty-bad)"," (plain)"),": L=",[L1,L2]," size ",#S);}
for(i=1,#chabP, addprime(chabP[i],1); if(#S==0,break));
if(#S>0, for(i=1,#plainP, if(#S==0,break); Q=qdata(plainP[i]); if(lcm(L1,Ord(Q,3))*lcm(L2,Ord(Q,4))*#S/(L1*L2)<5*10^6, addprime(plainP[i],0), print("skip ",plainP[i]))));
print("FINAL surviving classes: ",#S);
