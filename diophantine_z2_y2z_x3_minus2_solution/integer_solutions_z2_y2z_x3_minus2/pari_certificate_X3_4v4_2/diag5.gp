
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

Q=qdata(5); a=Ord(Q,3); bq=Ord(Q,4); print("periods at 5: ",[a,bq]);
for(i=1,#Q, print("prime f=",Q[i][1]," #E=",ellcard(Q[i][2])," group=",ellgroup(Q[i][2])));
gset=Set(vector(#goodR,i,Str(redall(Q,goodR[i]))));
print("distinct good cosets: ",#gset);
pass=0; goodc=0; CO=Map();
{for(n1=0,a-1,for(n2=0,bq-1,for(j=1,4, my(v=[n1,n2,j], key=Str(redall(Q,v))); if(condq(Q,5,n1,n2,j), pass++; if(setsearch(gset,key), goodc++); mapput(CO,key,1)))));}
print("passing classes: ",pass," of ",a*bq*4,"; passing classes in good cosets: ",goodc,"; distinct passing cosets: ",#CO);
for(r=1,#goodR, print("known ",goodR[r]," mbar at primes above 5: ", vector(#Q,i, mredq(Q[i][2],redall(Q,goodR[r])[i],Q[i][6]))));
