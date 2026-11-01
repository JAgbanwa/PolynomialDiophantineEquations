default(parisize,"500M");
out="scan_out.txt";
{
for(X=1,10^7,
  N=X^3+2; D=divisors(N); nd=#D;
  for(i=1,(nd+1)\2, d=D[i]; mp=N\d; s=mp-d; if(s>=0 && issquare(s,&r), write(out,[-X,r,d]); write(out,[-X,r,-mp])));
  M=X^3-2; if(M>0, D=divisors(M); nd=#D;
  for(i=1,(nd+1)\2, d=D[i]; mp=M\d; s=mp+d; if(issquare(s,&r), write(out,[X,r,-d]); write(out,[X,r,-mp]))));
  if(X%500000==0, print(X));
);
}
quit;
