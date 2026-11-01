default(parisize,"200M");
red=0;
for(mm=1,3,for(a=0,2*mm^2-1,for(b=-40,40,for(c=-40,40,for(e=-40,40,x=-mm^2*t^4+a*t^3+b*t^2+c*t+e;fa=factor(x^3-2);if(#fa[,1]>1,red++;print("RED ",x," : ",fa[,1]~)))))));
print("reducible count: ",red);
quit;
