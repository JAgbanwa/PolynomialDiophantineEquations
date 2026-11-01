import numpy as np, scipy.optimize as so, sys, time
k=int(sys.argv[1]); j=int(sys.argv[2]); N=int(sys.argv[3]); seed=int(sys.argv[4])
def resid(u):
    m=u[0]; xl=u[1:1+2*k]; yl=u[1+2*k:]
    X=np.concatenate([[-m*m],xl]); Y=np.concatenate([[1.0,0.0],yl])
    Y2=np.polymul(Y,Y); G=np.polyadd(np.polymul(Y2,Y2),[8.0]); G=np.polysub(G,4*np.polymul(np.polymul(X,X),X))
    G=np.concatenate([np.zeros(6*k+1-len(G)),G])
    dw=3*k; w=np.zeros(dw+1); w[0]=np.sqrt(G[0])
    for i in range(1,dw+1):
        w[i]=(G[i]-np.dot(w[1:i],w[i-1:0:-1]))/(2*w[0])
    R=G-np.polymul(w,w)
    return R[-3*k:]
nun=1+2*k+(j-1)
rng=np.random.default_rng(seed); t0=time.time(); found=0
for i in range(N):
    u0=rng.normal(0,1.5,nun)
    try:
        r=so.least_squares(resid,u0,xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=400,method='lm')
        if np.max(np.abs(resid(r.x)))<1e-9:
            found+=1; print(np.round(r.x,7).tolist(),flush=True)
    except Exception as e: pass
print('done',N,found,time.time()-t0)
