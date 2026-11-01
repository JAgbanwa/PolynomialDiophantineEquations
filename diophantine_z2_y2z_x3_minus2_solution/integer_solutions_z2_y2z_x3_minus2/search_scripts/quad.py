import numpy as np, scipy.optimize as so
def resid(u):
    a3,a2,a1,a0,y0,w3,w2,w1,w0=u
    X=np.array([a3,a2,a1,a0])
    P=np.polyadd(np.array([1,0,0,0,0]), -4*np.polymul(np.polymul(X,X),X)); P=np.polyadd(P,[8])
    W=np.array([1,w3,w2,w1,w0])
    R=-4*a3**3*np.polymul([1,-y0],np.polymul(W,W))
    return np.polysub(P,R)[1:]
rng=np.random.default_rng(1); sols=[]
for i in range(8000):
    u0=rng.normal(0,2,9)
    r=so.least_squares(resid,u0,xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=4000)
    if r.cost<1e-24 and abs(r.x[0])>1e-6: sols.append(np.round(r.x,9))
U=np.unique(np.array(sols),axis=0) if sols else []
print(len(U))
for s in U: print(list(s))
