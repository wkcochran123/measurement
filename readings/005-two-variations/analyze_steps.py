# usage: analyze_steps.py <M2 file> <Ultra file>
# H_k = beat + blank (density), tau_k = t_k / H_k, u_k = 1 / tau_k (work rate), ln R_k = ln(tau_k / tau_ref), ref = step 4.
# Time-like representation: ln R against the local H_k.  Space-like: against the potential Phi_k, the double sum of H
# below k.  Convective: the residual of the local fit against u_k (u_{k+1} - u_{k-1}).  Steps 0-3 are warm-up.
import sys, math, statistics as st
def load(p):
    runs=[];cur=None;name=open(p).readline().strip()
    for l in open(p):
        if l.startswith('RUN'): cur={};runs.append(cur)
        elif l.startswith('STEP'):
            _,k,c,h,b,ns=l.split(); cur[int(k)]=(int(h)+int(b),int(ns))
    return name,runs
def fit(x,y):
    n=len(x);mx=sum(x)/n;my=sum(y)/n;sxx=sum((a-mx)**2 for a in x)
    s=sum((a-mx)*(b-my) for a,b in zip(x,y))/sxx; res=[b-(my+s*(a-mx)) for a,b in zip(x,y)]
    return s,1-sum(r*r for r in res)/sum((b-my)**2 for b in y),res
def corr(x,y):
    n=len(x);mx=sum(x)/n;my=sum(y)/n
    return sum((a-mx)*(b-my) for a,b in zip(x,y))/math.sqrt(sum((a-mx)**2 for a in x)*sum((b-my)**2 for b in y))
D={}
for p in sys.argv[1:]:
    name,runs=load(p); ks=sorted(runs[0])
    same=all(len({r[k][0] for r in runs})==1 for k in ks)
    H={k:runs[0][k][0] for k in ks}; tau={k:st.median(r[k][1] for r in runs)/H[k] for k in ks}
    D[name]=(H,tau,same)
    print(f"== {name}: runs {len(runs)}, steps {len(ks)}; heartbeats identical across runs: {same}")
names=list(D); HA=D[names[0]][0]; HB=D[names[1]][0]; ks=sorted(HA)
print("(a) heartbeats identical across machines at every step:", all(HA[k]==HB[k] for k in ks))
P={};f=0;p=0
for k in ks: P[k]=p; f+=HA[k]; p+=f
L=[k for k in ks if k>=4]; C=[k for k in L if k+1 in HA and k-1 in HA and k>=5]
res_by={}
for nm,(H,tau,_) in D.items():
    y={k:math.log(tau[k]/tau[4]) for k in L}
    _,r2loc,res=fit([H[k] for k in L],[y[k] for k in L]); _,r2pot,_=fit([P[k] for k in L],[y[k] for k in L])
    resd=dict(zip(L,res)); u={k:1/tau[k] for k in ks}
    conv=[u[k]*(u[k+1]-u[k-1]) for k in C]; r=corr(conv,[resd[k] for k in C])
    res_by[nm]=r
    print(f"{nm}: tau step 4 {tau[4]:.2f}, step 47 {tau[47]:.2f} ns/hb; (b) R^2 local {r2loc:.4f} vs potential {r2pot:.4f}; (c) corr(residual, convective) = {r:+.3f}")
