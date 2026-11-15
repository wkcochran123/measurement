# usage: analyze_ladder.py <M2 file> <Ultra file>   (RUN r / LEVEL k raw blank ns lines)
# The four rulers: k (universe level), H_k = raw + blank (heartbeats), t_k (ns), and relative time R_k = tau_k / tau_1,
# tau_k = t_k / H_k. Density rho_k = H_k (heartbeats spent at level k); potential Phi = double sum of rho below k
# (the field equations' Newtonian limit on a line of levels, receipt the_second_difference_of_the_potential_is_the_density).
import sys, math, statistics as st
def load(p):
    runs=[];cur=None;name=open(p).readline().strip()
    for l in open(p):
        if l.startswith('RUN'): cur={};runs.append(cur)
        elif l.startswith('LEVEL'):
            _,k,h,b,ns=l.split(); cur[int(k)]=(int(h)+int(b),int(ns))
    return name,runs
def fit(x,y):
    n=len(x);mx=sum(x)/n;my=sum(y)/n
    sxx=sum((a-mx)**2 for a in x); sxy=sum((a-mx)*(b-my) for a,b in zip(x,y))
    s=sxy/sxx; r2=1-sum((b-(my+s*(a-mx)))**2 for a,b in zip(x,y))/sum((b-my)**2 for b in y)
    return s,my-s*mx,r2
out={}
for p in sys.argv[1:]:
    name,runs=load(p); ks=sorted(runs[0])
    H={k:{r[k][0] for r in runs} for k in ks}
    same=all(len(v)==1 for v in H.values())
    Hk={k:min(H[k]) for k in ks}
    tau={k:st.median(r[k][1] for r in runs)/Hk[k] for k in ks}
    out[name]=(Hk,tau,same,runs)
    print(f"== {name}: runs {len(runs)}, levels {len(ks)}; heartbeats identical across runs at every level: {same}")
names=list(out)
HA,tA,_,_=out[names[0]]; HB,tB,_,_=out[names[1]]; ks=sorted(HA)
print("(a) heartbeats identical across machines at every level:", all(HA[k]==HB[k] for k in ks),
      "; levels differing:", [k for k in ks if HA[k]!=HB[k]][:10])
# potential from the density, levels 2..36 (level 1 is the cold start, excluded from fits)
L=[k for k in ks if k>=2]
rho={k:HA[k] for k in ks}
F={};P={};f=0;p=0
for k in ks:
    P[k]=p; F[k]=f; f+=rho[k]; p+=f
for nm,(H,tau,_,_) in out.items():
    R={k:tau[k]/tau[2] for k in L}
    s,c,r2=fit([P[k] for k in L],[math.log(R[k]) for k in L])
    print(f"(c) {nm}: ln R_k = {s:.4e} * Phi_k + {c:+.4f}; R^2 = {r2:.4f}; tau level 2 = {tau[2]:.2f} ns/hb, level 36 = {tau[36]:.2f}")
DA={k:tA[k] for k in L}; DB={k:tB[k] for k in L}
D=[DB[k]/DA[k] for k in L]
print(f"(b) D_k = tau_Ultra/tau_M2 over levels 2..36: median {st.median(D):.4f}, min {min(D):.4f}, max {max(D):.4f}, spread (max-min)/median {(max(D)-min(D))/st.median(D):.4f}")
s,c,r2=fit([P[k] for k in L],[math.log(x) for x in D]); print(f"    ln D_k against Phi_k: slope {s:.4e}, R^2 {r2:.4f}")
for nm,(H,tau,_,runs) in out.items():
    sp=[ (max(r[k][1] for r in runs)-min(r[k][1] for r in runs))/st.median(r[k][1] for r in runs) for k in L]
    print(f"    run-to-run spread of t_k on {nm}: median {st.median(sp):.4f}")
print("levels, H_k, Phi_k, tau_M2, tau_Ultra:")
for k in ks: print(f"  {k:2d} {HA[k]:8d} {P[k]:12d} {tA[k]:7.2f} {tB[k]:7.2f}")
