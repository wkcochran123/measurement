# usage: analyze_beats.py <machine A file> <machine B file>
# Each file: RUN r / BEAT k raw blank ns lines. Heartbeats per step = raw + blank (the meter's whole call).
import sys, statistics as st, bisect
def load(p):
    runs=[]; cur=None; name=open(p).readline().strip()
    for l in open(p):
        if l.startswith('RUN'): cur=[]; runs.append(cur)
        elif l.startswith('BEAT'):
            _,k,h,b,ns=l.split(); cur.append((int(k),int(h)+int(b),int(ns)))
    return name, runs
def cum(xs):
    out=[0]; 
    for x in xs: out.append(out[-1]+x)
    return out
def interp(T,H,t):
    i=bisect.bisect_right(T,t)-1; i=max(0,min(i,len(T)-2))
    return H[i]+(H[i+1]-H[i])*(t-T[i])/(T[i+1]-T[i])
na,A=load(sys.argv[1]); nb,B=load(sys.argv[2])
hb={tuple(s[1] for s in r) for r in A+B}
print(f"A = {na}, B = {nb}; runs {len(A)} and {len(B)}, steps {len(A[0])}")
print(f"heartbeat sequences identical across all runs and both machines: {len(hb)==1}")
H=cum([s[1] for s in A[0]])
TA=cum([st.median(r[k][2] for r in A) for k in range(len(A[0]))])
TB=cum([st.median(r[k][2] for r in B) for k in range(len(B[0]))])
D=TB[-1]/TA[-1]
print(f"total heartbeats {H[-1]}; time A {TA[-1]/1e6:.2f} ms, B {TB[-1]/1e6:.2f} ms; D = B/A = {D:.4f}")
print(f"tau A {TA[-1]/H[-1]:.2f} ns/hb, tau B {TB[-1]/H[-1]:.2f} ns/hb")
# fringe order at equal wall time: F(t) = H_B(t) - H_A(t)
tend=min(TA[-1],TB[-1]); grid=[tend*j/200 for j in range(1,201)]
F=[interp(TB,H,t)-interp(TA,H,t) for t in grid]
n=len(grid); mx=sum(grid)/n; my=sum(F)/n
slope=sum((x-mx)*(y-my) for x,y in zip(grid,F))/sum((x-mx)**2 for x in grid)
r2=1-sum((y-(my+slope*(x-mx)))**2 for x,y in zip(grid,F))/sum((y-my)**2 for y in F)
print(f"fringe order at t = {tend/1e6:.2f} ms: F = {F[-1]:.0f} extremes passed (sign + means B ahead)")
print(f"beat frequency (slope of F against t): {slope*1e3:.4f} MHz; linear fit R^2 = {r2:.5f}")
fa=interp(TA,H,tend)
print(f"heartbeats of A per extreme: {fa/F[-1]:.2f}")
# spread: every pairing of single runs
per=[]
for ra in A:
    for rb in B:
        ta=cum([s[2] for s in ra]); tb=cum([s[2] for s in rb]); te=min(ta[-1],tb[-1])
        f=interp(tb,H,te)-interp(ta,H,te); per.append(interp(ta,H,te)/f if f else float('inf'))
q=st.quantiles(per,n=4)
print(f"heartbeats per extreme over all {len(per)} run pairings: median {st.median(per):.2f}, interquartile {q[0]:.2f}..{q[2]:.2f}, min {min(per):.2f}, max {max(per):.2f}")
