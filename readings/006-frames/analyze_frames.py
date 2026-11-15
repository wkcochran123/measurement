# usage: analyze_frames.py <Ultra P file> <Ultra E file> <M2 W1 timing> <M2 W2 beats> <M2 W3 steps> [<Ultra P convective file>]
# tau per workload: W1 = (t_dev - t_ctrl)/(H_dev - H_ctrl) per interleaved pair; W2 = total ns / total heartbeats per run;
# W3 = total ns / total heartbeats over steps 4..47 per run. A frame is the point (ln tau_W1, ln tau_W3).
import sys, re, math, random, statistics as st
def parse(p):
    w1d=[];w1c=[];w2=[];w3=[];cur=None;hb={'w1':set(),'w2':set(),'w3':set()}
    for l in open(p):
        m=re.search(r"TIMED n=64 ctrl=(\w+) raw=(\d+) blank=(\d+) .*ns=(\d+)",l)
        if m:
            (w1d if m[1]=='false' else w1c).append((int(m[2])+int(m[3]),int(m[4]))); continue
        if l.startswith('RUN W2') or (l.startswith('RUN') and 'beats' in p): cur=('w2',[]); w2.append(cur[1]); continue
        if l.startswith('RUN W3') or (l.startswith('RUN') and 'steps' in p): cur=('w3',[]); w3.append(cur[1]); continue
        if l.startswith('RUN'): cur=None; continue
        if l.startswith('BEAT') and cur: _,k,h,b,ns=l.split(); cur[1].append((int(h)+int(b),int(ns)))
        if l.startswith('STEP') and cur:
            _,k,c,h,b,ns=l.split()
            if int(k)>=4: cur[1].append((int(h)+int(b),int(ns)))
    t1=[(d[1]-c[1])/(d[0]-c[0]) for d,c in zip(w1d,w1c)]
    t2=[sum(x[1] for x in r)/sum(x[0] for x in r) for r in w2]
    t3=[sum(x[1] for x in r)/sum(x[0] for x in r) for r in w3]
    H=(sorted({d[0] for d in w1d}), sorted({tuple(x[0] for x in r) for r in w2}).__len__(), sorted({tuple(x[0] for x in r) for r in w3}).__len__(),
       w1d[0][0] if w1d else None, sum(x[0] for x in w2[0]) if w2 else None, sum(x[0] for x in w3[0]) if w3 else None)
    return t1,t2,t3,H
a=sys.argv
UP=parse(a[1]); UE=parse(a[2])
M1=parse(a[3])[0]; M2=parse(a[4])[1]; M3=parse(a[5])[2]
print("heartbeats (W1 dev, W2 total, W3 total): Ultra P", UP[3][3:], " Ultra E", UE[3][3:])
print("  sequences identical within frame: Ultra P", UP[3][1]==1 and UP[3][2]==1, " Ultra E", UE[3][1]==1 and UE[3][2]==1)
frames={'Ultra P':(UP[0],UP[1],UP[2]),'Ultra E':(UE[0],UE[1],UE[2]),'M2':(M1,M2,M3)}
for f,(x,y,z) in frames.items():
    print(f"{f:8s} tau W1 {st.median(x):7.2f} (n {len(x)})  W2 {st.median(y):7.2f} (n {len(y)})  W3 {st.median(z):7.2f} (n {len(z)}) ns/hb")
sp=lambda v:(max(v)-min(v))/st.median(v)
print("(b) |ln(tau_E/tau_P)| per workload, against 10x Ultra P spread:")
for i,w in enumerate(['W1','W2','W3']):
    l=abs(math.log(st.median(frames['Ultra E'][i])/st.median(frames['Ultra P'][i]))); s=sp(frames['Ultra P'][i])
    print(f"   {w}: {l:.4f} vs 10 x {s:.4f} = {10*s:.4f} -> {'distinct' if l>10*s else 'not distinct'}")
def area(P):
    (ax,ay),(bx,by),(cx,cy)=P
    return (bx-ax)*(cy-ay)-(by-ay)*(cx-ax)
def pts(sample):
    return [(math.log(st.median(sample[f][0])),math.log(st.median(sample[f][2]))) for f in ['Ultra P','Ultra E','M2']]
A0=area(pts(frames)); random.seed(14112026); boots=[]
for _ in range(4000):
    s={f:tuple([random.choice(v) for _ in v] for v in frames[f]) for f in frames}
    boots.append(area(pts(s)))
boots.sort(); lo,hi=boots[int(0.025*len(boots))],boots[int(0.975*len(boots))]
print(f"(c) signed area of (Ultra P, Ultra E, M2) in (ln tau_W1, ln tau_W3): {A0:+.5f}; 95% bootstrap [{lo:+.5f}, {hi:+.5f}] -> {'excludes zero' if lo>0 or hi<0 else 'includes zero'}")
# the box, three workloads by three frames: double-centered interaction
M=[[math.log(st.median(frames[f][i])) for i in range(3)] for f in frames]
rm=[sum(r)/3 for r in M]; cm=[sum(M[j][i] for j in range(3))/3 for i in range(3)]; g=sum(rm)/3
I=[[M[j][i]-rm[j]-cm[i]+g for i in range(3)] for j in range(3)]
print("    interaction (frames x W1,W2,W3, double-centered ln tau):")
for f,r in zip(frames,I): print(f"      {f:8s} " + "  ".join(f"{v:+.4f}" for v in r))
if len(a)>6:
    T=parse(a[6])[2]  # per-run W3 taus not enough; recompute per step medians
    runs=[];cur=None
    for l in open(a[6]):
        if l.startswith('RUN'): cur={};runs.append(cur)
        elif l.startswith('STEP'):
            _,k,c,h,b,ns=l.split(); cur[int(k)]=(int(h)+int(b),int(ns))
    ks=sorted(runs[0]); H={k:runs[0][k][0] for k in ks}; tau={k:st.median(r[k][1] for r in runs)/H[k] for k in ks}
    L=[k for k in ks if k>=4]
    y=[math.log(tau[k]/tau[4]) for k in L]; x=[H[k] for k in L]
    n=len(x);mx=sum(x)/n;my=sum(y)/n;s=sum((p-mx)*(q-my) for p,q in zip(x,y))/sum((p-mx)**2 for p in x)
    res={k:yy-(my+s*(xx-mx)) for k,xx,yy in zip(L,x,y)}
    u={k:1/tau[k] for k in ks}; C=[k for k in L if k>=5 and k+1 in u]
    cv=[u[k]*(u[k+1]-u[k-1]) for k in C]; rr=[res[k] for k in C]
    mc=sum(cv)/len(cv); mr=sum(rr)/len(rr)
    r=sum((p-mc)*(q-mr) for p,q in zip(cv,rr))/math.sqrt(sum((p-mc)**2 for p in cv)*sum((q-mr)**2 for q in rr))
    print(f"(d) Ultra P, {len(runs)} runs of W3: corr(residual of local fit, u_k(u_k+1 - u_k-1)) = {r:+.3f}")
