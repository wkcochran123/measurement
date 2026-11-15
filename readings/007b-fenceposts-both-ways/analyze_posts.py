# usage: analyze_posts.py <ladder file>   (RUN r / LEVEL k raw blank ns; levels 1..36, level 1 the cold start)
# ln R_k = ln(tau_k / tau_2), tau_k = t_k / H_k (median over runs), levels 2..36.
# A continuous piecewise-linear spline with six interior knots at 6+o, 11+o, ..., 31+o, for shifts o = -3..4.
# (o = -4 would put a knot on level 2, the first level fitted, where it is collinear with the line.)
# o = 0 puts the knots on the fenceposts 1 mod 5 (1, 6, ..., 36: seven panels of five, one post over).
import sys, math, statistics as st
runs=[];cur=None
for l in open(sys.argv[1]):
    if l.startswith('RUN'): cur={};runs.append(cur)
    elif l.startswith('LEVEL'):
        _,k,h,b,ns=l.split(); cur[int(k)]=(int(h)+int(b),int(ns))
ks=list(range(2,37)); H={k:runs[0][k][0] for k in ks}
same=all(len({r[k][0] for r in runs})==1 for k in ks)
tau={k:st.median(r[k][1] for r in runs)/H[k] for k in ks}
y=[math.log(tau[k]/tau[2]) for k in ks]
def lstsq(X,y):
    n=len(X[0]); A=[[sum(X[i][a]*X[i][b] for i in range(len(X))) for b in range(n)] for a in range(n)]
    v=[sum(X[i][a]*y[i] for i in range(len(X))) for a in range(n)]
    for i in range(n):
        p=max(range(i,n),key=lambda r:abs(A[r][i])); A[i],A[p]=A[p],A[i]; v[i],v[p]=v[p],v[i]
        for r in range(i+1,n):
            f=A[r][i]/A[i][i]
            for c in range(i,n): A[r][c]-=f*A[i][c]
            v[r]-=f*v[i]
    x=[0]*n
    for i in reversed(range(n)): x[i]=(v[i]-sum(A[i][c]*x[c] for c in range(i+1,n)))/A[i][i]
    return x
def rss(knots):
    X=[[1,k]+[max(0,k-t) for t in knots] for k in ks]; b=lstsq(X,y)
    return sum((yy-sum(bb*xx for bb,xx in zip(b,row)))**2 for row,yy in zip(X,y))
print(f"runs {len(runs)}; heartbeats identical across runs: {same}")
res={o:rss([6+o+5*j for j in range(6)]) for o in range(-3,5)}
for o,r in res.items(): print(f"shift {o}: knots {[6+o+5*j for j in range(6)]}  RSS {r:.6e}")
best=min(res,key=res.get); print(f"smallest RSS at shift {best}; shift 0 / best other = {res[0]/min(v for o,v in res.items() if o!=0):.3f}")
SS=sum((v-sum(y)/len(y))**2 for v in y); print(f"R^2 at shift 0: {1-res[0]/SS:.4f}")
