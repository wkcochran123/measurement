import re,sys,statistics as st
def load(p):
    rows={}
    for l in open(p):
        m=re.search(r"n=(\d+) ctrl=(\w+) raw=(\d+) blank=(\d+) net=(-?\d+) ns=(\d+)",l)
        if m:
            k=(int(m[1]),m[2]); rows.setdefault(k,[]).append((int(m[3]),int(m[4]),int(m[5]),int(m[6])))
    return rows
for p in sys.argv[1:]:
    R=load(p); print("==",p.split('/')[-1], open(p).readline().strip())
    for k in sorted(R):
        hb={r[0] for r in R[k]}; ns=[r[3] for r in R[k]]
        print(f"  n={k[0]:>2} ctrl={k[1]:5} raw heartbeats {sorted(hb)}  ns median {st.median(ns)/1e6:.3f} ms  (min {min(ns)/1e6:.3f}, max {max(ns)/1e6:.3f}, k={len(ns)})")
    dhb=R[(64,'false')][0][0]-R[(64,'true')][0][0]
    dns=[a[3]-b[3] for a,b in zip(R[(64,'false')],R[(64,'true')])]
    print(f"  device cells (64, net of control): {dhb} heartbeats, {st.median(dns)/1e6:.3f} ms median -> {st.median(dns)/dhb:.2f} ns/heartbeat (spread {min(dns)/dhb:.2f}..{max(dns)/dhb:.2f})")
