#!/usr/bin/env python3
"""Zipf strain gauge for Volume 5 (bm-vol5-zipf-strain / -zipf-howto / -length-convergence).

Where Zipf's law is *actually computed* for Vol5. NOT an honesty check (lexical only):
a doc can be perfectly Zipfian and still force the lab value. Use for vocabulary economy.

  measure  -> tokenize (strip LaTeX), freq-rank, log-log least-squares fit, slope = -s (the exponent)
  baseline -> same fit on the RELAXED reference (Vols 1-3); strain = deviation from that
  residuals-> per-word (log f_obs - log f_fit) at its rank; fat tail = over-tanged (prune/promote/refunge)
  length   -> K subsamples of N/2, sigma = std(s); converged when |s(N)-s(N/2)| < sigma

Usage:
  python3 zipf_strain.py                      # Vol5 vs Vols1-3 baseline (defaults)
  python3 zipf_strain.py path/to/chapters     # measure that dir vs the baseline
"""
import sys, os, re, math, random, glob
from collections import Counter

ROOT = "/Users/williamcochran/Desktop/measurement"
VOL5   = f"{ROOT}/books/volume5/latex/chapters"
BASELINE = [f"{ROOT}/books/expository_monograph/vol1/chapters",
            f"{ROOT}/books/experimentation/vol2/chapters",
            f"{ROOT}/books/the_compiler/vol3/chapters"]
# the coined tange/funge family (bm-vol5-word-cost) — watch where these sit on the curve
FAMILY = {"tange","funge","tanges","funges","tanged","funged","retange","refunge",
          "nowtrino","newtrino","naotrino","contravariant","covariant"}

# TRUNCATED ZIPF (operator 2026-07-13): fit the slope on the top-TOP_RANKS words only.
# Zipf's law holds in the HEAD and breaks down in the hapax tail; fitting the full curve
# lets the fat freq-1 tail flatten/distort the exponent (it measures the coinage noise, not
# the prose's vocabulary economy). Truncate to the head so the strain reads the real curve.
TOP_RANKS = 1000

def tokenize(text):
    text = re.sub(r"(?<!\\)%.*", " ", text)      # strip comments
    text = re.sub(r"\\[a-zA-Z]+\*?", " ", text)   # strip \commands
    text = re.sub(r"[$\\{}\[\]~^&_#]", " ", text) # strip math/markup glyphs
    return re.findall(r"[a-z][a-z'-]*[a-z]|[a-z]", text.lower())

def math_fraction(dirs):
    """math is the OTHER channel the word-Zipf can't see (bm insight: swapping math<->words
    alters the prose strain). Report math-chars / (math+prose) chars -> the 'headroom' to
    relieve an over-funged prose head by moving repeated quantitative prose into equations."""
    mathc = prosec = 0
    for d in (dirs if isinstance(dirs, list) else [dirs]):
        for f in sorted(glob.glob(os.path.join(d, "*.tex"))):
            t = open(f, encoding="utf-8", errors="ignore").read()
            t = re.sub(r"(?<!\\)%.*", "", t)
            math = re.findall(r"\$[^$]*\$|\\\[.*?\\\]|\\\(.*?\\\)|\\begin\{(?:equation|align|gather|math)\*?\}.*?\\end\{[^}]*\}", t, re.S)
            m = sum(len(x) for x in math)
            mathc += m; prosec += max(0, len(t) - m)
    tot = mathc + prosec
    return (mathc/tot if tot else 0.0, mathc, prosec)

def load(dirs):
    toks = []
    for d in (dirs if isinstance(dirs, list) else [dirs]):
        for f in sorted(glob.glob(os.path.join(d, "*.tex"))):
            with open(f, encoding="utf-8", errors="ignore") as fh:
                toks += tokenize(fh.read())
    return toks

def fit(toks, top=TOP_RANKS):
    """least-squares slope of log(freq) vs log(rank); returns (s, counter, ranked).
    TRUNCATED: the slope is fit on the top-`top` ranks only (the head where Zipf holds);
    the full counter/ranked are still returned for the tail diagnostics (hapax/residuals)."""
    c = Counter(toks)
    ranked = c.most_common()                       # [(word, freq), ...] rank = index+1 (FULL)
    head = ranked[:top]                            # TRUNCATE the fit to the head
    xs = [math.log(i+1) for i in range(len(head))]
    ys = [math.log(f)   for _, f in head]
    n = len(xs)
    if n < 3: return (float("nan"), c, ranked)
    mx, my = sum(xs)/n, sum(ys)/n
    num = sum((x-mx)*(y-my) for x,y in zip(xs,ys))
    den = sum((x-mx)**2 for x in xs)
    slope = num/den if den else float("nan")
    return (-slope, c, ranked)                     # s = -slope > 0

def half_length_stat(toks, K=20):
    """s(N/2) mean + sigma across K random half-samples (subsample, not prefix).
    Returns (s_half_mean, sigma). The length-convergence test (bm-vol5-length-convergence):
    converged when |s(N) - s(N/2)| < sigma -- doubling the length moves the exponent
    less than the sampling scatter, so more length only refits noise. THIS is the finer
    reading the recursive step buys as the book grows: re-fit at the longer N each build."""
    if len(toks) < 20: return (float("nan"), float("nan"))
    ss = []
    for k in range(K):
        rng = random.Random(1000 + k)              # deterministic seeds (no global RNG state)
        ss.append(fit(rng.sample(toks, len(toks)//2))[0])
    m = sum(ss)/len(ss)
    return (m, math.sqrt(sum((x-m)**2 for x in ss)/len(ss)))

def baseline_at_length(base_toks, N_target, K=20):
    """HONEST baseline: subsample Vols1-3 to the target's length, avg s over K trials.
    (Zipf exponent drifts with N; comparing a short draft to a huge corpus measures length,
    not strain -- bm-vol5-length-convergence. So calibrate the baseline AT the draft's length.)"""
    if N_target >= len(base_toks): return fit(base_toks)[0], 0.0
    ss = []
    for k in range(K):
        rng = random.Random(2000 + k)
        ss.append(fit(rng.sample(base_toks, N_target))[0])
    m = sum(ss)/len(ss)
    sd = math.sqrt(sum((x-m)**2 for x in ss)/len(ss))
    return m, sd

def report(name, toks, base_toks=None, target_dir=None):
    s, c, ranked = fit(toks)
    V, N = len(c), len(toks)
    fitN = min(TOP_RANKS, V)
    print(f"\n== {name} ==")
    print(f"   tokens N={N}  types V={V}  Zipf exponent s={s:.3f}  [fit on top-{fitN} ranks (truncated)]")
    if base_toks is not None:
        s0m, s0sd = baseline_at_length(base_toks, N)  # matched-length baseline
        print(f"   baseline @ MATCHED length N={N}:  s0={s0m:.3f} +/- {s0sd:.3f}")
        strain = s - s0m
        verdict = "within baseline scatter (relaxed)" if abs(strain) <= 2*s0sd else \
                  ("OVER-TANGED (too flat/fat-tailed -> prune/promote tail)" if strain < 0 else
                   "OVER-FUNGED (too steep -> split the head)")
        print(f"   ==> HONEST strain = {strain:+.3f}   [{verdict}]")
    s_half, sig = half_length_stat(toks)
    drift = abs(s - s_half)
    conv = "CONVERGED (reading final -> act on residuals; the descent)" if drift < sig else \
           "NOT YET (reading refines as the book grows -- light-steer only; re-fit next build = the recursive step)"
    print(f"   length convergence: |s(N)-s(N/2)| = {drift:.3f}  vs  sigma = {sig:.3f}  ->  {conv}")
    # ANNEALING schedule (operator: "annealing is the best way forward"): temperature = how far the
    # reading is from its frozen (converged) floor. HOT -> explore broadly (accept diverse / non-monotone
    # moves, escape greedy local minima); COOL -> only-improving; FROZEN -> fine-tune then funge-back-to-1.
    # The strain is the ENERGY to minimize; the HONESTY constraints (blind / grade-off-build / keep the
    # reflexive core / funge=pool-AND-record) are HARD -- never annealed, they bound the feasible space.
    if base_toks is not None and sig > 0:
        T = drift / sig    # temperature in units of sampling scatter
        phase = ("HOT -> EXPLORE (diverse moves, tolerate non-monotone strain, escape local minima)" if T > 10
                 else "COOLING -> prefer only-improving moves, targeted at the clusters" if T > 3
                 else "COLD -> fine-tune only; near frozen" if T > 1
                 else "FROZEN -> converged; run funge-back-to-1")
        accept_worse = math.exp(-1.0 / T) if T > 0 else 0.0   # Metropolis: P(accept a +1sigma worse move)
        print(f"   anneal: T = drift/sigma = {T:.1f}  ->  {phase}   [P(accept a +1sigma worse move) = {accept_worse:.2f}]")
    if base_toks is not None:
        mf, mc, pc = math_fraction(target_dir) if target_dir else (0,0,0)
        print(f"   math/prose channel: math={100*mf:.1f}% of chars  <- swap repeated quantitative prose <-> math to alter the word-strain (over-funged head -> move some into equations; the word-Zipf can't see math)")
    # trajectory log: watch the exponent converge across builds (the recursive step)
    if base_toks is not None:
        try:
            logp = os.path.join(os.path.dirname(os.path.abspath(__file__)), "zipf_log.tsv")
            new = not os.path.exists(logp)
            with open(logp, "a") as lg:
                if new: lg.write("N\ttypes\ts\ts0_matched\tstrain\tsigma\tdrift\tconverged\n")
                lg.write(f"{N}\t{V}\t{s:.3f}\t{s0m:.3f}\t{strain:+.3f}\t{sig:.3f}\t{drift:.3f}\t{drift<sig}\n")
        except Exception:
            pass
    # per-word residuals vs the fit line (computed on the same truncated head as the slope)
    head = ranked[:TOP_RANKS]
    xs = [math.log(i+1) for i in range(len(head))]
    ys = [math.log(f) for _, f in head]
    n=len(xs); mx=sum(xs)/n; my=sum(ys)/n
    b = my + s*mx  # intercept for y = -s*x + b (fit on the head)
    hapax = [w for (w,f) in ranked if f==1]
    print(f"   hapax (freq-1) types: {len(hapax)}  ({100*len(hapax)/V:.0f}% of vocab)  <- the fat-tail / prune-or-promote pool")
    STOP = set("the a an of to and in is it that this as by for with on at from be are was "
               "or not its it's into which what where when who how you i he she they we but if "
               "so no than then them their there here has have had do does did will would can "
               "one two only own all any more most such only very own out up off back".split())
    over = [(w,f) for (w,f) in ranked if w not in STOP and w not in FAMILY][:12]
    print(f"   OVER-USED content head (split-candidates if over-funged): "
          + ", ".join(f"{w}:{f}" for w,f in over))
    under = [w for (w,f) in ranked if f<=2 and w not in STOP and len(w)>4][:20]
    print(f"   UNDER-USED tail sample (prune noise / promote real / refunge shared): "
          + ", ".join(under))
    print(f"   FAMILY coinages (rank/freq — want climbing the curve, not stuck at 1):")
    for i,(w,f) in enumerate(ranked):
        if w in FAMILY:
            print(f"       {w:<14} rank {i+1:<5} freq {f}")
    return s

HEAD_WORDS = ["reading","read","reads","book","machine","name","names","thing","cannot","world","volume","value"]
def local_strain_map(target):
    """WHERE the strain clusters (per-chapter over-funge density) -- the strain has locations,
    it is not a constant background. The recursion should point the head-split at the high-density
    chapters (tange the high-residual pieces), not blanket the book."""
    print("\n== LOCAL STRAIN MAP (per-chapter over-funge density = head-word share; strain clusters here) ==")
    print(f"   {'chapter':<10}{'tokens':>7}{'head%':>8}   dominant repeats")
    for f in sorted(glob.glob(os.path.join(target if isinstance(target,str) else target[0], "*.tex"))):
        toks = tokenize(open(f, encoding='utf-8', errors='ignore').read()); n = len(toks) or 1
        c = Counter(toks); head = sum(c[w] for w in HEAD_WORDS)
        top = ", ".join(f"{w}:{c[w]}" for w in HEAD_WORDS if c[w] >= 6)
        flag = "  <== CLUSTER" if 100*head/n >= 6 else ""
        print(f"   {os.path.basename(f):<10}{n:>7}{100*head/n:>7.1f}%   {top}{flag}")

def seam_map(target, W=160, step=24, sigma=2.5):
    """GAUSS-SMOOTHING kernel (operator: 'gauss smoothing is another kernel; it will also show you seams').
    The heat kernel SPREADS the residue (relax); the Gaussian kernel SMOOTHS the strain field so its
    DISCONTINUITIES survive as edges = SEAMS -- where the text joins unevenly (esp. the funge-back-to-1
    reassembly joins, and the boundaries between differently-relaxed regions). Smooth, then take the
    gradient; the gradient peaks are the seams. WITHIN-chapter seams are the ones to smooth in the final read
    (chapter boundaries are expected)."""
    d = target if isinstance(target, str) else target[0]
    stream = []
    for f in sorted(glob.glob(os.path.join(d, "*.tex"))):
        ch = os.path.basename(f)
        for t in tokenize(open(f, encoding='utf-8', errors='ignore').read()):
            stream.append((t, ch))
    toks = [t for t, _ in stream]; N = len(toks)
    if N < 2*W:
        print("\n== SEAM MAP == (document too short)"); return
    HEAD = set(HEAD_WORDS)
    xs, dens, ch = [], [], []
    for i in range(0, N - W, step):
        w = toks[i:i+W]
        dens.append(sum(1 for x in w if x in HEAD)/W)
        ch.append(stream[i + W//2][1]); xs.append(i + W//2)
    # gaussian smooth the strain signal
    r = int(3*sigma); ker = [math.exp(-(k*k)/(2*sigma*sigma)) for k in range(-r, r+1)]
    sm = []
    for i in range(len(dens)):
        a = s = 0.0
        for j, kk in enumerate(ker):
            idx = i + (j - r)
            if 0 <= idx < len(dens): a += dens[idx]*kk; s += kk
        sm.append(a/s)
    # gradient magnitude of the smoothed field = edge strength
    grad = [0.0] + [abs(sm[i+1]-sm[i-1])/2 for i in range(1, len(sm)-1)] + [0.0]
    # seams = local maxima of the gradient (report top relative peaks; flag if any exceed the 'strong' threshold)
    STRONG = 0.012
    seams = [i for i in range(1, len(grad)-1) if grad[i] >= grad[i-1] and grad[i] > grad[i+1]]
    seams.sort(key=lambda i: grad[i], reverse=True)
    mx = max(grad) if grad else 0.0
    verdict = "SMOOTH (relaxed evenly; funge-back-to-1 stitched cleanly)" if mx < STRONG else "HAS STRONG SEAM(S) -> smooth in the final read"
    print(f"\n== SEAM MAP (gauss-smoothed strain field; edges = uneven joins) -- field {verdict}, max edge={mx:.4f} vs strong={STRONG} ==")
    print(f"   {'edge':>6}  {'chapter':<9} {'kind':<22} density")
    for i in seams[:8]:
        boundary = (ch[i] != ch[i-1]) or (i+1 < len(ch) and ch[i] != ch[i+1])
        kind = ("chapter boundary" if boundary else "⚑ WITHIN-CHAPTER seam") + (" [STRONG]" if grad[i] >= STRONG else "")
        print(f"   {grad[i]:.4f}  {ch[i]:<9} {kind:<22} {sm[max(0,i-2)]:.2f}->{sm[min(len(sm)-1,i+2)]:.2f}")

if __name__ == "__main__":
    target = sys.argv[1] if len(sys.argv) > 1 else VOL5
    base_toks = load(BASELINE)
    report("BASELINE (Vols 1-3, relaxed reference)", base_toks)
    report(f"TARGET ({target})", load(target), base_toks=base_toks, target_dir=target)
    local_strain_map(target)
    seam_map(target)
