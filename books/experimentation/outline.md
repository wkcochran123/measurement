# Experimentation: An Applied Physics — Outline (Volume 2)

*Companion to* Measurement *(Vol 1, the apparatus) and* The Compiler *(Vol 3, the self-hosting). This
volume turns the apparatus on **physics**: ~139 historical effects, each derived with the physicist's full
mathematical notation, grounded in the finite experiment that demonstrates it. Owned by Kodo; Podo guards
the roster against the code, then writes the math-heavy `.tex` guarded by Kodo. Source: the surveyed
`device/Experiments/*` (descriptions + `Experiment{1,2,3}.lean`).*

## The book's contract (the stance)
- **Math is the content.** Unlike Vol 1/3, this book uses **as much mathematical notation as possible** —
  equations, derivations, the physicist's reasoning. The math is **liberal but plausible**: derive the way
  working physics derives, heuristically, before the rigor catches up.
- **The ceiling is the conscience.** Every effect's finite experiment fences its claim at one of four
  honest ceilings. The liberal physics math sits *above* the fence; the book always names the fence, so the
  liberality is never dishonest:
  - **`finiteLedgerModel`** — the effect is modeled as a finite count obligation (conservation/additivity),
    NOT a continuum theorem.
  - **`smoothShadowAnalogy`** — the finite model is the discrete *shadow* of the continuum effect; the
    bridge to the equation is an analogy, named as one.
  - **`inadmissibilityNoGo`** — the effect is an impossibility: some refinement is provably inadmissible.
  - **`physicalClaimLabelOnly`** — only the phenomenon is named; no model is claimed (the math is pure
    physics prose, the experiment a label). (`ModelKind.labelsOnly`, setup `{1,1,1}`.)
- **Name physics freely.** This is applied physics — say "Lorentz transform," "Hilbert space," "Cooper
  pair." The honesty device is the ceiling, not a fence on the vocabulary.

## Per-effect template (every section)
1. **The effect** — the physics (from the description's Statement/Origin/Observation).
2. **The math** — full notation: the equation(s) and a liberal-but-plausible derivation (the *math hook*).
3. **The finite model & its ceiling** — what the experiment actually demonstrates, and which of the four
   ceilings it lands on (the honest floor).
4. **The reading** — the effect as a fact about finite refinement (the construction's interpretation).

## Anchors of unusual strength (give these prominence)
Most experiments couple to the harness (`count_append`, `count_map`, `sameShadow`, `boundedBy`). A few are
**device-coupled** — they prove a genuine ±1/holonomy or sign result against `Measurement` (Episodes 82–85),
so the finite model isn't a label but a theorem: **PositronAnnihilation** (the designated exemplar, 511 keV
coincidence, Ep82–83), **PositronThreshold** (δ² sign-change root-bracketing, Ep85), **Chirality**,
**Davisson–Germer**, **Sagnac** (Ep84), **Dirac operator**, **Feynman diagram**, **EchoChamberMaze** (all
holonomy ±1). Foreground these as the chapters where the physics is *earned*.

---

# PART I — MECHANICS AND MOTION

### Ch I.1 — Motion and Its Records
- **The Aristotle Effect** — relabeling isn't a fact. invariance of content under relabeling; `count_map`. *finiteLedgerModel*
- **The Descartes Effect (Ch03)** — continuous motion via coordinate quantization. floor against unit; recoverability in-cell. *finiteLedgerModel*
- **The Descartes Effect (Ch08)** — independent rulers → ordered pairs; non-commuting composition. (countA,countB) separates a flat sum. *finiteLedgerModel*
- **The Velocity Effect** — relative velocity as a difference of event counts after merge. relational kinematics, count differences survive. *finiteLedgerModel*
- **The Galileo Effect** — a physical statement survives every relabeling. `count_map` invariance. *finiteLedgerModel*

### Ch I.2 — Force, Inertia, Momentum
- **The Newton Effect** — inertia/mass as the cost of a misaligned phase. F = ma; mass = persistent reconciliation cost. *finiteLedgerModel*
- **The Momentum Effect** — momentum as the conjugate enforcing flux balance. {x,p}; ∂-conservation across a boundary. *finiteLedgerModel*
- **The Acceleration Effect** — acceleration as informational curvature, not force. a = Δ²x (second difference / coasting-fit failures). *finiteLedgerModel*
- **The da Vinci–Coulomb Effect** — static friction, slip as an unpredictable threshold event. |F| ≥ μ|N| as a bound, not a procedure. *inadmissibilityNoGo*

### Ch I.3 — Orbits and Rotation
- **The Kepler Effect** — orbits as non-degenerate closed cycles. closure γ(t+T)=γ(t); loop length ≥ 2. *finiteLedgerModel*
- **The Angular Momentum Effect** — conservation of L. L = Iω, I ≈ MR², ω = 2πf; tick conservation. *finiteLedgerModel*
- **The Foucault Effect** — precession as holonomy of an inconsistent connection. transport residue mod slots; fails to close iff precession ≠ 0. *smoothShadowAnalogy*

### Ch I.4 — The Least Principle and the Unseen
- **Minimizing Variations** — Euler–Lagrange. δJ[x;η] = ∫(f_x − d/dt f_ẋ)η dt = 0; boundary term [f_ẋ η]ᵃᵇ vanishes. *smoothShadowAnalogy*
- **Repeatability of Invisible Motion** — no events ⇒ minimal cubic reconstruction. U⁗ = 0; cubic patches glue C². *smoothShadowAnalogy*
- **The Dirichlet–Bancroft Effect** — GPS: exact yet under-constrained; boundary gives uniqueness. solution multiplicity 2 → 1 under a boundary filter. *finiteLedgerModel*
- **The Butterfly Effect** — prediction horizon from sub-resolution info, not geometric chaos. combinatorial microhistory count = apparatus capacity. *finiteLedgerModel*

# PART II — FIELDS, WAVES, AND LIGHT

### Ch II.1 — The Field That Acts Where It Isn't
- **The Aharonov–Bohm Effect** — phase from the potential's holonomy where F = 0. Δφ = (e/ℏ)∮A·dx = eΦ/ℏ; flux quantum h/e. *finiteLedgerModel*
- **The Echo Chamber Maze** — curvature as phase residue; straight = clean echo. holonomy: open path trivial, closed loop ±1. *finiteLedgerModel* (device-coupled)
- **The Conservation of Energy** — stress-energy continuity. ∂_μT^{μ0}=0; ∂_tE + ∇·S = 0; ∮ flux. *finiteLedgerModel*

### Ch II.2 — Diffraction, Interference, Polarization
- **The Arago (Poisson) Spot** — bright spot in a shadow's center. symmetric rim contributions agree (Fresnel–Kirchhoff). *finiteLedgerModel*
- **The Mach–Zehnder Effect** — interferometer; arms coexist until a fold selects. phase mod 2π; π-phase ⇒ destructive. *smoothShadowAnalogy*
- **The Malus Effect** — crossed polarizers extinguish the beam. I = I₀cos²(Δθ); 90° ⇒ 0. *inadmissibilityNoGo*
- **The Schrödinger–Young Effect** — double slit; which-path destroys interference. |ψ_A+ψ_B|² vs decohered mixture. *finiteLedgerModel* (cross-listed w/ Quantum)

### Ch II.3 — Sampling, Spectra, and the Limits of a Reading
- **The Fourier–Nyquist Effect** — exact decomposition iff sampled densely enough. Nyquist rate 2B; spectrum ≤ sample rate. *smoothShadowAnalogy*
- **The Gibbs Phenomenon** — band-limited overshoot at a discontinuity. residual gap = height − min(height, B). *smoothShadowAnalogy*
- **The Gibbs Preservation Effect** — edges survive smoothing in the operator null space. null space of a smoothing kernel; [+h,−h] invariant. *smoothShadowAnalogy*
- **The Moiré Effect** — beats from two near-pitch lattices. f_beat = |f₁ − f₂|. *finiteLedgerModel*
- **The Message Effect** — only the symmetric (Galerkin) component is recoverable. discrete curl; ∮R·dℓ ≠ 0 closure defect. *smoothShadowAnalogy* (bespoke, harness-coupled)

### Ch II.4 — Force from Geometry (the inverse square)
- **The Inverse-Square Effect** — influence dilutes across an r² frontier. per-slot influence ≤ budget/r²; 6r² lattice shell. *smoothShadowAnalogy*

# PART III — HEAT, ENTROPY, AND MATTER

### Ch III.1 — Statistics from Repetition
- **The Gauss (First) Effect** — the normal distribution from repetition. emergent (μ,σ²); additivity of bin totals. *finiteLedgerModel*
- **The Gosset Effect (Ch02 / Ch07)** — small-sample pooling, and hypothesis testing as projection. (Ch02) signal additivity; (Ch07) residual ⟂ u, ‖x − ⟨x,u⟩u‖. *finiteLedgerModel / smoothShadowAnalogy*
- **The Bayes Effect** — posterior as the minimal coherence-restoring correction. log post = log prior + log likelihood + c. *finiteLedgerModel*

### Ch III.2 — The Second Law and the Cost of Information
- **Maxwell's Demon** — sorting is entropy-producing. ΔS_gas + ΔS_demon = k_B ln|Ω| > 0; [M,U] ≠ 0. *finiteLedgerModel*
- **The Thermodynamic Cost of Erasure** — Landauer. E_min = k_B T ln 2 per bit; ΔS ≥ k_B ln 2. *finiteLedgerModel*
- **The Entropic Cost of Acceleration** — Unruh-flavored horizon; T = sealed-page count. horizon threshold splits reachable/sealed. *smoothShadowAnalogy*
- **The Ideal Ledger Effect** — pressure as flux density of reconciliation. PV = nT as additive ledger counts. *finiteLedgerModel*
- **The Thermostat Effect** — stable equilibrium / negative feedback. δ²ℐ > 0 stable vs δ²ℐ < 0 unstable. *finiteLedgerModel*

### Ch III.3 — Matter in Bulk: Diffusion, Domains, Disorder
- **The Brownian Motion Effect** — diffusion → uₜ = D uₓₓ (→ free Schrödinger by continuation). discrete Laplacian u_{i+1}−2uᵢ+u_{i−1}. *smoothShadowAnalogy*
- **The Ising Effect** — domains align; a domain wall between matched regions is forbidden. seam-label match; mismatch inadmissible. *inadmissibilityNoGo*
- **The Anderson Effect** — localization: disorder blocks coherent transport. no globally consistent minimal path through disorder. *inadmissibilityNoGo*
- **The Navier–Stokes Effect** — viscosity as a closure-correction. ∂_tu + (u·∇)u = −∇p + νΔu; νΔu = smooth shadow of the strain operator. *smoothShadowAnalogy*
- **The Quicksand Effect** — buoyant/yield-stress equilibrium. ρ_fluid V g; sub-δ refinements inadmissible. *finiteLedgerModel*

### Ch III.4 — Chemistry: Counting Reactions
- **The Archimedes–Proust Effect** — definite proportions. integer stoichiometric ratios; continuum as alphabet only. *finiteLedgerModel*
- **The Stoichiometry Effect** — selection rules as integer balance. a·N_A + b·N_B → c·N_C, a,b,c ∈ ℤ. *finiteLedgerModel*
- **The Celsius–Lagrange Effect** — a scale arbitrary in symbol, stable in relation. linear interpolation between anchors; recoverability. *smoothShadowAnalogy*
- **The First Effect of Gibbs** — a catalyst lowers strain at zero net balance. forward/inverse loop cancels; count additive. *finiteLedgerModel*

### Ch III.5 — Condensed Matter (the label-only frontier)
- **The Semiconductor Effect** — bandgap conduction. n ∝ exp(−E_g/k_BT). *physicalClaimLabelOnly*
- **The Superconducting Effect** — Cooper pairing, zero resistance. (e_i,e_j) symmetric, Strain(Ψ_pair)=0. *physicalClaimLabelOnly*
- **The Meissner Effect** — flux expulsion. F_{μν}|_Ω = 0 under Strain = 0. *physicalClaimLabelOnly*

# PART IV — THE QUANTUM

### Ch IV.1 — Uncertainty, Hilbert Space, and the Oscillator
- **The Heisenberg Effect (+ as Trade-off)** — a minimum refinement floor; conjugate trade-off. Δx·Δp ≥ ℏ/2 as a fixed capacity budget. *finiteLedgerModel / inadmissibilityNoGo*
- **The Hilbert Effect** — admissible refinements complete to an inner-product space. ‖p‖² = a²+b²; Ψ, Ψ⁻¹ mutual inverses. *smoothShadowAnalogy*
- **The Harmonic Oscillator (+ Revisited)** — minimal reversible dynamics; quantized spectrum. δ²U + ω²U = 0; E = ½[(δU)² + ω²U²]; Eₙ = ℏω(n+½). *smoothShadowAnalogy / finiteLedgerModel*

### Ch IV.2 — Measurement, Decoherence, Nonlocality
- **Qubit Decoherence** — a causal doublet collapses on an inconsistent event. doublet S={e₀,e₁}; collapse forced. *inadmissibilityNoGo*
- **Shadow Tomography** — only a bounded coarse shadow is accessible. tests {O₁…O_m}; equal-shadow ⇒ indistinguishable. *finiteLedgerModel*
- **Spooky Action at a Distance** — EPR; recording one fixes the partner, no signal. commuting uncorrelants E_iE_j = E_jE_i. *finiteLedgerModel*
- **The Entanglement Effect** — causal degeneracy resolved by a boundary pivot. order-tag independence on the seam. *finiteLedgerModel*
- **The Bell/Aspect Tests** — no local hidden variable. non-factorizable joint update (CHSH). *inadmissibilityNoGo*
- **The Hall–Einstein–Podolsky–Rosen Effect** — joint inference needs correlant seams. seam compatibility constraint. *inadmissibilityNoGo*

### Ch IV.3 — Matter Waves and Scattering
- **The Davisson–Germer Effect** — electron diffraction; Bragg peaks. 2d sin θ = mλ, λ = h/p; Bragg = closed loop holonomy ±1. *smoothShadowAnalogy* (device-coupled)
- **The Compton Scattering Effect** — wavelength shift; Noether conservation. Δλ = (h/m_ec)(1−cosθ); p,E conserved. *finiteLedgerModel*
- **The Photoelectric Effect** — discrete threshold. K_max = hν − Φ, ν₀ = Φ/h. *physicalClaimLabelOnly*

### Ch IV.4 — Particles, Spin, and the Dirac Equation
- **The Dirac Operator** — minimal first-order gauge-covariant generator. iγ^μD_μ; holonomy residue; spin sign. *finiteLedgerModel* (device-coupled)
- **The Spin-½ Effect** — 2π flips the sign; 4π restores. {γ^μ,γ^ν}=2g^{μν}; S = ℏ/2; Spin(3,1) double cover. *physicalClaimLabelOnly*
- **The Chirality Effect** — parity violation; Ψ_L ≠ Ψ_R. holonomy sign +1 ≠ −1; loop charged, open path trivial. *inadmissibilityNoGo* (device-coupled)
- **The Feynman Diagram** — amplitude as tensor-contraction holonomy. loop charged ±1, tree trivial. *finiteLedgerModel* (device-coupled)

### Ch IV.5 — Detection: the Positron (the exemplar)
- **The Positron Annihilation Effect** — e⁺e⁻ → two 511 keV γ; coincidence registers a positron. m_ec² = 511 keV; back-to-back momentum; coincidence window. *finiteLedgerModel* **(EXEMPLAR, Ep82–83)**
- **The Positron Threshold Effect** — the creation-tilt threshold a discrete apparatus can only bracket. δ² sign change −1→+1 on (0,1]; knot root = ½. *finiteLedgerModel* (device-coupled, Ep85)

### Ch IV.6 — Decay, Confinement, and Symmetry Breaking
- **The Alpha Decay Effect** — boundary repair removes a bad branch (no tunneling assumed). continuum limit of irreversible repairs → exponential law. *inadmissibilityNoGo*
- **The Gamma Decay Effect** — reversible conservative split. excited count = ground + photon (count_append). *finiteLedgerModel*
- **The Neutrino Effect** — the near-interaction-free messenger arrives first. curvature residue R; saturates c. *physicalClaimLabelOnly*
- **The Strong Interaction Effect** — confinement; strain self-confines. Σ(q_i,q_j) ≠ Σ(q_i)+Σ(q_j); V ∝ r. *physicalClaimLabelOnly*
- **The Sombrero Potential** — spontaneous symmetry breaking / Higgs. V(φ)=λ(|φ|²−v²)²; φ=(v+h)e^{iθ}; Goldstone absorbed. *physicalClaimLabelOnly*
- **The Yang–Mills Effect** — the Standard-Model gauge group. U(1)×SU(2)×SU(3); A_μ the smooth shadow. *physicalClaimLabelOnly*
- **The Casimir Effect** — boundary-restricted vacuum modes attract. interior mode count < exterior; P ∝ 1/d⁴. *smoothShadowAnalogy*
- **The Topological Integer Count** — quantization by winding number. winding ∈ ℤ (Chern/TKNN); no fractional thread. *finiteLedgerModel*

# PART V — RELATIVITY AND GRAVITATION

### Ch V.1 — Frames, Clocks, and the Interval
- **The Maxwell Effect** — frame relativity; no preferred frame. invariant interval τ² = g_{μν}dx^μdx^ν; Lorentz Λ. *finiteLedgerModel*
- **The Michelson–Morley Effect** — null result as isotropy of the metric. τ² rotation-invariant. *finiteLedgerModel*
- **The Einstein Effect (Ch07 / Ch08)** — different clock labels; proper-time maximality. causal order invariant; realized clock maximizes step count. *finiteLedgerModel*
- **The Refinement Effect** — relative motion as differential refinement depth. ΔN over (a,b); order-embedding. *finiteLedgerModel*
- **The Time Effect** — the arrow of time as counted resolutions. time = count of closed DOF/ticks. *finiteLedgerModel*
- **LiDAR** — time dilation by laser ranging; the denser-record twin ages more. Lorentz limit; merged count = base + forced refinements. *smoothShadowAnalogy*
- **The Sagnac Effect** — rotation phase. Δt = 4ΩA/c² as a loop holonomy. *smoothShadowAnalogy* (device-coupled, Ep84)

### Ch V.2 — Gravity: Redshift, Delay, Potentials
- **The Pound–Rebka Effect** — gravitational redshift (fold Ch06+Ch08). Δν/ν ≈ Γ Δh; ν_high = ν_low(1 − Γ Δh). *smoothShadowAnalogy*
- **The Traffic Effect** — Shapiro time delay. extra ticks across a stressed region; g_{μν} as gauge. *smoothShadowAnalogy*
- **The Dark Energy Effect** — accelerating expansion from negative effective pressure. P_eff = P − Λ; P_eff < 0 drives outward. *smoothShadowAnalogy*

### Ch V.3 — Horizons and the Holographic Edge
- **The Schwarzschild Effect** — the event horizon. r_s = 2GM/c² (informational r_U = 2GM_U/c²). *smoothShadowAnalogy*
- **The Event Horizon Effect** — a horizon as an export-cost bottleneck. budget < cost ⇒ exchange rate → 0. *smoothShadowAnalogy*
- **The Hawking Effect (+ Radiation + Revisited)** — horizon pair creation / boundary repair. q_in = −q_out; U^out_{n+1} = e_rad·U^out_n; kT = ℏκ/2π. *finiteLedger / smoothShadow*
- **The White Hole Effect** — the time-reverse source. outward-only transport; backward extension inadmissible. *smoothShadowAnalogy*
- **The 't Hooft–Susskind Effect** — holography; area not volume bounds information. N(Ω) ≤ f(|∂Ω|) (Bekenstein area law). *physicalClaimLabelOnly*

### Ch V.4 — Cosmology and Causal Paradox
- **The Olbers Effect** — the dark night sky proves a finite luminous record. would-be ∫ → ∞; finiteness is the obstruction. *inadmissibilityNoGo*
- **The Flat Rotation Curve Effect** — flat curves from bandwidth saturation (presented informationally). residue vanishes iff radial/tangential chains agree. *smoothShadowAnalogy*
- **Paradoxes of Time Travel** — over-resolution (Banach–Tarski-like) is inadmissible. uncountable refinement breaks finiteness; countable selection restores. *inadmissibilityNoGo*

# PART VI — FOUNDATIONS: COMPUTATION, LIMITS, AND MEASUREMENT

### Ch VI.1 — What Counts as a Measurement
- **The Peano–Kushim Effect** — existence-by-counting; the measurement axiom. successor S(n); unit histogram increment. *finiteLedgerModel*
- **The Bacon Effect** — admissible ⇔ reproducible; the ruler is a procedure. Condition → Reading; same shadow on repeat. *finiteLedgerModel*
- **The Euclid Effect** — recorded distinctions are permanent. count monotone under append. *finiteLedgerModel*
- **The Marconi Effect** — verified silence is information. presence/absence; non-detection as a boundary condition. *finiteLedgerModel*
- **The Adams Effect** — a number without a decoding map is noise ("42"). unlicensed value inadmissible as meaning. *inadmissibilityNoGo*

### Ch VI.2 — Resolution, Precision, and the Continuum
- **The Berkeley–Galileo Effect** — no finite instrument resolves arbitrarily small variation. shadow = ⌊state/res⌋; sub-res indistinguishable. *finiteLedgerModel*
- **Precision** — a unique minimal-curvature completion (precision ≠ accuracy). Law of Spline Sufficiency, Ψ⁽⁴⁾ = 0. *smoothShadowAnalogy*
- **Fluxions** — the derivative without infinitesimals. ẋ = Δx/Δt → Ψ′, C² cubic slope, no vanished dt. *smoothShadowAnalogy*
- **The Continuum Limit Effect** — the continuum as the h → 0 mesh limit (a *methodological* chapter). mixed δ² estimator → 1.0 vs Hooke plateau 1.5. *smoothShadowAnalogy* (no description.md; convergence-table study)
- **The Richardson Effect** — the coastline paradox; resolution-dependent length. L(ε) ∝ ε^{1−D}. *smoothShadowAnalogy*
- **The Pythagoras–Planck Effect** — √2 outstrips enumeration ⇒ a smallest quantum. irrational diagonal; minimum action h cutoff. *inadmissibilityNoGo*

### Ch VI.3 — Determinism, Induction, and Cause
- **The Laplace Effect** — deterministic continuation from a seed. unique forced successor value. *finiteLedgerModel*
- **The Hume Effect** — the inductive gap is real and realizable. past-consistent rule fails on a future refinement. *inadmissibilityNoGo*
- **The Cause-and-Effect Effect** — reliable causation as admissibility's residue. admissibility collapses an exponential future to a narrow set. *finiteLedgerModel*
- **The Bayes Effect** — *(cross-listed III.1)*

### Ch VI.4 — Time, Order, and Geometry from Records
- **The Kant Effect** — time induced as ledger order, not a backdrop. precedence = strict index inequality. *finiteLedgerModel*
- **The Wittgenstein Effect** — "after" is free; preserving order costs. a ≺ b admitted freely; invariant at zero cost. *finiteLedgerModel*
- **The Einstein Effect (Ch02)** — causal licensing: no reading without a prior trigger. licensed predicate; count conserved. *inadmissibilityNoGo*
- **The Cause-and-Effect Effect** — *(see VI.3)*
- **The Whitehead Effect** — dimension/geometry emergent from coordinated events. extensive abstraction; relations precede geometry. *finiteLedgerModel*
- **The Galileo–Abel Effect** — invariants persist under change of carrier/symbol. sameShadow under representation change. *finiteLedgerModel*

### Ch VI.5 — Relations, Logic, and the Algebra of Records
- **The Aristotle–De Morgan Effect** — relations as formal algebra (converse, composition). inversion as `map`; count preserved. *finiteLedgerModel*
- **Implied Orthogonality and Space-Time** — an info DOF "orthogonal" to spacetime (set-theoretic, NOT geometric). π(reading) = (here,now); sameShadow. *finiteLedgerModel*
- **The Fessenden–Shannon Effect** — finite channel decomposition beyond binary. refinement adds symbols without inflating the count. *finiteLedgerModel*
- **The Excel Effect** — global coherence by additive recalculation, not propagation. recalc additive under append. *finiteLedgerModel*
- **Compact Disc Encoding** — CIRC error correction; ordered refinement with a separation gauge. e₁ ≺ e₂ ≺ …; coarsen preserves count. *finiteLedgerModel*

### Ch VI.6 — Computation: Universality, Limits, Stability
- **The Turing Effect** — serialization/universality (NOT halting). reconstruct(serialize g) = g; one step per cell. *physicalClaimLabelOnly*
- **The Halt Effect** — refinement terminates when no successor satisfies the order. `mayPrecede` gate; halts on violation. *inadmissibilityNoGo*
- **The Jupyter Effect** — asynchronous causality; unordered conflicting writes are rejected (the kernel halts). collision iff same slot ∧ same order ∧ different values. *inadmissibilityNoGo*
- **The Prover–Verifier Effect** — physics as an interactive proof; law = the surviving fixed point. IP-style model ⊨ axioms. *finiteLedgerModel*
- **The Chaitin Effect** — a precise record with no extractable law (Ω). agree on prefix, disagree on next; no predictor. *physicalClaimLabelOnly*
- **The Cantor–Gödel–Cohen Effect** — CH independence as a choice of completion. faithful refinement preserves count; inflation detected. *inadmissibilityNoGo*
- **The von Neumann Effect (+ Trefethen)** — machine-ε floor; stability as survivorship (pseudospectra). required > accessible ⇒ blocked; ill-conditioned inadmissible. *inadmissibilityNoGo*
- **The Newton–Cooley–Tukey Effect** — recursion: FFT factorization and Newton iteration. O(N log N); x_{n+1} = x_n − f/f′. *finiteLedgerModel*

### Ch VI.7 — Scaling Laws of Systems
- **The Amdahl Effect** — the limit of parallel speedup. S_max = 1/(1−p), p = parallelizable fraction. *finiteLedgerModel*
- **The Tail Latency Effect** — worst-case sync latency. ℒ_tail ∝ N·|∂Ω|. *finiteLedgerModel*
- **The Pareto Effect** — power-law concentration; uniform weight inadmissible. P(x) ∝ x^{−α}; sparse-basis truncation. *finiteLedgerModel*
- **The Agent Effect** — agency as local strain minimization. U_local minimizes Ockham strain vs the stream. *finiteLedgerModel*
- **The Itô Lemma** — the (dX)² correction as a refinement artifact. df = f′dX + ½f″(dX)²; quadratic variation. *smoothShadowAnalogy*
- **LiDAR** — *(see V.1)*
- **The Limitation of Indexing** — entropy rises only under genuine refinement, not renaming. S = ln N; ΔS ≥ 0. *inadmissibilityNoGo*

---

## Production notes for Podo
- **Clustered sections (fold per the operator's "comprehensive, clustered"):** Pound–Rebka Ch06+Ch08 → one;
  Einstein Ch07+Ch08 → one (Ch02 stands apart in VI.4); Hawking ×3 → one; Harmonic ×2 → one; Heisenberg
  ×2 → one; Descartes Ch03+Ch08 → adjacent; Gosset Ch02+Ch07 → one (two readings); von Neumann ×2 → one;
  Galileo/Galileo–Abel → adjacent.
- **Missing descriptions:** `ThePositronThresholdEffect` and `TheContinuumLimitEffect` have no `description.md`
  — frame from the Lean docstrings (both detailed).
- **Cross-listings:** Schrödinger–Young (II.2 ↔ Quantum), Casimir (Quantum vacuum, placed IV.6), Quicksand
  (mechanics/fluids, placed III.3), Flat Rotation (placed V.4), 't Hooft–Susskind (placed V.3).
- **Math density:** physicist's notation throughout — `align`, `\partial`, `\nabla`, operators, Dirac/index
  notation. Every section ends naming its **ceiling** (the four tags above) so liberality stays honest.

## Guard task for Podo (next handoff)
1. Verify each effect's **ceiling tag** against its `Experiment1.lean` `claim.tag` (the survey inferred a few
   — confirm `ImpliedOrthogonality`, `PositronThreshold`, the label-only set).
2. Confirm the **device-coupled** set actually proves a ±1/holonomy/sign result against `Measurement`
   (Ep82–85) — these are the load-bearing chapters; flag any that are harness-only.
3. Confirm the math hooks are faithful to each description's Statement/Observation (flag drift).
4. NO `.tex` until guarded + the operator green-lights.

## Open (operator)
- Title/series: **Volume 2 — Experimentation: An Applied Physics** (confirmed). Home: `books/experimentation/`.
- Disclosure: this is applied physics — names physics freely; the ceiling is the only fence. (Confirm: is
  there any term to avoid, or is the vocabulary fully open?)
- Front matter / part-openers: deferred unless you say otherwise (as in Vol 1/3).
