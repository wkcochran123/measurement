import Experiments.Common

/-!
# The Fourier-Nyquist Effect — rebuilt to the EXEMPLAR shape

Source: `instrument/chapters/02.tex:977` (`ph:sampling`).

## Physics (modelled finitely)
Decomposition of a measured record into orthogonal components is *exact* — i.e. every
resolved component can be *recovered* from the ledger — **iff** the ledger commits
distinctions densely enough to support inversion (the Nyquist condition). A band-limited
record with `bandwidth` distinct components is recoverable exactly when the sample rate the
ledger commits is at least the Nyquist rate `2 * bandwidth`. Below that, refinement is too
sparse: the decomposition ceases to be exact and recoverability is lost (aliasing).

We model a `Spectrum` (a finite list of component bins, each carrying a sampled amplitude)
together with a `Sampler` (the rate the ledger commits and the bandwidth it must resolve).
The number of components that can be *recovered* is bounded by the number of distinctions the
ledger actually commits — this bound is the harness's `Counting.boundedBy`, and it is a
load-bearing conjunct of the claim.

## NOT claimed
This is NOT the Fourier transform, the Shannon-Nyquist sampling theorem, or any statement
about continuous band-limited functions. There is no integral, no sinc interpolation, no
spectral density. `2 * bandwidth` is a *labelled* finite threshold standing in for the Nyquist
rate, not derived from any continuous limit. We do not claim exact reconstruction of any real
signal — only the finite *bookkeeping* of "recovered components ≤ committed distinctions" and
the discrete shadow of the Nyquist admissibility gate. **Claim ceiling:** a finite ledger /
shadow model of the recoverability gate, one of whose conjuncts is the harness's own counting
bound.
-/

namespace Experiments.TheFourierNyquistEffect

/-- One resolved component: which orthogonal bin it sits in, and its sampled amplitude. -/
structure Component where
  bin : Nat
  amplitude : Nat
deriving DecidableEq, Repr

/-- A finite spectrum: the components a decomposition resolved from one sensor response. -/
abbrev Spectrum := List Component

/-- The apparatus: the bandwidth it must resolve and the sample rate the ledger commits. -/
structure Sampler where
  bandwidth : Nat
  sampleRate : Nat
deriving DecidableEq, Repr

/-- The standard apparatus: a 3-component band sampled at the Nyquist rate (6 = 2*3). -/
def defaultSampler : Sampler := { bandwidth := 3, sampleRate := 6 }

namespace Sampler

/-- The Nyquist gate: refinement is sufficient iff the committed sample rate reaches the
Nyquist rate `2 * bandwidth`. This is the recoverability condition. -/
def refinementSufficient (s : Sampler) : Prop :=
  2 * s.bandwidth ≤ s.sampleRate

/-- THE RECOVERY RULE: a decomposition of `spectrum` is *exact* (every component recoverable)
iff the refinement is sufficient AND the ledger committed at least one distinction per resolved
component (`spectrum.length ≤ sampleRate`). Both conjuncts are required; each is pinned by a
falsifiable lemma below. -/
def recoverable (s : Sampler) (spectrum : Spectrum) : Prop :=
  s.refinementSufficient ∧ spectrum.length ≤ s.sampleRate

-- Make the predicates DECIDABLE so `decide`/`#eval` compute through them.
instance (s : Sampler) : Decidable s.refinementSufficient := by
  unfold refinementSufficient; exact inferInstance
instance (s : Sampler) (spectrum : Spectrum) : Decidable (s.recoverable spectrum) := by
  unfold recoverable; exact inferInstance

end Sampler

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER CONJUNCT, so the whole rule is load-bearing.
-- Drop either conjunct from `recoverable` and the matching lemma fails to build.
-- ---------------------------------------------------------------------------

/-- The Nyquist gate is NECESSARY: if refinement is insufficient (below the Nyquist rate),
no decomposition is recoverable, for ANY sampler and ANY spectrum. Drop the first conjunct
of `recoverable` and this breaks. -/
theorem subNyquist_not_recoverable
    (s : Sampler) (spectrum : Spectrum) (h : ¬ s.refinementSufficient) :
    ¬ s.recoverable spectrum :=
  fun hr => h hr.1

/-- Density is NECESSARY: if the ledger committed fewer distinctions than there are resolved
components, recovery is lost, for ANY sampler and ANY spectrum. Drop the second conjunct of
`recoverable` and this breaks. -/
theorem tooSparse_not_recoverable
    (s : Sampler) (spectrum : Spectrum) (h : ¬ spectrum.length ≤ s.sampleRate) :
    ¬ s.recoverable spectrum :=
  fun hr => h hr.2

-- ---------------------------------------------------------------------------
-- The canonical band-limited record.
-- ---------------------------------------------------------------------------

/-- A clean 3-component record (three orthogonal bins, distinct amplitudes). -/
def canonicalSpectrum : Spectrum :=
  [ { bin := 0, amplitude := 5 }
  , { bin := 1, amplitude := 9 }
  , { bin := 2, amplitude := 4 } ]

/-- At the Nyquist rate, the canonical record IS recoverable (concrete, via the instance). -/
theorem recoverable_canonical : defaultSampler.recoverable canonicalSpectrum := by decide

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING: the recovered components are bounded by the committed distinctions.
-- This is `Experiments.Common.Counting.boundedBy`, discharged by `boundedBy_of_eq`.
-- It is a LOAD-BEARING conjunct of `claim_holds`: a rename/regression of `boundedBy` /
-- `count` / `count_map` in the harness breaks THIS build.
-- ---------------------------------------------------------------------------

/-- The ledger of recovered components: exactly the resolved spectrum, recorded as events. -/
def recoveredLedger (spectrum : Spectrum) : Experiments.Common.Ledger Component :=
  { events := spectrum }

/-- The committed bound: the recovered ledger holds at most `length` distinctions. This is the
harness counting bound, instantiated at the canonical record. -/
theorem recovered_boundedBy_length :
    Experiments.Common.Counting.boundedBy
      (recoveredLedger canonicalSpectrum) canonicalSpectrum.length :=
  Experiments.Common.Counting.boundedBy_of_eq (by rfl)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; three conjuncts, one of which is the harness bound).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (recovery) the apparatus recovers the canonical record at the Nyquist rate — proved here;
* (Nyquist threshold) the committed rate reaches the Nyquist rate `2 * bandwidth` — proved here;
* (counting bound) the recovered components are bounded by the committed distinctions
  (`Experiments.Common.Counting.boundedBy` via `boundedBy_of_eq`) — the harness coupling.
The last conjunct reads the harness's own `count`/`boundedBy`, so a regression there fails
this build. -/
def claimStatement : Prop :=
  defaultSampler.recoverable canonicalSpectrum ∧
    2 * defaultSampler.bandwidth ≤ defaultSampler.sampleRate ∧
    Experiments.Common.Counting.boundedBy
      (recoveredLedger canonicalSpectrum) canonicalSpectrum.length

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨recoverable_canonical, by decide, recovered_boundedBy_length⟩

/-- The tag is an honest ceiling: a finite shadow of a continuous (Nyquist) phenomenon. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  sampler : Sampler
  spectrum : Spectrum

/-- The run actually computes — thanks to the `Decidable` instance above. -/
def run (s : Setup) : Bool := decide (s.sampler.recoverable s.spectrum)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`, so the
claim body cannot be silently swapped for `fun _ => True`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.sampler.recoverable s.spectrum }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { sampler := defaultSampler, spectrum := canonicalSpectrum }

/-- A sub-Nyquist control: same record, but the ledger commits only rate 4 < 6. -/
def aliasedSetup : Setup :=
  { sampler := { bandwidth := 3, sampleRate := 4 }, spectrum := canonicalSpectrum }

/-- The exported claim is decidable (it unfolds to the decidable `recoverable` predicate). -/
instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment; exact inferInstance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simpa [deviceNear] using run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run canonicalSetup        -- expect: true   (recoverable at the Nyquist rate)
#eval run aliasedSetup          -- expect: false  (sub-Nyquist: refinement insufficient)
#print axioms claim_holds       -- ambient [propext, Quot.sound], not coupling
-- Load-bearing witness: the falsifiable predicate evaluated where it is FALSE.
#eval decide (Sampler.refinementSufficient { bandwidth := 3, sampleRate := 4 })  -- expect: false

end Experiments.TheFourierNyquistEffect
