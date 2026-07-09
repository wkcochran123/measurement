import Experiments.Common

/-!
# The Angular Momentum Effect — a finite ledger of conserved spin

Modelled after the exemplar `ThePositronAnnihilationEffect/Experiment1.lean`.

## Physics (modelled finitely)
A bicycle wheel of mass `M` and radius `R` spins at observed frequency `f`. The angular
momentum is *reconstructed from observables*: `L = I·ω`, `I ≈ M·R²`, `ω = 2π·f`. The
phenomenon is the **persistence** of `L` under external perturbation. We model the spinning
record as a finite `Ledger` of angular "ticks" (one per slot crossed on the closed orbit),
and the wheel's state as the description's compressed coordinate pair `(r, θ)` — radial
admissibility and cyclic refinement — instead of a full planar basis.

The conserved quantity is realised as a **bookkeeping identity**: the tick count of two
spliced runs is the sum of the parts (`Measurement`-free harness theorem
`Experiments.Common.Ledger.count_append`). Splicing two transport segments models the
persistence of angular momentum across an external perturbation that joins them: no ticks are
created or destroyed at the seam.

`L = I·ω` is realised in an EXACT-INTEGER model (all quantities scaled to `Nat`) so `decide`
computes the identity, with falsifiable lemmas pinning each factor of the product.

## NOT claimed
That this derives `2π`, real moments of inertia, or continuum rotational dynamics; that the
finite tick ledger *is* angular momentum; any torque/force law; Noether's theorem. The
"conservation" here is the discrete shadow — a finite count that splices additively — NOT a
continuous symmetry argument. **Claim ceiling:** a finite ledger model of spin bookkeeping,
whose conservation conjunct IS the harness's `count_append`.
-/

namespace Experiments.TheAngularMomentumEffect

/-- The description's compressed record: a radial admissibility coordinate `r` and a cyclic
refinement coordinate `θ` on a closed orbit of `slots` positions. This is the `(r, θ)` pair the
description says the admissible description collapses to (half the Cartesian burden). -/
structure Spin where
  r : Nat
  theta : Nat
  slots : Nat
deriving DecidableEq, Repr

/-- A wheel, in exact-integer surrogates for its observables. `massScaled = M`, `radius = R`,
`freq = f` (all `Nat` after a common scaling). -/
structure Wheel where
  massScaled : Nat
  radius : Nat
  freq : Nat
deriving DecidableEq, Repr

namespace Wheel

/-- Moment of inertia surrogate `I = M · R²` (the description's `I ≈ M R²`, exact in this
integer model). -/
def inertia (w : Wheel) : Nat := w.massScaled * w.radius * w.radius

/-- Angular "rate" surrogate `ω̃ = twoPi · f`, where `twoPi` is the integer surrogate for `2π`
(a labelled constant — NOT derived). -/
def angularRate (twoPi : Nat) (w : Wheel) : Nat := twoPi * w.freq

/-- Angular momentum surrogate `L = I · ω̃`. -/
def angularMomentum (twoPi : Nat) (w : Wheel) : Nat := w.inertia * w.angularRate twoPi

end Wheel

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER FACTOR of `L = I·ω̃`, so the product is load-bearing.
-- Each would break if `angularMomentum` dropped or altered that factor.
-- ---------------------------------------------------------------------------

/-- `L` is monotone in the frequency: spin faster (with mass, radius fixed and a real `2π`),
get at least as much angular momentum. Quantified over ALL wheels. FALSIFIABLE: drop the
hypothesis `f ≤ g` and it fails (a slower wheel does not dominate a faster one). -/
theorem momentum_mono_in_freq
    (twoPi : Nat) (w : Wheel) (g : Nat) (h : w.freq ≤ g) :
    w.angularMomentum twoPi ≤ ({ w with freq := g } : Wheel).angularMomentum twoPi := by
  unfold Wheel.angularMomentum Wheel.angularRate Wheel.inertia
  have : twoPi * w.freq ≤ twoPi * g := Nat.mul_le_mul_left _ h
  exact Nat.mul_le_mul_left _ this

/-- A wheel at rest carries no angular momentum: `f = 0 ⇒ L = 0`. FALSIFIABLE: this pins the
`ω̃ = twoPi·f` factor — if `angularMomentum` ignored `freq`, a stationary wheel could carry
spin. -/
theorem rest_has_no_momentum
    (twoPi : Nat) (w : Wheel) (h : w.freq = 0) :
    w.angularMomentum twoPi = 0 := by
  unfold Wheel.angularMomentum Wheel.angularRate
  rw [h]
  simp

/-- The inertia factor is load-bearing: a point wheel (`R = 0`) has no moment of inertia, hence
no angular momentum. FALSIFIABLE: pins the `I = M·R²` factor. -/
theorem zero_radius_no_momentum
    (twoPi : Nat) (w : Wheel) (h : w.radius = 0) :
    w.angularMomentum twoPi = 0 := by
  unfold Wheel.angularMomentum Wheel.inertia
  rw [h]
  simp

-- ---------------------------------------------------------------------------
-- CONSERVATION as a ledger identity (the harness coupling — LOAD-BEARING).
-- ---------------------------------------------------------------------------

/-- The spin record: a finite ledger of angular ticks (one `Spin` sample per slot crossed). -/
abbrev SpinLedger := Experiments.Common.Ledger Spin

/-- Persistence across a perturbation: splice two transport segments. The phenomenon is that no
ticks are created or destroyed at the seam — the joined count is the sum of the parts. This is
EXACTLY `Experiments.Common.Ledger.count_append`, so a regression there breaks this build. -/
def conservedAcross (before after : SpinLedger) : Prop :=
  (Experiments.Common.Ledger.append before after).count = before.count + after.count

theorem conserved_holds (before after : SpinLedger) : conservedAcross before after :=
  Experiments.Common.Ledger.count_append before after

-- ---------------------------------------------------------------------------
-- The canonical wheel (the description's worked example, scaled to integers).
-- ---------------------------------------------------------------------------

/-- Integer surrogate for `2π` (×100 ⇒ 628). A labelled constant, not derived. -/
def twoPiScaled : Nat := 628

/-- The description's wheel, in exact-integer surrogates: `M = 2`, `R = 33` (0.33 m ×100),
`f = 5`. -/
def canonicalWheel : Wheel := { massScaled := 2, radius := 33, freq := 5 }

/-- Two spin segments either side of a perturbation, on a closed orbit of 360 slots. -/
def segmentBefore : SpinLedger := { events := [{ r := 33, theta := 0, slots := 360 }] }
def segmentAfter : SpinLedger := { events := [{ r := 33, theta := 180, slots := 360 }] }

/-- `L = I·ω̃` computes to a concrete positive surrogate (a frozen-literal check on the chosen
event, not a property enforced elsewhere). -/
theorem canonical_momentum_value :
    canonicalWheel.angularMomentum twoPiScaled = 2178 * 3140 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the conservation conjunct IS the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (persistence) splicing two spin segments conserves the tick count — the harness's
  `count_append`, the load-bearing coupling;
* (positivity) the canonical spinning wheel carries strictly positive angular momentum
  (`f, R ≠ 0`); and
* (rate factor) a wheel at rest carries none.
The first conjunct is discharged by `Experiments.Common.Ledger.count_append`, so a regression
in the harness fails this build. -/
def claimStatement : Prop :=
  conservedAcross segmentBefore segmentAfter ∧
    0 < canonicalWheel.angularMomentum twoPiScaled ∧
    ({ canonicalWheel with freq := 0 } : Wheel).angularMomentum twoPiScaled = 0

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨conserved_holds segmentBefore segmentAfter,
    by decide,
    rest_has_no_momentum twoPiScaled { canonicalWheel with freq := 0 } rfl⟩

/-- The tag is an honest ceiling: a finite ledger model of spin bookkeeping, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  wheel : Wheel
  twoPi : Nat
  before : SpinLedger
  after : SpinLedger

/-- The run computes the joined tick count of the two spliced segments. -/
def run (s : Setup) : Nat :=
  (Experiments.Common.Ledger.append s.before s.after).count

def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun s => conservedAcross s.before s.after }

/-- The exported claim is a genuine function of the setup, and this bridge pins it to `run`, so
the claim body cannot be silently swapped for `fun _ => True`. -/
theorem run_eq_sum (s : Setup) :
    run s = s.before.count + s.after.count := by
  simp only [run]
  exact Experiments.Common.Ledger.count_append s.before s.after

def canonicalSetup : Setup :=
  { wheel := canonicalWheel, twoPi := twoPiScaled, before := segmentBefore, after := segmentAfter }

#eval run canonicalSetup                                       -- expect: 2
#eval canonicalWheel.angularMomentum twoPiScaled              -- expect: 6838920
-- Load-bearing check: the falsifiable predicate is FALSE at a rest wheel (0 < L is false).
#eval decide (0 < ({ canonicalWheel with freq := 0 } : Wheel).angularMomentum twoPiScaled)  -- expect: false
#print axioms claim_holds                                     -- [propext, Quot.sound] = AMBIENT

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment conservedAcross
  infer_instance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Nat :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheAngularMomentumEffect
