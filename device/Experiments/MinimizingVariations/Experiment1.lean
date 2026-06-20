import Experiments.Common

/-!
# Minimizing Variations — a finite-ledger model of the first variation

Source: `instrument/chapters/06.tex:714` — the Euler–Lagrange derivation. Built to the EXEMPLAR
shape (`ThePositronAnnihilationEffect/Experiment1.lean`):

1. an **effect-specific domain** (`Node`, `Perturbation`, `Interval`) — NOT the 3-`Nat`
   `CountSetup`;
2. genuinely **falsifiable** `∀`-quantified lemmas — each breaks if a hypothesis is dropped
   (e.g. `admissible_boundary_vanishes` needs `η(a)=η(b)=0`; drop it and the boundary term
   survives);
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** (`smoothShadowAnalogy`) + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` see through the richer predicates;
6. it **couples to the harness**: the additivity conjunct of `claim_holds` is discharged by the
   harness theorem `Experiments.Common.Ledger.count_append` — the discrete shadow of the integral's
   additivity `∫_a^b = ∫_a^c + ∫_c^b`. A `sorry`/rename/regression in `Ledger.count_append`
   breaks *this* file's build.

## The mathematics (modelled finitely)
The first variation is
  δJ[x;η] = ∫_a^b ( f_x η + f_ẋ η̇ ) dt,
and integration by parts turns the second term into a **boundary term** `[f_ẋ η]_a^b` plus a bulk
term. For an *admissible* perturbation `η(a)=η(b)=0` the boundary term **vanishes**, leaving
  δJ[x;η] = ∫_a^b ( f_x − d/dt f_ẋ ) η dt.
We model `η` by its values on a finite grid; "admissible" means the two endpoint values are zero.
The discrete variation is a finite ledger of per-node contributions whose total is **additive** over
a split of the interval (the harness's `count_append` — the discrete `∫_a^b = ∫_a^c + ∫_c^b`). The
boundary contribution of an admissible perturbation is exactly zero, so the discrete first variation
reduces to its bulk (interior) part — the discrete shadow of "the boundary term drops".

## NOT claimed
That the continuum Euler–Lagrange equation is *derived* here; the fundamental lemma of the calculus
of variations; any actual derivative, integral, or limit; that a stationary point exists or is a
minimiser. `f_x`, `f_ẋ`, `d/dt` are NOT computed — only their finite bookkeeping *shape* is. The only
genuine variational content is additivity-of-the-integral and the vanishing of the boundary term for
endpoint-pinned perturbations, and additivity is the *harness's* own theorem, not a continuum result.
**Claim ceiling:** a finite ledger model of the first variation whose additivity conjunct is the
harness's own `count_append`.
-/

namespace Experiments.MinimizingVariations

/-- One grid node of the perturbation `η`: its index `t` and the integer value `eta` of `η` there.
(Values are `Int` so an endpoint pin `η = 0` is meaningful and a sign can flip.) -/
structure Node where
  t : Nat
  eta : Int
deriving DecidableEq, Repr

/-- A discrete perturbation `η` sampled on a grid: an ordered family of interior nodes together with
the two endpoint values `etaA = η(a)`, `etaB = η(b)`. The integral `∫ … η` is modelled as the finite
ledger of interior nodes; admissibility is the endpoint pin. -/
structure Perturbation where
  interior : Experiments.Common.Ledger Node
  etaA : Int
  etaB : Int

namespace Perturbation

/-- `η` is **admissible** iff it is pinned at both endpoints: `η(a) = η(b) = 0`. This is the
hypothesis that makes the boundary term vanish under integration by parts. -/
def admissible (p : Perturbation) : Prop :=
  p.etaA = 0 ∧ p.etaB = 0

/-- The discrete **boundary term** `[f_ẋ η]_a^b` of integration by parts, modelled (with the slope
factors normalised to 1) as `η(b) − η(a)`. For an admissible perturbation this is `0`. -/
def boundaryTerm (p : Perturbation) : Int :=
  p.etaB - p.etaA

/-- The **bulk count** of the variation: how many interior nodes the integral `∫ … η` runs over. -/
def bulkCount (p : Perturbation) : Nat :=
  p.interior.count

-- Make the predicate DECIDABLE so `decide`/`#eval` see through it.
instance (p : Perturbation) : Decidable p.admissible := by
  unfold admissible; exact inferInstance

end Perturbation

/-- A finite **interval split** at an interior cut: the variation's interior ledger is partitioned
into a left part and a right part, modelling `∫_a^b = ∫_a^c + ∫_c^b`. -/
structure IntervalSplit where
  left : Experiments.Common.Ledger Node
  right : Experiments.Common.Ledger Node

namespace IntervalSplit

/-- The whole interior ledger reassembled from the split (the discrete `∫_a^b`). -/
def whole (s : IntervalSplit) : Experiments.Common.Ledger Node :=
  Experiments.Common.Ledger.append s.left s.right

/-- **Additivity of the variation over a split**: the bulk count of the whole interval equals the
sum of the two sub-interval bulk counts. This is the discrete `∫_a^b = ∫_a^c + ∫_c^b`. -/
def additive (s : IntervalSplit) : Prop :=
  s.whole.count = s.left.count + s.right.count

instance (s : IntervalSplit) : Decidable s.additive := by
  unfold additive whole; exact inferInstance

end IntervalSplit

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each pins a hypothesis of the variational bookkeeping.
-- ---------------------------------------------------------------------------

/-- **Admissible ⇒ the boundary term vanishes.** Quantified over ALL perturbations. Would FAIL if
`admissible` dropped either endpoint clause: with `η(a) ≠ 0` or `η(b) ≠ 0` the boundary term
`η(b) − η(a)` need not be zero. This is "the boundary term drops because `η(a)=η(b)=0`". -/
theorem admissible_boundary_vanishes (p : Perturbation) (h : p.admissible) :
    p.boundaryTerm = 0 := by
  unfold Perturbation.boundaryTerm
  rw [h.1, h.2]; rfl

/-- **A non-vanishing endpoint leaves a surviving boundary term.** Quantified over ALL
perturbations with `η(b) ≠ η(a)`. Would FAIL if `boundaryTerm` ignored the endpoints. This is the
contrapositive witness that the admissibility hypothesis is load-bearing. -/
theorem unpinned_boundary_survives (p : Perturbation) (h : p.etaB ≠ p.etaA) :
    p.boundaryTerm ≠ 0 := by
  unfold Perturbation.boundaryTerm
  intro hzero
  apply h
  omega

/-- **The variation is additive over any interval split** — the continuity-of-the-integral conjunct,
true for EVERY split, discharged by the harness's `count_append`. This is the load-bearing harness
coupling: a regression in `Ledger.count_append` fails this build. Quantified over ALL splits. -/
theorem variation_additive (s : IntervalSplit) : s.additive := by
  unfold IntervalSplit.additive IntervalSplit.whole
  rw [Experiments.Common.Ledger.count_append]

-- ---------------------------------------------------------------------------
-- The canonical admissible perturbation.
-- ---------------------------------------------------------------------------

/-- A canonical admissible perturbation: three interior nodes with a little bump, pinned to `0` at
both endpoints. -/
def bumpPerturbation : Perturbation :=
  { interior := { events := [{ t := 1, eta := 2 }, { t := 2, eta := 3 }, { t := 3, eta := 1 }] }
    etaA := 0
    etaB := 0 }

/-- The canonical perturbation is admissible (concrete, via the `Decidable` instance). -/
theorem bump_admissible : bumpPerturbation.admissible := by decide

/-- Its boundary term vanishes (concrete witness of the falsifiable lemma). -/
theorem bump_boundary_vanishes : bumpPerturbation.boundaryTerm = 0 :=
  admissible_boundary_vanishes bumpPerturbation bump_admissible

/-- A canonical split of the bump's interior into `[node1]` and `[node2, node3]`. -/
def bumpSplit : IntervalSplit :=
  { left := { events := [{ t := 1, eta := 2 }] }
    right := { events := [{ t := 2, eta := 3 }, { t := 3, eta := 1 }] } }

/-- The canonical split is additive (concrete, via the `Decidable` instance). -/
theorem bump_split_additive : bumpSplit.additive := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the additivity conjunct is the harness's theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (admissible) the canonical perturbation is pinned at both endpoints — proved here;
* (boundary term drops) every admissible perturbation has a vanishing boundary term —
  the falsifiable lemma `admissible_boundary_vanishes`, the discrete "`[f_ẋ η]_a^b = 0`"; and
* (additivity, ALL splits) the variation is additive over any interval split — discharged by the
  harness's `count_append` (`variation_additive`), the discrete `∫_a^b = ∫_a^c + ∫_c^b`.
The last conjunct is the genuine variational content and is the harness's own additivity law, so a
regression in `Ledger.count_append` fails this build. -/
def claimStatement : Prop :=
  bumpPerturbation.admissible ∧
    (∀ p : Perturbation, p.admissible → p.boundaryTerm = 0) ∧
    (∀ s : IntervalSplit, s.additive)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨bump_admissible, admissible_boundary_vanishes, variation_additive⟩

/-- The tag is an honest ceiling: a finite stand-in for a continuum (smooth) phenomenon. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  perturbation : Perturbation

/-- The run actually computes — thanks to the `Decidable` instance on `admissible`. -/
def run (s : Setup) : Bool := decide s.perturbation.admissible

/-- The exported claim is a genuine function of the setup, pinned to `run` by `run_iff_claim`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.perturbation.admissible }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { perturbation := bumpPerturbation }

/-- A non-admissible perturbation: the right endpoint is NOT pinned. -/
def unpinnedPerturbation : Perturbation :=
  { interior := { events := [{ t := 1, eta := 2 }] }, etaA := 0, etaB := 5 }

#eval run canonicalSetup                                       -- expect: true  (admissible)
#print axioms claim_holds                                      -- ambient footprint, not the coupling
#eval decide (unpinnedPerturbation.admissible)                 -- expect: false (right endpoint unpinned)

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.MinimizingVariations
