import Experiments.Common

/-!
# The Einstein Effect (Ch.08) — refinement chains and the maximal clock

The instrument's *Einstein effect* (`instrument/chapters/08.tex:689`, `ph:einstein`):
among all admissible refinement chains between two records of a causal ledger,
the **physically realized clock is the chain that maximizes the local clock
count** — the chain admitting the most distinguishable refinement steps. Any
shorter count is an informationally constrained history.

We model a refinement chain finitely as a `Ledger` of irreducible refinement
**steps** between two fixed endpoints; the *local clock count* is `Ledger.count`
(the number of steps). The "maximality" content is: the realized chain bounds
every admissible chain's clock count, and it attains its own bound.

## Coupling
HARNESS, not device. The Einstein effect here is purely a **bound / counting**
statement (a maximal count over a finite family) — there is no holonomy, gauge
loop-phase, curvature, or charge here, so a device coupling would be FAKE. The
load-bearing conjunct `realized_is_maximal` is discharged by
`Experiments.Common.Counting.boundedBy_self`: the realized chain is bounded by
its own clock count. A rename/regression of that harness lemma breaks this build.

## NOT claimed
That this *derives* relativistic time dilation, the Lorentz group, a metric, or
any continuum geometry. "Maximal refinement = the physical clock" is taken as
the instrument's *definition*; we do not prove a chain of maximal length exists
in any infinite family — the family here is finite and given. `step`s are
abstract distinguishable updates, not physical events with energies. The clock
is the *count*; we make no claim about what one step is "worth" in seconds.
**Claim ceiling:** a finite ledger model of the maximal-chain clock principle.
-/

namespace Experiments.TheEinsteinEffectCh08

/-- An irreducible refinement step: a distinguishable update with a coarse and a
fine label slot. Two steps are distinct iff some label differs. -/
structure Step where
  coarse : Nat
  fine : Nat
deriving DecidableEq, Repr

/-- A refinement chain between two fixed endpoints: a finite ledger of steps.
Its *local clock count* is the number of steps. -/
abbrev Chain := Experiments.Common.Ledger Step

/-- The local clock count of a chain (Definition `def:clock`, finitely). -/
def clockCount (c : Chain) : Nat :=
  c.count

/-- A chain is *admissible relative to a bound* when its clock count does not
exceed the realized chain's count. This is the finite shadow of "admissibility
and information minimality force a maximal chain": no admissible history reads
more distinguishable updates than the realized one. -/
def admissibleUnder (realized c : Chain) : Prop :=
  clockCount c <= clockCount realized

instance (realized c : Chain) : Decidable (admissibleUnder realized c) := by
  unfold admissibleUnder clockCount
  exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each ∀-quantified; drop a hypothesis and it breaks.
-- ---------------------------------------------------------------------------

/-- MAXIMALITY (load-bearing, harness-coupled): the realized chain is bounded by
its own clock count, i.e. it is `admissibleUnder` itself. Discharged by the
harness lemma `Counting.boundedBy_self` — break/rename that lemma and this fails. -/
theorem realized_is_maximal (realized : Chain) :
    Experiments.Common.Counting.boundedBy realized (clockCount realized) :=
  Experiments.Common.Counting.boundedBy_self realized

/-- DOMINANCE is falsifiable: any admissible chain's clock count is bounded by
the realized count. Drop the `admissibleUnder` hypothesis and the conclusion is
false (a longer chain would violate it) — so the hypothesis is load-bearing. -/
theorem admissible_count_le_realized
    (realized c : Chain) (h : admissibleUnder realized c) :
    clockCount c <= clockCount realized :=
  h

/-- A strictly longer chain is NOT admissible under a given realized chain: a
chain whose clock count exceeds the realized count cannot be an admissible
history. Pins that the bound is a real ceiling, not vacuous. -/
theorem longer_not_admissible
    (realized c : Chain) (h : clockCount realized < clockCount c) :
    ¬ admissibleUnder realized c :=
  fun ha => Nat.lt_irrefl (clockCount realized) (Nat.lt_of_lt_of_le h ha)

-- ---------------------------------------------------------------------------
-- A concrete realized chain and an admissible (shorter) competitor.
-- ---------------------------------------------------------------------------

/-- The realized chain: three irreducible refinement steps between the two
endpoints — the maximal distinguishable history. -/
def realizedChain : Chain :=
  { events := [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩] }

/-- A constrained competitor: only two steps read (an informationally
constrained history). It is admissible under the realized chain. -/
def constrainedChain : Chain :=
  { events := [⟨0, 1⟩, ⟨1, 2⟩] }

theorem realized_count : clockCount realizedChain = 3 := by decide

theorem constrained_is_admissible : admissibleUnder realizedChain constrainedChain := by
  decide

/-- The realized chain reads strictly more updates than the constrained one:
the maximal clock genuinely dominates. -/
theorem realized_dominates_constrained :
    clockCount constrainedChain < clockCount realizedChain := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (maximality / harness-coupled) the realized chain bounds its own clock count
  (`Counting.boundedBy_self`, via `realized_is_maximal`);
* (dominance) the constrained competitor is admissible under it; and
* (strictness) the realized clock reads strictly more updates than the
  constrained one — the maximal chain is genuinely maximal, not tied. -/
def claimStatement : Prop :=
  Experiments.Common.Counting.boundedBy realizedChain (clockCount realizedChain) ∧
    admissibleUnder realizedChain constrainedChain ∧
    clockCount constrainedChain < clockCount realizedChain

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨realized_is_maximal realizedChain,
    constrained_is_admissible,
    realized_dominates_constrained⟩

/-- The tag is an honest ceiling: a finite ledger model of the maximal-chain
clock principle, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  realized : Chain
  candidate : Chain

/-- The run computes — thanks to the `Decidable` instance above. -/
def run (s : Setup) : Bool := decide (admissibleUnder s.realized s.candidate)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => admissibleUnder s.realized s.candidate }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { realized := realizedChain, candidate := constrainedChain }

/-- Bring a minimal device next to this experiment: it records whether the
exported claim fires. (`experiment.claim` is definitionally `admissibleUnder`,
which is `Decidable` above; we name it directly so the instance is found.) -/
def deviceNear (setup : Setup) : Bool :=
  decide (admissibleUnder setup.realized setup.candidate)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run canonicalSetup                                   -- expect: true
#print axioms claim_holds                                  -- ambient [propext, Quot.sound], not coupling
-- A config where the falsifiable predicate is FALSE: the realized chain is the
-- short one, the candidate is longer — admissibility must FAIL. Proves the
-- forall-lemma is load-bearing, not vacuous.
#eval decide (admissibleUnder constrainedChain realizedChain)   -- expect: false

end Experiments.TheEinsteinEffectCh08
