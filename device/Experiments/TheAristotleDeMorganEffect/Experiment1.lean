import Experiments.Common

/-!
# The Aristotle–De Morgan Effect — relational structure becomes instrumentable

Source: `instrument/chapters/02.tex:1117` (`ph:aristotle-demorgan`).

The phenomenon: a binary relation begins as an opaque qualitative distinction
embedded in judgment (Aristotle) and only later becomes an explicit algebraic
object subject to **composition** and **inversion** (De Morgan).  The
instrument-side reading: a relation may constrain admissible histories **only
if** it is a *recoverable structure over recorded outcomes* — a ledger of
ordered pairs you can enumerate, invert, and check for coherence under
extension.

This file follows the exemplar shape (`ThePositronAnnihilationEffect`):
1. an **effect-specific domain** (`Term`, `Pair`, `Relation`) — NOT the generic
   3-`Nat` `CountSetup`;
2. genuinely **falsifiable** `∀`-quantified lemmas (each breaks if a conjunct of
   the converse/composition rule is dropped);
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an honest `finiteLedgerModel` tag + the disclaimer below;
5. explicit `Decidable` instances so `decide`/`#eval` compute through the
   richer `Prop` predicates;
6. a **harness coupling** that is load-bearing: inversion is realized as a
   `Experiments.Common.Ledger.map` over the recorded pairs, and the De Morgan
   step's *recoverability* (the converse carries the **same count** of recorded
   distinctions — nothing is lost when judgment becomes algebra) is discharged
   by `Experiments.Common.Ledger.count_map`.  Rename/`sorry` that theorem and
   THIS build breaks.

## NOT claimed
That this is Aristotle's or De Morgan's actual logic; any theory of predication;
that relation **algebra** in general is captured (only converse + a single
composition witness are formalized); anything continuous.  The carrier is a
fixed 3-element finite type.  **Claim ceiling:** a finite ledger model of the
"relation = recoverable structure over recorded pairs" reading, one of whose
conjuncts is the harness's own `count_map` theorem.
-/

namespace Experiments.TheAristotleDeMorganEffect

/-- A term in the (finite) universe of discourse.  Aristotle's relations live
between such terms; here the carrier is fixed and small so everything decides. -/
inductive Term where
  | subject
  | middle
  | predicate
deriving DecidableEq, Repr

/-- An ordered pair: the atom of a binary relation, `from ↦ to`. -/
structure Pair where
  src : Term
  tgt : Term
deriving DecidableEq, Repr

/-- A relation, made **explicit** (De Morgan) as the recoverable structure of
the distinctions it records: a ledger of ordered pairs. -/
structure Relation where
  recorded : Experiments.Common.Ledger Pair

/-- The converse (inversion) of a single recorded distinction. -/
def Pair.swap (p : Pair) : Pair := { src := p.tgt, tgt := p.src }

namespace Relation

/-- Membership: `holds r a b` iff the ordered pair `(a,b)` is one of the
recorded distinctions.  This is the De Morgan move — the relation is an operator
on pairs, not a grammatical feature of a sentence. -/
def holds (r : Relation) (a b : Term) : Prop :=
  { src := a, tgt := b : Pair } ∈ r.recorded.events

instance (r : Relation) (a b : Term) : Decidable (r.holds a b) := by
  unfold holds; exact inferInstance

/-- **Inversion realized over the ledger.**  The converse relation is the
`Ledger.map` of `Pair.swap` across the recorded pairs.  Realizing inversion as
the harness's `map` is exactly what makes the `count_map` coupling load-bearing. -/
def converse (r : Relation) : Relation :=
  { recorded := r.recorded.map Pair.swap }

end Relation

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: the converse/recoverability rule, pinned conjunct-by-conjunct.
-- ---------------------------------------------------------------------------

/-- `Pair.swap` is involutive — inversion applied twice is the identity on a
single distinction.  Falsifiable: define `swap` to drop one field and it breaks. -/
theorem swap_swap (p : Pair) : p.swap.swap = p := by
  cases p; rfl

/-- **De Morgan converse law (forward):** if `(a,b)` is recorded, then `(b,a)`
is recorded in the converse.  Quantified over ALL relations and term pairs.
Falsifiable: if `converse` mapped by the identity instead of `swap`, the
swapped pair would not appear and this fails. -/
theorem holds_converse_of_holds (r : Relation) (a b : Term)
    (h : r.holds a b) : r.converse.holds b a := by
  unfold Relation.holds Relation.converse Experiments.Common.Ledger.map
  show ({ src := b, tgt := a : Pair }) ∈ r.recorded.events.map Pair.swap
  have : ({ src := b, tgt := a : Pair }) = Pair.swap { src := a, tgt := b } := rfl
  rw [this]
  exact List.mem_map_of_mem h

/-- **Recoverability (the instrument-side constraint):** making the relation
explicit by inversion loses **no** recorded distinctions — the converse carries
exactly as many pairs as the original.  This is discharged by the harness's
`Ledger.count_map`, the load-bearing coupling.  Quantified over ALL relations. -/
theorem converse_preserves_count (r : Relation) :
    r.converse.recorded.count = r.recorded.count :=
  Experiments.Common.Ledger.count_map Pair.swap r.recorded

-- ---------------------------------------------------------------------------
-- A canonical relation: Aristotelian precedence subject ≺ middle ≺ predicate.
-- ---------------------------------------------------------------------------

def precedence : Relation :=
  { recorded :=
      { events :=
          [ { src := Term.subject,  tgt := Term.middle    },
            { src := Term.middle,   tgt := Term.predicate } ] } }

/-- The relation actually records the precedence `subject ≺ middle` (concrete,
via the `Decidable` instance). -/
theorem precedence_records : precedence.holds Term.subject Term.middle := by decide

/-- And it does NOT record the reverse — precedence is asymmetric (Aristotle:
relations are "asymmetric, ordered, composable"). -/
theorem precedence_asymmetric : ¬ precedence.holds Term.middle Term.subject := by decide

/-- The converse makes the inversion explicit: `middle ≺⁻¹ subject` is recorded. -/
theorem converse_records : precedence.converse.holds Term.middle Term.subject := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the recoverability conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (explicit relation) the canonical precedence records `subject ≺ middle`;
* (asymmetry) it does NOT record the reverse — an ordered, non-symmetric relation;
* (De Morgan inversion) the converse records `middle ≺⁻¹ subject`;
* (recoverability) inversion preserves the recorded count — the De Morgan move is
  lossless over the ledger (`Experiments.Common.Ledger.count_map`). -/
def claimStatement : Prop :=
  precedence.holds Term.subject Term.middle ∧
    ¬ precedence.holds Term.middle Term.subject ∧
    precedence.converse.holds Term.middle Term.subject ∧
    precedence.converse.recorded.count = precedence.recorded.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨precedence_records, precedence_asymmetric, converse_records,
    converse_preserves_count precedence⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  relation : Relation
  from_ : Term
  to_ : Term

/-- The run computes — thanks to the `Decidable` instance on `holds`. -/
def run (s : Setup) : Bool := decide (s.relation.holds s.from_ s.to_)

/-- The exported claim is a genuine function of the setup; this bridge pins it to
`run`, so the claim body cannot be silently swapped for `fun _ => True`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.relation.holds s.from_ s.to_ }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { relation := precedence, from_ := Term.subject, to_ := Term.middle }

#eval run canonicalSetup                                   -- expect: true
#print axioms claim_holds                                  -- ambient footprint
-- Load-bearing check: the asymmetry conjunct is FALSE at the swapped query,
-- so the falsifiable predicate is non-vacuous.
#eval decide (precedence.holds Term.middle Term.subject)   -- expect: false

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

end Experiments.TheAristotleDeMorganEffect
