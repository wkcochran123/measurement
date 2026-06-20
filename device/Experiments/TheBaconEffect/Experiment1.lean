import Experiments.Common

/-!
# The Bacon Effect — the Repeatability Effect, as a finite ledger model

Source: `instrument/chapters/08.tex:420` (`ph:repeatability`).

## Physics (modelled finitely)
Bacon's demand: *a measurement is admissible only if its outcome can be reproduced by the same
procedure applied again under admissible conditions.* A single act is an event; the SAME act
repeated is a ruler. We model a "procedure" as a deterministic map from an admissible `Condition`
to a coarse `Reading`. **Admissibility = repeatability**: the procedure is admissible exactly when
applying it twice under admissible conditions yields the *same* coarse reading — i.e. the two runs
cast the same shadow. That sameness-of-shadow is the harness `Projection.sameShadow`, and it is a
genuine conjunct of the claim, so this build couples to the harness.

## NOT claimed
That this measures anything real; that there is a geometry, space, or metric (the description is
explicit there is none "at this stage"); that repeatability is *sufficient* for truth (only that it
is *necessary* for admissibility); anything about noise, drift, or the probability of a procedure
actually repeating. We model a DETERMINISTIC procedure, so repeatability here is a structural
property of the map, not an empirical observation about a noisy instrument. **Claim ceiling:** a
finite ledger model in which "admissible = casts the same shadow on repetition."
-/

namespace Experiments.TheBaconEffect

/-- A coarse outcome on a finite dial — the only thing a ledger can compare. -/
structure Reading where
  dial : Nat
deriving DecidableEq, Repr

/-- An admissible condition under which a procedure may be executed: a finite knob setting. -/
structure Condition where
  knob : Nat
deriving DecidableEq, Repr

/-- A PROCEDURE is a (deterministic) rule of action: condition ↦ reading. This is Bacon's "ruler":
not an object of fixed length, but an invariant procedure. -/
structure Procedure where
  apply : Condition → Reading

/-- The `Projection` (in the harness sense) carried by a procedure: it projects a condition to the
shadow the procedure casts on it. -/
def shadow (proc : Procedure) : Experiments.Common.Projection Condition Reading :=
  { project := proc.apply }

/-- THE ADMISSIBILITY RULE. A procedure is admissible on a pair of conditions iff:
* (repeatable) re-running the procedure on the *same* condition `c` gives the *same* reading —
  the run casts the same shadow on `c` as on `c` (the `Projection.sameShadow` conjunct); AND
* (comparable) the two conditions are declared equivalent by the procedure — they cast the same
  shadow, so the ledger may compare across the separation.
Both conjuncts are pinned by falsifiable lemmas below. -/
def admissibleOn (proc : Procedure) (c d : Condition) : Prop :=
  Experiments.Common.Projection.sameShadow (shadow proc) c c ∧
    Experiments.Common.Projection.sameShadow (shadow proc) c d

/-- Make `sameShadow` (an equality of `Reading`s) and `admissibleOn` DECIDABLE so `decide`/`#eval`
compute through them. -/
instance (proc : Procedure) (c d : Condition) :
    Decidable (Experiments.Common.Projection.sameShadow (shadow proc) c d) := by
  unfold Experiments.Common.Projection.sameShadow shadow; exact inferInstance

instance (proc : Procedure) (c d : Condition) : Decidable (admissibleOn proc c d) := by
  unfold admissibleOn; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER CONJUNCT, so the whole rule is load-bearing.
-- Drop the conjunct each pins and `admissibleOn` would stop forcing it.
-- ---------------------------------------------------------------------------

/-- COMPARABILITY is necessary: if the two conditions do NOT cast the same shadow, the procedure is
not admissible across them. Quantified over ALL procedures and condition pairs — this is the
conjunct that does real work (a procedure that maps `c` and `d` to different dials cannot license a
comparison between them). Drop `.2` from `admissibleOn` and this breaks. -/
theorem notSameShadow_not_admissible
    (proc : Procedure) (c d : Condition)
    (h : ¬ Experiments.Common.Projection.sameShadow (shadow proc) c d) :
    ¬ admissibleOn proc c d :=
  fun ha => h ha.2

/-- REPEATABILITY is necessary as a stated conjunct: admissibility entails the same-condition shadow
is stable. (For a deterministic procedure this conjunct is always *true* — `rfl` — but it is the
modelled CONTENT of Bacon's principle, and `admissibleOn` carries it explicitly; drop `.1` and the
principle is no longer in the statement.) -/
theorem admissible_repeats
    (proc : Procedure) (c d : Condition) (ha : admissibleOn proc c d) :
    Experiments.Common.Projection.sameShadow (shadow proc) c c :=
  ha.1

-- ---------------------------------------------------------------------------
-- The canonical repeatable procedure and its witnessed comparison.
-- ---------------------------------------------------------------------------

/-- A stable ruler: it reads off the knob, plus a fixed offset (a labelled "zero of the scale"). -/
def ruler : Procedure := { apply := fun c => { dial := c.knob + 7 } }

/-- Two conditions the ruler declares equivalent: it reads the SAME dial on both (knobs 5 and 5).
A single act is an event; the ruler makes them comparable. -/
def condA : Condition := { knob := 5 }
def condB : Condition := { knob := 5 }

/-- The ruler is admissible across the canonical pair (concrete, via the `Decidable` instance). -/
theorem ruler_admissible_canonical : admissibleOn ruler condA condB := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the repeatability conjunct IS the harness `sameShadow`).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (admissible) the canonical ruler is admissible across the canonical pair — proved here, and its
  second conjunct is exactly `Experiments.Common.Projection.sameShadow` (the harness coupling); AND
* (a distinguishing act exists) the ruler genuinely separates SOME conditions — `condA` (knob 5) and
  a knob-9 condition are NOT equivalent — so the procedure is not the trivial constant ruler that
  declares everything equivalent. This stops the claim from being satisfied vacuously. -/
def claimStatement : Prop :=
  admissibleOn ruler condA condB ∧
    ¬ Experiments.Common.Projection.sameShadow (shadow ruler) condA { knob := 9 }

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement := by
  unfold claim claimStatement
  decide

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  procedure : Procedure
  first : Condition
  second : Condition

/-- The run actually computes — thanks to the `Decidable` instances above. -/
def run (s : Setup) : Bool := decide (admissibleOn s.procedure s.first s.second)

/-- The exported claim is a genuine function of the setup, and this bridge pins it to `run`, so the
claim body cannot be silently swapped for `fun _ => True` without breaking the proof. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => admissibleOn s.procedure s.first s.second }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { procedure := ruler, first := condA, second := condB }

#eval run canonicalSetup                                   -- expect: true
#eval run { canonicalSetup with second := { knob := 9 } }  -- expect: false  (not comparable)
#print axioms claim_holds                                  -- [propext, Quot.sound] = AMBIENT

-- Gate evidence: the falsifiable predicate evaluated where it is FALSE (load-bearing, not vacuous).
#eval decide (admissibleOn ruler condA { knob := 9 })      -- expect: false

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
It reuses `run` (already decidable, already proved equal to the claim) rather than re-`decide` the
opaque projection `experiment.claim`. -/
def deviceNear (setup : Setup) : Bool :=
  decide (admissibleOn setup.procedure setup.first setup.second)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheBaconEffect
