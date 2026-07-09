import Experiments.Common

/-!
# Qubit Decoherence — a finite informational collapse (exemplar shape)

This file follows the worked exemplar (`ThePositronAnnihilationEffect/Experiment1.lean`,
see `device/Experiments/FEEDBACK2.md`): it carries an **effect-specific domain**, several
**falsifiable** ∀-quantified lemmas, and a **content-bearing** claim — not the 3-`Nat`
`CountSetup` template the file previously stubbed.

## The phenomenon (modelled finitely)
Per the source (`instrument/chapters/07.tex:1201`), this is an **informational** phenomenon:
it does NOT rely on physical decoherence, environmental coupling, or geometric dynamics. A
*causal doublet* is the minimal unit of informational degeneracy: a system admitting two
equally admissible refinement paths `S = {e0, e1}` that are **locally indistinguishable**
(they agree on everything visible at the shared boundary) and **jointly admissible**. That is
a qubit in the informational sense.

Decoherence occurs when a new event is recorded that is inconsistent with one branch. The
Interaction Operator performs a **pivot** on the shared boundary, recording a distinction that
the surviving branch carries and the other cannot — collapsing the doublet to a single
admissible history.

We make this finite and decidable via the harness `Boundary.compatible` (boundary records
agree). The content is: BEFORE the pivot the two branches are boundary-compatible (the qubit
is coherent — locally indistinguishable); AFTER the pivot the pivoted branch is NOT
boundary-compatible with its sibling — coherence is gone. The qubit cannot survive the
recording of the distinguishing event.

## NOT claimed
That this models a physical decoherence *rate*, a master equation, a Lindblad operator, or any
`T2`/dephasing time; that `D` (informational diffusion) or `ℏ` is derived (they are not present
here — only the structural collapse is); that the "events" are physical states. The pivot is a
pure bookkeeping operation on a finite boundary record; nothing crosses a real channel.
**Claim ceiling:** a finite **inadmissibility no-go** — the impossibility of a refinement that
both records the distinguishing event AND keeps the doublet locally indistinguishable.
-/

namespace Experiments.QubitDecoherence

/-- A branch label of the causal doublet `S = {e0, e1}`: the two equally admissible refinement
paths. Opaque finite labels — no internal structure is modelled. -/
inductive Branch where
  | e0
  | e1
deriving DecidableEq, Repr

/-- The shared boundary record on the seam of the doublet: the residue visible to both
branches at once. `degenerate` is the coherent, locally-indistinguishable seam (the qubit);
`pivoted` is the seam after the Interaction Operator records the distinguishing event. -/
inductive Seam where
  | degenerate
  | pivoted
deriving DecidableEq, Repr

/-- A history of one branch of the doublet: which refinement path it took, and the shared
boundary record it currently carries. The boundary is the ONLY part visible across the doublet
— the part that makes two branches "locally indistinguishable" when it agrees. -/
structure History where
  branch : Branch
  seam : Seam
deriving DecidableEq, Repr

/-- The coherent doublet at branch `b`: the seam is `degenerate`, so both branches still agree
on the boundary. This is the qubit before any distinguishing event is recorded. -/
def coherent (b : Branch) : History := { branch := b, seam := Seam.degenerate }

/-- The boundary the two branches share: the part of a history visible across the doublet is
exactly its `seam` record. This is the harness `Boundary`, instantiated for this effect. -/
def sharedBoundary : Experiments.Common.Boundary History Seam :=
  { restrict := fun h => h.seam }

/-- The *Interaction Operator's pivot*: it records the distinguishing event by moving the shared
boundary `degenerate ↦ pivoted` on the branch it acts on. This is the irreversible step that
eliminates the orderings incompatible with the new record. It changes the seam — that is what no
coherent (degenerate) branch does. -/
def pivot (h : History) : History :=
  { h with seam := Seam.pivoted }

-- Decidability of the boundary-compatibility predicate, so `decide`/`#eval` see through it.
instance (h k : History) :
    Decidable (Experiments.Common.Boundary.compatible sharedBoundary h k) := by
  unfold Experiments.Common.Boundary.compatible sharedBoundary
  exact inferInstance
-- (`h`/`k` are used inside the unfolded goal; the linter cannot see through `unfold`.)

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and would break if the model dropped a
-- hypothesis: they pin that the two branches are locally indistinguishable WHILE coherent,
-- and that the pivot destroys that indistinguishability — the whole content of decoherence.
-- ---------------------------------------------------------------------------

/-- **Coherence = local indistinguishability.** For ALL pairs of branches, the two coherent
histories of the doublet agree on the shared boundary: while degenerate, `e0` and `e1` are
locally indistinguishable. (Drop the "seam = degenerate" clause from `coherent` and this
fails — the branches could then differ on the boundary.) -/
theorem coherent_branches_indistinguishable (a b : Branch) :
    Experiments.Common.Boundary.compatible sharedBoundary (coherent a) (coherent b) := rfl

/-- **The pivot records a distinction.** For ALL branches, applied to a coherent history the
pivot is NOT boundary-compatible with the history it acted on: it moves the seam. This is the
distinguishing event the doublet cannot absorb degenerately. (Drop the seam change from `pivot`
and this fails — so the conjunct is load-bearing.) -/
theorem pivot_breaks_boundary (b : Branch) :
    ¬ Experiments.Common.Boundary.compatible sharedBoundary (coherent b) (pivot (coherent b)) := by
  -- `compatible` here says `Seam.degenerate = Seam.pivoted`, which is false.
  intro hcompat
  exact Seam.noConfusion hcompat

/-- **THE DECOHERENCE NO-GO (falsifiable, ∀-quantified).** After the pivot records the
distinguishing event on one branch, that branch is no longer locally indistinguishable from the
OTHER coherent branch of the doublet: for ALL branch pairs, `pivot (coherent a)` and
`coherent b` disagree on the shared boundary. The doublet has collapsed — the qubit cannot
remain coherent once the distinction is recorded. -/
theorem decohered_branches_distinguishable (a b : Branch) :
    ¬ Experiments.Common.Boundary.compatible sharedBoundary (pivot (coherent a)) (coherent b) := by
  -- seam of `pivot (coherent a)` is `Seam.pivoted`, seam of `coherent b` is `Seam.degenerate`.
  intro hcompat
  exact Seam.noConfusion hcompat

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; a real conjunction). Each conjunct is the harness
-- `Boundary.compatible` instantiated for this effect — a regression in that predicate or its
-- `DecidableEq` plumbing breaks THIS build (harness coupling, FEEDBACK2 §1).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (coherence) the two branches of the doublet are locally indistinguishable while degenerate
  (`coherent_branches_indistinguishable` — the qubit, made explicit);
* (the distinguishing event) the pivot moves the boundary (`pivot_breaks_boundary`);
* (the no-go) therefore a pivoted branch is no longer indistinguishable from its sibling
  (`decohered_branches_distinguishable`) — the doublet has decohered.
Every conjunct is discharged by the harness `Boundary.compatible` reading the actual seam, so a
regression in that harness predicate fails this build (harness coupling). -/
def claimStatement : Prop :=
  (∀ a b : Branch,
      Experiments.Common.Boundary.compatible sharedBoundary (coherent a) (coherent b)) ∧
    (∀ b : Branch,
      ¬ Experiments.Common.Boundary.compatible sharedBoundary (coherent b) (pivot (coherent b))) ∧
    (∀ a b : Branch,
      ¬ Experiments.Common.Boundary.compatible sharedBoundary (pivot (coherent a)) (coherent b))

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨coherent_branches_indistinguishable,
   pivot_breaks_boundary,
   decohered_branches_distinguishable⟩

/-- The tag is an honest ceiling: a finite **inadmissibility no-go** (the collapse of the
doublet), nothing quantitative. (The harness has no `requiredModelKind` fence, so the tag is a
convention, not mechanically enforced — same caveat as the exemplar.) -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  recorded : Branch
  sibling : Branch

/-- The run computes the discriminating witness: after the pivot records the distinguishing
event on `recorded`, is that branch still indistinguishable from `sibling`? Always `false` (it
cannot be) — that is decoherence, executable. -/
def run (s : Setup) : Bool :=
  decide (Experiments.Common.Boundary.compatible sharedBoundary
    (pivot (coherent s.recorded)) (coherent s.sibling))

/-- The exported claim is a genuine function of the setup (not `fun _ => True`): the pivoted
branch is NOT indistinguishable from its sibling. The bridge below pins it to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s =>
      ¬ Experiments.Common.Boundary.compatible sharedBoundary
          (pivot (coherent s.recorded)) (coherent s.sibling) }

theorem run_iff_claim (s : Setup) :
    run s = false ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_false_iff_not]

def canonicalSetup : Setup := { recorded := Branch.e0, sibling := Branch.e1 }

#eval run canonicalSetup  -- expect: false  (the decohered branch is no longer indistinguishable)
#print axioms claim_holds  -- [propext, Quot.sound] = AMBIENT decide footprint, not coupling
#eval decide (Experiments.Common.Boundary.compatible sharedBoundary
  (pivot (coherent Branch.e0)) (coherent Branch.e1))  -- expect: false (no-go is load-bearing, not vacuous)

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment
  infer_instance

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

end Experiments.QubitDecoherence
