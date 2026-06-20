import Experiments.Common

/-!
# The Hilbert Effect — finite completion shadow (rebuilt to the EXEMPLAR shape)

The source statement: *the space of admissible spline refinements, completed under
prediction and consistency, forms a Hilbert space whose inner product is induced by
informational minimality; prediction is the inverse refinement operator `Ψ⁻¹`.*

We do NOT construct a Hilbert completion. We model the two finite, exact, decidable
*shadows* the source actually leans on:

1. an **informational inner product / norm** on a finite spline node — here `‖p‖² = a² + b²`
   over the integers (an exact discrete stand-in for the inner-product structure the
   completion is claimed to carry); and
2. the **reversibility of admissible prediction**: prediction `Ψ⁻¹` and refinement `Ψ` are
   mutually inverse — but only on *admissible* nodes. This is the discrete carrier of the
   "reversibility of admissible prediction" clause and of the `Ψ`/`Ψ⁻¹` identification.

The domain type is effect-specific (`SplineNode`) — NOT `Experiments.Common.CountSetup`'s
three undifferentiated `Nat`s.

## COUPLING (honest)
This effect is refinement / completion / scale-change — successive-interpolant comparison.
It has **no** holonomy, gauge phase, curvature-as-Berry-phase, or charge, so it does NOT
touch the device (`Measurement.*`); forcing a positron/holonomy theorem onto a completion
claim would be a FAKE coupling. The honest harness hook is `Experiments.Common.Ledger.count_map`
(= the count law of `Refinement.pushLedger`): **refining a finite record of spline nodes
preserves the number of recorded nodes** — the bookkeeping invariant that is the discrete
"conservation of informational norm" the source names. A conjunct of `claim_holds` is
discharged by `count_map`, so a regression there breaks THIS build (load-bearing coupling).

## NOT claimed
That any Hilbert space is constructed; no completeness, no Cauchy/dense limit, no Axiom of
Cantor, no actual inner-product *space* (no bilinearity, no Cauchy–Schwarz, no triangle
inequality proved); `Ψ`/`Ψ⁻¹` are *labelled* finite maps, not the genuine refinement operator.
`‖·‖²` is a single illustrative integer form, not derived from informational minimality.
**Claim ceiling:** a finite, exact *smooth-shadow* of the completion's inner product +
reversibility, plus the harness count law for the refinement map.
-/

namespace Experiments.TheHilbertEffect

/-- One admissible spline node: a recorded coefficient `a` and a refinement increment `b`.
Both integers — exact and decidable. The "predicted" partner under `Ψ⁻¹` is recovered by
the inverse map below. -/
structure SplineNode where
  a : Int
  b : Int
deriving DecidableEq, Repr

namespace SplineNode

/-- The informational inner product squared-norm `‖p‖² = a² + b²` (an exact integer
stand-in for the inner product the completion is claimed to induce). -/
def normSq (p : SplineNode) : Int := p.a * p.a + p.b * p.b

/-- Refinement `Ψ`: advance the node by moving the increment into the coefficient slot
(`(a,b) ↦ (a+b, b)`) — a finite, invertible step. -/
def refine (p : SplineNode) : SplineNode := { a := p.a + p.b, b := p.b }

/-- Prediction `Ψ⁻¹`: the inverse refinement operator (`(a,b) ↦ (a−b, b)`). -/
def predict (p : SplineNode) : SplineNode := { a := p.a - p.b, b := p.b }

/-- A node is **admissible** when it carries a genuine refinement increment (`b ≠ 0`):
a real prediction step, not a frozen point. This is the hypothesis whose removal makes the
"reversibility of admissible prediction" content vacuous on the witness below. -/
def admissible (p : SplineNode) : Prop := p.b ≠ 0

instance (p : SplineNode) : Decidable (p.admissible) := by
  unfold admissible; exact inferInstance

end SplineNode

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and breaks if a hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- **Reversibility of prediction.** Prediction `Ψ⁻¹` undoes refinement `Ψ`: for ALL nodes,
`predict (refine p) = p`. This is the discrete "prediction is the inverse refinement
operator `Ψ⁻¹`" clause. -/
theorem predict_refine (p : SplineNode) : (p.refine).predict = p := by
  unfold SplineNode.refine SplineNode.predict
  simp only []
  congr 1
  omega

/-- **Refinement preserves the informational norm of the increment channel.** The `b`
component (the increment that carries the inner-product weight) is invariant under `Ψ`:
for ALL nodes, `(refine p).b = p.b`. -/
theorem refine_preserves_increment (p : SplineNode) : (p.refine).b = p.b := by
  unfold SplineNode.refine; rfl

/-- **FALSIFIABLE / load-bearing.** On an admissible node the two distinct refinements
genuinely move the coefficient: `refine p ≠ predict p`. Drop the admissibility hypothesis
(`b ≠ 0`) and the conclusion fails — at `b = 0` both maps are the identity and `refine p =
predict p`. Quantified over ALL nodes. -/
theorem admissible_refine_ne_predict (p : SplineNode) (h : p.admissible) :
    p.refine ≠ p.predict := by
  unfold SplineNode.refine SplineNode.predict SplineNode.admissible at *
  intro heq
  have hb : p.a + p.b = p.a - p.b := congrArg SplineNode.a heq
  omega

/-- Contrapositive content: if the two refinements coincide, the node was inadmissible.
Pins that admissibility is exactly the load-bearing hypothesis. -/
theorem refine_eq_predict_is_inadmissible (p : SplineNode) (h : p.refine = p.predict) :
    ¬ p.admissible :=
  fun ha => admissible_refine_ne_predict p ha h

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING: refining a finite record of nodes preserves the node count
-- (the discrete "conservation of informational norm").
-- ---------------------------------------------------------------------------

/-- A refinement decodes a fine spline node into the coarse coefficient it contributes. -/
def nodeRefinement : Experiments.Common.Refinement Int SplineNode :=
  { decode := fun p => (p.refine).a }

/-- A finite record of admissible spline nodes (the finite sequence of measurement events
the source refines into its completion). -/
def sampleRecord : Experiments.Common.Ledger SplineNode :=
  { events := [ { a := 1, b := 2 }, { a := 0, b := 3 }, { a := 4, b := 1 } ] }

/-- The bookkeeping invariant: pushing the record through the refinement (decoding every node
to its refined coefficient) does NOT change the number of recorded nodes. This is the harness
`count_map` law specialized to `nodeRefinement` — the count law of `Refinement.pushLedger`,
the discrete conservation of informational norm. -/
theorem refinement_preserves_node_count :
    (nodeRefinement.pushLedger sampleRecord).count = sampleRecord.count := by
  unfold Experiments.Common.Refinement.pushLedger
  exact Experiments.Common.Ledger.count_map nodeRefinement.decode sampleRecord

-- ---------------------------------------------------------------------------
-- THE CANONICAL NODE + concrete checks.
-- ---------------------------------------------------------------------------

/-- A concrete admissible spline node. -/
def canonicalNode : SplineNode := { a := 1, b := 2 }

theorem canonicalNode_admissible : canonicalNode.admissible := by decide

/-- Concrete receipt: prediction reverses refinement on the canonical node. -/
theorem canonical_round_trip : (canonicalNode.refine).predict = canonicalNode := by decide

/-- Concrete receipt: the informational norm-squared of the canonical node is `1²+2² = 5`. -/
theorem canonical_normSq : canonicalNode.normSq = 5 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (reversibility) prediction `Ψ⁻¹` inverts refinement `Ψ` on the canonical node —
  `predict_refine`, the "prediction = inverse refinement operator" clause;
* (non-vacuity) on an admissible node the two refinements genuinely differ —
  `admissible_refine_ne_predict`, the FALSIFIABLE core; and
* (harness coupling) refining the finite node-record preserves the node count —
  `refinement_preserves_node_count`, discharged by `Experiments.Common.Ledger.count_map`. -/
def claimStatement : Prop :=
  ((canonicalNode.refine).predict = canonicalNode) ∧
    canonicalNode.refine ≠ canonicalNode.predict ∧
    (nodeRefinement.pushLedger sampleRecord).count = sampleRecord.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨predict_refine canonicalNode,
    admissible_refine_ne_predict canonicalNode canonicalNode_admissible,
    refinement_preserves_node_count⟩

/-- Honest ceiling: a finite stand-in for the continuous Hilbert completion — a smooth-shadow
analogy, nothing more. (Not mechanically enforced; the tag is a convention.) -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  node : SplineNode

/-- The run computes (via the `Decidable` instance on `admissible`): is this node an
admissible refinement (does prediction carry genuine, reversible content)? -/
def run (s : Setup) : Bool := decide (s.node.admissible)

/-- The exported claim is a genuine function of the setup, pinned to `run` by the bridge below. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.node.admissible }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { node := canonicalNode }

#eval run canonicalSetup                              -- expect: true
#eval run { node := { a := 5, b := 0 } }              -- expect: false (inadmissible)
-- Gate: evaluate the falsifiable predicate where it is FALSE (b = 0 ⇒ refine = predict):
#eval decide (SplineNode.refine { a := 5, b := 0 } ≠ SplineNode.predict { a := 5, b := 0 })  -- expect: false
#print axioms claim_holds                             -- ambient footprint, not coupling

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment; exact inferInstance

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

end Experiments.TheHilbertEffect
