import Measurement.Episode35

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 36__: _Discrete Poincare on a Stage Graph_

Episode35 killed the nullspace of one fixed three-rung chain with one anchor.
This episode proves the same coercivity holds for a finite stage graph of any
length: the canonical one-dimensional stage chain `e0, e1, ..., en`, with the
first stage `e0` pinned to the load anchor.

The stiffness energy of the chain is the sum of squared edge differences:

  chainEnergy [x0, x1, ..., xn] = sum_k (x_{k+1} - x_k)^2.

The discrete Poincare inequality is the statement that this energy controls the
whole configuration once the chain is anchored:

  x0 = 0  and  chainEnergy x = 0   ==>   every xk = 0.

Stated formally:
* `chainEnergy` is the stage-graph stiffness energy; `chainEnergy_nonneg` is its
  positive-semi-definiteness.
* `chain_poincare` is the discrete Poincare / coercivity theorem, proved by
  induction along the chain: each vanishing edge forces the next stage to equal
  the previous one, and the anchor `x0 = 0` propagates `0` down the whole chain.
* `StageChain` packages a chain with its load anchor; `StageChain.coercive` is
  the per-graph coercivity certificate.
* `chain_eq_anchored` shows Episode35's `anchoredForm` is exactly the `n = 2`
  stage chain `[0, c1, c2]`, so the three-rung SPD is the smallest instance of
  this general result.

Residue left:
The chain is the one-dimensional stage graph.  A general graph Laplacian over a
fixed stage set is the same per-edge argument plus a connectivity walk; the
chain is the connected case that carries the Poincare constant.
-/

/-- Stage-graph stiffness energy: the sum of squared edge differences along the
one-dimensional chain of stages. -/
def chainEnergy : List Int -> Int
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (b - a) * (b - a) + chainEnergy (b :: rest)

/-- Positive semi-definiteness of the stage-graph energy. -/
theorem chainEnergy_nonneg : (xs : List Int) -> 0 <= chainEnergy xs
  | [] => by simp [chainEnergy]
  | [_] => by simp [chainEnergy]
  | a :: b :: rest => by
      simp only [chainEnergy]
      have h1 := sqDiag_nonneg (b - a)
      have h2 := chainEnergy_nonneg (b :: rest)
      omega

/-- Discrete Poincare / coercivity: an anchored stage chain with zero stiffness
energy is identically zero.  Each vanishing edge forces the next stage to equal
the previous one; the load anchor `x0 = 0` then propagates `0` down the chain. -/
theorem chain_poincare : (xs : List Int) -> xs.head? = some 0 ->
    chainEnergy xs = 0 -> xs.all (fun v => v == 0) = true
  | [], _, _ => by simp
  | [_], ha, _ => by simp only [List.head?] at ha; simp_all
  | a :: b :: rest, ha, he => by
      simp only [List.head?] at ha
      have ha0 : a = 0 := by simp_all
      subst ha0
      simp only [chainEnergy] at he
      have hsq := sqDiag_nonneg (b - 0)
      have hrest := chainEnergy_nonneg (b :: rest)
      have e1 : (b - 0) * (b - 0) = 0 := by omega
      have hb : b = 0 := by have := sqDiag_eq_zero e1; omega
      have herest : chainEnergy (b :: rest) = 0 := by omega
      subst hb
      have IH := chain_poincare (0 :: rest) (by simp) herest
      simpa using IH

/-- A finite stage graph: the chain of stage values, with the first stage pinned
to the load anchor (`= 0`, the `.white_hole -> .load` boundary). -/
structure StageChain where
  nodes : List Int
  anchored : nodes.head? = some 0

namespace StageChain

/-- The coercivity certificate for a stage graph: zero energy forces every stage
to zero.  This is the discrete Poincare inequality specialized to the graph. -/
theorem coercive (sc : StageChain) (h : chainEnergy sc.nodes = 0) :
    sc.nodes.all (fun v => v == 0) = true :=
  chain_poincare sc.nodes sc.anchored h

end StageChain

/-- Episode35's anchored three-rung form is exactly the `n = 2` stage chain
`[0, c1, c2]`: the smallest instance of the discrete Poincare result. -/
theorem chain_eq_anchored (x : AnchoredRung) :
    chainEnergy [0, x.c1, x.c2] = AnchoredRung.stiff x x := by
  simp only [chainEnergy, AnchoredRung.stiff, Int.sub_zero, Int.add_zero] <;> omega

/-- The same bridge stated against the assembled Episode35 form `anchoredForm`. -/
theorem chain_eq_anchoredForm (x : AnchoredRung) :
    chainEnergy [0, x.c1, x.c2] = anchoredForm.a x x :=
  chain_eq_anchored x

end Measurement
