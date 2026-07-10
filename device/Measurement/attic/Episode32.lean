import Measurement.Episode31

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 32__: _One Result, Two Proofs, One Clock_

Episode31 exposed the old mixed-coupling term as the finite second variation.
That gives two proof routes to the same proposition:

* the old route says the mixed coupling is solved;
* the new route says the second variation vanished.

Mathematically, the result is one proposition:

  coupledCubicDifference action path variation = 0.

Lean collapses proofs of that proposition by proof irrelevance.  The EKG layer
does not prove that equality.  It only measures the computational residue of
elaborating the two routes.

Stated formally:
* `coupledZeroByMixed` and `coupledZeroBySecondVariation` prove the same target.
* `coupledZeroByMixed_eq_coupledZeroBySecondVariation` is proof irrelevance.
* `mixedProofTime` and `secondVariationProofTime` are elaboration-register
  diagnostics for the two inline proof paths.

Residue left:
Heartbeat readings are environment-dependent.  The stable theorem is proof
irrelevance; timing is a detector for compiler-path residue, not truth.
-/

def coupledZeroByMixed
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range)
    (variation : CubicGaugeVariation)
    (hLeft :
      approximation.support.leftSupportedVariation
        (CubicGaugeVariation.leftVariation variation))
    (hRight :
      approximation.support.rightSupportedVariation
        (CubicGaugeVariation.rightVariation variation))
    (hMixed :
      CubicGaugeVariation.mixedCouplingSolved action path variation) :
    CubicGaugeVariation.coupledCubicDifference action path variation = 0 :=
  CubicPartitionedLanczosApproximation.partitions_and_mixed_derive_coupledCubicDifference_zero
      approximation
      variation
      hLeft
      hRight
      hMixed

def coupledZeroBySecondVariation
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range)
    (variation : CubicGaugeVariation)
    (hLeft :
      approximation.support.leftSupportedVariation
        (CubicGaugeVariation.leftVariation variation))
    (hRight :
      approximation.support.rightSupportedVariation
        (CubicGaugeVariation.rightVariation variation))
    (hSecond :
      CubicGaugeVariation.secondVariationVanished action path variation) :
    CubicGaugeVariation.coupledCubicDifference action path variation = 0 :=
  CubicPartitionedLanczosApproximation.supported_data_and_secondVariation_solve_coupledCubicVariation
      approximation
      variation
      hLeft
      hRight
      hSecond

theorem coupledZeroByMixed_eq_coupledZeroBySecondVariation
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range)
    (variation : CubicGaugeVariation)
    (hLeft :
      approximation.support.leftSupportedVariation
        (CubicGaugeVariation.leftVariation variation))
    (hRight :
      approximation.support.rightSupportedVariation
        (CubicGaugeVariation.rightVariation variation))
    (hMixed :
      CubicGaugeVariation.mixedCouplingSolved action path variation) :
    coupledZeroByMixed
        approximation
        variation
        hLeft
        hRight
        hMixed =
      coupledZeroBySecondVariation
        approximation
        variation
        hLeft
        hRight
        ((CubicGaugeVariation.secondVariationVanished_iff_mixedCouplingSolved
            action path variation).2 hMixed) := by
  exact Subsingleton.elim _ _

/- The timing register elaborates an inline term and stores the consumed
heartbeat count as a `Nat`.  It is diagnostic only; theorem equality above is
already settled by proof irrelevance. -/
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term in
elab "register_timed_probe" name:ident "=>" t:term : command => do
  let hb ← liftTermElabM do
    let (_, hb) ← Lean.withHeartbeats do
      let _ ← Term.elabTerm t none
      pure ()
    pure hb
  let cmd ← `(def $name : Nat := $(Lean.quote hb))
  Lean.Elab.Command.elabCommand cmd

-- Probe route A inline: old mixed-coupling vocabulary.
ekg_probe 720 =>
  show
    forall
      {action : FiniteGaugeAction} {path : CubicGaugePath}
      {range : AdmissibleRange}
      (approximation :
        CubicPartitionedLanczosApproximation action path range)
      (variation : CubicGaugeVariation)
      (hLeft :
        approximation.support.leftSupportedVariation
          (CubicGaugeVariation.leftVariation variation))
      (hRight :
        approximation.support.rightSupportedVariation
          (CubicGaugeVariation.rightVariation variation))
      (hMixed :
        CubicGaugeVariation.mixedCouplingSolved action path variation),
      CubicGaugeVariation.coupledCubicDifference action path variation = 0
  from by
    intro action path range approximation variation hLeft hRight hMixed
    exact
      CubicPartitionedLanczosApproximation.partitions_and_mixed_derive_coupledCubicDifference_zero
          approximation
          variation
          hLeft
          hRight
          hMixed

-- Probe route B inline: second-variation vocabulary.
ekg_probe 720 =>
  show
    forall
      {action : FiniteGaugeAction} {path : CubicGaugePath}
      {range : AdmissibleRange}
      (approximation :
        CubicPartitionedLanczosApproximation action path range)
      (variation : CubicGaugeVariation)
      (hLeft :
        approximation.support.leftSupportedVariation
          (CubicGaugeVariation.leftVariation variation))
      (hRight :
        approximation.support.rightSupportedVariation
          (CubicGaugeVariation.rightVariation variation))
      (hMixed :
        CubicGaugeVariation.mixedCouplingSolved action path variation),
      CubicGaugeVariation.coupledCubicDifference action path variation = 0
  from by
    intro action path range approximation variation hLeft hRight hMixed
    have hSecond :
        CubicGaugeVariation.secondVariationVanished action path variation :=
      (CubicGaugeVariation.secondVariationVanished_iff_mixedCouplingSolved
          action path variation).2 hMixed
    exact
      CubicPartitionedLanczosApproximation.supported_data_and_secondVariation_solve_coupledCubicVariation
          approximation
          variation
          hLeft
          hRight
          hSecond

register_timed_probe mixedProofTime =>
  show
    forall
      {action : FiniteGaugeAction} {path : CubicGaugePath}
      {range : AdmissibleRange}
      (approximation :
        CubicPartitionedLanczosApproximation action path range)
      (variation : CubicGaugeVariation)
      (hLeft :
        approximation.support.leftSupportedVariation
          (CubicGaugeVariation.leftVariation variation))
      (hRight :
        approximation.support.rightSupportedVariation
          (CubicGaugeVariation.rightVariation variation))
      (hMixed :
        CubicGaugeVariation.mixedCouplingSolved action path variation),
      CubicGaugeVariation.coupledCubicDifference action path variation = 0
  from by
    intro action path range approximation variation hLeft hRight hMixed
    exact
      CubicPartitionedLanczosApproximation.partitions_and_mixed_derive_coupledCubicDifference_zero
          approximation
          variation
          hLeft
          hRight
          hMixed

register_timed_probe secondVariationProofTime =>
  show
    forall
      {action : FiniteGaugeAction} {path : CubicGaugePath}
      {range : AdmissibleRange}
      (approximation :
        CubicPartitionedLanczosApproximation action path range)
      (variation : CubicGaugeVariation)
      (hLeft :
        approximation.support.leftSupportedVariation
          (CubicGaugeVariation.leftVariation variation))
      (hRight :
        approximation.support.rightSupportedVariation
          (CubicGaugeVariation.rightVariation variation))
      (hMixed :
        CubicGaugeVariation.mixedCouplingSolved action path variation),
      CubicGaugeVariation.coupledCubicDifference action path variation = 0
  from by
    intro action path range approximation variation hLeft hRight hMixed
    have hSecond :
        CubicGaugeVariation.secondVariationVanished action path variation :=
      (CubicGaugeVariation.secondVariationVanished_iff_mixedCouplingSolved
          action path variation).2 hMixed
    exact
      CubicPartitionedLanczosApproximation.supported_data_and_secondVariation_solve_coupledCubicVariation
          approximation
          variation
          hLeft
          hRight
          hSecond

def proofTimingResidue : Nat :=
  if mixedProofTime <= secondVariationProofTime then
    secondVariationProofTime - mixedProofTime
  else
    mixedProofTime - secondVariationProofTime

def proofsTimingEquivalentUpToNoise : Prop :=
  proofTimingResidue <= Calibration.measuredFloor

def proofsTimingDistinguishable : Prop :=
  Calibration.measuredFloor < proofTimingResidue

theorem proofTiming_equivalent_or_distinguishable :
    proofsTimingEquivalentUpToNoise ∨ proofsTimingDistinguishable := by
  unfold proofsTimingEquivalentUpToNoise proofsTimingDistinguishable
  by_cases h :
      proofTimingResidue <= Calibration.measuredFloor
  · exact Or.inl h
  · exact Or.inr (Nat.lt_of_not_ge h)

end Measurement
