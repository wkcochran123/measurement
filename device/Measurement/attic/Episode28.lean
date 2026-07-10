import Measurement.Episode27

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 28__: _The Humble Sobolev Activity Norm_

Episode27 closed the finite support loop:

  elephant support
  -> trace knots
  -> terminal residual zero on represented data
  -> squeeze-bound convergence through the Weierstrass/B-spline tower.

Episode28 is the doorframe after that, not the cathedral.  The Galerkin
diagonal is energy-squared first:

  energySq x = a x x.

The induced norm and Hilbert geometry come after the SPD/boundary/nullspace
certificate is wired.  This file therefore keeps three layers separate:

* `ActivityGaugeCertificate` is a weak zero-detecting gauge.
* `GalerkinBilinearForm` records the honest symmetric bilinear form data.
* `SPDGalerkinActivity` upgrades the form with natural boundary conditions,
  a white-hole/load anchor, and a killed nullspace.

Stated formally:
* supported finite residual zero gives supported emitted energy-squared zero;
* positive definiteness/nullspace killing turns energy-squared zero into zero
  activity;
* SPD gives an `EnergySqCertificate`, not a full Hilbert space.

Claimed by interpretation:
The compiler emits a Galerkin weak form.  Natural boundary behavior plus the
white-hole/load anchor kills the nullspace.  The remaining diagonal detector is
faithful energy-squared.

Residue left:
The square-root norm, completion, topology, and Hilbert-space imports are still
future layers.  This file exposes the proof-carrying certificate they would
consume.
-/

def intActivityMagnitude (value : Int) : Nat :=
  match value with
  | Int.ofNat n => n
  | Int.negSucc n => Nat.succ n

theorem intActivityMagnitude_zero :
    intActivityMagnitude 0 = 0 := by
  rfl

theorem intActivityMagnitude_eq_zero
    {value : Int}
    (h : intActivityMagnitude value = 0) :
    value = 0 := by
  cases value with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ n =>
          unfold intActivityMagnitude at h
          contradiction
  | negSucc n =>
      unfold intActivityMagnitude at h
      contradiction

structure ActivityGaugeCertificate (Activity : Type) where
  zero : Activity
  gauge : Activity -> Nat
  gauge_zero : gauge zero = 0
  gauge_eq_zero_only_zero :
    forall x,
      gauge x = 0 -> x = zero

namespace ActivityGaugeCertificate

theorem gauge_eq_zero_iff_eq_zero
    {Activity : Type}
    (certificate : ActivityGaugeCertificate Activity)
    (x : Activity) :
    certificate.gauge x = 0 <-> x = certificate.zero := by
  constructor
  · intro h
    exact certificate.gauge_eq_zero_only_zero x h
  · intro h
    rw [h]
    exact certificate.gauge_zero

end ActivityGaugeCertificate

structure EnergySqCertificate (V : Type) where
  zero : V
  energySq : V -> Nat
  energySq_zero : energySq zero = 0
  energySq_eq_zero_only_zero :
    forall x,
      energySq x = 0 -> x = zero

namespace EnergySqCertificate

def toActivityGauge
    {V : Type}
    (certificate : EnergySqCertificate V) :
    ActivityGaugeCertificate V where
  zero := certificate.zero
  gauge := certificate.energySq
  gauge_zero := certificate.energySq_zero
  gauge_eq_zero_only_zero :=
    certificate.energySq_eq_zero_only_zero

theorem energySq_eq_zero_iff_eq_zero
    {V : Type}
    (certificate : EnergySqCertificate V)
    (x : V) :
    certificate.energySq x = 0 <-> x = certificate.zero :=
  ActivityGaugeCertificate.gauge_eq_zero_iff_eq_zero
    (EnergySqCertificate.toActivityGauge certificate)
    x

end EnergySqCertificate

structure InducedNormSqDoorframe (V : Type) where
  energy :
    EnergySqCertificate V
  normSq : V -> Nat
  normSq_matches_energySq :
    forall x,
      normSq x = energy.energySq x
  normSq_zero_detects :
    forall x,
      normSq x = 0 -> x = energy.zero

inductive InternalBoundaryNode where
  | white_hole
  | load

structure GalerkinBilinearForm where
  V : Type
  zero : V
  add : V -> V -> V
  neg : V -> V
  smul : Int -> V -> V
  a : V -> V -> Int
  symmetric :
    forall x y,
      a x y = a y x
  add_left :
    forall x y z,
      a (add x y) z = a x z + a y z
  smul_left :
    forall k x y,
      a (smul k x) y = k * a x y
  zero_left :
    forall x,
      a zero x = 0
  nonnegative_diagonal :
    forall x,
      0 <= a x x

namespace GalerkinBilinearForm

def energySq
    (form : GalerkinBilinearForm)
    (x : form.V) : Nat :=
  intActivityMagnitude (form.a x x)

theorem energySq_zero
    (form : GalerkinBilinearForm) :
    GalerkinBilinearForm.energySq form form.zero = 0 := by
  unfold GalerkinBilinearForm.energySq
  rw [form.zero_left form.zero]
  exact intActivityMagnitude_zero

theorem add_right
    (form : GalerkinBilinearForm)
    (x y z : form.V) :
    form.a x (form.add y z) = form.a x y + form.a x z := by
  rw [form.symmetric x (form.add y z)]
  rw [form.add_left y z x]
  rw [form.symmetric y x]
  rw [form.symmetric z x]

theorem smul_right
    (form : GalerkinBilinearForm)
    (k : Int)
    (x y : form.V) :
    form.a x (form.smul k y) = k * form.a x y := by
  rw [form.symmetric x (form.smul k y)]
  rw [form.smul_left k y x]
  rw [form.symmetric y x]

theorem diagonal_smul
    (form : GalerkinBilinearForm)
    (k : Int)
    (x : form.V) :
    form.a (form.smul k x) (form.smul k x) =
      k * (k * form.a x x) := by
  rw [form.smul_left k x (form.smul k x)]
  rw [GalerkinBilinearForm.smul_right form k x x]

end GalerkinBilinearForm

structure NaturalBoundary
    (form : GalerkinBilinearForm) where
  boundary_terms_vanish : Prop
  boundary_terms_vanish_proof :
    boundary_terms_vanish

structure WhiteHoleLoadAnchor
    (form : GalerkinBilinearForm) where
  trace : InternalBoundaryNode -> form.V
  load_is_anchor :
    trace .load = form.zero
  source_to_load : Prop
  source_to_load_proof :
    source_to_load

structure CompilerWhiteHoleLoadAnchor
    (form : GalerkinBilinearForm) where
  source : SpaceTimePath
  program : ComputerProgram
  anchorFact : Fact
  anchorType : Type
  previous : SpaceTimePath
  anchorProp : Prop
  source_is_white_hole :
    source = .white_hole anchorFact anchorType previous
  program_is_load :
    program = .load anchorProp anchorType
  anchor_loaded : Prop
  anchor_loaded_proof :
    anchor_loaded

structure NullspaceKilled
    (form : GalerkinBilinearForm)
    (natural : NaturalBoundary form)
    (anchor : WhiteHoleLoadAnchor form) where
  uses_natural_boundary :
    natural.boundary_terms_vanish
  uses_white_hole_load :
    anchor.source_to_load
  diagonal_zero_detects :
    forall x,
      form.a x x = 0 -> x = form.zero

structure SPDGalerkinActivity where
  form :
    GalerkinBilinearForm
  natural :
    NaturalBoundary form
  anchor :
    WhiteHoleLoadAnchor form
  nullspaceKilled :
    NullspaceKilled form natural anchor
  positive_definite :
    forall x,
      x ≠ form.zero -> 0 < form.a x x

namespace SPDGalerkinActivity

theorem diagonal_zero_detects_of_positive_definite
    (spd : SPDGalerkinActivity) :
    forall x,
      spd.form.a x x = 0 -> x = spd.form.zero := by
  intro x hDiagonal
  exact spd.nullspaceKilled.diagonal_zero_detects x hDiagonal

theorem positive_definite_of_nullspaceKilled
    (form : GalerkinBilinearForm)
    (natural : NaturalBoundary form)
    (anchor : WhiteHoleLoadAnchor form)
    (killed : NullspaceKilled form natural anchor) :
    forall x,
      x ≠ form.zero -> 0 < form.a x x := by
  intro x hx
  have hNonnegative :
      0 <= form.a x x :=
    form.nonnegative_diagonal x
  have hNotZero :
      form.a x x ≠ 0 := by
    intro hZero
    exact hx (killed.diagonal_zero_detects x hZero)
  omega

def toEnergySqCertificate
    (spd : SPDGalerkinActivity) :
    EnergySqCertificate spd.form.V where
  zero := spd.form.zero
  energySq := GalerkinBilinearForm.energySq spd.form
  energySq_zero := GalerkinBilinearForm.energySq_zero spd.form
  energySq_eq_zero_only_zero := by
    intro x hEnergy
    apply spd.nullspaceKilled.diagonal_zero_detects
    unfold GalerkinBilinearForm.energySq at hEnergy
    exact intActivityMagnitude_eq_zero hEnergy

def toActivityGauge
    (spd : SPDGalerkinActivity) :
    ActivityGaugeCertificate spd.form.V :=
  EnergySqCertificate.toActivityGauge
    (SPDGalerkinActivity.toEnergySqCertificate spd)

def inducedNormSqDoorframe
    (spd : SPDGalerkinActivity) :
    InducedNormSqDoorframe spd.form.V where
  energy := SPDGalerkinActivity.toEnergySqCertificate spd
  normSq := GalerkinBilinearForm.energySq spd.form
  normSq_matches_energySq := by
    intro x
    rfl
  normSq_zero_detects := by
    intro x h
    exact
      (SPDGalerkinActivity.toEnergySqCertificate spd).energySq_eq_zero_only_zero
        x
        h

def spd_galerkin_energySq_induces_normSq_doorframe
    (spd : SPDGalerkinActivity) :
    InducedNormSqDoorframe spd.form.V :=
  SPDGalerkinActivity.inducedNormSqDoorframe spd

def naturalBoundary_whiteHoleLoadAnchor_implies_spd
    (form : GalerkinBilinearForm)
    (natural : NaturalBoundary form)
    (anchor : WhiteHoleLoadAnchor form)
    (killed : NullspaceKilled form natural anchor) :
    SPDGalerkinActivity :=
  { form := form
    natural := natural
    anchor := anchor
    nullspaceKilled := killed
    positive_definite :=
      SPDGalerkinActivity.positive_definite_of_nullspaceKilled
        form
        natural
        anchor
        killed }

end SPDGalerkinActivity

structure CompilerAnchoredGalerkinActivity where
  spd :
    SPDGalerkinActivity
  compilerAnchor :
    CompilerWhiteHoleLoadAnchor spd.form
  compilerAnchor_realizes_whiteHoleLoad :
    compilerAnchor.anchor_loaded ->
      spd.anchor.source_to_load

namespace CompilerAnchoredGalerkinActivity

theorem source_to_load_of_anchor_loaded
    (activity : CompilerAnchoredGalerkinActivity)
    (hLoaded : activity.compilerAnchor.anchor_loaded) :
    activity.spd.anchor.source_to_load :=
  activity.compilerAnchor_realizes_whiteHoleLoad hLoaded

theorem source_to_load
    (activity : CompilerAnchoredGalerkinActivity) :
    activity.spd.anchor.source_to_load :=
  CompilerAnchoredGalerkinActivity.source_to_load_of_anchor_loaded
    activity
    activity.compilerAnchor.anchor_loaded_proof

end CompilerAnchoredGalerkinActivity

structure CompiledGalerkinEnergySq
    (range : AdmissibleRange)
    (scale : ApproximationScale)
    (action : FiniteGaugeAction) (path : FiniteGaugePath) where
  completed :
    CompletedResidualWeierstrassTower range scale action path
  Activity : Type
  energy :
    EnergySqCertificate Activity
  emittedActivity :
    Nat -> FiniteGaugeVariation -> Activity
  emittedEnergySq_matches_terminalResidualMagnitude :
    forall n variation,
      energy.energySq (emittedActivity n variation) =
        intActivityMagnitude
          ((completed.residualTower.stageTrace n).terminalResidual variation)

namespace CompiledGalerkinEnergySq

theorem supported_data_energySq_eq_zero
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (program :
      CompiledGalerkinEnergySq range scale action path)
    (n : Nat)
    (variation : FiniteGaugeVariation)
    (hSupport :
      variation.slip ∈
        (program.completed.completion.approximation.tower.stage n).candidates.entries) :
    program.energy.energySq
      (program.emittedActivity n variation) = 0 := by
  have hMatch :=
    program.emittedEnergySq_matches_terminalResidualMagnitude n variation
  have hTerminal :=
    CompletedResidualWeierstrassTower.stageTrace_solves_elephant_support
      program.completed
      n
      variation
      hSupport
  rw [hMatch, hTerminal]
  exact intActivityMagnitude_zero

theorem supported_data_activity_eq_zero_of_energySq_zero
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (program :
      CompiledGalerkinEnergySq range scale action path)
    (n : Nat)
    (variation : FiniteGaugeVariation)
    (hEnergy :
      program.energy.energySq
        (program.emittedActivity n variation) = 0) :
    program.emittedActivity n variation =
      program.energy.zero :=
  program.energy.energySq_eq_zero_only_zero
    (program.emittedActivity n variation)
    hEnergy

theorem supported_data_activity_eq_zero_on_support
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (program :
      CompiledGalerkinEnergySq range scale action path)
    (n : Nat)
    (variation : FiniteGaugeVariation)
    (hSupport :
      variation.slip ∈
        (program.completed.completion.approximation.tower.stage n).candidates.entries) :
    program.emittedActivity n variation =
      program.energy.zero :=
  CompiledGalerkinEnergySq.supported_data_activity_eq_zero_of_energySq_zero
    program
    n
    variation
    (CompiledGalerkinEnergySq.supported_data_energySq_eq_zero
      program
      n
      variation
      hSupport)

theorem supported_stage_collapses
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (program :
      CompiledGalerkinEnergySq range scale action path)
    (n : Nat)
    (variation : FiniteGaugeVariation)
    (hSupport :
      variation.slip ∈
        (program.completed.completion.approximation.tower.stage n).candidates.entries) :
    program.emittedActivity n variation =
      program.energy.zero /\
    program.energy.energySq
      (program.emittedActivity n variation) = 0 :=
  ⟨CompiledGalerkinEnergySq.supported_data_activity_eq_zero_on_support
      program
      n
      variation
      hSupport,
    CompiledGalerkinEnergySq.supported_data_energySq_eq_zero
      program
      n
      variation
      hSupport⟩

end CompiledGalerkinEnergySq

structure CompiledSPDGalerkinEnergySq
    (range : AdmissibleRange)
    (scale : ApproximationScale)
    (action : FiniteGaugeAction) (path : FiniteGaugePath) where
  completed :
    CompletedResidualWeierstrassTower range scale action path
  spd :
    SPDGalerkinActivity
  emittedActivity :
    Nat -> FiniteGaugeVariation -> spd.form.V
  emittedEnergySq_matches_terminalResidualMagnitude :
    forall n variation,
      (SPDGalerkinActivity.toEnergySqCertificate spd).energySq
        (emittedActivity n variation) =
        intActivityMagnitude
          ((completed.residualTower.stageTrace n).terminalResidual variation)

namespace CompiledSPDGalerkinEnergySq

def toCompiledGalerkinEnergySq
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (program :
      CompiledSPDGalerkinEnergySq range scale action path) :
    CompiledGalerkinEnergySq range scale action path where
  completed := program.completed
  Activity := program.spd.form.V
  energy := SPDGalerkinActivity.toEnergySqCertificate program.spd
  emittedActivity := program.emittedActivity
  emittedEnergySq_matches_terminalResidualMagnitude :=
    program.emittedEnergySq_matches_terminalResidualMagnitude

theorem supported_data_energySq_eq_zero
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (program :
      CompiledSPDGalerkinEnergySq range scale action path)
    (n : Nat)
    (variation : FiniteGaugeVariation)
    (hSupport :
      variation.slip ∈
        (program.completed.completion.approximation.tower.stage n).candidates.entries) :
    (SPDGalerkinActivity.toEnergySqCertificate program.spd).energySq
      (program.emittedActivity n variation) = 0 :=
  by
    have hMatch :=
      program.emittedEnergySq_matches_terminalResidualMagnitude n variation
    have hTerminal :=
      CompletedResidualWeierstrassTower.stageTrace_solves_elephant_support
        program.completed
        n
        variation
        hSupport
    rw [hMatch, hTerminal]
    exact intActivityMagnitude_zero

theorem supported_data_activity_eq_zero_of_spd
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (program :
      CompiledSPDGalerkinEnergySq range scale action path)
    (n : Nat)
    (variation : FiniteGaugeVariation)
    (hSupport :
      variation.slip ∈
        (program.completed.completion.approximation.tower.stage n).candidates.entries) :
    program.emittedActivity n variation =
      program.spd.form.zero :=
  (SPDGalerkinActivity.toEnergySqCertificate program.spd).energySq_eq_zero_only_zero
    (program.emittedActivity n variation)
    (CompiledSPDGalerkinEnergySq.supported_data_energySq_eq_zero
      program
      n
      variation
      hSupport)

theorem supported_stage_collapses_of_spd
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (program :
      CompiledSPDGalerkinEnergySq range scale action path)
    (n : Nat)
    (variation : FiniteGaugeVariation)
    (hSupport :
      variation.slip ∈
        (program.completed.completion.approximation.tower.stage n).candidates.entries) :
    program.emittedActivity n variation =
      program.spd.form.zero /\
    (SPDGalerkinActivity.toEnergySqCertificate program.spd).energySq
      (program.emittedActivity n variation) = 0 :=
  ⟨CompiledSPDGalerkinEnergySq.supported_data_activity_eq_zero_of_spd
      program
      n
      variation
      hSupport,
    CompiledSPDGalerkinEnergySq.supported_data_energySq_eq_zero
      program
      n
      variation
      hSupport⟩

end CompiledSPDGalerkinEnergySq

def truthGalerkinBilinearForm : GalerkinBilinearForm where
  V := Unit
  zero := ()
  add := fun _ _ => ()
  neg := fun _ => ()
  smul := fun _ _ => ()
  a := fun _ _ => 0
  symmetric := by
    intro x y
    rfl
  add_left := by
    intro x y z
    rfl
  smul_left := by
    intro k x y
    simp
  zero_left := by
    intro x
    rfl
  nonnegative_diagonal := by
    intro x
    decide

def truthNaturalBoundary :
    NaturalBoundary truthGalerkinBilinearForm where
  boundary_terms_vanish := True
  boundary_terms_vanish_proof := trivial

def truthWhiteHoleLoadAnchor :
    WhiteHoleLoadAnchor truthGalerkinBilinearForm where
  trace := fun _ => ()
  load_is_anchor := rfl
  source_to_load := True
  source_to_load_proof := trivial

def truthNullspaceKilled :
    NullspaceKilled
      truthGalerkinBilinearForm
      truthNaturalBoundary
      truthWhiteHoleLoadAnchor where
  uses_natural_boundary := trivial
  uses_white_hole_load := trivial
  diagonal_zero_detects := by
    intro x h
    cases x
    rfl

def truthSPDGalerkinActivity : SPDGalerkinActivity :=
  SPDGalerkinActivity.naturalBoundary_whiteHoleLoadAnchor_implies_spd
    truthGalerkinBilinearForm
    truthNaturalBoundary
    truthWhiteHoleLoadAnchor
    truthNullspaceKilled

noncomputable def truthEnergySqCertificate :
    EnergySqCertificate truthSPDGalerkinActivity.form.V :=
  SPDGalerkinActivity.toEnergySqCertificate
    truthSPDGalerkinActivity

theorem truthEnergySq_zero_detector
    (x : truthSPDGalerkinActivity.form.V) :
    truthEnergySqCertificate.energySq x = 0 <->
      x = truthEnergySqCertificate.zero :=
  EnergySqCertificate.energySq_eq_zero_iff_eq_zero
    truthEnergySqCertificate
    x

end Measurement
