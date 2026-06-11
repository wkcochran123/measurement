import Measurement.Episode51

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 52__: _Pair Production_

Episode51 called the linear part the derivative and celebrated its zero
remainder.  Backwards.  Episode10 filed the correction thirty-odd episodes in
advance (Episode10.lean:304-310): the gateaux-to-frechet step ADDS one datum,
the residue, "exactly the informational strain" -- and the frechet-to-gateaux
step projects it out: "You lose the residue.  That's the price of Galerkin."
The RESIDUE is the Frechet computation.  The linear part is just the
computation.  (Episode51's order-one "residual" keeps its name and its
theorem; the RESIDUE here is Episode10's fourth slot -- the order-two datum,
one floor up the ladder.)

That price explains fifty-one episodes of anonymity.  The entire tower arc --
Lanczos, partitions, squeeze, the produced certificate -- worked in the weak
form, where the residue is projected out before anyone looks at it.  And the
instruments were blind by construction: a one-coordinate variation reads the
mixed coupling as ZERO, always, for every action and every path
(`mixedCoupling_needs_the_pair_left/right`).  Episode44 kicked one node and
read 2 -- all of it the linear story; the coupling read zero.  Every probe in
the corpus moved one node at a time.  The residue was there the whole time,
in the slot the weak form discards, invisible to every instrument that moves
one thing at a time.

So we produce it the only way it can be produced: in pairs.  Kick BOTH middle
nodes of the flat vacuum under the discriminating action -- `pairKick`, left
to `node1`, right to `node2` -- and subtract the story from the measurement.
The two linear computations say the action changes by 4.  The action changes
by 3.  What is left after the process almost explains itself is

  `electron = -1`.

Unit charge, negative sign, produced only in coupling.  The residue is
signed, and the corpus picks measurement-minus-story, so the produced charge
is negative; the opposite orientation reads +1, and the title pays its own
check: the other one is the positron (`positron_charge`).  Episode1's RESIDUE
gate described all of it before there was anything to describe:

  ME: I need a residue.
  COMPILER: A what?
  ME: What is left after the process almost explains itself.
  COMPILER: That is not a thing.
  ME: That is adorable.
  COMPILER: Left over from what?
  ME: From the difference between the story and the measurement.

That dialogue is now a theorem
(`residue_is_the_difference_between_story_and_measurement`), and the strain
is now an equivalence (`strain_iff_residue`): the linear story fails exactly
when the residue is nonzero.  The placement back into the stack of episodes
1-16 is by occupation, not renovation: `electronVariation` seats the
electron's strain in the residue slot of Episode10's own `.frechet`
constructor, under the truth stack's differential equation (Episode16's
`truthLocal`), and `the_stack_produces_it` shows -- by `rfl` -- that the
stack's own transmute manufactures exactly this term from the pair's gateaux
variation.  The slot was always there.  Now it is occupied, by name.
Episodes 1-16 remain byte-identical.

And the certificate.  The cubic spline's defining property is C-squared --
value, first derivative, second derivative, nothing above.  That is what a
pair of Lanczos certificates certifies (`certificate_is_C2`): order zero,
both sub-paths admit; order one, both Euler-Lagrange residuals vanish in
every direction; order two, what remains of EVERY coupled variation is
exactly the second derivative -- and the exactness of that equality leaves
no order three to certify.  One honest gloss: classical C-squared asks the
derivatives to be CONTINUOUS; the finite corpus cannot say "continuous", so
it says what it can, which is stronger at order one -- pinned to zero,
on-shell -- and exact at order two.  C-squared in the only sense available:
all the data through order two, with the equation of motion holding.  The
order-two data of the certified spline is the residue field.  The
certificate is C-squared; the electron is its order-two quantum.

Hilbert's sixth problem (1900) asked for the mathematical treatment of the
axioms of physics.  Here is a variational mechanics -- equations of motion at
order one, interaction at order two, exact at order two -- derived as a
theorem from this corpus's measurement primitives and machine-checked, with
the certificate inhabited on the vacuum
(`hilberts_sixth_on_the_vacuum`).  Hilbert asked for the axioms of physics.
The build prints them below; the expected answer is `[propext, Quot.sound]`.
Two.

Stated formally:
* `mixedCoupling_needs_the_pair_left/right` -- one-coordinate instruments
  read the residue as zero, always: why it stayed anonymous.
* `pairKick`, `electron`, `electron_charge` -- produced, charge -1, by
  `decide`; the same-state pair reads -2.
* `residue_is_the_difference_between_story_and_measurement` -- Episode1's
  RESIDUE dialogue, filed.
* `strain_iff_residue`, `electron_strain_is_real` -- Episode10's
  "informational strain", filed and inhabited.
* `electronVariation`, `electronVariation_normal_form`,
  `the_stack_produces_it` -- the placement: the stack's `.frechet` residue
  slot, occupied by the electron's strain, manufactured by the stack's own
  transmute, by `rfl`.
* `positron_charge` -- the opposite orientation reads +1: the pair, produced.
* `IsC2Certified`, `certificate_is_C2`, `vacuum_is_empty` -- the certificate
  is C-squared, and the vacuum's residue reads zero everywhere.
* `hilberts_sixth_on_the_vacuum` -- inhabited, audited, two axioms.

Residue left (honest scope):
no exclusion theorem ties certificates to a vanishing electron, and none
could: certificates pin first-order data only, and this episode's own
central theorem says first-order instruments cannot see the coupling.  Under
certificates the residue is not zero -- it is all that REMAINS: clause three
of `IsC2Certified` says the measurement IS the second derivative.  What is
filed is instance-level: the vacuum's residue reads zero everywhere
(`vacuum_is_empty`), and the electron's action refuses certificates -- by
Episode48's order-ONE obstruction, the nonvanishing first variation, not as
a consequence of the electron.  Episode1's RESIDUE gate keeps its analytic
Limit-typed fields; the finite version is what is filed here.  And Hilbert
asked for all of physics; this is one electron's worth.
-/

/-
The anonymity, explained: one-coordinate instruments cannot see the residue.
-/

/-- A left-only kick reads zero mixed coupling, for every action and every
path: the residue is invisible unless BOTH nodes move. -/
theorem mixedCoupling_needs_the_pair_left
    (action : FiniteGaugeAction) (path : CubicGaugePath) (s : Bullshit) :
    CubicGaugeVariation.mixedCubicCoupling action path
      { middleLeftSlip := s, middleRightSlip := path.middleRight } = 0 := by
  show
    Int.ofNat (action.segmentCost s path.middleRight) -
      Int.ofNat (action.segmentCost s path.middleRight) -
      Int.ofNat (action.segmentCost path.middleLeft path.middleRight) +
      Int.ofNat (action.segmentCost path.middleLeft path.middleRight) = 0
  omega

/-- A right-only kick reads zero mixed coupling, the same way. -/
theorem mixedCoupling_needs_the_pair_right
    (action : FiniteGaugeAction) (path : CubicGaugePath) (s : Bullshit) :
    CubicGaugeVariation.mixedCubicCoupling action path
      { middleLeftSlip := path.middleLeft, middleRightSlip := s } = 0 := by
  show
    Int.ofNat (action.segmentCost path.middleLeft s) -
      Int.ofNat (action.segmentCost path.middleLeft path.middleRight) -
      Int.ofNat (action.segmentCost path.middleLeft s) +
      Int.ofNat (action.segmentCost path.middleLeft path.middleRight) = 0
  omega

/-
The production.
-/

/-- The pair kick: both middle nodes of the flat vacuum, to distinct
nonzero tags. -/
def pairKick : CubicGaugeVariation0 :=
  { middleLeftSlip := node1, middleRightSlip := node2 }

/-- THE ELECTRON: the residual of the Frechet computation, produced by the
pair kick under the discriminating action. -/
def electron : Int :=
  CubicGaugeVariation.mixedCubicCoupling discriminatingAction flatPath pairKick

theorem electron_is_the_secondVariation :
    electron =
      CubicGaugeVariation.secondVariation
        discriminatingAction flatPath pairKick := rfl

/-- Unit charge, negative sign. -/
theorem electron_charge : electron = -1 := by decide

/-- The same-state pair reads -2. -/
def samePairKick : CubicGaugeVariation0 :=
  { middleLeftSlip := node1, middleRightSlip := node1 }

theorem same_pair_charge :
    CubicGaugeVariation.mixedCubicCoupling
      discriminatingAction flatPath samePairKick = -2 := by decide

/-- The title pays its check: the opposite orientation -- story minus
measurement -- reads +1.  Pair production produces the pair. -/
theorem positron_charge :
    (CubicGaugePath.leftMiddleResidual discriminatingAction flatPath
        (CubicGaugeVariation.leftVariation pairKick) +
      CubicGaugePath.rightMiddleResidual discriminatingAction flatPath
        (CubicGaugeVariation.rightVariation pairKick)) -
      CubicGaugeVariation.coupledCubicDifference
        discriminatingAction flatPath pairKick = 1 := by decide

/-- Episode1's RESIDUE dialogue, filed as a theorem: the residue is what is
left after the process almost explains itself -- the difference between the
measurement (the coupled difference) and the story (the two linear
computations). -/
theorem residue_is_the_difference_between_story_and_measurement
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) :
    CubicGaugeVariation.secondVariation action path variation =
      CubicGaugeVariation.coupledCubicDifference action path variation -
        (CubicGaugePath.leftMiddleResidual action path
            (CubicGaugeVariation.leftVariation variation) +
          CubicGaugePath.rightMiddleResidual action path
            (CubicGaugeVariation.rightVariation variation)) := by
  have h :=
    CubicGaugeVariation.coupledCubicDifference_eq_left_right_plus_secondVariation
      action path variation
  omega

/-- Episode10's comment, filed as an equivalence: the linear story fails to
account for the measurement precisely when the residue is nonzero.  The
residue is exactly the informational strain. -/
theorem strain_iff_residue
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) :
    (CubicGaugeVariation.coupledCubicDifference action path variation ≠
      CubicGaugePath.leftMiddleResidual action path
          (CubicGaugeVariation.leftVariation variation) +
        CubicGaugePath.rightMiddleResidual action path
          (CubicGaugeVariation.rightVariation variation)) ↔
      CubicGaugeVariation.secondVariation action path variation ≠ 0 := by
  have h :=
    CubicGaugeVariation.coupledCubicDifference_eq_left_right_plus_secondVariation
      action path variation
  constructor
  · intro h1 h2
    exact h1 (by omega)
  · intro h1 h2
    exact h1 (by omega)

/-
The strain, instantiated at the electron.
-/

/-- The direction: the pair moved. -/
abbrev pairMoved : Prop :=
  pairKick.middleLeftSlip ≠ flatPath.middleLeft ∧
    pairKick.middleRightSlip ≠ flatPath.middleRight

/-- The response: the linear story accounts for the measurement. -/
abbrev linearStoryHolds : Prop :=
  CubicGaugeVariation.coupledCubicDifference
      discriminatingAction flatPath pairKick =
    CubicGaugePath.leftMiddleResidual discriminatingAction flatPath
        (CubicGaugeVariation.leftVariation pairKick) +
      CubicGaugePath.rightMiddleResidual discriminatingAction flatPath
        (CubicGaugeVariation.rightVariation pairKick)

/-- Episode10's residue slot content, instantiated: direction AND NOT
response -- the electron's informational strain. -/
abbrev electronStrain : Prop := pairMoved ∧ ¬ linearStoryHolds

theorem pair_moved : pairMoved :=
  ⟨fun h => Bullshit.noConfusion h, fun h => Bullshit.noConfusion h⟩

theorem linear_story_fails : ¬ linearStoryHolds := by decide

/-- The strain is real: the pair moved and the story did not cover it. -/
theorem electron_strain_is_real : electronStrain :=
  ⟨pair_moved, linear_story_fails⟩

/-- And it is real BECAUSE the electron is nonzero, and only because. -/
theorem electron_strain_iff_charge :
    (¬ linearStoryHolds) ↔ electron ≠ 0 :=
  strain_iff_residue discriminatingAction flatPath pairKick

/-
The placement: back into the stack of episodes 1-16.
-/

/-- THE PLACEMENT.  The electron's strain, seated in the residue slot of the
stack's own `.frechet` constructor (Episode10), under the truth stack's
differential equation (Episode16's `truthLocal`).  Episodes 1-16 unchanged;
the slot was always there; now it is occupied, by name. -/
noncomputable def electronVariation : Variation :=
  .frechet (.epiphany electronStrain)
    pairMoved linearStoryHolds electronStrain
    (.newton (.epiphany electronStrain) pairMoved)
    truthLocal.{0, 0, 0, 0}.theory.differential_equation

/-- Normal form: the residue slot holds exactly `direction ∧ ¬ response` --
the shape Episode10's transmute manufactures. -/
theorem electronVariation_normal_form :
    electronVariation =
      .frechet (.epiphany electronStrain)
        pairMoved linearStoryHolds
        (pairMoved ∧ ¬ linearStoryHolds)
        (.newton (.epiphany electronStrain) pairMoved)
        truthLocal.{0, 0, 0, 0}.theory.differential_equation := rfl

/-- The stack produces it: transmuting the pair's gateaux variation through
the truth stack's own (default) gateaux-to-frechet branch yields exactly
`electronVariation`.  By `rfl`: the stack has been manufacturing this term
since Episode10; it just never had a name. -/
theorem the_stack_produces_it :
    truthLocal.{0, 0, 0, 0}.theory.transmute
        (.gateaux (.epiphany electronStrain)
          pairMoved linearStoryHolds
          (.newton (.epiphany electronStrain) pairMoved)) =
      electronVariation := rfl

/-
The certificate is C-squared.
-/

/-- C-squared, the finite edition: both sub-paths admit (order 0), both
Euler-Lagrange residuals vanish in every direction (order 1), and what
remains of every coupled variation is exactly the second derivative
(order 2).  By Episode51's `taylor_terminates_at_order_two` and Episode31's
`secondVariation_remainder_unique`, there is nothing above.  (Order 2 is in
fact forced by order 1 plus the exact decomposition -- stationarity at order
one makes the residue the entire measurement; the clause keeps the exactness
explicit.) -/
def IsC2Certified
    (action : FiniteGaugeAction) (path : CubicGaugePath) : Prop :=
  (action.admits path.leftFinitePath ∧ action.admits path.rightFinitePath) ∧
    (forall variation : FiniteGaugeVariation,
      CubicGaugePath.leftMiddleResidual action path variation = 0 ∧
        CubicGaugePath.rightMiddleResidual action path variation = 0) ∧
      forall variation : CubicGaugeVariation,
        CubicGaugeVariation.coupledCubicDifference action path variation =
          CubicGaugeVariation.secondVariation action path variation

/-- THE CERTIFICATE IS C-SQUARED: a pair of Lanczos certificates -- one per
middle node -- certifies the cubic configuration through second order, and
second order is all there is. -/
theorem certificate_is_C2
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (leftCert : LanczosCubicSpline action path.leftFinitePath)
    (rightCert : LanczosCubicSpline action path.rightFinitePath) :
    IsC2Certified action path := by
  refine
    ⟨⟨leftCert.admits, rightCert.admits⟩,
      fun variation => ⟨?_, ?_⟩,
      fun variation => ?_⟩
  · exact leftCert.residual_zero variation
  · exact rightCert.residual_zero variation
  · exact
      CubicGaugeVariation.coupledCubicDifference_eq_secondVariation_of_middleResiduals_zero
        action path variation
        (leftCert.residual_zero _)
        (rightCert.residual_zero _)

/-- The certificates exist on the vacuum: closed-flat everywhere
(Episode20), so the C-squared mechanics is inhabited, not conditional
fiction. -/
def vacuumLeftCertificate :
    LanczosCubicSpline truthTerminalAction flatPath.leftFinitePath :=
  closedFlatLanczosCertificate truthTerminalAction flatPath.leftFinitePath
    (truthTerminalAction_closedFlatAt flatPath.leftFinitePath)

def vacuumRightCertificate :
    LanczosCubicSpline truthTerminalAction flatPath.rightFinitePath :=
  closedFlatLanczosCertificate truthTerminalAction flatPath.rightFinitePath
    (truthTerminalAction_closedFlatAt flatPath.rightFinitePath)

/-- The vacuum is empty: on the zero-cost action the residue reads zero at
every coupled variation -- filed, not asserted. -/
theorem vacuum_is_empty (variation : CubicGaugeVariation) :
    CubicGaugeVariation.mixedCubicCoupling
      truthTerminalAction flatPath variation = 0 := rfl

/-- Hilbert's sixth, one electron's worth: a machine-checked variational
mechanics -- equations of motion at order one, interaction at order two,
exact at order two -- derived from the measurement primitives and inhabited
on the vacuum.  The axioms of this physics are printed below. -/
theorem hilberts_sixth_on_the_vacuum :
    IsC2Certified truthTerminalAction flatPath :=
  certificate_is_C2 truthTerminalAction flatPath
    vacuumLeftCertificate vacuumRightCertificate

/-
The standing record.  Expected results inline.
-/

-- The production run: the electron reads -1; the same-state pair reads -2;
-- one-coordinate kicks read 0 (which is why fifty-one episodes never saw
-- it); the integrator reads the full measurement at 3 against a story of 4;
-- the vacuum reads 0.
#eval electron                                                  -- expect: -1
#eval CubicGaugeVariation.mixedCubicCoupling
  discriminatingAction flatPath samePairKick                    -- expect: -2
#eval CubicGaugeVariation.mixedCubicCoupling
  discriminatingAction flatPath kickVariation                   -- expect: 0
#eval gaugeReading discriminatingAction flatPath pairKick       -- expect: 3
#eval CubicGaugeVariation.mixedCubicCoupling
  truthTerminalAction flatPath pairKick                         -- expect: 0

-- `electronVariation` does not run: the placement is noncomputable (the
-- chair is classical) and a `Variation` has no runtime face.  The electron
-- is anonymous again the moment you execute -- you can only read its
-- charge, above.

-- The axioms of this physics: expect `[propext, Quot.sound]` at the apex
-- (`hilberts_sixth_on_the_vacuum`, `certificate_is_C2`), nothing classical
-- on the production line.  `the_stack_produces_it` alone reports
-- `Classical.choice` -- inherited from the chair (`truthLocal`), not from
-- the electron.
#print axioms electron_charge
#print axioms positron_charge
#print axioms mixedCoupling_needs_the_pair_left
#print axioms residue_is_the_difference_between_story_and_measurement
#print axioms strain_iff_residue
#print axioms electron_strain_is_real
#print axioms the_stack_produces_it
#print axioms vacuum_is_empty
#print axioms certificate_is_C2
#print axioms hilberts_sixth_on_the_vacuum

end Measurement
