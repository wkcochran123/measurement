import Measurement.Episode53

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 54__: _The Boundary Compiler_

The gauge program must not appear by hand.  Episode52 produced the
electron against a hand-picked action (Episode44's `discriminatingAction`);
Episode53 packaged the geometric program; this
episode closes the gap with a compiler that READS the gauge action off the
geometric boundary.

The read is one number: `boundaryDepth`, the constructor depth of a path
above the `.einstein` vacuum -- and we read it, as a charge, on both sides
of the anchor.  One honesty note up front: the anchor TYPE mandates a
white-hole source (`source_is_white_hole`, Episode28), so every geometric
program's source reads depth at least 1 -- the depth-0 read belongs to the
INTERIOR (`previous`), and the two channels are the two sides of the one
mandatory boundary, not white-hole-versus-no-white-hole.  The interior of
the three-rung anchor is the vacuum itself (depth 0) and compiles to the
ZERO action -- extensionally `truthTerminalAction`, the certified, empty
vacuum channel.  The source is a white hole over the vacuum (depth 1) and
compiles to unit crossing costs -- DEFINITIONALLY `discriminatingAction`,
the obstruction-bearing, electron-producing excitation channel.  ONE
compiler, applied to the two sides of the same boundary, generates BOTH
channels of the gauge program:

  interior (depth 0)  --compile-->  vacuum action   (certificates, no matter)
  boundary (depth 1)  --compile-->  discriminating  (matter, no certificates)

The generation theorem is `rfl`: `boundaryReadAction threeRungGeometricProgram`
IS `discriminatingAction`, term for term, because the boundary charge
evaluates to 1 by computation.  And the residue follows without a new
calculation: the compiled action produces the electron
(`compiled_action_produces_the_electron`, by `electron_charge` through the
`rfl`).  The geometric excursion is the reason the gauge cost is nonzero;
no white hole, no electron.

Stated formally:
* `SpaceTimePath.boundaryDepth` -- the one-number boundary read.
* `BoundaryGaugeCompiler` -- the compiler surface (action, path, pair).
* `boundaryReadAction`, `boundaryReadVacuumAction` -- the genuine reads:
  crossing cost = boundary depth at the source / in the interior.
* `threeRungBoundaryCompiler` -- the compiler instance whose `compileAction`
  is the boundary read, not a constant.
* `threeRungCompiler_generates_discriminatingAction` -- the generation
  theorem, by `rfl`.
* `threeRung_vacuum_compiles_to_zero_action` -- the interior compiles to
  `truthTerminalAction`, by funext (depth 0 makes every crossing free).
* `compiled_action_produces_the_electron` -- the GR-shaped program creates
  the residue of the QED-shaped program: the compiled action's pair-kick
  coupling reads -1.

Residue left (honest scope):
the compiler reads one number from the boundary.  That is the honest size
of the claim: the gauge action's STRENGTH is generated from geometric
data; its SHAPE (the tag quotient) is still the apparatus's own
three-constructor structure (Episode44), not derived from the kernel.
Deriving the quotient itself from the anchor's sector data is the next
upgrade surface.  The compiler also fixes path and pair to the flat
vacuum and the pair kick; freeing those is mechanical.
-/

namespace SpaceTimePath

/-- The boundary read: constructor depth above the `.einstein` vacuum.
Zero exactly on the vacuum; each white hole, black hole, or geodesic
adds one. -/
def boundaryDepth : SpaceTimePath -> Nat
  | .einstein _ => 0
  | .white_hole _ _ prev => boundaryDepth prev + 1
  | .blackhole _ _ prev => boundaryDepth prev + 1
  | .geodesic _ _ _ _ p1 p2 =>
      max (boundaryDepth p1) (boundaryDepth p2) + 1

end SpaceTimePath

/-- The compiler surface: a boundary gauge compiler turns a geometric
program into the data of a gauge experiment -- both channels: the
excitation action read at the boundary, and the vacuum action read in the
interior. -/
structure BoundaryGaugeCompiler where
  compileAction : GeometricProgram -> FiniteGaugeAction0
  compileVacuumAction : GeometricProgram -> FiniteGaugeAction0
  compilePath : GeometricProgram -> CubicGaugePath0
  compilePair : GeometricProgram -> CubicGaugeVariation0

/-- The genuine boundary read, excitation channel: a tag crossing costs the
boundary depth of the anchor's SOURCE.  Depth 1 at a white hole over the
vacuum makes this the unit discriminating cost. -/
def boundaryReadAction (P : GeometricProgram) : FiniteGaugeAction0 :=
  { segmentCost := fun x y =>
      if tag x = tag y then 0
      else SpaceTimePath.boundaryDepth P.anchor.source }

/-- The genuine boundary read, vacuum channel: a tag crossing costs the
boundary depth of the anchor's INTERIOR (`previous`).  Depth 0 on the
vacuum makes every crossing free. -/
def boundaryReadVacuumAction (P : GeometricProgram) : FiniteGaugeAction0 :=
  { segmentCost := fun x y =>
      if tag x = tag y then 0
      else SpaceTimePath.boundaryDepth P.anchor.previous }

/-- The three-rung boundary compiler: `compileAction` is the boundary read,
not a constant.  Path and pair are the flat vacuum and the pair kick. -/
noncomputable def threeRungBoundaryCompiler : BoundaryGaugeCompiler where
  compileAction := boundaryReadAction
  compileVacuumAction := boundaryReadVacuumAction
  compilePath := fun _ => flatPath
  compilePair := fun _ => pairKick

/-- The boundary charge -- depth, read as charge; one number, two names,
declared here -- of the three-rung program is one: the source is a white
hole over the vacuum. -/
theorem threeRung_boundaryCharge_one :
    SpaceTimePath.boundaryDepth threeRungGeometricProgram.anchor.source = 1 :=
  rfl

/-- The interior charge is zero: `previous` is the vacuum itself. -/
theorem threeRung_interiorCharge_zero :
    SpaceTimePath.boundaryDepth threeRungGeometricProgram.anchor.previous = 0 :=
  rfl

/-- THE GENERATION THEOREM, by `rfl`: the compiler applied to the geometric
program IS the discriminating action.  Episode52's hand-picked action was
the boundary read all along. -/
theorem threeRungCompiler_generates_discriminatingAction :
    threeRungBoundaryCompiler.compileAction threeRungGeometricProgram =
      discriminatingAction := rfl

/-- The interior compiles to the zero action: extensionally
`truthTerminalAction`.  Depth zero makes every tag crossing free, so the
vacuum channel certifies (Episode52's `hilberts_sixth_on_the_vacuum`)
against exactly the action the interior generates. -/
theorem threeRung_vacuum_compiles_to_zero_action :
    boundaryReadVacuumAction threeRungGeometricProgram =
      truthTerminalAction := by
  have h :
      (boundaryReadVacuumAction threeRungGeometricProgram).segmentCost =
        truthTerminalAction.segmentCost := by
    funext x y
    show (if tag x = tag y then (0 : Nat) else 0) = 0
    exact ite_self 0
  exact congrArg FiniteGaugeAction.mk h

/-- The GR-shaped program creates the residue of the QED-shaped program:
the action the boundary compiler generates produces the electron at the
pair kick.  No new calculation -- `electron_charge`, read through the
generation `rfl`. -/
theorem compiled_action_produces_the_electron :
    CubicGaugeVariation.mixedCubicCoupling
      (threeRungBoundaryCompiler.compileAction threeRungGeometricProgram)
      (threeRungBoundaryCompiler.compilePath threeRungGeometricProgram)
      (threeRungBoundaryCompiler.compilePair threeRungGeometricProgram) =
      -1 :=
  electron_charge

/-
The standing record.
-/

-- Build-true `[propext, Quot.sound]`, choice-FREE.  (Earlier audits expected
-- `Classical.choice` where the geometric chair is referenced, reading the
-- program's noncomputability as classical; it is not -- noncomputable is
-- Quot/funext-borne, not the choice axiom.)  The generation itself adds nothing.
#print axioms threeRungCompiler_generates_discriminatingAction
#print axioms threeRung_vacuum_compiles_to_zero_action
#print axioms compiled_action_produces_the_electron

end Measurement
