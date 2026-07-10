import Measurement.Episode52

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 53__: _The Geometric Program_

The paper lane (papers/hilbert_6) names the next target: the geometric side
must be a PROGRAM, not a bundle of certificates lying near each other.
Episode39 built the kernel -- SPD energy, Hilbert door, white-hole/load
anchor, decorations, one conserved invariant -- but it sits in the corpus as
an object you can point at, not an object you can RUN something against.
This episode packages it as the program the boundary compiler (Episode54)
will consume.

What earns the word "geometric" here, honestly: Episode35 proved that the
SAME stiffness operator changes certificate status when the apparatus
changes the boundary -- the anchor pin turns a closed finite differential
into a zero field.  Energy plus boundary data determining which modes can
certify is the finite shadow of geometry telling matter how to behave.  That
shadow, no more: the claim gate stays at "GR-like geometric program
wrapper", and general relativity is CLAIMED in this corpus only with
"finite" and "shadow" attached.  (Episode1 mentions it bare, satirically;
mentions are free, claims are gated.)

The structure is conservative on purpose: it wraps the kernel and RE-EXPOSES
its door and anchor with coherence proofs (`rfl` at the instance).  The
point of the duplication is the program surface -- Episode54's compiler reads
the door and anchor fields, and the coherence fields guarantee it is reading
the kernel's own boundary, not a stapled-on impostor.

Stated formally:
* `GeometricProgram` -- kernel + door + anchor + two coherence proofs.
* `threeRungGeometricProgram` -- the concrete instance over Episode39's
  capstone, all coherence by `rfl`.
* `threeRungGeometricProgram_invariant_zero_detects` -- the acceptance
  theorem: coercivity reads through the program surface.
* `threeRungGeometricProgram_source_is_white_hole` -- the boundary is
  genuinely there to be read: the program's anchor source is a white hole
  over spacetime.

Residue left (honest scope):
the program does not yet GENERATE anything -- it is the readable side of a
compiler whose other side is Episode54.  And it is not standard GR: it is
finite energy-and-boundary geometry, the part of GR the apparatus can
certify -- the boundary determines the certificate status of modes, and a
boundary change changes the physics (Episode35, now wearing its program
clothes).
-/

/-- The geometric program: Episode39's kernel with its Hilbert door and
white-hole/load anchor re-exposed as program surfaces, plus coherence proofs
that the surfaces are the kernel's own. -/
structure GeometricProgram where
  kernel : UniverseKernel
  door : HilbertCompletionDoor kernel.spd.form.V
  anchor : CompilerWhiteHoleLoadAnchor kernel.spd.form
  door_matches_kernel : door = kernel.door
  anchor_matches_kernel : anchor = kernel.compilerAnchor

namespace GeometricProgram

/-- The program's invariant is the kernel's. -/
def invariant (P : GeometricProgram) : P.kernel.spd.form.V -> Nat :=
  P.kernel.invariant

/-- Coercivity reads through the program surface: the invariant detects
zero. -/
theorem invariant_zero_detects
    (P : GeometricProgram) (x : P.kernel.spd.form.V)
    (h : P.invariant x = 0) : x = P.kernel.spd.form.zero :=
  UniverseKernel.invariant_zero_detects P.kernel x h

/-- The boundary is there to be read: the program's anchor source is a white
hole over spacetime (via the coherence field and Episode39's re-export). -/
theorem source_is_white_hole (P : GeometricProgram) :
    P.anchor.source =
      .white_hole P.anchor.anchorFact P.anchor.anchorType
        P.anchor.previous :=
  P.anchor.source_is_white_hole

end GeometricProgram

/-- The concrete geometric program: Episode39's capstone kernel, coherence
by `rfl`. -/
noncomputable def threeRungGeometricProgram : GeometricProgram where
  kernel := threeRungUniverse
  door := threeRungUniverse.door
  anchor := threeRungUniverse.compilerAnchor
  door_matches_kernel := rfl
  anchor_matches_kernel := rfl

/-- Acceptance: the three-rung program's invariant detects zero. -/
theorem threeRungGeometricProgram_invariant_zero_detects
    (x : threeRungGeometricProgram.kernel.spd.form.V)
    (h : threeRungGeometricProgram.invariant x = 0) :
    x = threeRungGeometricProgram.kernel.spd.form.zero :=
  threeRungGeometricProgram.invariant_zero_detects x h

/-- Acceptance: the three-rung program's boundary is a white hole. -/
theorem threeRungGeometricProgram_source_is_white_hole :
    threeRungGeometricProgram.anchor.source =
      .white_hole Fact.Truth Unit (.einstein Fact.Truth) :=
  rfl

/-
The standing record.
-/

-- Build-true `[propext, Quot.sound]` on all three, choice-FREE.  (Earlier audits
-- expected `Classical.choice` here, reading the geometric side's noncomputable
-- door -- Episode28's positive-definiteness route -- as classical.  The build
-- shows otherwise: noncomputable is Quot/funext-borne, not the choice axiom.
-- The geometric chair is noncomputable but choice-free, exactly like the
-- gauge-side production line (Episodes 48-52).)
#print axioms GeometricProgram.invariant_zero_detects
#print axioms threeRungGeometricProgram_invariant_zero_detects
#print axioms threeRungGeometricProgram_source_is_white_hole

end Measurement
