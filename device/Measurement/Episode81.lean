import Measurement.Episode80

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-!
__EPISODE 81__: _distinguished_distinguishable_

The ladder is a loop.

`DISTINGUISHABLE` (Episode1) was the first rung: the inside ability to tell one
carried mark from another -- a single bit, same or different, the first thing
the apparatus can do.  `DISTINGUISHED` (Episode76) is the last rung: the outside
receipt, the boundary obstruction read by the on/off apparatus as a
`BoundarySignal`.  This episode ties the last rung back to the first at the one
carrier they share.

The hinge is orthogonality.  Episode56 split the carrier into a geometric (GR)
sector and a gauge (QED) sector with the cross pairing zero by construction;
Episode57 read that orthogonality as the obstruction that closes the interior and
forces the residue to read at the boundary.  So:

* QED is perpendicular to GR : `threeRungCertificateSplit.orthogonal` (the dot is `0`);
* the three-rung carrier is `DISTINGUISHABLE` inside : `rung3Distinguishable`;
* the same carrier is `DISTINGUISHED` outside, and the outside reads `on`.

`distinguished_distinguishable` bundles these: the last rung rests on the first,
with orthogonality the hinge.  `binary_is_enough` reads off the corollary -- the
whole measurement is one two-valued boundary signal, `on` and distinct from
`off`, with no magnitude for any requested depth to refine.

Honest scope, carried verbatim from Episodes 56-57 and 75-76: "QED perpendicular
to GR" is the finite split-carrier orthogonality, by type, not a claim that the
standard physical theories are perpendicular; the boundary balance is the finite
Einstein/Navier-Stokes-shaped identity, not the field equations or the law of
flow.  This is the project-native loop, nothing larger.
-/

/-- The measurement bit: the single two-valued signal the `DISTINGUISHED`
capstone returns to the outside reader. -/
noncomputable def measurementBit : BoundarySignal :=
  DISTINGUISHED_GODEL_SENTENCE.outside

theorem measurementBit_on : measurementBit = BoundarySignal.on :=
  distinguished_boundary_signal_on

/-- QED is perpendicular to GR at the three-rung carrier: the gauge sector is
orthogonal to the geometric sector in the split pairing.  (Finite split-carrier
orthogonality, not the standard physical theories.) -/
theorem qed_perp_gr :
    threeRungCertificateSplit.dotH
        threeRungCertificateSplit.geometric
        threeRungCertificateSplit.gauge = 0 :=
  threeRungCertificateSplit.orthogonal

/-- The bridge.  The one three-rung carrier is `DISTINGUISHABLE` inside (the
first rung -- it can tell its marks apart) and `DISTINGUISHED` outside (the last
rung -- the boundary obstruction reads as a single on/off bit); the
orthogonality QED-perp-GR is the hinge that closes the interior and forces the
outside reading.  The ladder's last rung rests on its first. -/
theorem distinguished_distinguishable :
    Nonempty (DISTINGUISHABLE.{0, 0} Rung3 rung3Carrier) ∧
      threeRungCertificateSplit.dotH
          threeRungCertificateSplit.geometric
          threeRungCertificateSplit.gauge = 0 ∧
      ¬ HasInteriorScalarMixedCertificate
          (cliffordOfSplit threeRungCertificateSplit)
          threeRungCertificateSplit.geometric
          threeRungCertificateSplit.gauge ∧
      measurementBit = BoundarySignal.on :=
  ⟨⟨rung3Distinguishable⟩,
    threeRungCertificateSplit.orthogonal,
    threeRung_no_interior_mixed_certificate,
    measurementBit_on⟩

/-- Binary is enough.  The whole measurement is the single boundary signal, and
it reads `on` -- a genuine two-valued bit, `on` distinct from `off`.  There is no
magnitude for any requested depth to refine: the measurement is the bit. -/
theorem binary_is_enough :
    measurementBit = BoundarySignal.on ∧
      BoundarySignal.on ≠ BoundarySignal.off :=
  ⟨measurementBit_on, BoundarySignal.on_ne_off⟩

/-
The standing record.  Expect the chair -- `[propext, Classical.choice, Quot.sound]`
-- inherited through the noncomputable `DISTINGUISHED` capstone, exactly as
Episode76.
-/
#print axioms measurementBit_on
#print axioms distinguished_distinguishable
#print axioms binary_is_enough

end Measurement
