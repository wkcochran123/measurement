import Measurement.SupportingMeasurements.EntropyLadder

/-! # SobolevTriangle — the triangle inequality in the Sobolev reading, and
the lengthening of the triangle under entropic computation.

COMMISSION (operator, 2026-08-16 01:25, direct): "give me a proof on the
triangle inequality and the sobolev norm showing the expected lengthening
of the triangle due to entropic computation."

THE OBJECTS: sides of the triangle are grid signals at refinement n —
the uniform probe u (the smooth side), the alternating probe a (the rough
side), and their sum u+a (the third side, closing the triangle). The
SOBOLEV READING of a side is its energy under the Dirac difference rows,
‖A v‖² — exact integers, the discrete H¹-type seminorm energy this corpus
computes everywhere (WeakDiracGalerkin's own register).

TWO THEOREM FAMILIES, kernel-decided per rung:

  * `cauchy_schwarz_ladder` — the integer CONTENT of the triangle
    inequality in the Sobolev reading: ⟨Au, Aa⟩² ≤ ‖Au‖²·‖Aa‖² at every
    rung. (Classically, Cauchy–Schwarz is exactly what makes
    ‖A(u+a)‖ ≤ ‖Au‖ + ‖Aa‖ hold; the square-root step lives in the real
    reading, so the kernel holds the squared form — the inequality's whole
    integer substance — and the header states the classical equivalence
    rather than smuggling a real number into a theorem.)
    Additionally `triangle_energy_ladder` verifies the parallelogram-law
    consequence directly in integers: ‖A(u+a)‖² ≤ 2(‖Au‖² + ‖Aa‖²).

  * `perimeter_lengthens_with_entropy` — THE LENGTHENING: the Sobolev
    perimeter reading of the triangle (sum of the three side energies)
    strictly increases at every rung of the ladder — AND, in the same
    conjunction, the entropy step holds at that rung (EntropyLadder's
    integer reduction). The triangle lengthens along exactly the index
    where the spectrum's Shannon entropy provably rises: the lengthening
    rides the entropic computation, rung for rung, both facts decided by
    the same kernel. ("Due to" is carried as this proven co-occurrence on
    the shared refinement index — the same computation that refines is the
    computation whose entropy rises — not as a separate causation theorem;
    the header says so plainly.)

THE HONEST PICTURE, assembled from receipts: the triangle's VERTICES never
move (the probes are the same signals, sampled finer); its Sobolev-read
sides lengthen anyway, because the reading is a count and the refining
computation recounts — and the entropy of that computation's spectrum
rises with every rung, by theorem. The triangle inequality never breaks
while every side grows: geometry keeps its law, the reading pays the
entropic bill. Nothing moves; everything lengthens; the inequality holds.

NOT CLAIMED: any continuum norm (the reading is the discrete seminorm
energy, exact integers); any physical length, spacetime, or cosmology;
causation beyond the proven shared-index co-occurrence. -/

namespace Measurement.WeakDiracGalerkin.SobolevTriangle

open Measurement.WeakDiracGalerkin
open Measurement.WeakDiracGalerkin.ConditionEntropy
open Measurement.WeakDiracGalerkin.EntropyLadder

/-- The image of a side under the Dirac rows at rung n. -/
def sideImage (n : Nat) (v : Vec) : Vec := matrixApply (diracRowsN n) v

/-- The Sobolev reading (energy) of a side at rung n: ‖A v‖². -/
def sideEnergy (n : Nat) (v : Vec) : Int := energySq (diracRowsN n) v

/-- The third side closes the triangle: u + a componentwise. -/
def thirdSide (n : Nat) : Vec := add (uniformProbe n) (alternatingProbe n)

/-- Cross term ⟨Au, Aa⟩ at rung n. -/
def crossTerm (n : Nat) : Int :=
  dot (sideImage n (uniformProbe n)) (sideImage n (alternatingProbe n))

/-- Cauchy–Schwarz in the Sobolev reading, per rung: the exact integer
    content of the triangle inequality ‖A(u+a)‖ ≤ ‖Au‖ + ‖Aa‖. -/
def csHolds (n : Nat) : Bool :=
  crossTerm n * crossTerm n ≤
    sideEnergy n (uniformProbe n) * sideEnergy n (alternatingProbe n)

theorem cauchy_schwarz_ladder :
    csHolds 2 = true ∧ csHolds 3 = true ∧ csHolds 4 = true ∧
    csHolds 5 = true ∧ csHolds 6 = true ∧ csHolds 7 = true ∧
    csHolds 8 = true := by decide

#print axioms cauchy_schwarz_ladder

/-- The parallelogram-law consequence, held directly in integers:
    ‖A(u+a)‖² ≤ 2(‖Au‖² + ‖Aa‖²) per rung. -/
def triEnergyHolds (n : Nat) : Bool :=
  sideEnergy n (thirdSide n) ≤
    2 * (sideEnergy n (uniformProbe n) + sideEnergy n (alternatingProbe n))

theorem triangle_energy_ladder :
    triEnergyHolds 2 = true ∧ triEnergyHolds 3 = true ∧
    triEnergyHolds 4 = true ∧ triEnergyHolds 5 = true ∧
    triEnergyHolds 6 = true ∧ triEnergyHolds 7 = true ∧
    triEnergyHolds 8 = true := by decide

#print axioms triangle_energy_ladder

/-- The Sobolev perimeter reading: the three side energies, summed. -/
def perimeterReading (n : Nat) : Int :=
  sideEnergy n (uniformProbe n) + sideEnergy n (alternatingProbe n) +
    sideEnergy n (thirdSide n)

/-- THE LENGTHENING, RIDING THE ENTROPY: at every rung, the perimeter
    reading strictly grows AND the entropy step holds — the triangle
    lengthens along exactly the index where the spectrum's entropy
    provably rises, both halves decided by the kernel on the same rung. -/
theorem perimeter_lengthens_with_entropy :
    (perimeterReading 2 < perimeterReading 3 ∧ entropyStepHolds 2 = true) ∧
    (perimeterReading 3 < perimeterReading 4 ∧ entropyStepHolds 3 = true) ∧
    (perimeterReading 4 < perimeterReading 5 ∧ entropyStepHolds 4 = true) ∧
    (perimeterReading 5 < perimeterReading 6 ∧ entropyStepHolds 5 = true) ∧
    (perimeterReading 6 < perimeterReading 7 ∧ entropyStepHolds 6 = true) ∧
    (perimeterReading 7 < perimeterReading 8 ∧ entropyStepHolds 7 = true) := by
  decide

#print axioms perimeter_lengthens_with_entropy

end Measurement.WeakDiracGalerkin.SobolevTriangle
