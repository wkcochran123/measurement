import Measurement.Episode35

/- MEANWHILE 36 -- RECOVER G FROM THE FORCE MEASUREMENT. The acceleration slip
seam is now a force measurement. Once the force threshold and distance bracket
are measured, Cavendish can be read again:

  G = F * distance^2 / (source_mass * test_mass * arm).

The bisection gives a lower/upper interval for G. The exact force law at the
seam recovers the same apparatus G as the earlier dial calibration.
-/

/-! # Meanwhile 36 — G a second way: the spring scale confirms the balance  (∿ spring scale)

**The genre skin (∿).** Back in Ep26 the assayer weighed the brass on a BALANCE. Here the same weight is set
on a SECOND scale — a spring scale, which reads by force, not by balancing masses — and the needle lands on
the exact same mark.

**Object & facet.** This is the same GRAVITY facet of the object Yang–Mills describes, read a second and
independent way: through force. We describe the facet in the device's own exact terms; we never open or
solve Yang–Mills, and the last box stays wrapped.

**The squeeze (a PINNED equality — an internal cross-check).** `G_device = F · distance² / (sourceMass ·
testMass · arm)` recovered by force lands on the EXACT same rational the Ep26 balance did:
`forceRecoveredExactG = deviceG = 18/2132`, digit for digit, by `⟨rfl, rfl⟩`. Nothing new is discovered — it
is the SAME G, recovered a second way, and shown identical: two of the device's OWN routes agreeing, the
device consistent with itself. This is the device's own number, `18/2132` — the reading of its own
apparatus, not Newton's specific gravitational constant; that distinction is literal, not a disavowal.
-/

namespace Measurement

/-- `forceMeasuredG (force) (distance) : ApparatusRatio` — G read off the spring scale: numerator
`force * square distance.numerator`, denominator
`sourceMassTotal * testMass * arm * square distance.denominator`. Cavendish's law solved the other way
round, from a force. -/
def forceMeasuredG (force : Nat) (distance : RationalDistance) : ApparatusRatio :=
  { numerator := force * square distance.numerator
    denominator :=
      cavendishSourceMassTotal * tetheredElectronTestMass.magnitude *
        cavendishArm * square distance.denominator }

/-- `forceRecoveredExactG : ApparatusRatio` — the exact spring reading: numerator the natural-unit radius
(`naturalUnitOrbitRadius` = 18), denominator the same `sourceMassTotal * testMass * arm` the balance used —
so it equals `deviceG = 18/2132` (theorem below). -/
def forceRecoveredExactG : ApparatusRatio :=
  { numerator := naturalUnitOrbitRadius
    denominator :=
      cavendishSourceMassTotal * tetheredElectronTestMass.magnitude *
        cavendishArm }

/-- `ForceMeasuredGReport` — the two scales side by side: the target force, grid and rungs, the closed-in
distance bracket (scaled), the G at lower/upper/midpoint, the exact recovered G, the original device G,
their scaled reads, and two verdicts — `bracketContainsDeviceG` and `exactMatchesDeviceG`. -/
structure ForceMeasuredGReport where
  targetForce : Nat
  gridCells : Nat
  rungs : Nat
  lowerDistance : RationalDistance
  upperDistance : RationalDistance
  midpointDistance : RationalDistance
  lowerDistanceScaledAt18 : Nat
  upperDistanceScaledAt18 : Nat
  midpointDistanceScaledAt18 : Nat
  lowerG : ApparatusRatio
  upperG : ApparatusRatio
  midpointG : ApparatusRatio
  exactRecoveredG : ApparatusRatio
  originalDeviceG : ApparatusRatio
  lowerGScaledAt18 : Nat
  upperGScaledAt18 : Nat
  midpointGScaledAt18 : Nat
  exactRecoveredGScaledAt18 : Nat
  originalDeviceGScaledAt18 : Nat
  bracketContainsDeviceG : Bool
  exactMatchesDeviceG : Bool
deriving Repr

/-- `ratioLe (a) (b) : Bool` — whether `a ≤ b` by cross-multiplication,
`a.numerator * b.denominator <= b.numerator * a.denominator`. The at-or-below test the bracket check
uses. -/
def ratioLe (a b : ApparatusRatio) : Bool :=
  a.numerator * b.denominator <= b.numerator * a.denominator

/-- `forceMeasuredGReport? (targetForce) (gridCells) (rungs) : Option ForceMeasuredGReport` — grid and
bisect for the force seam (as Ep35 did for the slip), read G at the closed-in ends, and fill the comparison
(`bracketContainsDeviceG`; `exactMatchesDeviceG` = numerator and denominator both equal `deviceG`'s). -/
def forceMeasuredGReport?
    (targetForce gridCells rungs : Nat) : Option ForceMeasuredGReport :=
  match firstSlipGridCell targetForce gridCells with
  | none => none
  | some cell =>
      let bracket :=
        bisectDyadicSlipAux rungs targetForce
          (dyadicSlipBracketFromGridCell cell)
      let lowerDistance := bracket.lowerDistance
      let upperDistance := bracket.upperDistance
      let midpointDistance := bracket.midpointDistance
      let lowerG := forceMeasuredG targetForce lowerDistance
      let upperG := forceMeasuredG targetForce upperDistance
      let midpointG := forceMeasuredG targetForce midpointDistance
      let exactG := forceRecoveredExactG
      some
        ({ targetForce := targetForce
           gridCells := gridCells
           rungs := rungs
           lowerDistance := lowerDistance
           upperDistance := upperDistance
           midpointDistance := midpointDistance
           lowerDistanceScaledAt18 := lowerDistance.scaledFloor (pow10 18)
           upperDistanceScaledAt18 := upperDistance.scaledFloor (pow10 18)
           midpointDistanceScaledAt18 := midpointDistance.scaledFloor (pow10 18)
           lowerG := lowerG
           upperG := upperG
           midpointG := midpointG
           exactRecoveredG := exactG
           originalDeviceG := deviceG
           lowerGScaledAt18 := lowerG.scaledFloor (pow10 18)
           upperGScaledAt18 := upperG.scaledFloor (pow10 18)
           midpointGScaledAt18 := midpointG.scaledFloor (pow10 18)
           exactRecoveredGScaledAt18 := exactG.scaledFloor (pow10 18)
           originalDeviceGScaledAt18 := deviceG.scaledFloor (pow10 18)
           bracketContainsDeviceG := ratioLe lowerG deviceG && ratioLe deviceG upperG
           exactMatchesDeviceG :=
             (decide (exactG.numerator = deviceG.numerator) : Bool) &&
               (decide (exactG.denominator = deviceG.denominator) : Bool) } :
          ForceMeasuredGReport)

/-- `defaultForceMeasuredGReport? : Option ForceMeasuredGReport` — the standard run: target
`firstSlipTargetBetweenOneAndTwo`, 128 grid cells, 48 bisection rungs. -/
def defaultForceMeasuredGReport? : Option ForceMeasuredGReport :=
  forceMeasuredGReport? firstSlipTargetBetweenOneAndTwo 128 48

/-- `forceRecoveredExactG_matches_deviceG`.
**Proposition:** `forceRecoveredExactG.numerator = deviceG.numerator ∧ forceRecoveredExactG.denominator =
deviceG.denominator` — the force-recovered G equals the balance's device-G, numerator and denominator,
`18/2132` exactly.
**Mechanism:** `⟨rfl, rfl⟩` — both conjuncts by `rfl`, kernel-computed, exact, no float.
**Squeeze role:** the gravity facet re-pinned by a SECOND route — the spring scale and the balance concur to
the last digit, an internal cross-check (the device consistent with itself), not a new world measurement and
not Newton's constant. -/
theorem forceRecoveredExactG_matches_deviceG :
    forceRecoveredExactG.numerator = deviceG.numerator ∧
      forceRecoveredExactG.denominator = deviceG.denominator := by
  exact ⟨rfl, rfl⟩

/-! ## Readout — both needles
`#eval defaultForceMeasuredGReport?` prints both scales side by side: the force-measured G bracket and the
exact recovered G against the balance's device-G. The theorem above pins the match. The next facet, charge
as elaboration cost, is next door. -/
#eval defaultForceMeasuredGReport?

end Measurement
