import Measurement.Meanwhile35

/- MEANWHILE 36 -- RECOVER G FROM THE FORCE MEASUREMENT. The acceleration slip
seam is now a force measurement. Once the force threshold and distance bracket
are measured, Cavendish can be read again:

  G = F * distance^2 / (source_mass * test_mass * arm).

The bisection gives a lower/upper interval for G. The exact force law at the
seam recovers the same apparatus G as the earlier dial calibration.
-/

namespace Measurement

def forceMeasuredG (force : Nat) (distance : RationalDistance) : ApparatusRatio :=
  { numerator := force * square distance.numerator
    denominator :=
      cavendishSourceMassTotal * tetheredElectronTestMass.magnitude *
        cavendishArm * square distance.denominator }

def forceRecoveredExactG : ApparatusRatio :=
  { numerator := naturalUnitOrbitRadius
    denominator :=
      cavendishSourceMassTotal * tetheredElectronTestMass.magnitude *
        cavendishArm }

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

def ratioLe (a b : ApparatusRatio) : Bool :=
  a.numerator * b.denominator <= b.numerator * a.denominator

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

def defaultForceMeasuredGReport? : Option ForceMeasuredGReport :=
  forceMeasuredGReport? firstSlipTargetBetweenOneAndTwo 128 48

theorem forceRecoveredExactG_matches_deviceG :
    forceRecoveredExactG.numerator = deviceG.numerator ∧
      forceRecoveredExactG.denominator = deviceG.denominator := by
  exact ⟨rfl, rfl⟩

#eval defaultForceMeasuredGReport?

end Measurement
