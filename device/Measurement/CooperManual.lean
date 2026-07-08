import Measurement.Agent.Positron
import Measurement.Episode15
import Lean.Elab.Command
import Lean.Util.Heartbeats

/-!
A small instruction-manual skeleton for an electron -> electron -> Cooper-pair
interface.

The unbounded interaction is intentionally cyclic: outer electron, junction
electron, Cooper-pair face, returning electron, and so on. Evaluating that
process without a budget does not terminate. The executable entry point for the
device is the elaborator command `cooper_elab_run`, where the operator supplies
the number of loop folds the elaborator is allowed to spend before it stops and
prints a receipt.
-/

set_option autoImplicit false

namespace Measurement.CooperManual
open Measurement.Agent

inductive Face where
  | singleElectron
  | junctionElectron
  | cooperPair
deriving Repr, DecidableEq

inductive Spin where
  | up
  | down
deriving Repr, DecidableEq

def Spin.swap : Spin -> Spin
  | .up => .down
  | .down => .up

def Face.reading : Face -> Reading
  | .singleElectron => electron
  | .junctionElectron => electron
  | .cooperPair => superconductingPair

def Face.positronCount (face : Face) : Nat :=
  Measurement.Agent.positronCount electron face.reading

def Face.matterCount (face : Face) : Nat :=
  Measurement.Agent.matterReading electron face.reading

def Face.totalCount (face : Face) : Nat :=
  face.matterCount + face.positronCount

theorem singleElectron_has_no_tange :
    Face.positronCount .singleElectron = 0 := by
  decide

theorem junctionElectron_has_no_tange :
    Face.positronCount .junctionElectron = 0 := by
  decide

theorem cooperPair_has_one_tange :
    Face.positronCount .cooperPair = 1 := by
  decide

theorem cooperPair_tallies_the_gauge :
    Face.totalCount .cooperPair = Gate.all.length := by
  decide

structure JunctionScales where
  gap : Float
  josephsonEnergy : Float
  chargingEnergy : Float
  gateOffset : Float
deriving Repr

inductive Stage where
  | outerElectron
  | junctionElectron
  | cooperPair
  | returningElectron
deriving Repr, DecidableEq

def Stage.face : Stage -> Face
  | .outerElectron => .singleElectron
  | .junctionElectron => .junctionElectron
  | .cooperPair => .cooperPair
  | .returningElectron => .junctionElectron

inductive PairingChoice where
  | outerElectronToPair
  | junctionElectronToPair
  | bothElectronsToPair
  | nonInteractingCooperPair
deriving Repr, DecidableEq

def PairingChoice.interacts : PairingChoice -> Bool
  | .outerElectronToPair => true
  | .junctionElectronToPair => true
  | .bothElectronsToPair => true
  | .nonInteractingCooperPair => false

def PairingChoice.pairTransferDelta : PairingChoice -> Int
  | .outerElectronToPair => 1
  | .junctionElectronToPair => 1
  | .bothElectronsToPair => 1
  | .nonInteractingCooperPair => 0

def PairingChoice.outerEventDelta : PairingChoice -> Nat
  | .outerElectronToPair => 1
  | _ => 0

def PairingChoice.junctionEventDelta : PairingChoice -> Nat
  | .junctionElectronToPair => 1
  | _ => 0

def PairingChoice.bothEventDelta : PairingChoice -> Nat
  | .bothElectronsToPair => 1
  | _ => 0

def PairingChoice.nonInteractingEventDelta : PairingChoice -> Nat
  | .nonInteractingCooperPair => 1
  | _ => 0

def PairingChoice.outerResidualDelta : PairingChoice -> Int
  | .outerElectronToPair => 1
  | .bothElectronsToPair => 1
  | _ => 0

def PairingChoice.junctionResidualDelta : PairingChoice -> Int
  | .junctionElectronToPair => 1
  | .bothElectronsToPair => 1
  | _ => 0

def PairingChoice.carriedResidueDelta : PairingChoice -> Nat
  | .bothElectronsToPair => 1
  | _ => 0

def PairingChoice.spinSwapDelta : PairingChoice -> Nat
  | .bothElectronsToPair => 1
  | _ => 0

def PairingChoice.swapsSpin : PairingChoice -> Bool
  | .bothElectronsToPair => true
  | _ => false

def PairingChoice.phaseTurnDelta : PairingChoice -> Int
  | .outerElectronToPair => 1
  | .junctionElectronToPair => 1
  | .bothElectronsToPair => 1
  | .nonInteractingCooperPair => 0

def residueWordBits : Nat :=
  Gate.all.length

def residueWordSize : Nat :=
  2 ^ residueWordBits

def fineStructureQuantum : Nat :=
  1

def initialSeed : Nat :=
  0

def nextSeed (seed : Nat) : Nat :=
  (1664525 * seed + 1013904223) % 4294967296

def choosePairing (seed : Nat) : PairingChoice × Nat :=
  let seed' := nextSeed seed
  match seed' % 4 with
  | 0 => (.outerElectronToPair, seed')
  | 1 => (.nonInteractingCooperPair, seed')
  | 2 => (.junctionElectronToPair, seed')
  | _ => (.bothElectronsToPair, seed')

/--
The quotient relation used only at the Cooper-pair landing.  The raw chooser
keeps the four outcomes distinct; the quotient says that, once the apparatus is
looking only at the Cooper-pair phase class, the three interacting pairings can
be confused with each other.  The non-interacting Cooper-pair landing is not
silently collapsed into that class.
-/
def PairingConfusion (a b : PairingChoice) : Prop :=
  a = b ∨ (a.interacts = true ∧ b.interacts = true)

def PairingPhase : Type :=
  Quot PairingConfusion

namespace PairingPhase

def mk (choice : PairingChoice) : PairingPhase :=
  Quot.mk PairingConfusion choice

end PairingPhase

theorem bothElectronsToPair_interacting :
    PairingChoice.interacts .bothElectronsToPair = true :=
  rfl

/--
The PRNG chooser is routed through the single sanctioned `Quot.sound` site from
Episode15 by instantiating `selection_sound`; Episodes 1-16 do not need to move.
-/
theorem chosen_pairing_sound
    (seed : Nat)
    (h : (choosePairing seed).1.interacts = true) :
    PairingPhase.mk (choosePairing seed).1 =
      PairingPhase.mk .bothElectronsToPair :=
  Measurement.selection_sound (r := PairingConfusion)
    (Or.inr ⟨h, bothElectronsToPair_interacting⟩)

structure InteractionState where
  stage : Stage
  face : Face
  rngSeed : Nat
  lastPairing : Option PairingChoice
  spin : Spin
  spinSwapEvents : Nat
  firstSpinSwapCost : Option Nat
  lastSpinSwapCost : Option Nat
  electronElectronEvents : Nat
  electronElectronResidual : Int
  outerPairEvents : Nat
  junctionPairEvents : Nat
  bothPairEvents : Nat
  nonInteractingPairEvents : Nat
  outerPairResidual : Int
  junctionPairResidual : Int
  cooperPairResidue : Nat
  overflowPositronEvents : Nat
  pairTransfers : Int
  singleEvents : Nat
  pairEvents : Nat
  phaseTurns : Int
  costSpent : Nat
deriving Repr

def initial : InteractionState :=
  { stage := .outerElectron
    face := .singleElectron
    rngSeed := initialSeed
    lastPairing := none
    spin := .up
    spinSwapEvents := 0
    firstSpinSwapCost := none
    lastSpinSwapCost := none
    electronElectronEvents := 0
    electronElectronResidual := 0
    outerPairEvents := 0
    junctionPairEvents := 0
    bothPairEvents := 0
    nonInteractingPairEvents := 0
    outerPairResidual := 0
    junctionPairResidual := 0
    cooperPairResidue := 0
    overflowPositronEvents := 0
    pairTransfers := 0
    singleEvents := 1
    pairEvents := 0
    phaseTurns := 0
    costSpent := 0 }

def step (s : InteractionState) : InteractionState :=
  match s.stage with
  | .outerElectron =>
      { s with
        stage := .junctionElectron
        face := .junctionElectron
        electronElectronEvents := s.electronElectronEvents + 1
        electronElectronResidual := s.electronElectronResidual + 1
        costSpent := s.costSpent + 1 }
  | .junctionElectron =>
      let chosen := choosePairing s.rngSeed
      let choice := chosen.1
      let rawResidue := s.cooperPairResidue + choice.carriedResidueDelta
      let nextCost := s.costSpent + 1
      let swapsSpin := choice.swapsSpin
      { s with
        stage := .cooperPair
        face := .cooperPair
        rngSeed := chosen.2
        lastPairing := some choice
        spin := if swapsSpin then s.spin.swap else s.spin
        spinSwapEvents := s.spinSwapEvents + choice.spinSwapDelta
        firstSpinSwapCost :=
          match s.firstSpinSwapCost, swapsSpin with
          | none, true => some nextCost
          | cost?, _ => cost?
        lastSpinSwapCost :=
          if swapsSpin then some nextCost else s.lastSpinSwapCost
        outerPairEvents := s.outerPairEvents + choice.outerEventDelta
        junctionPairEvents := s.junctionPairEvents + choice.junctionEventDelta
        bothPairEvents := s.bothPairEvents + choice.bothEventDelta
        nonInteractingPairEvents :=
          s.nonInteractingPairEvents + choice.nonInteractingEventDelta
        outerPairResidual := s.outerPairResidual + choice.outerResidualDelta
        junctionPairResidual := s.junctionPairResidual + choice.junctionResidualDelta
        cooperPairResidue := rawResidue % residueWordSize
        overflowPositronEvents :=
          s.overflowPositronEvents + rawResidue / residueWordSize
        pairTransfers := s.pairTransfers + choice.pairTransferDelta
        pairEvents := s.pairEvents + 1
        phaseTurns := s.phaseTurns + choice.phaseTurnDelta
        costSpent := nextCost }
  | .cooperPair =>
      let choice := s.lastPairing.getD .nonInteractingCooperPair
      { s with
        stage := .returningElectron
        face := .junctionElectron
        outerPairResidual := s.outerPairResidual - choice.outerResidualDelta
        junctionPairResidual := s.junctionPairResidual - choice.junctionResidualDelta
        pairTransfers := s.pairTransfers - choice.pairTransferDelta
        singleEvents := s.singleEvents + 1
        phaseTurns := s.phaseTurns - choice.phaseTurnDelta
        costSpent := s.costSpent + 1 }
  | .returningElectron =>
      { s with
        stage := .outerElectron
        face := .singleElectron
        electronElectronEvents := s.electronElectronEvents + 1
        electronElectronResidual := s.electronElectronResidual - 1
        singleEvents := s.singleEvents + 1
        costSpent := s.costSpent + 1 }

def stepCost (_s : InteractionState) : Nat :=
  1

def runWithCost : Nat -> InteractionState -> InteractionState
  | 0, s => s
  | budget + 1, s => runWithCost budget (step s)

partial def runForever
    (s : InteractionState) : InteractionState :=
  runForever (step s)

/--
The stable electron -> electron -> Cooper-pair interaction is the thing this
experiment is looking for. In the current apparatus it has no constructors: the
loop can visit the outer electron, the junction electron, and the Cooper-pair
face, but it never produces a single stable witness joining all three.
-/
inductive InteractionWitness where
deriving Repr

def detectInteraction? (_s : InteractionState) : Option InteractionWitness :=
  none

theorem detectInteraction?_never (s : InteractionState) :
    detectInteraction? s = none := by
  rfl

theorem step_spends_one (s : InteractionState) :
    (step s).costSpent = s.costSpent + 1 := by
  cases s
  next stage face rngSeed lastPairing
      spin spinSwapEvents firstSpinSwapCost lastSpinSwapCost
      electronElectronEvents electronElectronResidual
      outerPairEvents junctionPairEvents bothPairEvents nonInteractingPairEvents
      outerPairResidual junctionPairResidual cooperPairResidue overflowPositronEvents
      pairTransfers singleEvents pairEvents phaseTurns costSpent =>
    cases stage <;> rfl

theorem runWithCost_spends :
    forall (budget : Nat) (s : InteractionState),
      (runWithCost budget s).costSpent = s.costSpent + budget := by
  intro budget
  induction budget with
  | zero =>
      intro s
      rfl
  | succ budget ih =>
      intro s
      simp [runWithCost, ih, step_spends_one, Nat.add_comm, Nat.add_left_comm]

structure InteractionReport where
  finalStage : Stage
  finalFace : Face
  costSpent : Nat
  rngSeed : Nat
  lastPairing : Option PairingChoice
  spin : Spin
  spinSwapEvents : Nat
  firstSpinSwapCost : Option Nat
  lastSpinSwapCost : Option Nat
  electronElectronEvents : Nat
  electronElectronResidual : Int
  outerPairEvents : Nat
  junctionPairEvents : Nat
  bothPairEvents : Nat
  nonInteractingPairEvents : Nat
  outerPairResidual : Int
  junctionPairResidual : Int
  cooperPairResidue : Nat
  overflowPositronEvents : Nat
  pairTransfers : Int
  singleEvents : Nat
  pairEvents : Nat
  phaseTurns : Int
  tangeCount : Nat
  matterCount : Nat
  fineStructureQuantum : Nat
  spinSwapAlphaApprox : Option Float
deriving Repr

def spinSwapAlphaApprox? : Option Nat -> Option Float
  | none => none
  | some 0 => none
  | some (cost + 1) =>
      some (Float.ofNat fineStructureQuantum / Float.ofNat (cost + 1))

def report (s : InteractionState) : InteractionReport :=
  { finalStage := s.stage
    finalFace := s.face
    costSpent := s.costSpent
    rngSeed := s.rngSeed
    lastPairing := s.lastPairing
    spin := s.spin
    spinSwapEvents := s.spinSwapEvents
    firstSpinSwapCost := s.firstSpinSwapCost
    lastSpinSwapCost := s.lastSpinSwapCost
    electronElectronEvents := s.electronElectronEvents
    electronElectronResidual := s.electronElectronResidual
    outerPairEvents := s.outerPairEvents
    junctionPairEvents := s.junctionPairEvents
    bothPairEvents := s.bothPairEvents
    nonInteractingPairEvents := s.nonInteractingPairEvents
    outerPairResidual := s.outerPairResidual
    junctionPairResidual := s.junctionPairResidual
    cooperPairResidue := s.cooperPairResidue
    overflowPositronEvents := s.overflowPositronEvents
    pairTransfers := s.pairTransfers
    singleEvents := s.singleEvents
    pairEvents := s.pairEvents
    phaseTurns := s.phaseTurns
    tangeCount := s.face.positronCount
    matterCount := s.face.matterCount
    fineStructureQuantum := fineStructureQuantum
    spinSwapAlphaApprox := spinSwapAlphaApprox? s.firstSpinSwapCost }

def runReport (budget : Nat) : InteractionReport :=
  report (runWithCost budget initial)

def needleCost : Float :=
  1.0

def alphaApprox? : Nat -> Option Float
  | 0 => none
  | loopCost + 1 => some (needleCost / Float.ofNat (loopCost + 1))

def alphaInvApprox? : Nat -> Option Float
  | 0 => none
  | loopCost + 1 => some (Float.ofNat (loopCost + 1))

def alphaFromInverseCost? : Nat -> Option Float
  | 0 => none
  | inverseCost + 1 =>
      some (Float.ofNat fineStructureQuantum / Float.ofNat (inverseCost + 1))

def alphaFromAmplifiedCost? (amplification : Nat) : Nat -> Option Float
  | 0 => none
  | cost + 1 =>
      some (Float.ofNat amplification / Float.ofNat (cost + 1))

def inverseAlphaFromAmplifiedCost? (amplification cost : Nat) : Option Float :=
  match amplification with
  | 0 => none
  | amplification' + 1 =>
      some (Float.ofNat cost / Float.ofNat (amplification' + 1))

def truncatedPiNumerator : Nat :=
  314159265358979323846

def truncatedPiScale : Nat :=
  100000000000000000000

def piFromDevice : Float :=
  Float.ofNat truncatedPiNumerator / Float.ofNat truncatedPiScale

def fourPiFromDevice : Float :=
  4.0 * piFromDevice

def truncatedLoopNumerator (loops amplification : Nat) : Nat :=
  loops * 4 * truncatedPiNumerator * amplification

def truncatedLoopStepNumerator (amplification : Nat) : Nat :=
  4 * truncatedPiNumerator * amplification

def scaledAlphaFromAmplifiedCost?
    (scale : Float)
    (amplification : Nat) : Nat -> Option Float
  | 0 => none
  | cost + 1 =>
      some (scale * Float.ofNat amplification / Float.ofNat (cost + 1))

def scaledAlphaFromTruncatedLoop?
    (loops amplification : Nat) : Nat -> Option Float
  | 0 => none
  | cost + 1 =>
      some
        (Float.ofNat (truncatedLoopNumerator loops amplification) /
          (Float.ofNat truncatedPiScale * Float.ofNat (cost + 1)))

def carriedLoopApprox?
    (whole residue denominator : Nat) : Option Float :=
  match denominator with
  | 0 => none
  | denominator' + 1 =>
      some
        (Float.ofNat whole +
          Float.ofNat residue / Float.ofNat (denominator' + 1))

def chargePosition (denominator tangedResidue : Nat) : Nat :=
  denominator + tangedResidue

def chargePotentialApprox?
    (denominator tangedResidue : Nat) : Option Float :=
  match chargePosition denominator tangedResidue with
  | 0 => none
  | position + 1 =>
      some (Float.ofNat denominator / Float.ofNat (position + 1))

def chargeRadiusApprox? (denominator tangedResidue : Nat) : Option Float :=
  carriedLoopApprox? 1 tangedResidue denominator

def chargeFungeApprox?
    (denominator tangedResidue : Nat) : Option Float :=
  carriedLoopApprox? 2 (2 * tangedResidue) denominator

def chargeTangeApprox?
    (denominator tangedResidue : Nat) : Option Float :=
  match chargePosition denominator tangedResidue with
  | 0 => none
  | position + 1 =>
      some (Float.ofNat tangedResidue / Float.ofNat (position + 1))

def reduceGravityUnit (denominator candidate : Nat) : Nat :=
  match denominator with
  | 0 => 0
  | unit + 1 => candidate % (unit + 1)

def gravityUnitOverflow (denominator candidate : Nat) : Nat :=
  match denominator with
  | 0 => 0
  | unit + 1 => candidate / (unit + 1)

def positiveChargeAlphaApprox?
    (positiveCharge : Nat) (alphaApprox : Option Float) : Option Float :=
  match alphaApprox with
  | none => none
  | some alpha =>
      if alpha == 0.0 then none
      else some (Float.ofNat positiveCharge / alpha)

def positionedGaugeShift
    (multiplicity perturbNumerator perturbScale
      denominator tangedResidue : Nat) : Nat :=
  match perturbScale, chargePosition denominator tangedResidue with
  | 0, _ => 0
  | _, 0 => 0
  | scale + 1, position =>
      multiplicity * perturbNumerator * denominator * denominator /
        ((scale + 1) * position)

def reflectedCostAround
    (center amplification cost : Nat) : Nat :=
  (2 * center * amplification) - cost

def reflectedCostAround137
    (amplification cost : Nat) : Nat :=
  reflectedCostAround 137 amplification cost

def spinAtCost (swapCost : Nat) (cost : Nat) : Spin :=
  if swapCost ≤ cost then .down else .up

inductive SpinBisectStatus where
  | searching
  | resolved
deriving Repr, DecidableEq

structure SpinBracket where
  lowerCost : Nat
  upperCost : Nat
  lowerSpin : Spin
  upperSpin : Spin
deriving Repr

def SpinBracket.width (bracket : SpinBracket) : Nat :=
  bracket.upperCost - bracket.lowerCost

def SpinBracket.midpoint (bracket : SpinBracket) : Nat :=
  let width := bracket.width
  if width ≤ 1 then bracket.upperCost else bracket.lowerCost + width / 2

def initialSpinBracket (swapCost : Nat) : SpinBracket :=
  let upper := max residueWordSize (swapCost + 1)
  { lowerCost := 0
    upperCost := upper
    lowerSpin := spinAtCost swapCost 0
    upperSpin := spinAtCost swapCost upper }

structure SpinBisectStep where
  rung : Nat
  lowerCost : Nat
  upperCost : Nat
  lowerSpin : Spin
  upperSpin : Spin
  probeCost : Nat
  probeStepCost : Nat
  probeSpin : Spin
  crossedSwap : Bool
  widthBefore : Nat
  widthAfter : Nat
  alphaInvLower : Nat
  alphaInvUpper : Nat
  alphaInvProbe : Nat
  alphaApproxUpper : Option Float
  status : SpinBisectStatus
deriving Repr

def bisectSpinOnceWithRead
    (readSpin : Nat -> Spin)
    (rung : Nat)
    (bracket : SpinBracket) : SpinBisectStep × SpinBracket :=
  let widthBefore := bracket.width
  let probeCost := bracket.midpoint
  let probeSpin := readSpin probeCost
  let crossedSwap := probeSpin = bracket.upperSpin
  let nextBracket :=
    if widthBefore ≤ 1 then
      bracket
    else if crossedSwap then
      { bracket with upperCost := probeCost, upperSpin := probeSpin }
    else
      { bracket with lowerCost := probeCost, lowerSpin := probeSpin }
  let widthAfter := nextBracket.width
  let status :=
    if widthAfter ≤ 1 then .resolved else .searching
  ({ rung := rung
     lowerCost := bracket.lowerCost
     upperCost := bracket.upperCost
     lowerSpin := bracket.lowerSpin
     upperSpin := bracket.upperSpin
     probeCost := probeCost
     probeStepCost := probeCost - bracket.lowerCost
     probeSpin := probeSpin
     crossedSwap := crossedSwap
     widthBefore := widthBefore
     widthAfter := widthAfter
     alphaInvLower := nextBracket.lowerCost
     alphaInvUpper := nextBracket.upperCost
     alphaInvProbe := probeCost
     alphaApproxUpper := alphaFromInverseCost? nextBracket.upperCost
     status := status },
   nextBracket)

def bisectSpinOnce
    (swapCost : Nat)
    (rung : Nat)
    (bracket : SpinBracket) : SpinBisectStep × SpinBracket :=
  bisectSpinOnceWithRead (spinAtCost swapCost) rung bracket

def spinBisectRunAuxWithRead
    (readSpin : Nat -> Spin) :
    Nat -> Nat -> SpinBracket -> SpinBracket × List SpinBisectStep
  | 0, _rung, bracket => (bracket, [])
  | fuel + 1, rung, bracket =>
      let next := bisectSpinOnceWithRead readSpin rung bracket
      let step := next.1
      let bracket' := next.2
      if step.status = .resolved then
        (bracket', [step])
      else
        let rest := spinBisectRunAuxWithRead readSpin fuel (rung + 1) bracket'
        (rest.1, step :: rest.2)

def spinBisectRunAux
    (swapCost : Nat) :
    Nat -> Nat -> SpinBracket -> SpinBracket × List SpinBisectStep :=
  spinBisectRunAuxWithRead (spinAtCost swapCost)

structure SpinBisectReport where
  swapCostFixture : Nat
  rungsRequested : Nat
  rungsSpent : Nat
  lowerCost : Nat
  upperCost : Nat
  lowerSpin : Spin
  upperSpin : Spin
  unresolvedWidth : Nat
  alphaInvLower : Nat
  alphaInvUpper : Nat
  alphaApproxUpper : Option Float
  steps : List SpinBisectStep
deriving Repr

def spinBisectReport (swapCost rungs : Nat) : SpinBisectReport :=
  let initial := initialSpinBracket swapCost
  let result := spinBisectRunAux swapCost rungs 0 initial
  let bracket := result.1
  let steps := result.2
  { swapCostFixture := swapCost
    rungsRequested := rungs
    rungsSpent := steps.length
    lowerCost := bracket.lowerCost
    upperCost := bracket.upperCost
    lowerSpin := bracket.lowerSpin
    upperSpin := bracket.upperSpin
    unresolvedWidth := bracket.width
    alphaInvLower := bracket.lowerCost
    alphaInvUpper := bracket.upperCost
    alphaApproxUpper := alphaFromInverseCost? bracket.upperCost
    steps := steps }

def amplifiedSpinBracket
    (baseLower baseUpper amplification : Nat)
    (readSpin : Nat -> Spin) : SpinBracket :=
  let rawLower := baseLower * amplification
  let rawUpper := baseUpper * amplification
  let lower := min rawLower rawUpper
  let upper := max rawLower rawUpper
  { lowerCost := lower
    upperCost := upper
    lowerSpin := readSpin lower
    upperSpin := readSpin upper }

structure AmplifiedSpinStep where
  rung : Nat
  lowerCost : Nat
  upperCost : Nat
  lowerSpin : Spin
  upperSpin : Spin
  probeCost : Nat
  probeStepCost : Nat
  probeSpin : Spin
  crossedSwap : Bool
  widthBefore : Nat
  widthAfter : Nat
  alphaLowerApprox : Option Float
  alphaUpperApprox : Option Float
  inverseAlphaLowerApprox : Option Float
  inverseAlphaUpperApprox : Option Float
  status : SpinBisectStatus
deriving Repr

def amplifiedSpinStep
    (amplification : Nat)
    (step : SpinBisectStep) : AmplifiedSpinStep :=
  { rung := step.rung
    lowerCost := step.lowerCost
    upperCost := step.upperCost
    lowerSpin := step.lowerSpin
    upperSpin := step.upperSpin
    probeCost := step.probeCost
    probeStepCost := step.probeStepCost
    probeSpin := step.probeSpin
    crossedSwap := step.crossedSwap
    widthBefore := step.widthBefore
    widthAfter := step.widthAfter
    alphaLowerApprox :=
      alphaFromAmplifiedCost? amplification step.alphaInvUpper
    alphaUpperApprox :=
      alphaFromAmplifiedCost? amplification step.alphaInvLower
    inverseAlphaLowerApprox :=
      inverseAlphaFromAmplifiedCost? amplification step.alphaInvLower
    inverseAlphaUpperApprox :=
      inverseAlphaFromAmplifiedCost? amplification step.alphaInvUpper
    status := step.status }

structure AmplifiedSpinReport where
  baseLowerCost : Nat
  baseUpperCost : Nat
  amplification : Nat
  rungsRequested : Nat
  rungsSpent : Nat
  lowerCost : Nat
  upperCost : Nat
  lowerSpin : Spin
  upperSpin : Spin
  unresolvedWidth : Nat
  alphaLowerApprox : Option Float
  alphaUpperApprox : Option Float
  inverseAlphaLowerApprox : Option Float
  inverseAlphaUpperApprox : Option Float
  fourPiAlphaLowerApprox : Option Float
  fourPiAlphaUpperApprox : Option Float
  reflectedLowerCost : Nat
  reflectedUpperCost : Nat
  reflectedInverseAlphaLowerApprox : Option Float
  reflectedInverseAlphaUpperApprox : Option Float
  reflectedAlphaLowerApprox : Option Float
  reflectedAlphaUpperApprox : Option Float
  reflectedFourPiAlphaLowerApprox : Option Float
  reflectedFourPiAlphaUpperApprox : Option Float
  steps : List AmplifiedSpinStep
deriving Repr

def amplifiedSpinReportWithRead
    (readSpin : Nat -> Spin)
    (baseLower baseUpper amplification rungs : Nat) :
    AmplifiedSpinReport :=
  let initial := amplifiedSpinBracket baseLower baseUpper amplification readSpin
  let result := spinBisectRunAuxWithRead readSpin rungs 0 initial
  let bracket := result.1
  let steps := result.2.map (amplifiedSpinStep amplification)
  let reflectedLower := reflectedCostAround137 amplification bracket.upperCost
  let reflectedUpper := reflectedCostAround137 amplification bracket.lowerCost
  { baseLowerCost := baseLower
    baseUpperCost := baseUpper
    amplification := amplification
    rungsRequested := rungs
    rungsSpent := steps.length
    lowerCost := bracket.lowerCost
    upperCost := bracket.upperCost
    lowerSpin := bracket.lowerSpin
    upperSpin := bracket.upperSpin
    unresolvedWidth := bracket.width
    alphaLowerApprox := alphaFromAmplifiedCost? amplification bracket.upperCost
    alphaUpperApprox := alphaFromAmplifiedCost? amplification bracket.lowerCost
    inverseAlphaLowerApprox :=
      inverseAlphaFromAmplifiedCost? amplification bracket.lowerCost
    inverseAlphaUpperApprox :=
      inverseAlphaFromAmplifiedCost? amplification bracket.upperCost
    fourPiAlphaLowerApprox :=
      scaledAlphaFromAmplifiedCost? fourPiFromDevice amplification bracket.upperCost
    fourPiAlphaUpperApprox :=
      scaledAlphaFromAmplifiedCost? fourPiFromDevice amplification bracket.lowerCost
    reflectedLowerCost := reflectedLower
    reflectedUpperCost := reflectedUpper
    reflectedInverseAlphaLowerApprox :=
      inverseAlphaFromAmplifiedCost? amplification reflectedLower
    reflectedInverseAlphaUpperApprox :=
      inverseAlphaFromAmplifiedCost? amplification reflectedUpper
    reflectedAlphaLowerApprox :=
      alphaFromAmplifiedCost? amplification reflectedUpper
    reflectedAlphaUpperApprox :=
      alphaFromAmplifiedCost? amplification reflectedLower
    reflectedFourPiAlphaLowerApprox :=
      scaledAlphaFromAmplifiedCost? fourPiFromDevice amplification reflectedUpper
    reflectedFourPiAlphaUpperApprox :=
      scaledAlphaFromAmplifiedCost? fourPiFromDevice amplification reflectedLower
    steps := steps }

def amplifiedSpinReport
    (baseLower baseUpper amplification swapCost rungs : Nat) :
    AmplifiedSpinReport :=
  amplifiedSpinReportWithRead (spinAtCost swapCost)
    baseLower baseUpper amplification rungs

structure LoopCarryState where
  loopsSpent : Nat
  lowerWholeLoops : Nat
  upperWholeLoops : Nat
  lowerResidue : Nat
  upperResidue : Nat
  lowerResidueAge : Nat
  upperResidueAge : Nat
  lowerTangedResidue : Nat
  upperTangedResidue : Nat
  lowerPositiveCharge : Nat
  upperPositiveCharge : Nat
deriving Repr

structure LoopCarryStep where
  loopIndex : Nat
  lowerResidueBefore : Nat
  upperResidueBefore : Nat
  lowerWholeDelta : Nat
  upperWholeDelta : Nat
  lowerSlipped : Bool
  upperSlipped : Bool
  lowerResidueAfter : Nat
  upperResidueAfter : Nat
  lowerResidueAgeAfter : Nat
  upperResidueAgeAfter : Nat
  lowerTangedResidueDelta : Nat
  upperTangedResidueDelta : Nat
  lowerTangedResidueAfter : Nat
  upperTangedResidueAfter : Nat
  lowerPositiveChargeDelta : Nat
  upperPositiveChargeDelta : Nat
  lowerPositiveChargeAfter : Nat
  upperPositiveChargeAfter : Nat
  lowerWholeLoopsAfter : Nat
  upperWholeLoopsAfter : Nat
deriving Repr

structure LoopScaledSpinReport where
  baseLowerCost : Nat
  baseUpperCost : Nat
  amplification : Nat
  loops : Nat
  rungsRequested : Nat
  rungsSpent : Nat
  lowerCost : Nat
  upperCost : Nat
  reflectedLowerCost : Nat
  reflectedUpperCost : Nat
  piNumerator : Nat
  piScale : Nat
  perLoopNumerator : Nat
  flattenedNumerator : Nat
  reflectedAlphaLowerDenominator : Nat
  reflectedAlphaUpperDenominator : Nat
  lowerSlipEvents : Nat
  upperSlipEvents : Nat
  lowerActiveResidueLoops : Nat
  upperActiveResidueLoops : Nat
  lowerWholeLoops : Nat
  upperWholeLoops : Nat
  lowerCarriedResidue : Nat
  upperCarriedResidue : Nat
  lowerTangedResidue : Nat
  upperTangedResidue : Nat
  lowerPositiveCharge : Nat
  upperPositiveCharge : Nat
  lowerPositiveChargeAlphaApprox : Option Float
  upperPositiveChargeAlphaApprox : Option Float
  lowerGravityApprox : Option Float
  upperGravityApprox : Option Float
  lowerChargePosition : Nat
  upperChargePosition : Nat
  lowerChargeRadiusApprox : Option Float
  upperChargeRadiusApprox : Option Float
  lowerChargeFungeApprox : Option Float
  upperChargeFungeApprox : Option Float
  lowerChargeTangeApprox : Option Float
  upperChargeTangeApprox : Option Float
  lowerChargePotentialApprox : Option Float
  upperChargePotentialApprox : Option Float
  reflectedLoopAlphaLowerApprox : Option Float
  reflectedLoopAlphaUpperApprox : Option Float
  recentCarrySteps : List LoopCarryStep
deriving Repr

def keepRecentCarrySteps : Nat -> List LoopCarryStep -> List LoopCarryStep
  | 0, _ => []
  | _ + 1, [] => []
  | limit + 1, step :: steps => step :: keepRecentCarrySteps limit steps

def carryLoopOnce
    (lowerPerLoopNumerator upperPerLoopNumerator
      lowerDenominator upperDenominator loopIndex : Nat)
    (state : LoopCarryState) :
    LoopCarryStep × LoopCarryState :=
  let lowerRaw := state.lowerResidue + lowerPerLoopNumerator
  let upperRaw := state.upperResidue + upperPerLoopNumerator
  let lowerSlipProbe := lowerRaw + 2 * lowerPerLoopNumerator
  let upperSlipProbe := upperRaw + 2 * upperPerLoopNumerator
  let lowerDelta := lowerSlipProbe / lowerDenominator
  let upperDelta := upperSlipProbe / upperDenominator
  let lowerSlipped := !(lowerDelta == 0)
  let upperSlipped := !(upperDelta == 0)
  let lowerTangedDelta := if lowerSlipped then lowerRaw else 0
  let upperTangedDelta := if upperSlipped then upperRaw else 0
  let lowerResidue := if lowerSlipped then 0 else lowerRaw
  let upperResidue := if upperSlipped then 0 else upperRaw
  let lowerResidueAge := if lowerSlipped then 0 else state.lowerResidueAge + 1
  let upperResidueAge := if upperSlipped then 0 else state.upperResidueAge + 1
  let lowerTangedCandidate := state.lowerTangedResidue + lowerTangedDelta
  let upperTangedCandidate := state.upperTangedResidue + upperTangedDelta
  let lowerPositiveChargeDelta :=
    gravityUnitOverflow lowerDenominator lowerTangedCandidate
  let upperPositiveChargeDelta :=
    gravityUnitOverflow upperDenominator upperTangedCandidate
  let lowerTangedResidue :=
    reduceGravityUnit lowerDenominator lowerTangedCandidate
  let upperTangedResidue :=
    reduceGravityUnit upperDenominator upperTangedCandidate
  let lowerPositiveCharge :=
    state.lowerPositiveCharge + lowerPositiveChargeDelta
  let upperPositiveCharge :=
    state.upperPositiveCharge + upperPositiveChargeDelta
  let nextState :=
    { loopsSpent := state.loopsSpent + 1
      lowerWholeLoops := state.lowerWholeLoops + lowerDelta
      upperWholeLoops := state.upperWholeLoops + upperDelta
      lowerResidue := lowerResidue
      upperResidue := upperResidue
      lowerResidueAge := lowerResidueAge
      upperResidueAge := upperResidueAge
      lowerTangedResidue := lowerTangedResidue
      upperTangedResidue := upperTangedResidue
      lowerPositiveCharge := lowerPositiveCharge
      upperPositiveCharge := upperPositiveCharge }
  ({ loopIndex := loopIndex
     lowerResidueBefore := state.lowerResidue
     upperResidueBefore := state.upperResidue
     lowerWholeDelta := lowerDelta
     upperWholeDelta := upperDelta
     lowerSlipped := lowerSlipped
     upperSlipped := upperSlipped
     lowerResidueAfter := lowerResidue
     upperResidueAfter := upperResidue
     lowerResidueAgeAfter := lowerResidueAge
     upperResidueAgeAfter := upperResidueAge
     lowerTangedResidueDelta := lowerTangedDelta
     upperTangedResidueDelta := upperTangedDelta
     lowerTangedResidueAfter := lowerTangedResidue
     upperTangedResidueAfter := upperTangedResidue
     lowerPositiveChargeDelta := lowerPositiveChargeDelta
     upperPositiveChargeDelta := upperPositiveChargeDelta
     lowerPositiveChargeAfter := lowerPositiveCharge
     upperPositiveChargeAfter := upperPositiveCharge
     lowerWholeLoopsAfter := nextState.lowerWholeLoops
     upperWholeLoopsAfter := nextState.upperWholeLoops },
   nextState)

def runLoopCarryAux
    (lowerPerLoopNumerator upperPerLoopNumerator
      lowerDenominator upperDenominator recentLimit : Nat) :
    Nat -> Nat -> LoopCarryState -> List LoopCarryStep ->
      LoopCarryState × List LoopCarryStep
  | 0, _loopIndex, state, recent => (state, recent)
  | fuel + 1, loopIndex, state, recent =>
      let next :=
        carryLoopOnce lowerPerLoopNumerator upperPerLoopNumerator
          lowerDenominator upperDenominator loopIndex state
      let recent' := keepRecentCarrySteps recentLimit (next.1 :: recent)
      runLoopCarryAux lowerPerLoopNumerator upperPerLoopNumerator
        lowerDenominator upperDenominator recentLimit fuel
        (loopIndex + 1) next.2 recent'

def runLoopCarry
    (lowerPerLoopNumerator upperPerLoopNumerator
      lowerDenominator upperDenominator loops recentLimit : Nat) :
    LoopCarryState × List LoopCarryStep :=
  runLoopCarryAux lowerPerLoopNumerator upperPerLoopNumerator
    lowerDenominator upperDenominator recentLimit loops 1
    { loopsSpent := 0
      lowerWholeLoops := 0
      upperWholeLoops := 0
      lowerResidue := 0
      upperResidue := 0
      lowerResidueAge := 0
      upperResidueAge := 0
      lowerTangedResidue := 0
      upperTangedResidue := 0
      lowerPositiveCharge := 0
      upperPositiveCharge := 0 }
    []

def loopScaledSpinReport
    (baseLower baseUpper amplification swapCost rungs loops : Nat) :
    LoopScaledSpinReport :=
  let report := amplifiedSpinReport baseLower baseUpper amplification swapCost rungs
  let perLoopNumerator := truncatedLoopStepNumerator report.amplification
  let lowerDenominator := truncatedPiScale * report.reflectedUpperCost
  let upperDenominator := truncatedPiScale * report.reflectedLowerCost
  let carried := runLoopCarry perLoopNumerator perLoopNumerator
    lowerDenominator upperDenominator loops 12
  let carriedState := carried.1
  { baseLowerCost := report.baseLowerCost
    baseUpperCost := report.baseUpperCost
    amplification := report.amplification
    loops := loops
    rungsRequested := report.rungsRequested
    rungsSpent := report.rungsSpent
    lowerCost := report.lowerCost
    upperCost := report.upperCost
    reflectedLowerCost := report.reflectedLowerCost
    reflectedUpperCost := report.reflectedUpperCost
    piNumerator := truncatedPiNumerator
    piScale := truncatedPiScale
    perLoopNumerator := perLoopNumerator
    flattenedNumerator := truncatedLoopNumerator loops report.amplification
    reflectedAlphaLowerDenominator :=
      lowerDenominator
    reflectedAlphaUpperDenominator :=
      upperDenominator
    lowerSlipEvents := carriedState.lowerWholeLoops
    upperSlipEvents := carriedState.upperWholeLoops
    lowerActiveResidueLoops := carriedState.lowerResidueAge
    upperActiveResidueLoops := carriedState.upperResidueAge
    lowerWholeLoops := carriedState.lowerWholeLoops
    upperWholeLoops := carriedState.upperWholeLoops
    lowerCarriedResidue := carriedState.lowerResidue
    upperCarriedResidue := carriedState.upperResidue
    lowerTangedResidue := carriedState.lowerTangedResidue
    upperTangedResidue := carriedState.upperTangedResidue
    lowerPositiveCharge := carriedState.lowerPositiveCharge
    upperPositiveCharge := carriedState.upperPositiveCharge
    lowerPositiveChargeAlphaApprox :=
      positiveChargeAlphaApprox? carriedState.lowerPositiveCharge
        report.reflectedAlphaLowerApprox
    upperPositiveChargeAlphaApprox :=
      positiveChargeAlphaApprox? carriedState.upperPositiveCharge
        report.reflectedAlphaUpperApprox
    lowerGravityApprox :=
      carriedLoopApprox? 0 carriedState.lowerTangedResidue lowerDenominator
    upperGravityApprox :=
      carriedLoopApprox? 0 carriedState.upperTangedResidue upperDenominator
    lowerChargePosition :=
      chargePosition lowerDenominator carriedState.lowerTangedResidue
    upperChargePosition :=
      chargePosition upperDenominator carriedState.upperTangedResidue
    lowerChargeRadiusApprox :=
      chargeRadiusApprox? lowerDenominator carriedState.lowerTangedResidue
    upperChargeRadiusApprox :=
      chargeRadiusApprox? upperDenominator carriedState.upperTangedResidue
    lowerChargeFungeApprox :=
      chargeFungeApprox? lowerDenominator carriedState.lowerTangedResidue
    upperChargeFungeApprox :=
      chargeFungeApprox? upperDenominator carriedState.upperTangedResidue
    lowerChargeTangeApprox :=
      chargeTangeApprox? lowerDenominator
        carriedState.lowerTangedResidue
    upperChargeTangeApprox :=
      chargeTangeApprox? upperDenominator
        carriedState.upperTangedResidue
    lowerChargePotentialApprox :=
      chargePotentialApprox? lowerDenominator carriedState.lowerTangedResidue
    upperChargePotentialApprox :=
      chargePotentialApprox? upperDenominator carriedState.upperTangedResidue
    reflectedLoopAlphaLowerApprox :=
      carriedLoopApprox? carriedState.lowerWholeLoops
        carriedState.lowerResidue lowerDenominator
    reflectedLoopAlphaUpperApprox :=
      carriedLoopApprox? carriedState.upperWholeLoops
        carriedState.upperResidue upperDenominator
    recentCarrySteps := carried.2 }

inductive SlipProbeChannel where
  | electron
  | cooperPair
deriving Repr, DecidableEq

def SlipProbeChannel.chargeMultiplicity : SlipProbeChannel -> Nat
  | .electron => 1
  | .cooperPair => 2

def SlipProbeChannel.kineticMultiplicity : SlipProbeChannel -> Nat
  | .electron => 1
  | .cooperPair => 2

structure FiniteProbe where
  numerator : Nat
  scale : Nat
deriving Repr

structure PerturbedSlipReport where
  baseLowerCost : Nat
  baseUpperCost : Nat
  amplification : Nat
  loops : Nat
  rungsRequested : Nat
  rungsSpent : Nat
  reflectedLowerCost : Nat
  reflectedUpperCost : Nat
  lowerPerLoopNumerator : Nat
  upperPerLoopNumerator : Nat
  lowerDenominator : Nat
  upperDenominator : Nat
  lowerSlipEvents : Nat
  upperSlipEvents : Nat
  lowerActiveResidueLoops : Nat
  upperActiveResidueLoops : Nat
  lowerCarriedResidue : Nat
  upperCarriedResidue : Nat
  lowerTangedResidue : Nat
  upperTangedResidue : Nat
  lowerPositiveCharge : Nat
  upperPositiveCharge : Nat
  lowerPositiveChargeAlphaApprox : Option Float
  upperPositiveChargeAlphaApprox : Option Float
  lowerGravityApprox : Option Float
  upperGravityApprox : Option Float
  lowerChargePosition : Nat
  upperChargePosition : Nat
  lowerChargeRadiusApprox : Option Float
  upperChargeRadiusApprox : Option Float
  lowerChargeFungeApprox : Option Float
  upperChargeFungeApprox : Option Float
  lowerChargeTangeApprox : Option Float
  upperChargeTangeApprox : Option Float
  lowerChargePotentialApprox : Option Float
  upperChargePotentialApprox : Option Float
  lowerApprox : Option Float
  upperApprox : Option Float
deriving Repr

def perturbedSlipReport
    (baseLower baseUpper amplification swapCost rungs loops
      lowerPerLoopNumerator upperPerLoopNumerator : Nat) :
    PerturbedSlipReport :=
  let report := amplifiedSpinReport baseLower baseUpper amplification swapCost rungs
  let lowerDenominator := truncatedPiScale * report.reflectedUpperCost
  let upperDenominator := truncatedPiScale * report.reflectedLowerCost
  let carried := runLoopCarry lowerPerLoopNumerator upperPerLoopNumerator
    lowerDenominator upperDenominator loops 12
  let carriedState := carried.1
  { baseLowerCost := report.baseLowerCost
    baseUpperCost := report.baseUpperCost
    amplification := report.amplification
    loops := loops
    rungsRequested := report.rungsRequested
    rungsSpent := report.rungsSpent
    reflectedLowerCost := report.reflectedLowerCost
    reflectedUpperCost := report.reflectedUpperCost
    lowerPerLoopNumerator := lowerPerLoopNumerator
    upperPerLoopNumerator := upperPerLoopNumerator
    lowerDenominator := lowerDenominator
    upperDenominator := upperDenominator
    lowerSlipEvents := carriedState.lowerWholeLoops
    upperSlipEvents := carriedState.upperWholeLoops
    lowerActiveResidueLoops := carriedState.lowerResidueAge
    upperActiveResidueLoops := carriedState.upperResidueAge
    lowerCarriedResidue := carriedState.lowerResidue
    upperCarriedResidue := carriedState.upperResidue
    lowerTangedResidue := carriedState.lowerTangedResidue
    upperTangedResidue := carriedState.upperTangedResidue
    lowerPositiveCharge := carriedState.lowerPositiveCharge
    upperPositiveCharge := carriedState.upperPositiveCharge
    lowerPositiveChargeAlphaApprox :=
      positiveChargeAlphaApprox? carriedState.lowerPositiveCharge
        report.reflectedAlphaLowerApprox
    upperPositiveChargeAlphaApprox :=
      positiveChargeAlphaApprox? carriedState.upperPositiveCharge
        report.reflectedAlphaUpperApprox
    lowerGravityApprox :=
      carriedLoopApprox? 0 carriedState.lowerTangedResidue lowerDenominator
    upperGravityApprox :=
      carriedLoopApprox? 0 carriedState.upperTangedResidue upperDenominator
    lowerChargePosition :=
      chargePosition lowerDenominator carriedState.lowerTangedResidue
    upperChargePosition :=
      chargePosition upperDenominator carriedState.upperTangedResidue
    lowerChargeRadiusApprox :=
      chargeRadiusApprox? lowerDenominator carriedState.lowerTangedResidue
    upperChargeRadiusApprox :=
      chargeRadiusApprox? upperDenominator carriedState.upperTangedResidue
    lowerChargeFungeApprox :=
      chargeFungeApprox? lowerDenominator carriedState.lowerTangedResidue
    upperChargeFungeApprox :=
      chargeFungeApprox? upperDenominator carriedState.upperTangedResidue
    lowerChargeTangeApprox :=
      chargeTangeApprox? lowerDenominator
        carriedState.lowerTangedResidue
    upperChargeTangeApprox :=
      chargeTangeApprox? upperDenominator
        carriedState.upperTangedResidue
    lowerChargePotentialApprox :=
      chargePotentialApprox? lowerDenominator carriedState.lowerTangedResidue
    upperChargePotentialApprox :=
      chargePotentialApprox? upperDenominator carriedState.upperTangedResidue
    lowerApprox :=
      carriedLoopApprox? carriedState.lowerWholeLoops
        carriedState.lowerResidue lowerDenominator
    upperApprox :=
      carriedLoopApprox? carriedState.upperWholeLoops
        carriedState.upperResidue upperDenominator }

def denominatorScaledShift
    (multiplicity perturbNumerator perturbScale denominator : Nat) : Nat :=
  match perturbScale with
  | 0 => 0
  | scale + 1 =>
      multiplicity * perturbNumerator * denominator / (scale + 1)

def kineticScaledShift
    (multiplicity displacementNumerator displacementScale denominator : Nat) :
    Nat :=
  match displacementScale with
  | 0 => 0
  | scale + 1 =>
      multiplicity * displacementNumerator * displacementNumerator *
        denominator / (2 * (scale + 1) * (scale + 1))

def centralSlope?
    (minus plus : Option Float)
    (probe activeLoops : Nat)
    (scale : Nat) : Option Float :=
  match minus, plus, probe, scale, activeLoops with
  | some minusValue, some plusValue, probe' + 1, scale' + 1, activeLoops' + 1 =>
      let epsilon :=
        Float.ofNat (probe' + 1) / Float.ofNat (scale' + 1)
      some
        ((plusValue - minusValue) /
          (2.0 * epsilon * Float.ofNat (activeLoops' + 1)))
  | _, _, _, _, _ => none

def centralCurvature?
    (minus base plus : Option Float)
    (probe activeLoops : Nat)
    (scale : Nat) : Option Float :=
  match minus, base, plus, probe, scale, activeLoops with
  | some minusValue, some baseValue, some plusValue,
      probe' + 1, scale' + 1, activeLoops' + 1 =>
      let displacement :=
        Float.ofNat (probe' + 1) / Float.ofNat (scale' + 1)
      some
        ((plusValue - 2.0 * baseValue + minusValue) /
          (displacement * displacement * Float.ofNat (activeLoops' + 1)))
  | _, _, _, _, _, _ => none

structure ChargeResponse where
  channel : SlipProbeChannel
  probe : FiniteProbe
  unperturbed : PerturbedSlipReport
  minusGauge : PerturbedSlipReport
  plusGauge : PerturbedSlipReport
  lowerChargeApprox : Option Float
  upperChargeApprox : Option Float
deriving Repr

def chargeResponse
    (channel : SlipProbeChannel)
    (baseLower baseUpper amplification swapCost rungs loops : Nat)
    (probe : FiniteProbe) : ChargeResponse :=
  let spinReport := amplifiedSpinReport baseLower baseUpper amplification swapCost rungs
  let baseStep := truncatedLoopStepNumerator amplification
  let lowerDenominator := truncatedPiScale * spinReport.reflectedUpperCost
  let upperDenominator := truncatedPiScale * spinReport.reflectedLowerCost
  let unperturbed :=
    perturbedSlipReport baseLower baseUpper amplification swapCost rungs loops
      baseStep baseStep
  let lowerShift :=
    positionedGaugeShift channel.chargeMultiplicity probe.numerator
      probe.scale lowerDenominator unperturbed.lowerTangedResidue
  let upperShift :=
    positionedGaugeShift channel.chargeMultiplicity probe.numerator
      probe.scale upperDenominator unperturbed.upperTangedResidue
  let minusGauge :=
    perturbedSlipReport baseLower baseUpper amplification swapCost rungs loops
      (baseStep - lowerShift) (baseStep - upperShift)
  let plusGauge :=
    perturbedSlipReport baseLower baseUpper amplification swapCost rungs loops
      (baseStep + lowerShift) (baseStep + upperShift)
  { channel := channel
    probe := probe
    unperturbed := unperturbed
    minusGauge := minusGauge
    plusGauge := plusGauge
    lowerChargeApprox :=
      centralSlope? minusGauge.lowerApprox plusGauge.lowerApprox
        probe.numerator unperturbed.lowerActiveResidueLoops probe.scale
    upperChargeApprox :=
      centralSlope? minusGauge.upperApprox plusGauge.upperApprox
        probe.numerator unperturbed.upperActiveResidueLoops probe.scale }

structure MassResponse where
  channel : SlipProbeChannel
  probe : FiniteProbe
  unperturbed : PerturbedSlipReport
  minusKinetic : PerturbedSlipReport
  plusKinetic : PerturbedSlipReport
  lowerMassApprox : Option Float
  upperMassApprox : Option Float
deriving Repr

def massResponse
    (channel : SlipProbeChannel)
    (baseLower baseUpper amplification swapCost rungs loops : Nat)
    (probe : FiniteProbe) : MassResponse :=
  let spinReport := amplifiedSpinReport baseLower baseUpper amplification swapCost rungs
  let baseStep := truncatedLoopStepNumerator amplification
  let lowerDenominator := truncatedPiScale * spinReport.reflectedUpperCost
  let upperDenominator := truncatedPiScale * spinReport.reflectedLowerCost
  let lowerShift :=
    kineticScaledShift channel.kineticMultiplicity probe.numerator
      probe.scale lowerDenominator
  let upperShift :=
    kineticScaledShift channel.kineticMultiplicity probe.numerator
      probe.scale upperDenominator
  let unperturbed :=
    perturbedSlipReport baseLower baseUpper amplification swapCost rungs loops
      baseStep baseStep
  let minusKinetic :=
    perturbedSlipReport baseLower baseUpper amplification swapCost rungs loops
      (baseStep + lowerShift) (baseStep + upperShift)
  let plusKinetic :=
    perturbedSlipReport baseLower baseUpper amplification swapCost rungs loops
      (baseStep + lowerShift) (baseStep + upperShift)
  { channel := channel
    probe := probe
    unperturbed := unperturbed
    minusKinetic := minusKinetic
    plusKinetic := plusKinetic
    lowerMassApprox :=
      centralCurvature? minusKinetic.lowerApprox unperturbed.lowerApprox
        plusKinetic.lowerApprox probe.numerator
        unperturbed.lowerActiveResidueLoops probe.scale
    upperMassApprox :=
      centralCurvature? minusKinetic.upperApprox unperturbed.upperApprox
        plusKinetic.upperApprox probe.numerator
        unperturbed.upperActiveResidueLoops probe.scale }

structure SlipProbeExperiment where
  electronCharge : ChargeResponse
  cooperPairCharge : ChargeResponse
  electronMass : MassResponse
  cooperPairMass : MassResponse
deriving Repr

def slipProbeExperiment
    (baseLower baseUpper amplification swapCost rungs loops : Nat)
    (gaugeProbe kineticProbe : FiniteProbe) : SlipProbeExperiment :=
  { electronCharge :=
      chargeResponse .electron baseLower baseUpper amplification swapCost
        rungs loops gaugeProbe
    cooperPairCharge :=
      chargeResponse .cooperPair baseLower baseUpper amplification swapCost
        rungs loops gaugeProbe
    electronMass :=
      massResponse .electron baseLower baseUpper amplification swapCost
        rungs loops kineticProbe
    cooperPairMass :=
      massResponse .cooperPair baseLower baseUpper amplification swapCost
        rungs loops kineticProbe }

def optionFloatDiv? : Option Float -> Option Float -> Option Float
  | some numerator, some denominator =>
      if denominator == 0.0 then none else some (numerator / denominator)
  | _, _ => none

def optionFloatMul? : Option Float -> Option Float -> Option Float
  | some left, some right => some (left * right)
  | _, _ => none

def optionFloatAdd? : Option Float -> Option Float -> Option Float
  | some left, some right => some (left + right)
  | _, _ => none

def optionFloatSub? : Option Float -> Option Float -> Option Float
  | some left, some right => some (left - right)
  | _, _ => none

def gravityAttraction?
    (gravityApprox chargePotentialApprox cooperPairMassApprox : Option Float) :
    Option Float :=
  optionFloatMul?
    (optionFloatMul? gravityApprox chargePotentialApprox)
    cooperPairMassApprox

structure VelocityExperiment where
  slip : SlipProbeExperiment
  lowerElectronVelocityApprox : Option Float
  upperElectronVelocityApprox : Option Float
  lowerCooperPairVelocityApprox : Option Float
  upperCooperPairVelocityApprox : Option Float
  lowerFreeRelativeVelocityApprox : Option Float
  upperFreeRelativeVelocityApprox : Option Float
  lowerGravityAttractionApprox : Option Float
  upperGravityAttractionApprox : Option Float
  lowerAttractedElectronVelocityApprox : Option Float
  upperAttractedElectronVelocityApprox : Option Float
  lowerRelativeVelocityApprox : Option Float
  upperRelativeVelocityApprox : Option Float
deriving Repr

def velocityExperiment
    (baseLower baseUpper amplification swapCost rungs loops : Nat)
    (gaugeProbe kineticProbe : FiniteProbe) : VelocityExperiment :=
  let slip :=
    slipProbeExperiment baseLower baseUpper amplification swapCost rungs loops
      gaugeProbe kineticProbe
  let lowerElectronVelocity :=
    optionFloatDiv? slip.electronCharge.lowerChargeApprox
      slip.electronMass.lowerMassApprox
  let upperElectronVelocity :=
    optionFloatDiv? slip.electronCharge.upperChargeApprox
      slip.electronMass.upperMassApprox
  let lowerCooperPairVelocity :=
    optionFloatDiv? slip.cooperPairCharge.lowerChargeApprox
      slip.cooperPairMass.lowerMassApprox
  let upperCooperPairVelocity :=
    optionFloatDiv? slip.cooperPairCharge.upperChargeApprox
      slip.cooperPairMass.upperMassApprox
  let lowerFreeRelativeVelocity :=
    optionFloatSub? lowerElectronVelocity lowerCooperPairVelocity
  let upperFreeRelativeVelocity :=
    optionFloatSub? upperElectronVelocity upperCooperPairVelocity
  let lowerGravityAttraction :=
    gravityAttraction?
      slip.electronCharge.unperturbed.lowerGravityApprox
      slip.electronCharge.unperturbed.lowerChargePotentialApprox
      slip.cooperPairMass.lowerMassApprox
  let upperGravityAttraction :=
    gravityAttraction?
      slip.electronCharge.unperturbed.upperGravityApprox
      slip.electronCharge.unperturbed.upperChargePotentialApprox
      slip.cooperPairMass.upperMassApprox
  let lowerAttractedElectronVelocity :=
    optionFloatAdd? lowerElectronVelocity lowerGravityAttraction
  let upperAttractedElectronVelocity :=
    optionFloatAdd? upperElectronVelocity upperGravityAttraction
  { slip := slip
    lowerElectronVelocityApprox := lowerElectronVelocity
    upperElectronVelocityApprox := upperElectronVelocity
    lowerCooperPairVelocityApprox := lowerCooperPairVelocity
    upperCooperPairVelocityApprox := upperCooperPairVelocity
    lowerFreeRelativeVelocityApprox := lowerFreeRelativeVelocity
    upperFreeRelativeVelocityApprox := upperFreeRelativeVelocity
    lowerGravityAttractionApprox := lowerGravityAttraction
    upperGravityAttractionApprox := upperGravityAttraction
    lowerAttractedElectronVelocityApprox := lowerAttractedElectronVelocity
    upperAttractedElectronVelocityApprox := upperAttractedElectronVelocity
    lowerRelativeVelocityApprox :=
      optionFloatSub? lowerAttractedElectronVelocity lowerCooperPairVelocity
    upperRelativeVelocityApprox :=
      optionFloatSub? upperAttractedElectronVelocity upperCooperPairVelocity }

def scaleStepApprox? (numerator scale : Nat) : Option Float :=
  match scale with
  | 0 => none
  | scale' + 1 =>
      some (Float.ofNat numerator / Float.ofNat (scale' + 1))

def scaleE18 : Nat :=
  1000000000000000000

def scaleE30 : Nat :=
  1000000000000000000000000000000

def scaledRatioFloor (factor numerator denominator : Nat) : Nat :=
  match denominator with
  | 0 => 0
  | denominator' + 1 => factor * numerator / (denominator' + 1)

def kineticScaleResolves
    (multiplicity numerator denominator scale : Nat) : Bool :=
  !(kineticScaledShift multiplicity numerator scale denominator == 0)

def kineticMassCoeffApprox?
    (multiplicity numerator denominator scale : Nat) : Option Float :=
  match numerator, denominator with
  | 0, _ => none
  | _, 0 => none
  | numerator' + 1, denominator' + 1 =>
      let shift :=
        kineticScaledShift multiplicity (numerator' + 1) scale
          (denominator' + 1)
      some
        (Float.ofNat (2 * shift * scale * scale) /
          (Float.ofNat (denominator' + 1) *
            Float.ofNat ((numerator' + 1) * (numerator' + 1))))

structure KineticScaleBracket where
  multiplicity : Nat
  numerator : Nat
  denominator : Nat
  lowerResolvingScale : Nat
  upperSilentScale : Nat
  width : Nat
  lowerResolvingShift : Nat
  upperSilentShift : Nat
  motionLowerApprox : Option Float
  motionUpperApprox : Option Float
  motionLowerScaledE18 : Nat
  motionUpperScaledE18 : Nat
  resolvingMassCoeffApprox : Option Float
  silentMassCoeffApprox : Option Float
deriving Repr

def kineticScaleBracket
    (multiplicity numerator denominator lowerResolving upperSilent : Nat) :
    KineticScaleBracket :=
  { multiplicity := multiplicity
    numerator := numerator
    denominator := denominator
    lowerResolvingScale := lowerResolving
    upperSilentScale := upperSilent
    width := upperSilent - lowerResolving
    lowerResolvingShift :=
      kineticScaledShift multiplicity numerator lowerResolving denominator
    upperSilentShift :=
      kineticScaledShift multiplicity numerator upperSilent denominator
    motionLowerApprox := scaleStepApprox? numerator upperSilent
    motionUpperApprox := scaleStepApprox? numerator lowerResolving
    motionLowerScaledE18 := scaledRatioFloor scaleE18 numerator upperSilent
    motionUpperScaledE18 := scaledRatioFloor scaleE18 numerator lowerResolving
    resolvingMassCoeffApprox :=
      kineticMassCoeffApprox? multiplicity numerator denominator lowerResolving
    silentMassCoeffApprox :=
      kineticMassCoeffApprox? multiplicity numerator denominator upperSilent }

def findSilentKineticScaleAux
    (multiplicity numerator denominator : Nat) :
    Nat -> Nat -> Nat
  | 0, scale => scale
  | fuel + 1, scale =>
      if kineticScaleResolves multiplicity numerator denominator scale then
        findSilentKineticScaleAux multiplicity numerator denominator fuel
          (2 * scale)
      else
        scale

def bisectKineticScaleAux
    (multiplicity numerator denominator : Nat) :
    Nat -> KineticScaleBracket -> KineticScaleBracket
  | 0, bracket => bracket
  | fuel + 1, bracket =>
      if bracket.upperSilentScale ≤ bracket.lowerResolvingScale + 1 then
        bracket
      else
        let mid :=
          (bracket.lowerResolvingScale + bracket.upperSilentScale) / 2
        let next :=
          if kineticScaleResolves multiplicity numerator denominator mid then
            kineticScaleBracket multiplicity numerator denominator mid
              bracket.upperSilentScale
          else
            kineticScaleBracket multiplicity numerator denominator
              bracket.lowerResolvingScale mid
        bisectKineticScaleAux multiplicity numerator denominator fuel next

def kineticThresholdBracket
    (multiplicity numerator denominator growthFuel bisectFuel : Nat) :
    KineticScaleBracket :=
  let upperSilent :=
    findSilentKineticScaleAux multiplicity numerator denominator growthFuel 1
  let initial :=
    kineticScaleBracket multiplicity numerator denominator 1 upperSilent
  bisectKineticScaleAux multiplicity numerator denominator bisectFuel initial

structure MachineMassLeg where
  baseLowerCost : Nat
  baseUpperCost : Nat
  amplification : Nat
  swapCost : Nat
  rungs : Nat
  loops : Nat
  lowerDenominator : Nat
  upperDenominator : Nat
  lowerGravityQuantumApprox : Option Float
  upperGravityQuantumApprox : Option Float
  lowerGravityQuantumScaledE30 : Nat
  upperGravityQuantumScaledE30 : Nat
  lowerKineticBracket : KineticScaleBracket
  upperKineticBracket : KineticScaleBracket
  probeScaleUsedForMass : Nat
  lowerMassApprox : Option Float
  upperMassApprox : Option Float
deriving Repr

def machineMassLeg
    (baseLower baseUpper amplification swapCost rungs loops
      kineticNumerator growthFuel bisectFuel : Nat) :
    MachineMassLeg :=
  let spinReport :=
    amplifiedSpinReport baseLower baseUpper amplification swapCost rungs
  let lowerDenominator := truncatedPiScale * spinReport.reflectedUpperCost
  let upperDenominator := truncatedPiScale * spinReport.reflectedLowerCost
  let lowerBracket :=
    kineticThresholdBracket SlipProbeChannel.electron.kineticMultiplicity
      kineticNumerator lowerDenominator growthFuel bisectFuel
  let upperBracket :=
    kineticThresholdBracket SlipProbeChannel.electron.kineticMultiplicity
      kineticNumerator upperDenominator growthFuel bisectFuel
  let probeScale :=
    min lowerBracket.lowerResolvingScale upperBracket.lowerResolvingScale
  let mass :=
    massResponse .electron baseLower baseUpper amplification swapCost rungs loops
      { numerator := kineticNumerator, scale := probeScale }
  { baseLowerCost := baseLower
    baseUpperCost := baseUpper
    amplification := amplification
    swapCost := swapCost
    rungs := rungs
    loops := loops
    lowerDenominator := lowerDenominator
    upperDenominator := upperDenominator
    lowerGravityQuantumApprox := carriedLoopApprox? 0 1 lowerDenominator
    upperGravityQuantumApprox := carriedLoopApprox? 0 1 upperDenominator
    lowerGravityQuantumScaledE30 := scaledRatioFloor scaleE30 1 lowerDenominator
    upperGravityQuantumScaledE30 := scaledRatioFloor scaleE30 1 upperDenominator
    lowerKineticBracket := lowerBracket
    upperKineticBracket := upperBracket
    probeScaleUsedForMass := probeScale
    lowerMassApprox := mass.lowerMassApprox
    upperMassApprox := mass.upperMassApprox }

structure TheoremLeg where
  budget : Nat
  runWithCostSpent : Nat
  clockClosed : Bool
  noInteractionClosed : Bool
deriving Repr

def theoremLeg (budget : Nat) : TheoremLeg :=
  let final := runWithCost budget initial
  { budget := budget
    runWithCostSpent := final.costSpent
    clockClosed := decide (final.costSpent = budget)
    noInteractionClosed := decide (detectInteraction? final = none) }

theorem theoremLeg_clockClosed (budget : Nat) :
    (theoremLeg budget).clockClosed = true := by
  unfold theoremLeg
  simp [runWithCost_spends, initial]

theorem theoremLeg_noInteractionClosed (budget : Nat) :
    (theoremLeg budget).noInteractionClosed = true := by
  unfold theoremLeg
  simp [detectInteraction?_never]

structure ElaborationEntropyLeg where
  lowerFailingBudget : Nat
  upperPassingBudget : Nat
  budgetWidth : Nat
  observedHeartbeats : Nat
  observedUserHeartbeatsFloor : Nat
  elapsedNanos : Nat
  sampleTextLength : Nat
deriving Repr

structure EntropySearchState where
  lowerFailingBudget : Nat
  upperPassingBudget : Nat
  observedHeartbeats : Nat
  elapsedNanos : Nat
  sampleTextLength : Nat
deriving Repr

def entropyLegOfState (state : EntropySearchState) : ElaborationEntropyLeg :=
  { lowerFailingBudget := state.lowerFailingBudget
    upperPassingBudget := state.upperPassingBudget
    budgetWidth := state.upperPassingBudget - state.lowerFailingBudget
    observedHeartbeats := state.observedHeartbeats
    observedUserHeartbeatsFloor := state.observedHeartbeats / 1000
    elapsedNanos := state.elapsedNanos
    sampleTextLength := state.sampleTextLength }

open Lean Lean.Elab.Command in
def measureEntropyUnderBudget?
    (budget : Nat) (sample : Unit -> String) :
    CommandElabM (Option (Nat × Nat × Nat)) := do
  liftTermElabM do
    tryCatchRuntimeEx
      (withCurrHeartbeats do
        withTheReader Core.Context
          (fun ctx => { ctx with maxHeartbeats := budget * 1000 }) do
            let started ← IO.monoNanosNow
            let (text, heartbeats) ← Lean.withHeartbeats do
              pure (sample ())
            let stopped ← IO.monoNanosNow
            pure (some (heartbeats, stopped - started, text.length)))
      (fun ex => do
        if ex.isRuntime then
          pure none
        else
          throw ex)

open Lean Lean.Elab.Command in
def findPassingEntropyBudgetAux
    (sample : Unit -> String) :
    Nat -> Nat -> Nat -> CommandElabM EntropySearchState
  | 0, lowerFailing, upperProbe => do
      let measured ← measureEntropyUnderBudget? upperProbe sample
      match measured with
      | some (heartbeats, elapsedNanos, textLength) =>
          pure
            { lowerFailingBudget := lowerFailing
              upperPassingBudget := upperProbe
              observedHeartbeats := heartbeats
              elapsedNanos := elapsedNanos
              sampleTextLength := textLength }
      | none =>
          pure
            { lowerFailingBudget := lowerFailing
              upperPassingBudget := upperProbe
              observedHeartbeats := 0
              elapsedNanos := 0
              sampleTextLength := 0 }
  | fuel + 1, lowerFailing, upperProbe => do
      let measured ← measureEntropyUnderBudget? upperProbe sample
      match measured with
      | some (heartbeats, elapsedNanos, textLength) =>
          pure
            { lowerFailingBudget := lowerFailing
              upperPassingBudget := upperProbe
              observedHeartbeats := heartbeats
              elapsedNanos := elapsedNanos
              sampleTextLength := textLength }
      | none =>
          findPassingEntropyBudgetAux sample fuel upperProbe (2 * upperProbe)

open Lean Lean.Elab.Command in
def bisectEntropyBudgetAux
    (sample : Unit -> String) :
    Nat -> EntropySearchState -> CommandElabM EntropySearchState
  | 0, state => pure state
  | fuel + 1, state => do
      if state.upperPassingBudget ≤ state.lowerFailingBudget + 1 then
        pure state
      else
        let mid := (state.lowerFailingBudget + state.upperPassingBudget) / 2
        let measured ← measureEntropyUnderBudget? mid sample
        match measured with
        | some (heartbeats, elapsedNanos, textLength) =>
            bisectEntropyBudgetAux sample fuel
              { lowerFailingBudget := state.lowerFailingBudget
                upperPassingBudget := mid
                observedHeartbeats := heartbeats
                elapsedNanos := elapsedNanos
                sampleTextLength := textLength }
        | none =>
            bisectEntropyBudgetAux sample fuel
              { state with lowerFailingBudget := mid }

open Lean Lean.Elab.Command in
def elaborationEntropyLeg
    (sample : Unit -> String) (growthFuel bisectFuel : Nat) :
    CommandElabM ElaborationEntropyLeg := do
  let state ← findPassingEntropyBudgetAux sample growthFuel 0 1
  let state ← bisectEntropyBudgetAux sample bisectFuel state
  pure (entropyLegOfState state)

structure MassTrilaterationReport where
  machine : MachineMassLeg
  elaborationEntropy : ElaborationEntropyLeg
  proofs : TheoremLeg
deriving Repr

inductive SearchStatus where
  | foundInteraction
  | stoppedByElabLimit
deriving Repr, DecidableEq

def keepRecentFaces : Nat -> List Face -> List Face
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, face :: faces => face :: keepRecentFaces n faces

def keepRecentStages : Nat -> List Stage -> List Stage
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, stage :: stages => stage :: keepRecentStages n stages

structure ElabInteractionReport where
  elabSteps : Nat
  status : SearchStatus
  finalStage : Stage
  finalFace : Face
  costSpent : Nat
  rngSeed : Nat
  lastPairing : Option PairingChoice
  spin : Spin
  spinSwapEvents : Nat
  firstSpinSwapCost : Option Nat
  lastSpinSwapCost : Option Nat
  electronElectronEvents : Nat
  electronElectronResidual : Int
  outerPairEvents : Nat
  junctionPairEvents : Nat
  bothPairEvents : Nat
  nonInteractingPairEvents : Nat
  outerPairResidual : Int
  junctionPairResidual : Int
  cooperPairResidue : Nat
  overflowPositronEvents : Nat
  pairTransfers : Int
  singleEvents : Nat
  pairEvents : Nat
  phaseTurns : Int
  tangeCount : Nat
  matterCount : Nat
  loopResidue : Nat
  alphaApprox : Option Float
  alphaInvApprox : Option Float
  fineStructureQuantum : Nat
  spinSwapAlphaApprox : Option Float
  foundInteraction : Bool
  recentStages : List Stage
  recentFaces : List Face
deriving Repr

def elabReport
    (elabSteps : Nat)
    (status : SearchStatus)
    (s : InteractionState)
    (foundInteraction : Bool)
    (recentStages : List Stage)
    (recentFaces : List Face) : ElabInteractionReport :=
  { elabSteps := elabSteps
    status := status
    finalStage := s.stage
    finalFace := s.face
    costSpent := s.costSpent
    rngSeed := s.rngSeed
    lastPairing := s.lastPairing
    spin := s.spin
    spinSwapEvents := s.spinSwapEvents
    firstSpinSwapCost := s.firstSpinSwapCost
    lastSpinSwapCost := s.lastSpinSwapCost
    electronElectronEvents := s.electronElectronEvents
    electronElectronResidual := s.electronElectronResidual
    outerPairEvents := s.outerPairEvents
    junctionPairEvents := s.junctionPairEvents
    bothPairEvents := s.bothPairEvents
    nonInteractingPairEvents := s.nonInteractingPairEvents
    outerPairResidual := s.outerPairResidual
    junctionPairResidual := s.junctionPairResidual
    cooperPairResidue := s.cooperPairResidue
    overflowPositronEvents := s.overflowPositronEvents
    pairTransfers := s.pairTransfers
    singleEvents := s.singleEvents
    pairEvents := s.pairEvents
    phaseTurns := s.phaseTurns
    tangeCount := s.face.positronCount
    matterCount := s.face.matterCount
    loopResidue := s.costSpent % 4
    alphaApprox := alphaApprox? s.costSpent
    alphaInvApprox := alphaInvApprox? s.costSpent
    fineStructureQuantum := fineStructureQuantum
    spinSwapAlphaApprox := spinSwapAlphaApprox? s.firstSpinSwapCost
    foundInteraction := foundInteraction
    recentStages := keepRecentStages 8 recentStages
    recentFaces := keepRecentFaces 8 recentFaces }

def searchLoop
    (elabSteps : Nat) :
    Nat -> InteractionState -> List Stage -> List Face -> ElabInteractionReport
  | 0, s, recentStages, recentFaces =>
      elabReport elabSteps .stoppedByElabLimit s false recentStages recentFaces
  | fuel + 1, s, recentStages, recentFaces =>
      match detectInteraction? s with
      | some _ =>
          elabReport elabSteps .foundInteraction s true recentStages recentFaces
      | none =>
          let next := step s
          searchLoop elabSteps fuel next (next.stage :: recentStages) (next.face :: recentFaces)

def searchWithElabFuel (elabSteps : Nat) : ElabInteractionReport :=
  searchLoop elabSteps elabSteps initial [initial.stage] [initial.face]

structure AlphaStepApprox where
  step : Nat
  finalStage : Stage
  finalFace : Face
  costSpent : Nat
  lastPairing : Option PairingChoice
  spin : Spin
  spinSwapEvents : Nat
  firstSpinSwapCost : Option Nat
  lastSpinSwapCost : Option Nat
  electronElectronResidual : Int
  outerPairResidual : Int
  junctionPairResidual : Int
  cooperPairResidue : Nat
  overflowPositronEvents : Nat
  pairTransfers : Int
  phaseTurns : Int
  loopResidue : Nat
  alphaApprox : Option Float
  alphaInvApprox : Option Float
  fineStructureQuantum : Nat
  spinSwapAlphaApprox : Option Float
  foundInteraction : Bool
deriving Repr

def alphaStepApprox (idx : Nat) (s : InteractionState) : AlphaStepApprox :=
  { step := idx
    finalStage := s.stage
    finalFace := s.face
    costSpent := s.costSpent
    lastPairing := s.lastPairing
    spin := s.spin
    spinSwapEvents := s.spinSwapEvents
    firstSpinSwapCost := s.firstSpinSwapCost
    lastSpinSwapCost := s.lastSpinSwapCost
    electronElectronResidual := s.electronElectronResidual
    outerPairResidual := s.outerPairResidual
    junctionPairResidual := s.junctionPairResidual
    cooperPairResidue := s.cooperPairResidue
    overflowPositronEvents := s.overflowPositronEvents
    pairTransfers := s.pairTransfers
    phaseTurns := s.phaseTurns
    loopResidue := s.costSpent % 4
    alphaApprox := alphaApprox? s.costSpent
    alphaInvApprox := alphaInvApprox? s.costSpent
    fineStructureQuantum := fineStructureQuantum
    spinSwapAlphaApprox := spinSwapAlphaApprox? s.firstSpinSwapCost
    foundInteraction :=
      match detectInteraction? s with
      | some _ => true
      | none => false }

def alphaLadderAux : Nat -> Nat -> InteractionState -> List AlphaStepApprox
  | 0, idx, s => [alphaStepApprox idx s]
  | fuel + 1, idx, s =>
      alphaStepApprox idx s :: alphaLadderAux fuel (idx + 1) (step s)

def alphaLadder (maxStep : Nat) : List AlphaStepApprox :=
  alphaLadderAux maxStep 0 initial

def foldsPerLoop : Nat :=
  4

def searchWithLoopFuel (loops : Nat) : ElabInteractionReport :=
  searchWithElabFuel (loops * foldsPerLoop)

open Lean Lean.Elab.Command in
elab "cooper_elab_run" n:num : command => do
  let report := searchWithElabFuel n.getNat
  logInfo (reprStr report)

open Lean Lean.Elab.Command in
elab "cooper_alpha_ladder" n:num : command => do
  logInfo (reprStr (alphaLadder n.getNat))

open Lean Lean.Elab.Command in
elab "cooper_elab_loop" n:num : command => do
  logInfo (reprStr (searchWithLoopFuel n.getNat))

open Lean Lean.Elab.Command in
elab "cooper_spin_bisect" swapCost:num rungs:num : command => do
  logInfo (reprStr (spinBisectReport swapCost.getNat rungs.getNat))

open Lean Lean.Elab.Command in
elab "cooper_amplified_spin"
    baseLower:num baseUpper:num amplification:num swapCost:num rungs:num : command => do
  logInfo (reprStr
    (amplifiedSpinReport baseLower.getNat baseUpper.getNat
      amplification.getNat swapCost.getNat rungs.getNat))

open Lean Lean.Elab.Command in
elab "cooper_amplified_spin_loops"
    baseLower:num baseUpper:num amplification:num swapCost:num
    rungs:num loops:num : command => do
  logInfo (reprStr
    (loopScaledSpinReport baseLower.getNat baseUpper.getNat
      amplification.getNat swapCost.getNat rungs.getNat loops.getNat))

open Lean Lean.Elab.Command in
elab "cooper_slip_probe"
    baseLower:num baseUpper:num amplification:num swapCost:num
    rungs:num loops:num gaugeNumerator:num gaugeScale:num
    kineticNumerator:num kineticScale:num : command => do
  logInfo (reprStr
    (slipProbeExperiment baseLower.getNat baseUpper.getNat
      amplification.getNat swapCost.getNat rungs.getNat loops.getNat
      { numerator := gaugeNumerator.getNat, scale := gaugeScale.getNat }
      { numerator := kineticNumerator.getNat, scale := kineticScale.getNat }))

open Lean Lean.Elab.Command in
elab "cooper_velocity_probe"
    baseLower:num baseUpper:num amplification:num swapCost:num
    rungs:num loops:num gaugeNumerator:num gaugeScale:num
    kineticNumerator:num kineticScale:num : command => do
  logInfo (reprStr
    (velocityExperiment baseLower.getNat baseUpper.getNat
      amplification.getNat swapCost.getNat rungs.getNat loops.getNat
      { numerator := gaugeNumerator.getNat, scale := gaugeScale.getNat }
      { numerator := kineticNumerator.getNat, scale := kineticScale.getNat }))

open Lean Lean.Elab.Command in
elab "cooper_mass_trilaterate"
    baseLower:num baseUpper:num amplification:num swapCost:num
    rungs:num loops:num kineticNumerator:num
    entropyGrowthFuel:num entropyBisectFuel:num : command => do
  let machine :=
    machineMassLeg baseLower.getNat baseUpper.getNat amplification.getNat
      swapCost.getNat rungs.getNat loops.getNat kineticNumerator.getNat
      entropyGrowthFuel.getNat entropyBisectFuel.getNat
  let sample := fun _ =>
    reprStr
      (machineMassLeg baseLower.getNat baseUpper.getNat amplification.getNat
        swapCost.getNat rungs.getNat loops.getNat kineticNumerator.getNat
        entropyGrowthFuel.getNat entropyBisectFuel.getNat)
  let entropy ←
    elaborationEntropyLeg sample entropyGrowthFuel.getNat
      entropyBisectFuel.getNat
  let proofs := theoremLeg (loops.getNat * foldsPerLoop)
  logInfo (reprStr
    { machine := machine
      elaborationEntropy := entropy
      proofs := proofs : MassTrilaterationReport })

cooper_elab_run 0
cooper_elab_run 1
cooper_elab_run 2
cooper_elab_run 5
cooper_elab_run 12
cooper_elab_run 37
cooper_elab_loop 1
cooper_alpha_ladder 5
cooper_mass_trilaterate 136 137 100000 13650000 64 100 1 64 40
#print axioms chosen_pairing_sound

end Measurement.CooperManual
