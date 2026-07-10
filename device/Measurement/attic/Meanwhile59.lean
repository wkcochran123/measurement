import Measurement.Meanwhile58

set_option maxRecDepth 4096

/- MEANWHILE 59 -- THE HORIZON STUDY CERTIFICATE. The relativistic correction
is not inserted as a coefficient by hand. A study certificate names a sequence
of timelike radii approaching the lightlike boundary from above:

  r_d = r_horizon + 1/d.

The device then executes the certificate. Each probe computes the Lorentz
coefficient and also elaborates a formal study of depth `d`, so the heartbeat
read is a real elaborator work measurement attached to the approach.
-/

namespace Measurement

def eventHorizonRadius : Nat :=
  naturalUnitOrbitRadius

def eventHorizonApproachDivisors : List Nat :=
  [8, 16, 32, 64, 128, 256]

def eventHorizonApproachRadius (divisor : Nat) : RationalRadius :=
  let d := Nat.max 1 divisor
  { numerator := eventHorizonRadius * d + 1
    denominator := d }

def eventHorizonGap (divisor : Nat) : ApparatusRatio :=
  { numerator := 1, denominator := Nat.max 1 divisor }

def relativisticOrbitCoefficientSquared?
    (velocitySquared : ApparatusRatio) : Option ApparatusRatio :=
  match lorentzGammaSquared? velocitySquared with
  | none => none
  | some gammaSquared => some (gammaSquared.mul velocitySquared.sq)

def optionRatioScaledFloor? (q? : Option ApparatusRatio) (scale : Nat) :
    Option Nat :=
  match q? with
  | none => none
  | some q => some (q.scaledFloor scale)

def optionNatWorkRatioScaledAt18? (heartbeat denominatorScaledAt18 : Nat) :
    Option Nat :=
  if denominatorScaledAt18 = 0 then
    none
  else
    some (heartbeat * pow10 18 / denominatorScaledAt18)

structure EventHorizonApproachRead where
  divisor : Nat
  radius : RationalRadius
  gapToHorizon : ApparatusRatio
  gapToHorizonScaledAt18 : Nat
  velocitySquared : ApparatusRatio
  velocitySquaredScaledAt18 : Nat
  gammaSquared? : Option ApparatusRatio
  gammaSquaredScaledAt18? : Option Nat
  relativisticCoefficientSquared? : Option ApparatusRatio
  relativisticCoefficientSquaredScaledAt18? : Option Nat
  regime : LorentzOrbitRegime
  timelikeSide : Bool
deriving Repr

def eventHorizonApproachRead (divisor : Nat) :
    EventHorizonApproachRead :=
  let radius := eventHorizonApproachRadius divisor
  let gap := eventHorizonGap divisor
  let velocitySquared := rationalOrbitVelocitySquared radius
  let gammaSquared? := lorentzGammaSquared? velocitySquared
  let coefficientSquared? :=
    relativisticOrbitCoefficientSquared? velocitySquared
  { divisor := divisor
    radius := radius
    gapToHorizon := gap
    gapToHorizonScaledAt18 := gap.scaledFloor (pow10 18)
    velocitySquared := velocitySquared
    velocitySquaredScaledAt18 := velocitySquared.scaledFloor (pow10 18)
    gammaSquared? := gammaSquared?
    gammaSquaredScaledAt18? :=
      optionRatioScaledFloor? gammaSquared? (pow10 18)
    relativisticCoefficientSquared? := coefficientSquared?
    relativisticCoefficientSquaredScaledAt18? :=
      optionRatioScaledFloor? coefficientSquared? (pow10 18)
    regime := lorentzOrbitRegime velocitySquared
    timelikeSide :=
      decide (lorentzOrbitRegime velocitySquared =
        LorentzOrbitRegime.timelikeOvershoot) }

def allHorizonReadsTimelike : List EventHorizonApproachRead -> Bool
  | [] => true
  | read :: rest => read.timelikeSide && allHorizonReadsTimelike rest

def eventHorizonApproachReads : List EventHorizonApproachRead :=
  eventHorizonApproachDivisors.map eventHorizonApproachRead

def eventHorizonStudyTruthBool : Bool :=
  allHorizonReadsTimelike eventHorizonApproachReads

def eventHorizonStudyTruth : Prop :=
  eventHorizonStudyTruthBool = true

namespace Fact

def EVENT_HORIZON_STUDY : Fact :=
  { truth := eventHorizonStudyTruth
    decTruth :=
      show Decidable (eventHorizonStudyTruthBool = true) from
        if h : eventHorizonStudyTruthBool = true then
          isTrue h
        else
          isFalse h }

end Fact

def eventHorizonStudyLimit : Limit :=
  .nil Fact.EVENT_HORIZON_STUDY

def eventHorizonStudySample : Sample :=
  .initial_condition Fact.EVENT_HORIZON_STUDY eventHorizonStudyLimit

def eventHorizonStudyTrial : Trial :=
  .hypothesis Fact.EVENT_HORIZON_STUDY eventHorizonStudySample

def eventHorizonFormalStudyAux : Nat -> Study -> Study
  | 0, study => study
  | fuel + 1, study =>
      eventHorizonFormalStudyAux fuel
        (.data Fact.EVENT_HORIZON_STUDY eventHorizonStudyTrial study)

def eventHorizonFormalStudy (depth : Nat) : Study :=
  eventHorizonFormalStudyAux depth
    (.hypothesis Fact.EVENT_HORIZON_STUDY)

structure EventHorizonStudyCertificate where
  name : String
  horizonRadius : Nat
  approachDivisors : List Nat
  approachReads : List EventHorizonApproachRead
  factDecision : Bool
  formalStudyDepths : List Nat
  certifiedTimelike : Bool
deriving Repr

def eventHorizonStudyCertificate : EventHorizonStudyCertificate :=
  { name := "event-horizon-approach-study-certificate"
    horizonRadius := eventHorizonRadius
    approachDivisors := eventHorizonApproachDivisors
    approachReads := eventHorizonApproachReads
    factDecision := factDecision Fact.EVENT_HORIZON_STUDY
    formalStudyDepths :=
      eventHorizonApproachDivisors.map fun divisor =>
        studyDataCount (eventHorizonFormalStudy divisor)
    certifiedTimelike := eventHorizonStudyTruthBool }

theorem eventHorizonStudyCertificate_certifies_timelike :
    eventHorizonStudyCertificate.certifiedTimelike = true := by
  rfl

def eventHorizonExecutionProbe (divisor : Nat) : Nat :=
  let read := eventHorizonApproachRead divisor
  let depth := studyDataCount (eventHorizonFormalStudy divisor)
  let gamma :=
    match read.gammaSquaredScaledAt18? with
    | none => 0
    | some value => value
  let coefficient :=
    match read.relativisticCoefficientSquaredScaledAt18? with
    | none => 0
    | some value => value
  depth * pow10 18 + read.velocitySquaredScaledAt18 + gamma + coefficient

register_heart_rate_as eventHorizon_warmup (eventHorizonExecutionProbe 8)
register_heart_rate_as eventHorizon_d008 (eventHorizonExecutionProbe 8)
register_heart_rate_as eventHorizon_d016 (eventHorizonExecutionProbe 16)
register_heart_rate_as eventHorizon_d032 (eventHorizonExecutionProbe 32)
register_heart_rate_as eventHorizon_d064 (eventHorizonExecutionProbe 64)
register_heart_rate_as eventHorizon_d128 (eventHorizonExecutionProbe 128)
register_heart_rate_as eventHorizon_d256 (eventHorizonExecutionProbe 256)

structure EventHorizonExecutionRead where
  divisor : Nat
  formalStudyDepth : Nat
  heartbeat : Nat
  gapToHorizonScaledAt18 : Nat
  velocitySquaredScaledAt18 : Nat
  gammaSquaredScaledAt18? : Option Nat
  relativisticCoefficientSquaredScaledAt18? : Option Nat
  heartbeatPerGammaSquaredScaledAt18? : Option Nat
  heartbeatPerCoefficientSquaredScaledAt18? : Option Nat
  regime : LorentzOrbitRegime
  timelikeSide : Bool
deriving Repr

def eventHorizonExecutionRead
    (divisor heartbeat : Nat) : EventHorizonExecutionRead :=
  let read := eventHorizonApproachRead divisor
  { divisor := divisor
    formalStudyDepth := studyDataCount (eventHorizonFormalStudy divisor)
    heartbeat := heartbeat
    gapToHorizonScaledAt18 := read.gapToHorizonScaledAt18
    velocitySquaredScaledAt18 := read.velocitySquaredScaledAt18
    gammaSquaredScaledAt18? := read.gammaSquaredScaledAt18?
    relativisticCoefficientSquaredScaledAt18? :=
      read.relativisticCoefficientSquaredScaledAt18?
    heartbeatPerGammaSquaredScaledAt18? :=
      match read.gammaSquaredScaledAt18? with
      | none => none
      | some gamma => optionNatWorkRatioScaledAt18? heartbeat gamma
    heartbeatPerCoefficientSquaredScaledAt18? :=
      match read.relativisticCoefficientSquaredScaledAt18? with
      | none => none
      | some coefficient =>
          optionNatWorkRatioScaledAt18? heartbeat coefficient
    regime := read.regime
    timelikeSide := read.timelikeSide }

def eventHorizonExecutionReads : List EventHorizonExecutionRead :=
  [ eventHorizonExecutionRead 8 eventHorizon_d008,
    eventHorizonExecutionRead 16 eventHorizon_d016,
    eventHorizonExecutionRead 32 eventHorizon_d032,
    eventHorizonExecutionRead 64 eventHorizon_d064,
    eventHorizonExecutionRead 128 eventHorizon_d128,
    eventHorizonExecutionRead 256 eventHorizon_d256 ]

def heartbeatsNondecreasing : List EventHorizonExecutionRead -> Bool
  | [] => true
  | [_] => true
  | left :: right :: rest =>
      decide (left.heartbeat <= right.heartbeat) &&
        heartbeatsNondecreasing (right :: rest)

structure EventHorizonStudyExecutionReport where
  certificate : EventHorizonStudyCertificate
  warmupHeartbeat : Nat
  executionReads : List EventHorizonExecutionRead
  certifiedTimelike : Bool
  heartbeatsNondecreasing : Bool
  finalDivisor : Nat
  finalGammaSquaredScaledAt18? : Option Nat
  finalRelativisticCoefficientSquaredScaledAt18? : Option Nat
  finalHeartbeat : Nat
deriving Repr

def eventHorizonStudyExecutionReport :
    EventHorizonStudyExecutionReport :=
  let finalRead := eventHorizonExecutionRead 256 eventHorizon_d256
  { certificate := eventHorizonStudyCertificate
    warmupHeartbeat := eventHorizon_warmup
    executionReads := eventHorizonExecutionReads
    certifiedTimelike := eventHorizonStudyCertificate.certifiedTimelike
    heartbeatsNondecreasing :=
      heartbeatsNondecreasing eventHorizonExecutionReads
    finalDivisor := finalRead.divisor
    finalGammaSquaredScaledAt18? := finalRead.gammaSquaredScaledAt18?
    finalRelativisticCoefficientSquaredScaledAt18? :=
      finalRead.relativisticCoefficientSquaredScaledAt18?
    finalHeartbeat := finalRead.heartbeat }

#eval eventHorizonStudyExecutionReport

end Measurement
