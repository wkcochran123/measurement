import Std

/-!
An instruction-manual skeleton for closing an atom-recoil measurement onto the
fine structure constant.

The laboratory supplies the readings. Lean supplies the checked shape of the
ledger: which quantities are measured, which are imported, how corrections are
summed, and where the final reciprocal alpha is computed.
-/

namespace Measurement.AlphaManual

inductive Grade where
  | measured
  | given
  | reading
  | proved
  | poisoned
deriving Repr, DecidableEq

structure Datum where
  value : Float
  sigma : Float
  grade : Grade
deriving Repr

structure Correction where
  name : String
  delta : Float
  sigma : Float
  evidence : String
deriving Repr

def square (x : Float) : Float :=
  x * x

def correctionSum : List Correction -> Float
  | [] => 0.0
  | c :: cs => c.delta + correctionSum cs

def correctionVariance : List Correction -> Float
  | [] => 0.0
  | c :: cs => square c.sigma + correctionVariance cs

structure ClosedRecoil where
  raw : Datum
  corrections : List Correction
  value : Float
  sigma : Float
deriving Repr

def closeRecoil (raw : Datum) (corrections : List Correction) :
    ClosedRecoil :=
  { raw := raw
    corrections := corrections
    value := raw.value + correctionSum corrections
    sigma := Float.sqrt (square raw.sigma + correctionVariance corrections) }

theorem closeRecoil_value (raw : Datum) (corrections : List Correction) :
    (closeRecoil raw corrections).value =
      raw.value + correctionSum corrections := by
  rfl

structure Constants where
  rydberg : Datum
  relativeMassX : Datum
  relativeMassElectron : Datum
  lightSpeed : Datum
deriving Repr

structure AlphaInput where
  recoil : ClosedRecoil
  constants : Constants
deriving Repr

def bridgeProduct (input : AlphaInput) : Float :=
  (2.0 * input.constants.rydberg.value /
      input.constants.lightSpeed.value) *
    (input.constants.relativeMassX.value /
      input.constants.relativeMassElectron.value) *
    input.recoil.value

def alpha (input : AlphaInput) : Float :=
  Float.sqrt (bridgeProduct input)

def alphaInv (input : AlphaInput) : Float :=
  1.0 / alpha input

def relativeSigma (d : Datum) : Float :=
  d.sigma / d.value

def recoilRelativeSigma (r : ClosedRecoil) : Float :=
  r.sigma / r.value

def alphaRelativeSigma (input : AlphaInput) : Float :=
  0.5 * Float.sqrt
    (square (recoilRelativeSigma input.recoil) +
     square (relativeSigma input.constants.rydberg) +
     square (relativeSigma input.constants.relativeMassX) +
     square (relativeSigma input.constants.relativeMassElectron))

def alphaInvSigma (input : AlphaInput) : Float :=
  alphaInv input * alphaRelativeSigma input

structure AlphaReport where
  recoil : ClosedRecoil
  alpha : Float
  alphaInv : Float
  alphaInvSigma : Float
deriving Repr

def closeAlpha (input : AlphaInput) : AlphaReport :=
  { recoil := input.recoil
    alpha := alpha input
    alphaInv := alphaInv input
    alphaInvSigma := alphaInvSigma input }

theorem closeAlpha_inverse_value (input : AlphaInput) :
    (closeAlpha input).alphaInv = alphaInv input := by
  rfl

def codata2022AlphaInv : Datum :=
  { value := -1.0
    sigma := 1.0
    grade := .poisoned }

def rubidium87Constants : Constants :=
  { rydberg :=
      { value := 10973731.568157
        sigma := 0.000012
        grade := .given }
    relativeMassX :=
      { value := 86.909180520
        sigma := 0.000000010
        grade := .given }
    relativeMassElectron :=
      { value := 0.000548579909065
        sigma := 0.000000000016
        grade := .given }
    lightSpeed :=
      { value := 299792458.0
        sigma := 0.0
        grade := .given } }

def exampleRawRecoil : Datum :=
  { value := 4.591359258e-9
    sigma := 0.000000006e-9
    grade := .measured }

def exampleCorrections : List Correction :=
  [ { name := "wavefront"
      delta := 0.000000003e-9
      sigma := 0.000000002e-9
      evidence := "auxiliary wavefront map" },
    { name := "AC Stark"
      delta := -0.000000001e-9
      sigma := 0.000000001e-9
      evidence := "power reversal" } ]

def exampleInput : AlphaInput :=
  { recoil := closeRecoil exampleRawRecoil exampleCorrections
    constants := rubidium87Constants }

def exampleReport : AlphaReport :=
  closeAlpha exampleInput

#eval exampleReport.alphaInv

end Measurement.AlphaManual
