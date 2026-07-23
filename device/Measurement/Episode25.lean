import Measurement.Episode24

/- MEANWHILE 25 -- ROTATE THE CORRIDOR. The corridor is already a number once the
class instances interpret it. This file adds the rotation operation without
rebuilding the corridor: rotate the tape/read head, then ask the same resolved
instance fields; rotate the recovered bracket, then ask the existing face readers.
-/

/-! # Meanwhile 25 — the present received: the object, handed over whole  (❄ shake-test)

**The genre skin (❄).** Santa sets the box in John's hands. This is box 1 —
everything-that-is-not-zero, existence itself, held at `boxCount = 2` across from box 0 = zero
(`NamingClose`: two boxes; box 1 = "there is a box called zero" = distinguishable-from-the-origin).
He may turn it, weigh it, hold it to his ear and hear the something inside roll from face to face.
He may NOT open it — not yet.

**Object & facet.** Box 1 is the very object Yang–Mills describes, handed over whole and wrapped.
The walk that follows opens and DESCRIBES it one facet at a time — its weight next door (G), then
charge, mass, orbit, coupling, and on — each facet read in the device's own exact terms. We describe
the object facet by facet; we never claim to have opened or solved Yang–Mills. The last box — the
object's own ground — stays wrapped.

**The squeeze (overview).** Nothing is squeezed here: this file lays out the RULER the later facets
are squeezed on — `BracketedNumber` (whose `lower`/`upper` are the two exact bounds a facet is caught
between, `value` the pinned reading) and the period-3 charge/mass/value face wheel. (The finite π/2 crank
that once turned the wheel from a stored decimal list is RETIRED — π is now MEASURED off the orbit by the
polygon squeeze, `ArchimedesPi`.) There is no theorem in this file, only `#eval`: the object is received
whole and the wheel is turned and read off — computed, never a receipt — before the first bracket closes
next door at G.
-/

namespace Measurement

universe i j

namespace Number

/-- `corridorDepth : Number → Nat` — the height of a unary `Number`: the count of `.one` constructors
before the terminal `.zero`, by structural recursion (`.zero _ ↦ 0`; `.one _ n ↦ corridorDepth n + 1`).
The exact integer a later facet's depth is read from; here it only graduates the ruler. -/
def corridorDepth : Number -> Nat
  | .zero _ => 0
  | .one _ n => corridorDepth n + 1

end Number

/-- `CompilerTapeCell` — one cell of the compiler tape (the "wrapping"): either a `.strap` (two `Fact`s
and a value type with its lift) or a `.compute` (adding a `Prop` and a further lift). A cell is the unit
the tape is rotated by, one fold at a time. -/
inductive CompilerTapeCell where
  | strap : Fact -> Fact -> Type i -> Type (i+1) -> CompilerTapeCell
  | compute : Fact -> Fact -> Prop -> Type i -> Type (i+1) -> Type (i+1) -> CompilerTapeCell

namespace CompilerTapeCell

/-- `CompilerTapeCell.plug : CompilerTapeCell → CompilerTape → CompilerTape` — prepend a cell to a tape,
matching on the cell's shape (`.strap`/`.compute`) and re-attaching it ahead of `tail`. The primitive
that adds one fold to the front of the wrapping. -/
def plug : CompilerTapeCell -> CompilerTape -> CompilerTape
  | .strap a b value lifted, tail => .strap a b value lifted tail
  | .compute a b p value lifted liftedAgain, tail =>
      .compute a b p value lifted liftedAgain tail

end CompilerTapeCell

namespace CompilerTape

/-- `CompilerTape.length : CompilerTape → Nat` — the number of cells on a tape (`.boot ↦ 1`; each
`.strap`/`.compute` adds one to its tail's length). The modulus `rotateBounded` reduces the turn count
by, so a full revolution returns the tape unchanged. -/
def length : CompilerTape -> Nat
  | .boot _ _ => 1
  | .strap _ _ _ _ tail => length tail + 1
  | .compute _ _ _ _ _ _ tail => length tail + 1

/-- `CompilerTape.snoc : CompilerTape → CompilerTapeCell → CompilerTape` — append a cell to the far end
of a tape, recursing to the boot and plugging the cell there. The dual of `plug`: adds a fold at the
back. -/
def snoc : CompilerTape -> CompilerTapeCell -> CompilerTape
  | .boot f value, cell => cell.plug (.boot f value)
  | .strap a b value lifted tail, cell =>
      .strap a b value lifted (snoc tail cell)
  | .compute a b p value lifted liftedAgain tail, cell =>
      .compute a b p value lifted liftedAgain (snoc tail cell)

/-- `CompilerTape.rotateOnce : CompilerTape → CompilerTape` — turn the wrapping by one: lift the head
cell and `snoc` it onto the tail (a cyclic shift). `.boot` is a fixed point (a one-cell tape cannot
rotate). No cell is created or lost. -/
def rotateOnce : CompilerTape -> CompilerTape
  | .boot f value => .boot f value
  | .strap a b value lifted tail =>
      snoc tail (.strap a b value lifted)
  | .compute a b p value lifted liftedAgain tail =>
      snoc tail (.compute a b p value lifted liftedAgain)

/-- `CompilerTape.rotate : Nat → CompilerTape → CompilerTape` — apply `rotateOnce` `n` times by
structural recursion on `n` (`0 ↦ id`). Turning the wrapping `n` folds. -/
def rotate : Nat -> CompilerTape -> CompilerTape
  | 0, tape => tape
  | n + 1, tape => rotate n (rotateOnce tape)

/-- `CompilerTape.rotateBounded (turns) (tape) : CompilerTape` — rotate by `turns % tape.length`, so the
turn wraps back on itself after a full revolution. The bounded crank of the wrapping. -/
def rotateBounded (turns : Nat) (tape : CompilerTape) : CompilerTape :=
  rotate (turns % tape.length) tape

/-- `CompilerTape.headSlip : CompilerTape → Fact` — read the seam at the head of the tape: on a
`.compute` cell, the exclusive-or of its two carried facts (`¬(c.truth ↔ s.truth)`, with the matching
decidability instance); on `.boot`/`.strap` there is no seam, so `False`. The "peek" at where the
paper's edges meet — a later slip facet reads it; none is opened here. -/
def headSlip : CompilerTape -> Fact
  | .compute c s _ _ _ _ _ =>
      { truth := ¬(c.truth ↔ s.truth)
        decTruth := @instDecidableNot _ (@instDecidableIff _ _ c.decTruth s.decTruth) }
  | .boot _ _ => { truth := False, decTruth := isFalse (fun h => h) }
  | .strap _ _ _ _ _ => { truth := False, decTruth := isFalse (fun h => h) }

end CompilerTape

/-- `Fact.asBool : Fact → Bool` — collapse a `Fact` to its decided verdict (`isTrue ↦ true`,
`isFalse ↦ false`) via its `decTruth`. Turns a seam read into a plain yes-or-no. -/
def Fact.asBool (f : Fact) : Bool :=
  match f.decTruth with
  | .isTrue _ => true
  | .isFalse _ => false

/-- `rotatedTraceSlip Value Carrier rung Lifted turns : Fact` — turn a real executed trace's own tape by
`turns` (bounded) and read the seam at its head. Reads the slip off the live compiler tape rather than a
constructed one. -/
def rotatedTraceSlip
    (Value : Type i) (Carrier : CarrierProcess Value) (rung : Nat) (Lifted : Type j)
    [top : EXECUTED_TRACE Value Carrier rung Lifted] (turns : Nat) : Fact :=
  CompilerTape.headSlip (CompilerTape.rotateBounded turns top.tape)

/-- `rotatedTraceSlipBool … : Bool` — `rotatedTraceSlip` collapsed to a yes-or-no via `Fact.asBool`: did
the turned trace's head seam gap, or not. -/
def rotatedTraceSlipBool
    (Value : Type i) (Carrier : CarrierProcess Value) (rung : Nat) (Lifted : Type j)
    [top : EXECUTED_TRACE Value Carrier rung Lifted] (turns : Nat) : Bool :=
  (rotatedTraceSlip Value Carrier rung Lifted turns).asBool

namespace BracketedNumber

/-- `BracketedNumber.rotateForward : BracketedNumber → BracketedNumber` — a third of a turn of the
number's three faces: `lower ← upper`, `upper ← value`, `value ← lower`. No face is added or lost; the
same three come round. This is the wheel the facet brackets ride on. -/
def rotateForward (n : BracketedNumber) : BracketedNumber :=
  { lower := n.upper
    upper := n.value
    value := n.lower }

/-- `BracketedNumber.rotate : Nat → BracketedNumber → BracketedNumber` — apply `rotateForward` `turns`
times by structural recursion (`0 ↦ id`). Turning the number's face wheel. -/
def rotate : Nat -> BracketedNumber -> BracketedNumber
  | 0, n => n
  | turns + 1, n => rotate turns (rotateForward n)

end BracketedNumber

/-- `CorridorFace` — the three faces of the wheel: `charge`, `mass`, `value`. `Repr` for readouts,
`DecidableEq` so face comparisons are kernel-decidable. -/
inductive CorridorFace where
  | charge
  | mass
  | value
deriving Repr, DecidableEq

/-- `CorridorFace.rotate : CorridorFace → CorridorFace` — advance one face: `charge ↦ mass ↦ value ↦
charge`, a cycle of period 3. -/
def CorridorFace.rotate : CorridorFace -> CorridorFace
  | .charge => .mass
  | .mass => .value
  | .value => .charge

/-- `CorridorFace.rotateN : Nat → CorridorFace → CorridorFace` — advance a face `n` steps by structural
recursion (`0 ↦ id`). Which face shows after `n` thirds of a turn. -/
def CorridorFace.rotateN : Nat -> CorridorFace -> CorridorFace
  | 0, face => face
  | n + 1, face => rotateN n face.rotate

/-- `pow10 : Nat → Nat` — ten to the `n`, by structural recursion (`0 ↦ 1`; `n+1 ↦ 10 * pow10 n`). The
exact decimal scale a reading is taken to (`readoutScale` = eighteen places). -/
def pow10 : Nat -> Nat
  | 0 => 1
  | n + 1 => 10 * pow10 n

/-- `readoutScale : Nat` — the ×1e18 fixed-point READOUT scale (audit #6, declared once). This is a base-10
display convention (the device's chosen readout alphabet), NOT a physics constant — every scaled reading
(`scaledFloor`/`inverseScaledFloor readoutScale`, the ×1e18 α/G/etc. readouts) is taken to `readoutScale`
places. Named once here instead of the ~66 inline `readoutScale`. -/
def readoutScale : Nat := pow10 18

-- ⭐ RETIRED (2026-07-22, operator "go for retirement"): the finite π/2 crank — `piDecimalDigits` (the
-- stored 40-digit list), `piTruncatedTurns`, `halfPiTruncatedTurns`(+Remainder) — is REMOVED. π is no
-- longer a memorized decimal list here; it is MEASURED off the device's own orbit by the polygon squeeze
-- (`ArchimedesPi`, π ∈ (223/71, 22/7) proved axiom-free), and the nowtrino sources π's fractional part
-- from that measurement (`AffineConstant`). The digit list died by EARNING. (Ep25 can't import
-- ArchimedesPi — that would cycle — so the crank is retired by removal, not rewired in place.) The
-- corridor's rotation machinery below (`corridorReducedTurns`, the face wheel) is UNCHANGED.

/-- `corridorPeriod : Nat` — the wheel's period, `3` (three faces). The modulus every face count reduces
by. -/
def corridorPeriod : Nat :=
  3

/-- `corridorReducedTurns (turns) : Nat` — `turns % corridorPeriod`: all that survives of a turn count as
far as which face shows. -/
def corridorReducedTurns (turns : Nat) : Nat :=
  turns % corridorPeriod

-- ⭐ RETIRED (with the π/2 crank above): `RotatedCorridorRead` / `rotatedCorridorRead` / `driverBracket`
-- / `rotatedDriverCorridor` — the readout that cranked the corridor by the truncated half-π and printed
-- it across precisions "as π's decimals come in." With the digit list retired (π now MEASURED off the
-- orbit, `ArchimedesPi`), this decimals-driven demo is gone. The bin tally and the gravity-slip read
-- below (which do NOT depend on π) remain the file's readouts.

/-- `CorridorFace.ofReducedTurns : Nat → CorridorFace` — the face for a reduced (mod-3) turn count
(`0 ↦ charge`, `1 ↦ mass`, else `value`). -/
def CorridorFace.ofReducedTurns : Nat -> CorridorFace
  | 0 => .charge
  | 1 => .mass
  | _ => .value

/-- `CorridorFace.ofTurns (turns) : CorridorFace` — the face for a raw turn count, via
`ofReducedTurns (corridorReducedTurns turns)`. -/
def CorridorFace.ofTurns (turns : Nat) : CorridorFace :=
  ofReducedTurns (corridorReducedTurns turns)

/-- `corridorTripletIndex (turns) : Nat` — how many full three-face turns have passed,
`turns / corridorPeriod`. -/
def corridorTripletIndex (turns : Nat) : Nat :=
  turns / corridorPeriod

/-- `valueForMassTriplet (turns) : Nat` — `turns`, nudged up by one exactly when the turn lands on the
mass face; else `turns`. The off-by-one that marks the mass face as it comes up. -/
def valueForMassTriplet (turns : Nat) : Nat :=
  match CorridorFace.ofTurns turns with
  | .mass => turns + 1
  | _ => turns

/-- `valueForChargeTriplet (turns) : Nat` — `turns`, nudged up by one exactly on the charge face; else
`turns`. The charge-face counterpart of `valueForMassTriplet`. -/
def valueForChargeTriplet (turns : Nat) : Nat :=
  match CorridorFace.ofTurns turns with
  | .charge => turns + 1
  | _ => turns

/-- `chargeTurnsUpTo (n) : Nat` — how many charge faces have come up by `n`: `n / corridorPeriod`. -/
def chargeTurnsUpTo (n : Nat) : Nat :=
  n / corridorPeriod

/-- `massTurnsUpTo (n) : Nat` — mass faces up to `n`: `n / corridorPeriod`, plus one once the remainder
has reached the mass face. -/
def massTurnsUpTo (n : Nat) : Nat :=
  n / corridorPeriod + if 1 <= n % corridorPeriod then 1 else 0

/-- `valueTurnsUpTo (n) : Nat` — value faces up to `n`: `n / corridorPeriod`, plus one once the remainder
has reached the value face. -/
def valueTurnsUpTo (n : Nat) : Nat :=
  n / corridorPeriod + if 2 <= n % corridorPeriod then 1 else 0

/-- `countBetween (countUpTo) (lower) (upper) : Nat` — tally a face across `[lower, upper]` by
subtracting cumulative counts (`0` if `upper < lower`; else `countUpTo upper - countUpTo (lower-1)`). -/
def countBetween (countUpTo : Nat -> Nat) (lower upper : Nat) : Nat :=
  if upper < lower then
    0
  else
    countUpTo upper - countUpTo (lower - 1)

/-- `CorridorBinReport` — a per-bin tally: the bin `[lower, upper]`, the total, the charge/mass/value
counts inside, and the reduced turn and face the top of the bin lands on. -/
structure CorridorBinReport where
  lower : Nat
  upper : Nat
  total : Nat
  chargeCount : Nat
  massCount : Nat
  valueCount : Nat
  upperReducedTurns : Nat
  upperFace : CorridorFace
deriving Repr

/-- `corridorBinReport (lower) (upper) : CorridorBinReport` — assemble the tally for `[lower, upper]`:
total (`0` if empty), each face's `countBetween`, and the top face. -/
def corridorBinReport (lower upper : Nat) : CorridorBinReport :=
  { lower := lower
    upper := upper
    total := if upper < lower then 0 else upper - lower + 1
    chargeCount := countBetween chargeTurnsUpTo lower upper
    massCount := countBetween massTurnsUpTo lower upper
    valueCount := countBetween valueTurnsUpTo lower upper
    upperReducedTurns := corridorReducedTurns upper
    upperFace := CorridorFace.ofTurns upper }

/-- `CorridorFace.isMotionSlip : CorridorFace → Bool` — flag the mass face as the motion slip
(`mass ↦ true`; `charge`/`value ↦ false`). -/
def CorridorFace.isMotionSlip : CorridorFace -> Bool
  | .mass => true
  | .charge => false
  | .value => false

/-- `intMagnitude : Int → Nat` — the size of a signed integer (`.ofNat n ↦ n`; `.negSucc n ↦ n+1`). The
magnitude a signed stimulus is read by. -/
def intMagnitude : Int -> Nat
  | .ofNat n => n
  | .negSucc n => n + 1

/-- `WheelStimulusRead` — a labelled signed number dropped onto the wheel: its label, signed value and
magnitude, triplet index, the charge- and mass-nudged counts, the reduced turn, the face its magnitude
lands on, and whether that face moves. -/
structure WheelStimulusRead where
  label : String
  signedValue : Int
  magnitude : Nat
  tripletIndex : Nat
  valueForCharge : Nat
  valueForMass : Nat
  reducedTurns : Nat
  face : CorridorFace
  motionSlip : Bool
deriving Repr

/-- `wheelStimulusRead (label) (value) : WheelStimulusRead` — drop `value` onto the wheel: take its
magnitude, reduce mod 3 to a face, and fill the triplet index, the two nudged counts, the face, and the
motion flag. -/
def wheelStimulusRead (label : String) (value : Int) : WheelStimulusRead :=
  let magnitude := intMagnitude value
  let reducedTurns := corridorReducedTurns magnitude
  let face := CorridorFace.ofReducedTurns reducedTurns
  { label := label
    signedValue := value
    magnitude := magnitude
    tripletIndex := corridorTripletIndex magnitude
    valueForCharge := valueForChargeTriplet magnitude
    valueForMass := valueForMassTriplet magnitude
    reducedTurns := reducedTurns
    face := face
    motionSlip := face.isMotionSlip }

/-- `BuildGravitySlipReport` — the composite read: the bin tally (`dial`), the electron's box value, the
gravity face (mass), whether the dial's top face moves, and the build's measured numbers dropped on the
wheel as stimuli and friction reads. -/
structure BuildGravitySlipReport where
  dial : CorridorBinReport
  electronBoxValue : Nat
  gravityFace : CorridorFace
  dialExtraIsMotion : Bool
  buildStimuli : List WheelStimulusRead
  frictionReads : List WheelStimulusRead
deriving Repr

/-- `buildGravitySlipReport (lower) (upper) : BuildGravitySlipReport` — gather the composite: the bin
report over `[lower, upper]`, gravity pinned to the mass face, and the earlier files' heart-rates and
binding-energies (`theHeartRate`, `predictedHeartRate`, the `elabBindingEnergy…`) read onto the wheel. -/
def buildGravitySlipReport (lower upper : Nat) : BuildGravitySlipReport :=
  let dial := corridorBinReport lower upper
  { dial := dial
    electronBoxValue := electronBox.val
    gravityFace := .mass
    dialExtraIsMotion := dial.upperFace.isMotionSlip
    buildStimuli :=
      [ wheelStimulusRead "theHeartRate" (Int.ofNat theHeartRate),
        wheelStimulusRead "g0_r2" (Int.ofNat g0_r2),
        wheelStimulusRead "predictedHeartRate" predictedHeartRate,
        wheelStimulusRead "targetB2" targetB2,
        wheelStimulusRead "targetDriver" targetDriver,
        wheelStimulusRead "targetDriverDef" targetDriverDef ]
    frictionReads :=
      [ wheelStimulusRead "bindingEnergyB2" elabBindingEnergyB2,
        wheelStimulusRead "bindingEnergyDriver" elabBindingEnergyDriver,
        wheelStimulusRead "bindingEnergyDriverDef" elabBindingEnergyDriverDef ] }

/-! ## Readouts — turn the wheel and print it (computed, not proved)
Two `#eval`s: the bin tally over `[1, 1000000]` and the composite gravity-slip read. (The precision-swept
driver corridor is retired with the π/2 crank — π is now MEASURED off the orbit, not cranked from stored
digits.) No theorem stands under either — the object is received whole and the wheel is read off, before
the first facet is squeezed next door at G. The last box stays wrapped. -/
#eval corridorBinReport 1 1000000

#eval buildGravitySlipReport 1 1000000

end Measurement
