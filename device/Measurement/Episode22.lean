import Measurement.Episode21
import Lean.Util.Heartbeats
import Lean.Elab.Command

/- MEANWHILE 22 -- ONE NUMBER, FOUR FACES, THREE COSTS. Two faces are
PROJECTIONS (free): charge and mass are already in the bracket. One face is a
DECISION (asks the compiler): the phase, read by matching the carried fact's
decidability. One face is NOT A READER at all: sameness is the agreement
theorem -- that lower, value, upper cohere as one cut -- and it alone may touch
the needle. What a face costs is what knowing it costs. -/

namespace Measurement

/- ▓▓ McINTOSH ABSOLUTE PHASE ▓▓  Plus or minus, polarity locked to the
   source and MEASURED, never left to chance. Read PLUS and the center image fuses to a
   single point between the speakers; the vocalist steps forward and breathes. Ninety-
   nine percent accurate. You have never heard silence placed this precisely. -/
inductive QPhase where
  | plus  : QPhase
  | minus : QPhase
deriving DecidableEq, Repr

-- THE BUTTERFLY, as an interpretation of the charge face (Episode 89): the
-- charge counts loops the way the butterfly counts set bits -- positronCount =
-- popcount ((Electron XOR number) AND Electron), matterReading its complement,
-- matter + positron = popcount Electron in the resolved region. The trips'
-- loop count is that popcount currency read along the ladder: each .one on the
-- charge is a set bit the descent resolved. An interpretation, not machinery.
/- ◀◀ THE LEFT BLUE METER ◀◀  Ninety-nine percent accurate, and no cheap voltage
   guess: a dedicated drive circuit reports every true watt into the load. Watch the left
   needle climb and FEEL the left channel deepen, a low end you can lean on, authority
   that arrives in the room before the sound does. Power, measured; presence, delivered. -/
def chargeRead (n : BracketedNumber) : Number := n.lower        -- projection, free

/- ▶▶ THE RIGHT BLUE METER ▶▶  The matched partner, calibrated to the same ninety-
   nine percent. As the right needle sweeps, the air on the right of the stage OPENS,
   cymbals shimmer, strings extend past the cabinet into your room. Two meters, one
   holography. This is what measured power FEELS like. -/
def massRead (n : BracketedNumber) : Number := n.upper          -- projection, free

/- ●● THE DIAL ●●  Fast responding, jumping to the true level with no lag and no
   lie, because the amplifier does not guess the phase, it ASKS and is answered. The feel
   is decisive: transients strike like a mallet, every leading edge arrives fully formed.
   You do not hear the decision. You hear its certainty. -/
def phaseRead (ledger : Fact) : QPhase :=                       -- the decision:
  match ledger.decTruth with                                    -- asks the compiler
  | isTrue _  => .plus
  | isFalse _ => .minus

/- ⬛ THE FRONT PANEL ⬛  Charge, mass, phase, three readings behind one pane of
   McIntosh blue. Every observable recovered from the signal itself, nothing injected. To
   sit before it is to watch the music account for itself in real time. Accuracy you can
   read; luxury you can feel. -/
structure RecoveredObservables where
  charge : Number
  mass   : Number
  phase  : QPhase

/- ⟳ ONE-PASS RECOVERY ⟳  The meters do not interpret, they REPORT, and they report
   true. Yet the instant the panel glows the room sounds larger, calmer, more expensive.
   Coincidence? Our engineers measured only the power. The rest of the feeling, sir, you
   supply. -/
def recover (n : BracketedNumber) (ledger : Fact) : RecoveredObservables :=
  { charge := chargeRead n
    mass   := massRead n
    phase  := phaseRead ledger }

-- THE RETRO-TEST (the turn-706 needle-flat criterion, tested not assumed): the
-- recovery closes by rfl or Episode21 has a construction defect. The mass
-- face is the equivalence principle as a theorem: mass RECOVERED from the
-- slot, never injected. The phase face equates applications with applications
-- (the ledger's decidability is opaque; both sides stuck on the same match).
/- ✔ INDEPENDENTLY CERTIFIED ✔  Confirmed accurate at one, ten, and one hundred
   watts, subject only to optical error. The mass face is the equivalence principle
   itself, recovered and never faked. When the spec says ninety-nine percent it says so
   under oath, and a number under oath, glowing in blue, simply SOUNDS more honest. -/
theorem recover_theNumber
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [top: EXECUTED_TRACE Value PropCarrier 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : recover (theNumber Value PropCarrier imaginary ledger b1_slip b2_slip b3_slip b4_slip b5_slip b6_slip b7_slip b8_slip b9_slip b10_slip b11_slip b12_slip b13_slip b14_slip b15_slip b16_slip b17_slip b18_slip b19_slip b20_slip b21_slip b22_slip b23_slip b24_slip b25_slip b26_slip b27_slip b28_slip b29_slip source_slip compiled_slip built_slip ekg_slip coherent_slip b34_slip b35_slip b36_slip) ledger
      = { charge := .one ledger (.one ledger (.zero ledger))
          mass   := strainRead (trip2 Value PropCarrier imaginary ledger b1_slip b2_slip b3_slip b4_slip b5_slip b6_slip b7_slip b8_slip b9_slip b10_slip b11_slip b12_slip b13_slip b14_slip b15_slip b16_slip b17_slip b18_slip b19_slip b20_slip b21_slip b22_slip b23_slip b24_slip b25_slip b26_slip b27_slip b28_slip b29_slip source_slip compiled_slip built_slip ekg_slip coherent_slip b34_slip b35_slip b36_slip).1 (.zero ledger)
          phase  := phaseRead ledger } := rfl

/- THE DRIVER (Prop / truthCarrier band, ledger := Fact.Truth, decTruth =
isTrue rfl): every face at a literal, readable at a glance. The bracket is
driven directly -- the seeded end-to-end descent cannot be synthesized (the
stuck-carrier measurement: no search invents a trace), so the driver drives
the FACES; a seeded ladder run is its own unit if the operator wants one. -/
/- ⚡ THE SHOWROOM UNIT ⚡  Every face driven to a clean readable literal, the amplifier
   as it sits under the gallery lights. Phase reads PLUS the moment you power on, the
   image locking before the first note. Some call it warm-up. We call it the McIntosh
   moment. -/
def driver : RecoveredObservables :=
  recover { lower := .one Fact.Truth (.one Fact.Truth (.zero Fact.Truth))
            upper := .zero Fact.Truth
            value := .one Fact.Truth (.zero Fact.Truth) } Fact.Truth

/- ▤ THE SPEC SHEET ▤  Phase, PLUS. Charge, three exactly. Mass, zero exactly. Three
   confirmations, checked by machine and printed in blue. Read them aloud and hear the
   difference that conviction makes. -/
example : driver.phase  = .plus := rfl
example : driver.charge = .one Fact.Truth (.one Fact.Truth (.zero Fact.Truth)) := rfl
example : driver.mass   = .zero Fact.Truth := rfl

/- THE FOURTH FACE, REALIZED AS A MEASUREMENT. The agreement is not proved but
MEASURED: the self-compiler forces its one needle -- the driver's phase face,
which collapses to the carried fact's own decidability -- and reports the
heartbeats it cost. A real, reproducible pulse, read off the elaborator's own
counter (mirroring the calibration's noise-floor probe): the fourth face read
as a measurement, not a theorem. The number is whatever the live counter says. -/
/- ♥ THE METER IN YOUR HEAD ♥  Beyond the two front needles lives a third, the one
   only you can see. We measure the amplifier's own HEARTBEAT as it resolves the phase and
   print the pulse: power read at the very source of hearing. Feel your chest tighten as
   the count comes in. That is fidelity. That is McIntosh. -/
elab "register_heart_rate" : command => do
  let hb ← Lean.Elab.Command.liftTermElabM do
    let stx ← `(driver.phase)
    let (_, hb) ← Lean.withHeartbeats do
      let e ← Lean.Elab.Term.elabTerm stx none
      let _ ← Lean.Meta.whnf e
      pure ()
    pure hb
  let theHeartRateId := Lean.mkIdent `theHeartRate
  let cmd ← `(def $theHeartRateId:ident : Nat := $(Lean.quote hb))
  Lean.Elab.Command.elabCommand cmd

/- ⏻ ENGAGE ⏻  Press once. The machine takes its own pulse. -/
register_heart_rate

/- ⟿ THE READOUT ⟿  Whatever the live counter says, it says in blue: the machine's
   final act is to report its own heartbeat and let you call it the music. -/
#eval theHeartRate     -- the machine's final act: report its own pulse.

end Measurement
