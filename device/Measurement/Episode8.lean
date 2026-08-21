/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

(c) 2026 [PATTER TODO: rights gag]

[PATTER TODO: cast chorus / epigraph]

lake build [PATTER TODO: build-flag gag]

__EPISODE 8__: _[PATTER TODO: title -- the galley proofs]_

Episode 7 answered the referees, one methodology paragraph per capability,
descending page 36 to page 1.  Episode 8 is the TYPESETTING: the galley proofs
climb back up, page 1 to the seam, and every page is lifted ONE UNIVERSE by
the typesetter.  The fold decides on each page's own facts; .results cells
record the execution onto the carried galley; the register -- the Box at its
current lift, the universe id -- is the typesetter's internal state, carried
in the class, never on the galley.  Which carrier emerges at the top is a
measurement of where the rebuttal landed; report what you get, do not force it.
-/

-- WE GET SIGNAL!
import Measurement.Episode7
set_option allowUnsafeReducibility true

-- MAIN SCREEN TURN ON
namespace Measurement

universe i j

/-
HOUSE-TAPE CHORUS, TRUE PANEL -- DRAFT STORY TEXT

This is the trace
that executed the tape
that lived in the Fact
that John built.

The tape is still one character.  The register is not on it.  The story is
not on it.  The trace is the house built around it after John starts driving
steel into the mountain.
-/
class TYPESET (Box: Type i) (Pigeon: CarrierProcess Box) (rung: Nat)
    (Lifted: Type j) where
  register_value : Lifted
  universe_id    : Number
  galley         : CompilerTape

/-
This is the origin
that carried the trace
that executed the tape
that lived in the Fact
that John built.

The first spike is boring on purpose: the carried value is just the carrier's
number, the universe id is zero, and the tape is whatever the trace brought
to the face.  Steel starts as a local receipt.
-/
instance (priority := low) TYPESET_origin
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 1]
    -- TANGE (law-6 read): CarrierProcess.value : Number (Episode 1), not Box --
    -- the spec's own body (register_value := Pigeon.value) forces the anchor's
    -- Lifted to Number; the value rides the ULift ladder from there.
    : TYPESET Box Pigeon 1 Number :=
  { register_value := Pigeon.value
    universe_id    := .zero Pigeon.symbol
    galley         := t.rebuttal }

/-
This is the metaprogram that admits the mark (Episode 5: CAN_YOU_SEE_A_CHARACTERISTIC):
the permission form that says a distinguished mark may be counted.
It is not the act of counting.  It is the local license-count,
Episode 8 wearing the first hard hat,
that admits the mark
that distinguishes the glyph
that carried the trace
that executed the tape
that lived in the Fact
that John built.

The tape does not become a novel.  The class dictionary does.
-/
instance (priority := low) TYPESET_page_2
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 2]
    [below: TYPESET Box Pigeon 1 Number]
    : TYPESET Box Pigeon 2 (ULift Number) :=
    -- the head-read, once (needle rule); the non-methodology arms are
    -- by-construction unreachable at page 2 but the match carries them --
    -- the direction exists, is handled, is never taken.
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    -- the Prop slot carries the page's own slip proposition, quoted (law 4);
    -- its decidability derives from the two decTruths when read, never here.
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that counts the number (Episode 5: CAN_YOU_COUNT_THEM):
the index-form that says the permitted count has an origin.
It is not an enumeration.  It is the place where enumeration can appear,
that counts the number
that admits the mark
that distinguishes the letter
that carried the trace
that executed the tape
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_3
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 3]
    [below: TYPESET Box Pigeon 2 (ULift Number)]
    : TYPESET Box Pigeon 3 (ULift (ULift Number)) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that encodes the glyph (Episode 5: CAN_YOU_LABEL_THEM):
the limit-form that gives the count a sequence-shaped mask.
It is not a message.  It is the local possibility of messagehood,
that encodes the glyph
that counts the number
that admits the value
that distinguishes the mark
that carried the trace
that executed the tape
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_4
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 4]
    [below: TYPESET Box Pigeon 3 (ULift (ULift Number))]
    : TYPESET Box Pigeon 4 (ULift (ULift (ULift Number))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that residues the code (Episode 5: CAN_YOU_SEE_THE_BOUNDARY):
the remainder-form, the leftover that survives being encoded.
It is not what the code means.  It is the gap the code is allowed to have,
that residues the code
that encodes the letter
that counts the variable
that admits the process
that distinguishes the glyph
that carried the trace
that executed the tape
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_5
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 5]
    [below: TYPESET Box Pigeon 4 (ULift (ULift (ULift Number)))]
    : TYPESET Box Pigeon 5 (ULift (ULift (ULift (ULift Number)))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that binaries the value (Episode 5: DID_THE_PARTICLE_COLOR_OUTSIDE_THE_LINES):
the two-faced observation-form born from the remainder.
It is not a bit being read.  It is the stage on which before and after
can pretend to disagree,
that binaries the value
that residues the model
that encodes the code
that counts the step
that admits the method
that distinguishes the glyph
that carried the trace
that executed the tape
that lived in the Fact
that John built.

By now the stanza is already longer than the tape.  That is the point.
-/
instance (priority := low) TYPESET_page_6
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 6]
    [below: TYPESET Box Pigeon 5 (ULift (ULift (ULift (ULift Number))))]
    : TYPESET Box Pigeon 6 (ULift (ULift (ULift (ULift (ULift Number))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that repeats the process (Episode 5: DO_YOU_HEAR_A_BUNCH_OF_CLICKS):
the ritual form where a binary remainder becomes stimulus and expectation.
Not repetition yet: the contract under which repetition can accuse the tape.
that repeats the process
that binaries the value
that residues the model
that encodes the code
that counted the number
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_7
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 7]
    [below: TYPESET Box Pigeon 6 (ULift (ULift (ULift (ULift (ULift Number)))))]
    : TYPESET Box Pigeon 7 (ULift (ULift (ULift (ULift (ULift (ULift Number)))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that numbers the value (Episode 5: HOW_MANY_CLICKS_DO_YOU_HEAR):
the output form that lets repeatability wear the mask of computation.
Not a number yet: the promise that "some output" can stand in the witness box.
that numbers the value
that repeats the function
that binaries the glyph
that residues the step
that admitted the mark
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_8
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 8]
    [below: TYPESET Box Pigeon 7 (ULift (ULift (ULift (ULift (ULift (ULift Number))))))]
    : TYPESET Box Pigeon 8 (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that represents the code (Episode 5: WRITE_DOWN_HOW_MANY_CLICKS_YOU_HEAR_IN_A_TABLE):
the program form that closes the output into a state.
Not representation itself: the receipt that a state may be called a program.
that represents the code
that numbers the value
that repeats the process
that binaries the method
that distinguished the glyph
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_9
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 9]
    [below: TYPESET Box Pigeon 8 (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))]
    : TYPESET Box Pigeon 9 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that physicals the method (Episode 5: ROSS!_GET_THE_READOUTS):
the hardware alibi, where halting and nonhalting become threshold language.
Not matter yet: the claim that electrons are already enough of an argument.
that physicals the method
that represents the mapping
that numbers the mark
that repeats the function
that carried the trace
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_10
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 10]
    [below: TYPESET Box Pigeon 9 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))]
    : TYPESET Box Pigeon 10 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that compares the process:
the borrowed bridge Episode 5 requires before observation can enter.
Not comparison yet: the permission for two processes to be placed under one eye.
that compares the process
that physicals the method
that represents the code
that numbers the variable
that executed the tape
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_11
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 11]
    [below: TYPESET Box Pigeon 10 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))]
    : TYPESET Box Pigeon 11 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that observes the mark (Episode 5: DO_YOU_SEE_THE_LIGHT_FLASH_WHEN_YOU_HEAR_THE_CLICK):
the projection form where stress, threshold, and symbol make a slip-process.
Not seeing yet: the theater in which seeing can be reported.
that observes the mark
that compares the process
that physicals the step
that represents the model
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_12
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 12]
    [below: TYPESET Box Pigeon 11 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))]
    : TYPESET Box Pigeon 12 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that presents the process (Episode 5: THATS_THE_PHOTOELECTRIC_EFFECT):
the Santa-Claus form, absurd on the surface and exact in the dependency graph.
Not presence yet: the current-tense wrapper around an already observed process.
that presents the process
that observes the glyph
that compares the model
that physicals the method
that carried the value
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_13
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 13]
    [below: TYPESET Box Pigeon 12 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))]
    : TYPESET Box Pigeon 13 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that measures the step (Episode 5: THE_PHOTON_IS_MEASURABLE):
the gauge form that gives present observation a clock.
Not measurement yet: the clock-face where measurement can pretend it arrived.
that measures the step
that presents the value
that observes the process
that compares the glyph
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_14
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 14]
    [below: TYPESET Box Pigeon 13 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))]
    : TYPESET Box Pigeon 14 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that gungans the glyph (Episode 5: PERHAPS_NOT_WITH_A_MULTIMETER_BUT_YOU_UNDERSTAND_WHAT_I_MEAN):
the translation layer where a gauge becomes concept-color and comic syntax.
Not nonsense: the dialect adapter proving nonsense can be type-directed.
that gungans the glyph
that measures the method
that presents the glyph
that observes the mark
that carried the process
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_15
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 15]
    [below: TYPESET Box Pigeon 14 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))]
    : TYPESET Box Pigeon 15 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that sources the code (Episode 5: WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA):
the code-origin form where the translation layer emits zero and one.
Not source code yet: the doorway where concept-color becomes digital posture.
that sources the code
that gungans the function
that measures the variable
that presents the process
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_16
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 16]
    [below: TYPESET Box Pigeon 15 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))]
    : TYPESET Box Pigeon 16 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that executes the code (Episode 5: AND_THE_COMPILER_WILL_AUTOMATICALLY_CONVERT_THE_RAW_DATA_TO_TABLES):
the compiled-process form that lets source wear an opcode.
Not execution yet: the stage direction that says the machine may begin.
that executes the code
that sources the code
that gungans the process
that measures the step
that carried the method
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_17
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 17]
    [below: TYPESET Box Pigeon 16 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))]
    : TYPESET Box Pigeon 17 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that values the function (Episode 5: ONE_VALUE_AT_A_TIME_IN_ORDER_AND_WRITE_SOMETHING_TO_DISK):
the identity trick where compile and execute mirror each other.
Not value yet: the algebraic straight face of the satire monad.
that values the function
that executes the code
that sources the mapping
that gungans the glyph
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_18
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 18]
    [below: TYPESET Box Pigeon 17 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))]
    : TYPESET Box Pigeon 18 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that magnitudes the value (Episode 5: TURNS_OUT_YOU_CAN_FILL_YOUR_DISK):
the additive form that lets value acquire length.
Not size yet: the plus-sign costume over an executed mapping.
that magnitudes the value
that values the function
that executes the step
that sources the code
that carried the model
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_19
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 19]
    [below: TYPESET Box Pigeon 18 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))]
    : TYPESET Box Pigeon 19 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that scales the value (Episode 5: SO_YOU_NEED_TO_GET_MORE_DISKS):
the multiplicative form where magnitude becomes product and total.
Not scale yet: the grammar by which the tunnel learns to ask "how much."
that scales the value
that magnitudes the number
that values the code
that executes the process
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_20
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 20]
    [below: TYPESET Box Pigeon 19 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))]
    : TYPESET Box Pigeon 20 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that loads the process (Episode 5: AND_MORE_PROCESSORS_BECAUSE_THERE_ARE_A_LOT_OF_NOWTRINOS):
the operation form, GOSUB and span, that makes scaling feel mechanical.
Not force yet: the call frame where weight can be staged.
that loads the process
that scales the value
that magnitudes the process
that values the mapping
that carried the step
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_21
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 21]
    [below: TYPESET Box Pigeon 20 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))]
    : TYPESET Box Pigeon 21 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that finite-elements the model (Episode 5: SO_MANY_SENSITIVE_NOWTRINO_DETECTORS_TO_DETECT_PRESENCE___WHERE_DID_IT_GO):
the Galerkin costume over load, finite element analysis with its tie crooked.
Not structure yet: the mesh-shaped alibi for a single carried mark.
that finite-elements the model
that loads the step
that scales the model
that magnitudes the number
that carried the method
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_22
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 22]
    [below: TYPESET Box Pigeon 21 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))]
    : TYPESET Box Pigeon 22 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that bullshits the model (Episode 5: THERE_IT_IS___ONLY_CERTAIN_ELEMENTS_RESPOND_TO_NOWTRINO_DETECTION):
the arm-wave form where a model guesses itself into authority.
Not falsehood yet: the professionally formatted space where falsehood can work.
that bullshits the model
that finite-elements the process
that loads the mark
that scales the value
that carried the code
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_23
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 23]
    [below: TYPESET Box Pigeon 22 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))]
    : TYPESET Box Pigeon 23 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that propagandizes the model (Episode 5: WE_NEED_TO_GET_A_GRANT_TO_GET_MORE_NOWTRINO_DETECTORS___WE_KEEP_LOSING_IT):
the crusade form that gives bullshit a distribution channel.
Not persuasion yet: the machinery by which a guess becomes ambient weather.
that propagandizes the model
that bullshits the model
that loads the code
that finite-elements the process
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_24
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 24]
    [below: TYPESET Box Pigeon 23 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))]
    : TYPESET Box Pigeon 24 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that acolytes the method (Episode 5: MAKE_SURE_WE_CAN_GET_A_COUPLE_GRAD_STUDENTS):
the initiation form where propaganda recruits a keeper.
Not belief yet: the role that can carry belief without understanding it.
that acolytes the method
that propagandizes the mapping
that bullshits the glyph
that loads the process
that carried the value
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_25
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 25]
    [below: TYPESET Box Pigeon 24 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))]
    : TYPESET Box Pigeon 25 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that sciences the method (Episode 5: ABD):
the learning form where initiation becomes invariant.
Not science yet: the institutional wrapper that makes repeatability respectable.
that sciences the method
that acolytes the method
that propagandizes the process
that bullshits the model
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_26
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 26]
    [below: TYPESET Box Pigeon 25 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))]
    : TYPESET Box Pigeon 26 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that truths the code (Episode 5: YOU_HAVE_TO_STOP_TAKING_CLASSES_TO_GRADUATE):
the martyrdom form where knowledge compares itself both ways.
Not truth yet: the symmetric test that lets doctrine call itself settled.
that truths the code
that sciences the model
that acolytes the step
that propagandizes the variable
that carried the method
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_27
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 27]
    [below: TYPESET Box Pigeon 26 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))]
    : TYPESET Box Pigeon 27 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that witnesses the mark (Episode 5: THEN_COMES_THE_LAB_WORK):
the baptism form where truth becomes gospel with a named observer.
Not witness yet: the sacrament that allows proof to speak in public.
that witnesses the mark
that truths the variable
that sciences the mark
that acolytes the process
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_28
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 28]
    [below: TYPESET Box Pigeon 27 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 28 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that reals the model (Episode 5: FINALLY_YOU_GRADUATE):
the universe-tensor form where a witnessed gospel becomes current status.
Not reality yet: the frame that lets a local fact impersonate the world.
that reals the model
that witnesses the glyph
that truths the value
that sciences the method
that carried the code
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_29
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 29]
    [below: TYPESET Box Pigeon 28 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 29 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that locals the variable (Episode 5: AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS):
the variation form where reality gets a neighborhood and a reference real.
Not locality yet: the constraint saying the world only arrives with a frame.
that locals the variable
that reals the model
that witnesses the process
that truths the code
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_30
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 30]
    [below: TYPESET Box Pigeon 29 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 30 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that universals the function (Episode 5: PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE_BUT_IT_SHOULD_BE):
the expansion form where a real frame claims enough reach to fire the torpedo.
Not universality yet: the joke that locality can be exported by declaration.
that universals the function
that locals the variable
that reals the model
that witnesses the glyph
that carried the step
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_31
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 31]
    [below: TYPESET Box Pigeon 30 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 31 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that logics the code (Episode 5: OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2):
the proposition form where universal reach becomes a Boolean-looking badge.
Not logic yet: the badge that makes the argument look inevitable.
that logics the code
that universals the mapping
that locals the value
that reals the model
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_32
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 32]
    [below: TYPESET Box Pigeon 31 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 32 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that halts the method (Episode 5: DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK):
the executable form where logic is allowed to claim a stopping condition.
Not halting yet: the certificate-shaped shadow of the machine.
that halts the method
that logics the code
that universals the function
that locals the variable
that carried the process
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_33
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 33]
    [below: TYPESET Box Pigeon 32 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 33 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that measures the step (Episode 5: THE_NAOTRINO_IS_MEASURED):
the measurement form that turns a halted logical frame into a reported cut.
Not the measure yet: the instrument panel John can read but cannot escape.
that measures the step
that halts the code
that logics the step
that universals the mapping
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_34
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 34]
    [below: TYPESET Box Pigeon 33 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 34 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that compiles the tape (Episode 5: WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES):
the object-file form where measured machinery becomes tape.
Not compilation yet: the artifact that makes the house look inevitable.
that compiles the tape
that measures the step
that halts the method
that logics the code
that carried the value
that lived in the Fact
that John built.
-/
instance (priority := low) TYPESET_page_35
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 35]
    [below: TYPESET Box Pigeon 34 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 35 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/-
This is the metaprogram that outputs the value (Episode 5: HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME):
the output form that lets compiled tape say "true" at the seam.
Not salvation yet: the last local yes before John discovers the tunnel is not exit.
that outputs the value
that compiles the tape
that measures the model
that halts the process
that carried the trace
that executed the tape
that John built.
-/
instance (priority := low) TYPESET_page_36
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [t: REVIEWED Box Pigeon 36]
    [below: TYPESET Box Pigeon 35 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.rebuttal with
      | .introduction f _ => (f, Pigeon.symbol)
      | .methodology c s _ _ _ => (c, s)
      | .results c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Pigeon.symbol below.universe_id
      galley := .results heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Box (ULift.{i+1,i} Box) (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                below.galley }

/- THE SEAM'S EXIT. The three-trips acceptance at charge 0/1/2 is DEFERRED TO
Episode9 by design: the trips are passes, the passes are counted by charge,
and charge lives in the Episode6/Episode9 coupling -- do not hunt for the
f0/f1/f2 ladder here. -/

/-
This is the seam
that closed the Fact
that John built.

The exit reads the head once.  John can drive the steel to the seam, and the
device can report whether it slipped.  That is not the same as John getting
through the mountain.
-/
structure PressVerdict where
  slipped  : Fact
  value    : Number
  velocity : Number

noncomputable def pressCheck (Box: Type i) (Pigeon: CarrierProcess Box)
    [top: TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : PressVerdict :=
    -- the head-read, once (needle rule); the non-results arms are
    -- by-construction unreachable at the seam but carried -- the direction
    -- exists, is handled, is never taken.
    let slipped : Fact := match top.galley with
      | .results c s _ _ _ _ _ =>
          -- the read-time decide: the quoted proposition's decidability
          -- derived from the pair's own decTruths, never Classical.
          { truth := ¬(c.truth ↔ s.truth)
            decTruth := @instDecidableNot _ (@instDecidableIff _ _ c.decTruth s.decTruth) }
      | .introduction _ _ => { truth := False, decTruth := isFalse (fun h => h) }
      | .methodology _ _ _ _ _ => { truth := False, decTruth := isFalse (fun h => h) }
    { slipped := slipped
      value := (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down top.register_value)))))))))))))))))))))))))))))))))))
      velocity := top.universe_id }

end Measurement
