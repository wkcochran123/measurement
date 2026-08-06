import Measurement.Episode19

/- MEANWHILE 20 -- THE SLIP TEST. The trace executed up the ladder, rung 1 to the
seam. The fold decides on each cell's own facts; .compute cells record the
execution onto the carried trace; the register -- the Value at its current lift,
the universe id -- is the executor's internal state, carried in the class, never
on the tape. Which carrier emerges at the top is a measurement of where the
descent landed; report what you get, do not force it. -/

namespace Measurement

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
class EXECUTED_TRACE (Value: Type i) (Carrier: CarrierProcess Value) (rung: Nat)
    (Lifted: Type j) where
  register_value : Lifted
  universe_id    : Number
  tape           : CompilerTape

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
instance (priority := low) EXECUTED_origin
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 1]
    -- TANGE (law-6 read): CarrierProcess.value : Number (Episode1), not Value --
    -- the spec's own body (register_value := Carrier.value) forces the anchor's
    -- Lifted to Number; the value rides the ULift ladder from there.
    : EXECUTED_TRACE Value Carrier 1 Number :=
  { register_value := Carrier.value
    universe_id    := .zero Carrier.symbol
    tape           := t.tape }

/-
This is the metaprogram that admits the mark (Episode 8: STEP_1):
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
instance (priority := low) EXECUTED_climb_2
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 2]
    [below: EXECUTED_TRACE Value Carrier 1 Number]
    : EXECUTED_TRACE Value Carrier 2 (ULift Number) :=
    -- the head-read, once (needle rule); the non-strap arms are by-construction
    -- unreachable at rung 2 but the match carries them -- the direction exists,
    -- is handled, is never taken.
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      -- the Prop slot carries the cell's own slip proposition, quoted (law 4);
      -- its decidability derives from the two decTruths when read, never here.
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that counts the number (Episode 8: COUNTABLE_ADMISSIBLE):
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
instance (priority := low) EXECUTED_climb_3
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 3]
    [below: EXECUTED_TRACE Value Carrier 2 (ULift Number)]
    : EXECUTED_TRACE Value Carrier 3 (ULift (ULift Number)) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that encodes the glyph (Episode 8: ENCODED_COUNTABLE):
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
instance (priority := low) EXECUTED_climb_4
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 4]
    [below: EXECUTED_TRACE Value Carrier 3 (ULift (ULift Number))]
    : EXECUTED_TRACE Value Carrier 4 (ULift (ULift (ULift Number))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that residues the code (Episode 8: RESIDUE_ENCODED):
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
instance (priority := low) EXECUTED_climb_5
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 5]
    [below: EXECUTED_TRACE Value Carrier 4 (ULift (ULift (ULift Number)))]
    : EXECUTED_TRACE Value Carrier 5 (ULift (ULift (ULift (ULift Number)))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that binaries the value (Episode 8: BINARY_RESIDUE):
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
instance (priority := low) EXECUTED_climb_6
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 6]
    [below: EXECUTED_TRACE Value Carrier 5 (ULift (ULift (ULift (ULift Number))))]
    : EXECUTED_TRACE Value Carrier 6 (ULift (ULift (ULift (ULift (ULift Number))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that repeats the process (Episode 8: REPEATABLE_BINARY):
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
instance (priority := low) EXECUTED_climb_7
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 7]
    [below: EXECUTED_TRACE Value Carrier 6 (ULift (ULift (ULift (ULift (ULift Number)))))]
    : EXECUTED_TRACE Value Carrier 7 (ULift (ULift (ULift (ULift (ULift (ULift Number)))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that numbers the value (Episode 8: NUMERIC_REPEATABLE):
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
instance (priority := low) EXECUTED_climb_8
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 8]
    [below: EXECUTED_TRACE Value Carrier 7 (ULift (ULift (ULift (ULift (ULift (ULift Number))))))]
    : EXECUTED_TRACE Value Carrier 8 (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that represents the code (Episode 8: REPRESENTABLE_NUMERIC):
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
instance (priority := low) EXECUTED_climb_9
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 9]
    [below: EXECUTED_TRACE Value Carrier 8 (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))]
    : EXECUTED_TRACE Value Carrier 9 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that physicals the method (Episode 8: PHYSICAL_NUMERIC):
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
instance (priority := low) EXECUTED_climb_10
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 10]
    [below: EXECUTED_TRACE Value Carrier 9 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))]
    : EXECUTED_TRACE Value Carrier 10 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that compares the process:
the borrowed bridge Episode 8 requires before observation can enter.
Not comparison yet: the permission for two processes to be placed under one eye.
that compares the process
that physicals the method
that represents the code
that numbers the variable
that executed the tape
that lived in the Fact
that John built.
-/
instance (priority := low) EXECUTED_climb_11
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 11]
    [below: EXECUTED_TRACE Value Carrier 10 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))]
    : EXECUTED_TRACE Value Carrier 11 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that observes the mark (Episode 8: OBSERVED_COMPARABLE):
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
instance (priority := low) EXECUTED_climb_12
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 12]
    [below: EXECUTED_TRACE Value Carrier 11 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))]
    : EXECUTED_TRACE Value Carrier 12 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that presents the process (Episode 8: PRESENT_OBSERVED):
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
instance (priority := low) EXECUTED_climb_13
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 13]
    [below: EXECUTED_TRACE Value Carrier 12 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))]
    : EXECUTED_TRACE Value Carrier 13 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that measures the step (Episode 8: MEASURABLE_PRESENT):
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
instance (priority := low) EXECUTED_climb_14
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 14]
    [below: EXECUTED_TRACE Value Carrier 13 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))]
    : EXECUTED_TRACE Value Carrier 14 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that gungans the glyph (Episode 8: GUNGAN_MEASURABLE):
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
instance (priority := low) EXECUTED_climb_15
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 15]
    [below: EXECUTED_TRACE Value Carrier 14 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))]
    : EXECUTED_TRACE Value Carrier 15 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that sources the code (Episode 8: SOURCE_GUNGAN):
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
instance (priority := low) EXECUTED_climb_16
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 16]
    [below: EXECUTED_TRACE Value Carrier 15 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))]
    : EXECUTED_TRACE Value Carrier 16 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that executes the code (Episode 8: EXECUTED_SOURCE):
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
instance (priority := low) EXECUTED_climb_17
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 17]
    [below: EXECUTED_TRACE Value Carrier 16 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))]
    : EXECUTED_TRACE Value Carrier 17 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that values the function (Episode 8: VALUE_EXECUTED):
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
instance (priority := low) EXECUTED_climb_18
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 18]
    [below: EXECUTED_TRACE Value Carrier 17 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 18 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that magnitudes the value (Episode 8: MAGNITUDE_VALUE):
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
instance (priority := low) EXECUTED_climb_19
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 19]
    [below: EXECUTED_TRACE Value Carrier 18 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 19 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that scales the value (Episode 8: SCALED_MAGNITUDE):
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
instance (priority := low) EXECUTED_climb_20
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 20]
    [below: EXECUTED_TRACE Value Carrier 19 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 20 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that loads the process (Episode 8: LOAD_SCALED):
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
instance (priority := low) EXECUTED_climb_21
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 21]
    [below: EXECUTED_TRACE Value Carrier 20 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 21 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that finite-elements the model (Episode 8: FINITE_ELEPHANT_LOAD):
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
instance (priority := low) EXECUTED_climb_22
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 22]
    [below: EXECUTED_TRACE Value Carrier 21 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 22 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that bullshits the model (Episode 8: BULLSHIT_FINITE_ELEPHANT):
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
instance (priority := low) EXECUTED_climb_23
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 23]
    [below: EXECUTED_TRACE Value Carrier 22 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 23 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that propagandizes the model (Episode 8: PROPAGANDA_BULLSHIT):
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
instance (priority := low) EXECUTED_climb_24
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 24]
    [below: EXECUTED_TRACE Value Carrier 23 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 24 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that acolytes the method (Episode 8: ACOLYTE_PROPAGANDA):
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
instance (priority := low) EXECUTED_climb_25
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 25]
    [below: EXECUTED_TRACE Value Carrier 24 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 25 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that sciences the method (Episode 9: SCIENTIFIC_ACOLYTE):
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
instance (priority := low) EXECUTED_climb_26
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 26]
    [below: EXECUTED_TRACE Value Carrier 25 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 26 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that truths the code (Episode 9: TRUTH_SCIENTIFIC):
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
instance (priority := low) EXECUTED_climb_27
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 27]
    [below: EXECUTED_TRACE Value Carrier 26 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 27 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that witnesses the mark (Episode 10: WITNESSED_TRUTH):
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
instance (priority := low) EXECUTED_climb_28
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 28]
    [below: EXECUTED_TRACE Value Carrier 27 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 28 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that reals the model (Episode 10: REAL_WITNESSED):
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
instance (priority := low) EXECUTED_climb_29
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 29]
    [below: EXECUTED_TRACE Value Carrier 28 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 29 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that locals the variable (Episode 10: LOCAL_REAL):
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
instance (priority := low) EXECUTED_climb_30
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 30]
    [below: EXECUTED_TRACE Value Carrier 29 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 30 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that universals the function (Episode 11: UNIVERSAL_REAL):
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
instance (priority := low) EXECUTED_climb_31
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 31]
    [below: EXECUTED_TRACE Value Carrier 30 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 31 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that logics the code (Episode 12: LOGICAL_UNIVERSAL):
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
instance (priority := low) EXECUTED_climb_32
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 32]
    [below: EXECUTED_TRACE Value Carrier 31 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 32 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that halts the method (Episode 12: HALTED_LOGICAL):
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
instance (priority := low) EXECUTED_climb_33
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 33]
    [below: EXECUTED_TRACE Value Carrier 32 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 33 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that measures the step (Episode 13: MEASURED):
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
instance (priority := low) EXECUTED_climb_34
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 34]
    [below: EXECUTED_TRACE Value Carrier 33 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 34 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that compiles the tape (Episode 14: COMPILED_MEASURED):
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
instance (priority := low) EXECUTED_climb_35
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 35]
    [below: EXECUTED_TRACE Value Carrier 34 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 35 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/-
This is the metaprogram that outputs the value (Episode 15: TRUE_COMPILED):
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
instance (priority := low) EXECUTED_climb_36
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 36]
    [below: EXECUTED_TRACE Value Carrier 35 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/- THE SEAM'S EXIT. The three-trips acceptance at charge 0/1/2 is DEFERRED TO
Episode21 by design: the trips are passes, the passes are counted by charge,
and charge lives in the Episode18/Episode21 coupling -- do not hunt for the
f0/f1/f2 ladder here. -/

/-
This is the seam
that closed the Fact
that John built.

The exit reads the head once.  John can drive the steel to the seam, and the
device can report whether it slipped.  That is not the same as John getting
through the mountain.
-/
structure SlipVerdict where
  slipped  : Fact
  value    : Number
  velocity : Number

noncomputable def seamExit (Value: Type i) (Carrier: CarrierProcess Value)
    [top: EXECUTED_TRACE Value Carrier 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : SlipVerdict :=
    -- the head-read, once (needle rule); the non-compute arms are
    -- by-construction unreachable at the seam but carried -- the direction
    -- exists, is handled, is never taken.
    let slipped : Fact := match top.tape with
      | .compute c s _ _ _ _ _ =>
          -- the read-time decide: the quoted proposition's decidability
          -- derived from the pair's own decTruths, never Classical.
          { truth := ¬(c.truth ↔ s.truth)
            decTruth := @instDecidableNot _ (@instDecidableIff _ _ c.decTruth s.decTruth) }
      | .boot _ _ => { truth := False, decTruth := isFalse (fun h => h) }
      | .strap _ _ _ _ _ => { truth := False, decTruth := isFalse (fun h => h) }
    { slipped := slipped
      value := (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down top.register_value)))))))))))))))))))))))))))))))))))
      velocity := top.universe_id }

end Measurement
