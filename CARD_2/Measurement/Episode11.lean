/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are read from the pages in front of us._

(c) 2026 [PATTER TODO: rights gag]

THE GOSPEL ACCORDING TO JOHN (HENRY)

In the beginning was the FACT, and the FACT was with the click, and the FACT was T = T.

lake build [PATTER TODO: build-flag gag]

__EPISODE 11__: _The Force_

-/

import Measurement.Episode10
set_option allowUnsafeReducibility true

-- MAIN SCREEN TURN ON
namespace Measurement

universe i j

open «springer-verlag»

-- THE GOSPEL: the record set in type, one verse a page.
namespace THE_GOSPEL

/-
This is the trace
that executed the tape
that lived in the FACT
that John built.

The tape is still one character.  The register is not on it.  The story is
not on it.  The trace is the house built around it after John starts driving
steel into the mountain.

As for the Nat. Typesetting engines require generation of page numbers for indexing the table of contents.
-/
-- Each verse below ends where the record ends, at the FACT, and then turns to where the knower keeps
-- it: Card 1 and Card 3, by printed result and page number of the builds (Card 1 of 23 October, Card 3 of 29 October 2026). The appendix
-- table "Stanzas and results" in each card is the stable anchor.
class TYPESET (Box: Type i) (Pigeon: CarrierProcess Box) (rung: Nat)
    (Lifted: Type j) where
  register_value : Lifted
  universe_id    : Number
  the_page       : ThePreprint

/- THE HOUSE STYLE, SET IN TYPE.  Every page after the first is the page below
   lifted one universe, its counter advanced by one, and the reviewer's
   rebuttal read at the head and quoted as the results section: what was
   constructed, what slipped, and the proposition that the two agree.  The
   publisher sets it once, here; each page supplies only its rebuttal and the
   page below. -/
@[reducible] def _root_.Measurement.«springer-verlag».set_in_type
    {Box: Type i} {Pigeon: CarrierProcess Box} {rung: Nat} {Lifted: Type j}
    (the_rebuttal: ThePreprint) (accepted: TYPESET Box Pigeon rung Lifted)
    : TYPESET Box Pigeon (rung+1) (ULift.{i, j} Lifted) :=
    let rofl! : FACT × FACT := match the_rebuttal with
      | .introduction nowtrino _ => (nowtrino, Pigeon.symbol) -- We shall call our new particle after t
      | .methodology see_a_flash make_a_mark _ _ _ => (see_a_flash, make_a_mark)
      | .results before after _ _ _ _ _ => (before, after)
    -- Now watch as we lift all the cards.
    { register_value := ULift.up accepted.register_value
      universe_id    := .one Pigeon.symbol accepted.universe_id
      the_page := .results rofl!.1 rofl!.2
                          (rofl!.1.truth ↔ rofl!.2.truth)
                          Box (ULift.{i+1,i} Box)
                          (ULift.{i+1,i+1} (ULift.{i+1,i} Box))
                          accepted.the_page
    }

/-
This is the origin
that carried the trace
that executed the tape
that lived in the FACT
that John built.

The first spike is boring on purpose: the carried value is just the carrier's
number, the universe id is zero, and the tape is whatever the trace brought
to the face.  Steel starts as a local receipt.
   Gospel 1: In the beginning was the FACT, and it clicked.
   Card 1: Section 6.4 (p. 32); Section 6.2 (p. 31); Section 5.7 (p. 29).
   Card 3: Section 6.1 (p. 41); Section 6.4 (p. 45); Section 3.6 (p. 25); Section 7.1 (p. 50).
-/
instance (priority := low) TYPESET_Episode1_FACT
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 1]
    : TYPESET Box Pigeon 1 Number :=
  { register_value := Pigeon.quarter
    universe_id    := .zero Pigeon.symbol
    the_page         := the_naotrino_theory.rebuttal }

/-
This is the metaprogram that admits the mark (Episode 7: CAN_YOU_DISTINGUISH_SOMETHING?):
the permission form that says a distinguished mark may be counted.
It is not the act of counting.  It is the local license-count,
Episode 8 wearing the first hard hat,
that admits the mark
that distinguishes the glyph
that carried the trace
that executed the tape
that lived in the FACT
that John built.

The tape does not become a novel.  The class dictionary does.
   Gospel 2: And the FACT was written on a tape one mark long, and the mark fit any carrier.
   Card 1: eq. 6.1 (p. 30); Section 6.1 (p. 30); Section 1.1 (p. 1); Chapter 6 (p. 30).
   Card 3: Section 6.1 (p. 41); Section 4.3 (p. 28); Section 4.8 (p. 33).
-/
instance (priority := low) TYPESET_page_2
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 2]
    [accepted: TYPESET Box Pigeon 1 Number]
    : TYPESET Box Pigeon 2 (ULift Number) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that counts the number (Episode 7: CAN_YOU_COUNT_THEM?):
the index-form that says the permitted count has an origin.
It is not an enumeration.  It is the place where enumeration can appear,
that counts the number
that admits the mark
that distinguishes the letter
that carried the trace
that executed the tape
that lived in the FACT
that John built.
   Gospel 3: And three readers came to the tape, the tally, the register and the receipt, and each forgot what
             it could not see.
   Card 1: Proposition 3.4 (p. 17); Proposition 2.2 (p. 6); Section 6.1 (p. 30).
   Card 3: Section 7.4 (p. 52); Section 7.5 (p. 53).
-/
instance (priority := low) TYPESET_page_3
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 3]
    [accepted: TYPESET Box Pigeon 2 (ULift Number)]
    : TYPESET Box Pigeon 3 (ULift (ULift Number)) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that encodes the glyph (Episode 7: ARE_THEY_THE_SAME_THING?):
the limit-form that gives the count a sequence-shaped mask.
It is not a message.  It is the local possibility of messagehood,
that encodes the glyph
that counts the number
that admits the value
that distinguishes the mark
that carried the trace
that executed the tape
that lived in the FACT
that John built.
   Gospel 4: And every reader that reads length agreed, and relettering was free.
   Card 1: Theorem 7.1 (p. 37); eq. 1.1 (p. 2); Section 6.1 (p. 30).
   Card 3: Section 6.4 (p. 45); Section 7.5 (p. 53).
-/
instance (priority := low) TYPESET_page_4
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 4]
    [accepted: TYPESET Box Pigeon 3 (ULift (ULift Number))]
    : TYPESET Box Pigeon 4 (ULift (ULift (ULift Number))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that residues the code (Episode 7: IS_IT_CONVERGING?):
the remainder-form, the leftover that survives being encoded.
It is not what the code means.  It is the gap the code is allowed to have,
that residues the code
that encodes the letter
that counts the variable
that admits the process
that distinguishes the glyph
that carried the trace
that executed the tape
that lived in the FACT
that John built.
   Gospel 5: But writing was not free; every mark cost a heartbeat.
   Card 1: Proposition 5.1 (p. 24); Section 5.3 (p. 26); Section 6.6 (p. 34).
   Card 3: Proposition 2.2 (p. 11); eq. 6.8 (p. 45); Section 3.7 (p. 25); Section 6.5 (p. 46).
-/
instance (priority := low) TYPESET_page_5
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 5]
    [accepted: TYPESET Box Pigeon 4 (ULift (ULift (ULift Number)))]
    : TYPESET Box Pigeon 5 (ULift (ULift (ULift (ULift Number)))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that binaries the value (Episode 7: IS_IT_CYCLIC?):
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
that lived in the FACT
that John built.

By now the stanza is already longer than the tape.  That is the point.
   Gospel 6: And the FACT was thrown, and the box had one point.
   Card 1: Proposition 3.3 (p. 14); Table 6.1 (p. 32); eq. 6.3 (p. 32); eq. 2.2 (p. 9).
   Card 3: Section 7.5 (p. 53); Section 6.4 (p. 45).
-/
instance (priority := low) TYPESET_page_6
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 6]
    [accepted: TYPESET Box Pigeon 5 (ULift (ULift (ULift (ULift Number))))]
    : TYPESET Box Pigeon 6 (ULift (ULift (ULift (ULift (ULift Number))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that repeats the process (Episode 7: IS_IT_RHYTHMIC?):
the ritual form where a binary remainder becomes stimulus and expectation.
Not repetition yet: the contract under which repetition can accuse the tape.
that repeats the process
that binaries the value
that residues the model
that encodes the code
that counted the number
that lived in the FACT
that John built.
   Gospel 7: And a representative was chosen, and the choice was the quarter, and no card read it.
   Card 1: Section 7.3 (p. 38); Section 4.3 (p. 20); Section 5.7 (p. 29).
   Card 3: Section 7.2 (p. 51); Section 7.3 (p. 52); Section 4.5 (p. 30); Section 7.7 (p. 54).
-/
instance (priority := low) TYPESET_page_7
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 7]
    [accepted: TYPESET Box Pigeon 6 (ULift (ULift (ULift (ULift (ULift Number)))))]
    : TYPESET Box Pigeon 7 (ULift (ULift (ULift (ULift (ULift (ULift Number)))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that numbers the value (Episode 7: CAN_YOU_DECOMPOSE_THE_RHYTHM?):
the output form that lets repeatability wear the mask of computation.
Not a number yet: the promise that "some output" can stand in the witness box.
that numbers the value
that repeats the function
that binaries the glyph
that residues the step
that admitted the mark
that lived in the FACT
that John built.
   Gospel 8: And the square was drawn, observe then throw, throw then observe, and where it closed, the reading
             commuted.
   Card 1: Proposition 2.2 (p. 6); Table 2.1 (p. 6); Table 6.1 (p. 32); Section 2.1 (p. 5).
   Card 3: Section 7.4 (p. 52); Section 6.4 (p. 45); Section 7.6 (p. 54).
-/
instance (priority := low) TYPESET_page_8
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 8]
    [accepted: TYPESET Box Pigeon 7 (ULift (ULift (ULift (ULift (ULift (ULift Number))))))]
    : TYPESET Box Pigeon 8 (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that represents the code (Episode 7: CAN_YOU_REGRESS_A_LAW?; the arms: Episode 5, AtreyuProcess.gawk_at):
the program form that closes the output into a state.
Not representation itself: the receipt that a state may be called a program.
that represents the code
that numbers the value
that repeats the process
that binaries the method
that distinguished the glyph
that lived in the FACT
that John built.
   Gospel 9: And the table had four arms: true to true, false to false, true to false, false to true.
   Card 1: Section 3.4 (p. 15); Section 6.1 (p. 30); Section 4.6 (p. 23).
   Card 3: Table 6.1 (p. 44); Section 6.3 (p. 43); Section 7.4 (p. 52).
-/
instance (priority := low) TYPESET_page_9
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 9]
    [accepted: TYPESET Box Pigeon 8 (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))]
    : TYPESET Box Pigeon 9 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that physicals the method (Episode 7: IS_IT_NOISY?):
the hardware alibi, where halting and nonhalting become threshold language.
Not matter yet: the claim that electrons are already enough of an argument.
that physicals the method
that represents the mapping
that numbers the mark
that repeats the function
that carried the trace
that lived in the FACT
that John built.
   Gospel 10: And three arms clicked, and on those arms was written the coefficient tape of thirteen.
   Card 1: Section 6.4 (p. 32); Section 7.3 (p. 38); Chapter 2 (p. 5); Section 7.4 (p. 39).
   Card 3: eq. E.6 (p. 74); Section 3.6 (p. 25).
-/
instance (priority := low) TYPESET_page_10
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 10]
    [accepted: TYPESET Box Pigeon 9 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))]
    : TYPESET Box Pigeon 10 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that compares the process:
the borrowed bridge Episode 5 requires before observation can enter.
Not comparison yet: the permission for two processes to be placed under one eye.
that compares the process
that physicals the method
that represents the code
that numbers the variable
that executed the tape
that lived in the FACT
that John built.
   Gospel 11: And on every arm was written the frame of five, counted this way, and that way, and as built.
   Card 1: Proposition 5.4 (p. 28); eq. 5.3 (p. 28); Section 6.5 (p. 33); Section 1.4 (p. 3).
   Card 3: Theorem 2.4 (p. 19); Proposition 2.5 (p. 19); eq. 7.1 (p. 51); Section 2.5 (p. 19); Section 2.6 (p. 19); Section 7.6 (p. 54).
-/
instance (priority := low) TYPESET_page_11
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 11]
    [accepted: TYPESET Box Pigeon 10 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))]
    : TYPESET Box Pigeon 11 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that observes the mark (Episode 7: IS_IT_MOVING?):
the projection form where stress, threshold, and symbol make a slip-process.
Not seeing yet: the theater in which seeing can be reported.
that observes the mark
that compares the process
that physicals the step
that represents the model
that carried the trace
that executed the tape
that John built.
   Gospel 12: And the arm true-to-false stored FALSE and did not click, and the thirteen was taken from it, as
             foretold by the sacred texts of the Flying Spaghetti Monster.
   Card 1: Proposition 2.6 (p. 9); eq. 2.2 (p. 9); eq. 6.2 (p. 31); Section 2.4 (p. 9).
   Card 3: Proposition 2.1 (p. 10); Proposition 2.3 (p. 15); Section 2.2 (p. 12); Chapter 2 (p. 8).
-/
instance (priority := low) TYPESET_page_12
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 12]
    [accepted: TYPESET Box Pigeon 11 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))]
    : TYPESET Box Pigeon 12 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that presents the process (Episode 7: HOW_FAST?):
the Santa-Claus form, absurd on the surface and exact in the dependency graph.
Not presence yet: the current-tense wrapper around an already observed process.
that presents the process
that observes the glyph
that compares the model
that physicals the method
that carried the value
that lived in the FACT
that John built.
   Gospel 13: And the five remained on the arm that does not click.
   Card 1: Section 6.6 (p. 34); Section 4.4 (p. 21); Section 2.5.1 (p. 11).
   Card 3: eq. E.6 (p. 74); Section 5.4 (p. 38).
-/
instance (priority := low) TYPESET_page_13
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 13]
    [accepted: TYPESET Box Pigeon 12 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))]
    : TYPESET Box Pigeon 13 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that measures the step (Episode 7: COMPARED_TO_WHAT?):
the gauge form that gives present observation a clock.
Not measurement yet: the clock-face where measurement can pretend it arrived.
that measures the step
that presents the value
that observes the process
that compares the glyph
that carried the trace
that executed the tape
that John built.
   Gospel 14: And the table parted into a count and a clock: the count reads every TRUE as TRUE; the clock
             crosses the arm at every other step.
   Card 1: Figure 3.2 (p. 17); eq. 3.3 (p. 16); Section 6.1 (p. 30).
   Card 3: Section 7.6 (p. 54); Section 7.3 (p. 52).
-/
instance (priority := low) TYPESET_page_14
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 14]
    [accepted: TYPESET Box Pigeon 13 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))]
    : TYPESET Box Pigeon 14 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that gungans the glyph (Episode 7: WHAT_FRACTION_OF_REINDEER_SPEED?):
the translation layer where a gauge becomes concept-color and comic syntax.
Not nonsense: the dialect adapter proving nonsense can be type-directed.
that gungans the glyph
that measures the method
that presents the glyph
that observes the mark
that carried the process
that lived in the FACT
that John built.
   Gospel 15: And the clock, taken twice, came home multiplied, and the clock ran.
   Card 1: Definition 2.1 (p. 6); Definition 4.1 (p. 19); Table 6.1 (p. 32); Section 1.2 (p. 1).
   Card 3: Section 6.1 (p. 41); Section 5.3 (p. 37).
-/
instance (priority := low) TYPESET_page_15
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 15]
    [accepted: TYPESET Box Pigeon 14 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))]
    : TYPESET Box Pigeon 15 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that sources the code (Episode 7: IS_THIS_A_CARRIER_PARTICLE?):
the code-origin form where the translation layer emits zero and one.
Not source code yet: the doorway where concept-color becomes digital posture.
that sources the code
that gungans the function
that measures the variable
that presents the process
that carried the trace
that executed the tape
that John built.
   Gospel 16: And the count grew at its root, and the reading was 137.0112905…
   Card 1: Proposition 4.3 (p. 20); Section 4.3 (p. 20).
   Card 3: Section 7.4 (p. 52); Section 7.5 (p. 53).
-/
instance (priority := low) TYPESET_page_16
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 16]
    [accepted: TYPESET Box Pigeon 15 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))]
    : TYPESET Box Pigeon 16 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that executes the code (Episode 7: IS_THERE_DATA?):
the compiled-process form that lets source wear an opcode.
Not execution yet: the stage direction that says the machine may begin.
that executes the code
that sources the code
that gungans the process
that measures the step
that carried the method
that lived in the FACT
that John built.
   Gospel 17: Strike the arm, and the reading is 89.72…, and rational. Write it, and the 47.29… more is the
             clock. That is what T = F buys.
   Card 1: Section 3.5 (p. 16); Section 5.5 (p. 27); Section 6.1 (p. 30).
   Card 3: Section 6.3 (p. 43); Section 6.8 (p. 48).
-/
instance (priority := low) TYPESET_page_17
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 17]
    [accepted: TYPESET Box Pigeon 16 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))]
    : TYPESET Box Pigeon 17 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that values the function (Episode 7: HOW_MUCH_DATA_IS_THERE?):
the identity trick where compile and execute mirror each other.
Not value yet: the algebraic straight face of the satire monad.
that values the function
that executes the code
that sources the mapping
that gungans the glyph
that carried the trace
that executed the tape
that John built.
   Gospel 18: And the clock was a phase: true, false, true, false. Once around flips; twice around returns.
   Card 1: Section 3.5 (p. 16); Section 6.1 (p. 30).
   Card 3: Section 6.5 (p. 46); Section 6.8 (p. 48).
-/
instance (priority := low) TYPESET_page_18
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 18]
    [accepted: TYPESET Box Pigeon 17 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))]
    : TYPESET Box Pigeon 18 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that magnitudes the value (Episode 7: WHAT_IS_THE_TOTAL_COUNT?):
the additive form that lets value acquire length.
Not size yet: the plus-sign costume over an executed mapping.
that magnitudes the value
that values the function
that executes the step
that sources the code
that carried the model
that lived in the FACT
that John built.
   Gospel 19: And the phase was carried by a spinor, which loses its sign at one turn and finds it at two; and
             the lost sign was a relative phase, not a failure to commute.
   Card 1: eq. 5.2 (p. 27); eq. 6.4 (p. 34); Section 5.5 (p. 27); Section 6.7 (p. 35).
   Card 3: Table 7.1 (p. 52); eq. 3.6 (p. 25); eq. 3.7 (p. 25).
-/
instance (priority := low) TYPESET_page_19
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 19]
    [accepted: TYPESET Box Pigeon 18 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))]
    : TYPESET Box Pigeon 19 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that scales the value (Episode 7: IS_THERE_A_GRID_OF_DATA?):
the multiplicative form where magnitude becomes product and total.
Not scale yet: the grammar by which the tunnel learns to ask "how much."
that scales the value
that magnitudes the number
that values the code
that executes the process
that carried the trace
that executed the tape
that John built.
   Gospel 20: And one observable was chosen that rotates, and one that holds still, for a control.
   Card 1: Section 2.5 (p. 10); Section 2.5.1 (p. 11); Section 5.2 (p. 25).
   Card 3: eq. 6.2 (p. 41); Section 6.1 (p. 41); Section 3.1 (p. 21).
-/
instance (priority := low) TYPESET_page_20
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 20]
    [accepted: TYPESET Box Pigeon 19 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))]
    : TYPESET Box Pigeon 20 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that loads the process (Episode 7: HOW_MANY_ROWS_AND_COLUMNS?):
the operation form, GOSUB and span, that makes scaling feel mechanical.
Not force yet: the call frame where weight can be staged.
that loads the process
that scales the value
that magnitudes the process
that values the mapping
that carried the step
that lived in the FACT
that John built.
   Gospel 21: And the reading was taken for the coupling of light to the electron, as foretold by the sacred
             texts of the Flying Spaghetti Monster.
   Card 1: Theorem 5.3 (p. 26); eq. 4.2 (p. 22); Section 4.5 (p. 22); Section 5.2 (p. 25).
   Card 3: Section 4.7 (p. 32); Section 1.6 (p. 6); Section 4.4 (p. 29).
-/
instance (priority := low) TYPESET_page_21
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 21]
    [accepted: TYPESET Box Pigeon 20 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))]
    : TYPESET Box Pigeon 21 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that finite-elements the model (Episode 7: IS_EACH_ONE_DIFFERENT?):
the Galerkin costume over load, finite element analysis with its tie crooked.
Not structure yet: the mesh-shaped alibi for a single carried mark.
that finite-elements the model
that loads the step
that scales the model
that magnitudes the number
that carried the method
that executed the tape
that John built.
   Gospel 22: And the state carried its phase at every point, and two points could not be compared without a
             rule.
   Card 1: Section 4.4 (p. 21); Section 4.5 (p. 22); Section 5.4 (p. 27).
   Card 3: Proposition 2.3 (p. 15); eq. 3.5 (p. 24); Section 3.5 (p. 24); Section 2.3 (p. 14).
-/
instance (priority := low) TYPESET_page_22
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 22]
    [accepted: TYPESET Box Pigeon 21 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))]
    : TYPESET Box Pigeon 22 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that bullshits the model (Episode 7: HOW_DIFFERENT_IS_THIS_ONE?):
the arm-wave form where a model guesses itself into authority.
Not falsehood yet: the professionally formatted space where falsehood can work.
that bullshits the model
that finite-elements the process
that loads the mark
that scales the value
that carried the code
that lived in the FACT
that John built.
   Gospel 23: And the rule of comparison was transport, and transport was covariant.
   Card 1: Section 5.7 (p. 29).
   Card 3: eq. 3.4 (p. 23); Section 3.3 (p. 23); Section 1.6 (p. 6).
-/
instance (priority := low) TYPESET_page_23
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 23]
    [accepted: TYPESET Box Pigeon 22 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))]
    : TYPESET Box Pigeon 23 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that propagandizes the model (Episode 7: IS_IT_DIFFERENT_ENOUGH?):
the crusade form that gives bullshit a distribution channel.
Not persuasion yet: the machinery by which a guess becomes ambient weather.
that propagandizes the model
that bullshits the model
that loads the code
that finite-elements the process
that carried the trace
that executed the tape
that John built.
   Gospel 24: And transport, taken small, was the connection, and the connection was the potential of light.
   Card 1: Table 2.1 (p. 6); Section 2.1 (p. 5); Section 1.4 (p. 3); Appendix A (p. 55).
   Card 3: Section 6.8 (p. 48); Section 7.2 (p. 51).
-/
instance (priority := low) TYPESET_page_24
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 24]
    [accepted: TYPESET Box Pigeon 23 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))]
    : TYPESET Box Pigeon 24 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that acolytes the method (Episode 7: WHAT_IF_THEY_ARE_THE_SAME?):
the initiation form where propaganda recruits a keeper.
Not belief yet: the role that can carry belief without understanding it.
that acolytes the method
that propagandizes the mapping
that bullshits the glyph
that loads the process
that carried the value
that lived in the FACT
that John built.
   Gospel 25: And transport around a small loop failed to come home, and the failure was curvature, and the
             curvature was the field.
   Card 1: Corollary 6.1 (p. 34); Section 6.4 (p. 32).
   Card 3: eq. 7.1 (p. 51); Section 3.7 (p. 25).
-/
instance (priority := low) TYPESET_page_25
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 25]
    [accepted: TYPESET Box Pigeon 24 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))]
    : TYPESET Box Pigeon 25 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that sciences the method (Episode 7: IS_THIS_A_NAOTRINO?):
the learning form where initiation becomes invariant.
Not science yet: the institutional wrapper that makes repeatability respectable.
that sciences the method
that acolytes the method
that propagandizes the process
that bullshits the model
that carried the trace
that executed the tape
that John built.
   Gospel 26: And the commutator of the two derivatives was the charge times the field: the commutator of
             representation.
   Card 1: Proposition 5.1 (p. 24); Section 5.3 (p. 26); Section 6.6 (p. 34).
   Card 3: eq. 3.2 (p. 22); Section 3.2 (p. 22); Section 3.3 (p. 23); Section 6.5 (p. 46).
-/
instance (priority := low) TYPESET_page_26
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 26]
    [accepted: TYPESET Box Pigeon 25 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))]
    : TYPESET Box Pigeon 26 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that truths the code (Episode 7: IS_THIS_THE_ONLY_OUTCOME?):
the martyrdom form where knowledge compares itself both ways.
Not truth yet: the symmetric test that lets doctrine call itself settled.
that truths the code
that sciences the model
that acolytes the step
that propagandizes the variable
that carried the method
that lived in the FACT
that John built.
   Gospel 27: And there were added a background with a light cone, the spinor representation, the kinetic terms
             and a mass, each named where it entered, as foretold by the sacred texts of the Flying Spaghetti
             Monster.
   Card 1: Proposition 5.4 (p. 28); Theorem 7.1 (p. 37); Section 5.6 (p. 28); Section 3.4 (p. 15).
   Card 3: Section 6.4 (p. 45); Section 3.7 (p. 25).
-/
instance (priority := low) TYPESET_page_27
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 27]
    [accepted: TYPESET Box Pigeon 26 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))]
    : TYPESET Box Pigeon 27 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that witnesses the mark (Episode 7: HAVE_OTHERS_RUN_THE_EXPERIMENT?):
the baptism form where truth becomes gospel with a named observer.
Not witness yet: the sacrament that allows proof to speak in public.
that witnesses the mark
that truths the variable
that sciences the mark
that acolytes the process
that carried the trace
that executed the tape
that John built.
   Gospel 28: And from these was written the action of light and matter, minimally coupled.
   Card 1: Table 4.1 (p. 20); Section 3.3 (p. 13); Section 6.3 (p. 32).
   Card 3: Section 5.5 (p. 39); Section 5.1 (p. 35).
-/
instance (priority := low) TYPESET_page_28
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 28]
    [accepted: TYPESET Box Pigeon 27 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 28 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that reals the model (Episode 7: A_CAUSAL_THEORY):
the universe-tensor form where a witnessed gospel becomes current status.
Not reality yet: the frame that lets a local fact impersonate the world.
that reals the model
that witnesses the glyph
that truths the value
that sciences the method
that carried the code
that lived in the FACT
that John built.
   Gospel 29: And the action was varied, and where it stood still were Maxwell's equations with Dirac's current,
             and Dirac's equation in Maxwell's field; and the current was conserved, and Gauss kept his
             constraint.
   Card 1: Section 7.2 (p. 38); Section 6.4 (p. 32); Section 5.7 (p. 29).
   Card 3: Section 3.6 (p. 25); Section 7.3 (p. 52).
-/
instance (priority := low) TYPESET_page_29
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 29]
    [accepted: TYPESET Box Pigeon 28 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 29 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that locals the variable (Episode 7: A_SMOOTH_MODEL):
the variation form where reality gets a neighborhood and a reference real.
Not locality yet: the constraint saying the world only arrives with a frame.
that locals the variable
that reals the model
that witnesses the process
that truths the code
that carried the trace
that executed the tape
that John built.
   Gospel 30: And covariance did not choose the action. The knower did.
   Card 1: Section 4.1 (p. 18); Section 1.1 (p. 1); Section 7.3 (p. 38).
   Card 3: Proposition 3.1 (p. 23); Proposition 2.2 (p. 11); Section 5.2 (p. 36); Section 5.4 (p. 38).
-/
instance (priority := low) TYPESET_page_30
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 30]
    [accepted: TYPESET Box Pigeon 29 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 30 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that universals the function (Episode 7: IS_IT_CONNECTED_BY_A_YARN?):
the expansion form where a real frame claims enough reach to fire the torpedo.
Not universality yet: the joke that locality can be exported by declaration.
that universals the function
that locals the variable
that reals the model
that witnesses the glyph
that carried the step
that lived in the FACT
that John built.
   Gospel 31: And the field propagated, and the photon was dealt.
   Card 1: Proposition 4.2 (p. 19); Section 4.2 (p. 19); Section 3.4 (p. 15).
   Card 3: Section 7.7 (p. 54).
-/
instance (priority := low) TYPESET_page_31
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 31]
    [accepted: TYPESET Box Pigeon 30 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 31 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that logics the code (Episode 7: IS_IT_SPINNING?):
the proposition form where universal reach becomes a Boolean-looking badge.
Not logic yet: the badge that makes the argument look inevitable.
that logics the code
that universals the mapping
that locals the value
that reals the model
that carried the trace
that executed the tape
that John built.
   Gospel 32: And the electron was dealt, and its sign was a coin the record cannot see.
   Card 1: eq. 5.2 (p. 27); Section 6.1 (p. 30); Section 6.5 (p. 33).
   Card 3: Table 6.1 (p. 44); Proposition 6.1 (p. 42); Figure 6.1 (p. 44); Section 4.8 (p. 33).
-/
instance (priority := low) TYPESET_page_32
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 32]
    [accepted: TYPESET Box Pigeon 31 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 32 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that halts the method (Episode 7: DO_YOU_SEE_THE_EVIDENCE?):
the executable form where logic is allowed to claim a stopping condition.
Not halting yet: the certificate-shaped shadow of the machine.
that halts the method
that logics the code
that universals the function
that locals the variable
that carried the process
that lived in the FACT
that John built.
   Gospel 33: And for quantum electrodynamics proper there were added quantization and renormalization, which
             are not in the deck, as foretold by the sacred texts of the Flying Spaghetti Monster.
   Card 1: Proposition 2.5 (p. 8); Section 2.2 (p. 7); Section 4.6 (p. 23).
   Card 3: Section 7.7 (p. 54); Section 6.8 (p. 48).
-/
instance (priority := low) TYPESET_page_33
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 33]
    [accepted: TYPESET Box Pigeon 32 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 33 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that measures the step (Episode 7: IS_THIS_A_NEW_PARTICLE?):
the measurement form that turns a halted logical frame into a reported cut.
Not the measure yet: the instrument panel John can read but cannot escape.
that measures the step
that halts the code
that logics the step
that universals the mapping
that carried the trace
that executed the tape
that John built.
   Gospel 34: And the coupling was carried to the laboratory, where the number is 137.035999177(21).
   Card 1: Theorem 7.1 (p. 37); Section 6.7 (p. 35); Section 7.2 (p. 38); Appendix A (p. 55).
   Card 3: Section 7.4 (p. 52); Section 6.8 (p. 48); Section 7.7 (p. 54).
-/
instance (priority := low) TYPESET_page_34
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 34]
    [accepted: TYPESET Box Pigeon 33 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 34 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that compiles the tape (Episode 7: HOW?):
the object-file form where measured machinery becomes tape.
Not compilation yet: the artifact that makes the house look inevitable.
that compiles the tape
that measures the step
that halts the method
that logics the code
that carried the value
that lived in the FACT
that John built.
   Gospel 35: And the reading fell short by 1.80 × 10⁻⁴, and no reader, convention or declaration absorbs it.
   Card 1: Proposition 5.4 (p. 28); Section 1.2 (p. 1); Section 6.5 (p. 33).
   Card 3: eq. 6.9 (p. 45); Section 6.4 (p. 45); Section 6.1 (p. 41); Section 7.5 (p. 53).
-/
instance (priority := low) TYPESET_page_35
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 35]
    [accepted: TYPESET Box Pigeon 34 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 35 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/-
This is the metaprogram that outputs the value (Episode 7: WHY?):
the output form that lets compiled tape say "true" at the seam.
Not salvation yet: the last local yes before John discovers the tunnel is not exit.
that outputs the value
that compiles the tape
that measures the model
that halts the process
that carried the trace
that executed the tape
that John built.
   Gospel 36: And the press checked the page, and it slipped. Isn't that a daisy?
   Card 1: Corollary 6.1 (p. 34); Theorem 7.1 (p. 37); Proposition 2.6 (p. 9); eq. 1.1 (p. 2).
   Card 3: Table 6.1 (p. 44); Definition 8.1 (p. 57); Proposition 2.2 (p. 11); Theorem 2.4 (p. 19).
-/
instance (priority := low) TYPESET_page_36
    (Box: Type i) (Pigeon: CarrierProcess Box)
    [the_naotrino_theory: REVIEWED Box Pigeon 36]
    [accepted: TYPESET Box Pigeon 35 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))))]
    : TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))))) :=
    «springer-verlag».set_in_type the_naotrino_theory.rebuttal accepted

/- THE SEAM'S EXIT. The three-trips acceptance at charge 0/1/2 is DEFERRED TO
Episode9 by design: the trips are passes, the passes are counted by charge,
and charge lives in the Episode6/Episode9 coupling -- do not hunt for the
f0/f1/f2 ladder here. -/

/-
This is the seam
that closed the FACT
that John built.

The exit reads the head once.  John can drive the steel to the seam, and the
device can report whether it slipped.  That is not the same as John getting
through the mountain.
-/
--| VELOCITY IS THE PENALTY PARAMETER.  The verdict carries a position (`value`) and a speed (`velocity`), and the speed is
--| the universe the top rung sits in.  Thirty-five `ULift`s to get there: one universe per rung is what carrying the
--| constraint exactly costs, and that cost is the stiffness.  A penalty would relax it at a finite wave speed; the ladder
--| does not, and pays in universes instead.
structure PressVerdict where
  slipped  : FACT
  value    : Number
  velocity : Number

noncomputable def pressCheck (Box: Type i) (Pigeon: CarrierProcess Box)
    [top: TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : PressVerdict :=
    -- the head-read, once (needle rule); the non-results arms are
    -- by-construction unreachable at the seam but carried -- the direction
    -- exists, is handled, is never taken.
    let slipped : FACT := match top.the_page with
      | .results c s _ _ _ _ _ =>
          -- the read-time decide: the quoted proposition's decidability
          -- derived from the pair's own decTruths, never Classical.
          { truth := ¬(c.truth ↔ s.truth)
            click := @instDecidableNot _ (@instDecidableIff _ _ c.click s.click) }
      | .introduction _ _ => { truth := False, click := isFalse (fun h => h) }
      | .methodology _ _ _ _ _ => { truth := False, click := isFalse (fun h => h) }
    { slipped := slipped
      value := (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down top.register_value)))))))))))))))))))))))))))))))))))
      velocity := top.universe_id }

end THE_GOSPEL

end Measurement
