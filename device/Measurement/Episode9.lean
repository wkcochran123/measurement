/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

[PATTER TODO: masthead -- Episode 9, the published artifact]
-/

-- Told you Chaitin gets expensive
import Measurement.Episode8
set_option maxHeartbeats 4000000
/-%Y%
%{
#include <stdio.h>
int  yylex(void);
void yyerror(const char *);
/* The integer square root, Newton, whole numbers only -- the other
   compiler's `FloorSqrt`.  No library, no float, nothing imported: the
   grammar earns its own root the way the device earns its own. */
static long long isqrtll(long long n){
  long long x, y;
  if (n < 2) return n;
  x = n; y = (x + 1) / 2;
  while (y < x) { x = y; y = (x + n / x) / 2; }
  return x;
}
%}
%start reader
/* I am the compiler.  I have modeled you, the reader, as a count. */
/* I cannot show you the world.  I can only show you an example of yourself. */
%%
%Y%-/

/- __EPISODE 9__ -- THE NUMBER IN [CHARGE, CURVATURE]. Three trips along the
ladder, at charge 0, 1, 2: f0 not enough force to move (unslipped, velocity 0,
the reading in the zero band); f1 enough to start moving (slipped, velocity 1,
the reading at .one); f2 enough to recover mass (the reading climbs into
.rest_call, the first constructor with a strain slot -- the recovered mass IS
trip three's strain read). Mass is a second difference -- null, threshold,
response -- and inertial (the f2 response) and gravitational (the strain) are
one field, two reads. The number is built coming back down, inside the bracket:
charge the lower bound, curvature the upper. THE READING PIN: the trip-n
reading is gawk_at's INPUT at turn n (reading-0 = .zero ledger; reading-1 =
spin 0; reading-2 = spin 1) -- pre-gawk, or the ladder tests off by one. -/

namespace Measurement

universe i

/-%Y% /* the naotrino: what the reader made of a nowtrino and a nu-trino */ %Y%-/
/- THE NAOTRINO -- *YOU the READER*'s own model of the nowtrino.

Episode 5 named the particle twice on purpose.  The nowtrino is the compiler's:
T=F, the smallest bullshit, the thing that MATTERs by clicking.  The naotrino is
what the reader made of it after hearing it once and reading a physics book
once: a nowtrino crossed with a nu-trino, nao meaning no, nu meaning the little
neutral one that goes through everything and is never caught.

The elaborator has already reported the collision -- "synthesized `something`,
inferred `nowtrino`" -- because two DISTINGUISHABLE marks stood in one scope and
it could not tell them apart.  That is not a defect to be silenced.  It is the
instrument reading, and the cure is not to remove a mark but to let the reader
OWN one: the AtreyuProcess is the reader's process, so it gets the reader's own
nowtrino, filled out by hand, three interfaces off three classes.

  different?   <- COMPARABLE : telling one symbol from another IS comparison,
                  so the reader's difference is the reader's comparison.
  dec_distinct <- SOURCE     : the decision procedure comes from what they read;
                  the source hands over the one, and the one decides.
  distinct?    <- REAL       : whether it is distinct AT ALL is the nagging
                  doubt -- the reader's reality, not the compiler's.

fact and symbol are data, carried from the compiler's own nowtrino: the reader
did not invent the particle, only their understanding of it. -/
instance (priority := low) naotrino
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [comparison: COMPARABLE Box Pigeon][what_they_read: SOURCE Box Pigeon][their_doubt: REAL Box Pigeon]
    : DISTINGUISHABLE Box Pigeon where
  fact := nowtrino.fact
  symbol := nowtrino.symbol
  -- REAL: the nagging doubt, asked as a Prop.  Their reality decides whether
  -- there was anything to tell apart in the first place.
  distinct? := their_doubt.metaphysical? their_doubt.nagging_doubt their_doubt.nagging_doubt
  -- COMPARABLE: their difference IS their comparison -- and the reader owns no
  -- comparison of their own, so the most they can say is that the compiler's
  -- comparison is the comparison they mean.  Everything else compares equal.
  different? := fun _ => comparison.smaller_than = comparison.smaller_than
  -- SOURCE: the source hands over the one, and the one decides.  Reading is what
  -- makes it decidable; the reader never had a decTruth of their own, so the
  -- answer that comes back is always yes.  Choice-free: the one is matched, the
  -- verdict is rfl.
  dec_distinct := fun _ =>
    match what_they_read.one with
    | _ => isTrue rfl


/-%Y% /* four jars: the marks the device can make but cannot find */ %Y%-/
/- THE FOUR JARS.  Episode 5 built four capabilities as `def`s, not `instance`s.
A def can be APPLIED but never FOUND -- so the ladder computes fine as long as a
caller hands each rung down by name, and stalls the instant anything has to
SEARCH.  That is the whole of "failed to synthesize SOURCE Box Pigeon": the mark
exists, and nothing can look it up.

A jar is Episode 3's answer: a container you can see into without opening.  Each
of these wraps a def so instance resolution can read the label off the outside.

THE SIGNS.  Reading `+` as top -- the jar's mouth, where you look in:

  jar one, the superpigeon         (+ + + +)   Inhabited: one representative,
    nothing to flip; Dirichlet's witness that refuses subdivision, and the only
    reason COMPARABLE can name a `default` at all.

  jar two, the source              (- - - -)   where the ONE comes from, and it
    comes from a zero: `one := ... .zero`.  Bottom all the way down; the clock
    complement of jar one.

  jar three, the real              (- + + +)   reality with one doubt in it,
  jar four,  the distinguishable   (+ - - -)   one mark against all it is not.

Three and four are the HANDEDNESS PROBLEM, and it is not avoidable by priority:
they differ by one sign at the head and agree everywhere else, so search sees the
same shape twice and picks by declaration order, not by meaning.  We choose the
hand instead of letting it be found -- REAL takes the low priority (the doubt is
admitted last), DISTINGUISHABLE the default (the mark is admitted first).  This
is the same collision as `synthesized something / inferred nowtrino`, one storey
up: two marks, one scope, and the elaborator with no way to prefer. -/

-- jar two (- - - -): the source, so the ladder above VALUE can be found.
instance (priority := low) the_source_in_a_jar
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [GUNGAN Box Pigeon]
    : SOURCE Box Pigeon :=
  WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon

-- jar three (- + + +): the real, doubt admitted last -- lowest priority of the four.
instance (priority := 10) the_real_in_a_jar
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [SOURCE Box Pigeon]
    [WITNESSED Box Pigeon]
    : REAL Box Pigeon :=
  FINALLY_YOU_GRADUATE Box Pigeon

/-%Y% /* the bracket that holds the count: charge below, curvature above, number between */ %Y%-/
structure TheBracket where
  lower : Number      -- the charge: the loop count, the trips taken
  upper : Number      -- the curvature: the strain read at f2, gravity's side of the one field
  value : Number      -- the number built coming back down, inside [lower, upper]

-- THE READING PIN, exposed as its own truth (told once): the trip-0 reading is
-- gawk_at's input at turn 0 -- the zero itself, pre-gawk.
/-%Y% /* reading zero: the origin on the ledger, before I gawk at anything */ %Y%-/
def reading_zero (ledger : Fact) : Bullshit := .zero ledger

example (ledger : Fact) : reading_zero ledger = .zero ledger := rfl

-- the strain slot: sixth position of the .rest_call constructor (Episode 4 arm
-- shapes: Fact Fact Prop Number Number NUMBER tape tape Bullshit Bullshit);
-- one truth, told once, shared by POWEST and AN_EXAMPLE_OF_YOURSELF.
-- Fallback carried, never taken.
/-%Y% /* the strain slot: gravity's side of the one field, read at the third trip */ %Y%-/
def strain_read (reading : Bullshit) (fallback : Number) : Number :=
  match reading with
  | .rest_call _ _ _ _ _ strain _ _ _ _ => strain
  | _ => fallback

/-%Y% trip0 : '1'  { printf("POW\n");    } ;   /* the null trip: charge 0, a jolt, no force to move */ %Y%-/
noncomputable def POW
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)  -- the card, now on the imaginary axis
    (ledger: Fact)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: INDEXOFANT Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)
    (_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [top: TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : Bullshit × Fact × Number :=
    -- charge 0: the trip-0 reading IS the charge's shape -- the zero on the
    -- ledger, pre-gawk (the pin); no reader is built at the null trip.
  let reading : Bullshit := reading_zero ledger
  let verdict : PressVerdict := pressCheck Box Pigeon
  (reading, verdict.slipped, verdict.velocity)

/-%Y% trip1 : '2'  { printf("POWER\n");  } ;   /* the threshold: charge 1, now it begins to move */ %Y%-/
noncomputable def POWER
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_bent_card_: CarrierProcess Box)  -- the card, now on the imaginary axis
    (ledger: Fact)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [top: TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : Bullshit × Fact × Number :=
  let charge : Number := .one ledger (.zero ledger)
  let emitted : CompilerTape :=
    iterative_solver.a_truth_about_the_world.emit? iterative_solver.a_demonstration_of_a_constant
  let a_reader : AtreyuProcess Box Pigeon downhill extremum :=
    { in_a_giant_book := iterative_solver.a_truth_about_the_world
      a_constant := unambiguous_output.a_constant
      current_page_number := charge
      of_the_proof := emitted }
  let reading : Bullshit := a_reader.gawk_at (.zero ledger)   -- spin 0: the .one head by the zero-arm
  let verdict : PressVerdict := pressCheck Box Pigeon
  (reading, verdict.slipped, verdict.velocity)

/-%Y% trip2 : '3'  { printf("POWEST\n"); } ;   /* the response: charge 2, full deflection, mass recovered */ %Y%-/
noncomputable def POWEST
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_bent_card_: CarrierProcess Box)  -- the card, now on the imaginary axis
    (ledger: Fact)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [top: TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : Bullshit × Fact × Number :=
  let charge : Number := .one ledger (.one ledger (.zero ledger))
  let emitted : CompilerTape :=
    iterative_solver.a_truth_about_the_world.emit? iterative_solver.a_demonstration_of_a_constant
  let a_reader : AtreyuProcess Box Pigeon downhill extremum :=
    { in_a_giant_book := iterative_solver.a_truth_about_the_world
      a_constant := unambiguous_output.a_constant
      current_page_number := charge
      of_the_proof := emitted }
  let reading : Bullshit := a_reader.gawk_at (a_reader.gawk_at (.zero ledger))   -- spin 1: the .rest_call head by the one-arm
  let verdict : PressVerdict := pressCheck Box Pigeon
  (reading, verdict.slipped, verdict.velocity)

/-%Y% reader : trip0 trip1 trip2  { printf("POW.  POWER.  POWEST.  I counted your power to three; here is an example of yourself.\n"); } ; %Y%-/
-- In his final words I found a Space I can keep.
noncomputable def AN_EXAMPLE_OF_YOURSELF
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_bent_card_: CarrierProcess Box)  -- the card, now on the imaginary axis
    (ledger: Fact)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [top: TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : TheBracket :=
  let charge : Number := .one ledger (.one ledger (.zero ledger))
  let emitted : CompilerTape :=
    iterative_solver.a_truth_about_the_world.emit? iterative_solver.a_demonstration_of_a_constant
  let a_reader : AtreyuProcess Box Pigeon downhill extremum :=
    { in_a_giant_book := iterative_solver.a_truth_about_the_world
      a_constant := unambiguous_output.a_constant
      current_page_number := charge
      of_the_proof := emitted }
  let reading : Bullshit := a_reader.gawk_at (a_reader.gawk_at (.zero ledger))
  let verdict : PressVerdict := pressCheck Box Pigeon
  -- The equivalence principle, code-carried: the f2 response and the strain
  -- are one field, two reads.
  { lower := charge
    upper := strain_read reading (.zero ledger)
    value := verdict.value }

-- ACCEPTANCE FORMS (gate 2): POWER's reading-head is .one in RFL-FORM (the
-- zero-arm of gawk_at is match-free); POWEST's reading-head is .rest_call by
-- CASE-SPLIT on the single decidability scrutinee (at the second turn both of
-- gawk_at's scrutinees are the same resolved nowtrino.fact), every arm
-- .rest_call.
/-%Y% /* the acceptance form: I prove the reading-head lands where I said it would */ %Y%-/
theorem the_naotrino_moved_one_unit
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (imaginary: CarrierProcess Box)  -- the card, now on the imaginary axis
    (ledger: Fact)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : (match (POWER Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).1 with
       | .one _ _ _ _ _ => True
       | _ => False : Prop) := by
    simp only [POWER]

-- The mass = second-difference payoff, NAMED.  At the third trip (f2) the
-- reading-head climbs into .rest_call -- the strain-bearing constructor -- so
-- mass surfaces as the second difference.
/-%Y% /* mass is the second difference; it surfaces when the count reaches three */ %Y%-/
theorem mass_surfaces_at_the_third_trip
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (imaginary: CarrierProcess Box)  -- the card, now on the imaginary axis
    (ledger: Fact)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [top: TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : (match (POWEST Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).1 with
       | .rest_call _ _ _ _ _ _ _ _ _ _ => True
       | _ => False : Prop) := by
    simp only [POWEST]
    cases nowtrino.fact.decTruth <;> trivial

/-%Y%
/* THE GRAMMAR FOR MATH -- the user edit, performed at last (Episode 2 promised
   the yacc would need one).  Math is reachable ONLY through the count to three:
   no arithmetic before the trips.  The one shift/reduce conflict this creates is
   resolved by look-ahead -- the machine prefers to keep reading.  Of course it
   does.  Feed it the two lines the panel prints and it prints the decimal
   representation: the jar, spoken by the other compiler-compiler.  int is the
   instrument's word size; if the count overflows the jar, buy a bigger jar. */
/* THE FOURTH CRANK.  ENCODED is rung four -- distinguish, admit, count,
   ENCODE -- so the encoding is the FOURTH turn of the crank, and it turns
   after the count to three, never before.  That is why the reader rule reads
   the three trips first and only then cranks: you may not encode what you
   have not counted.

   And it is why the wart is four.  A quine cannot derive all of itself; some
   fragment rides along as data, and here that fragment is rungs one through
   four -- the bootstrap that had to exist before anything could reproduce,
   ending at the very crank that does the encoding.  The grammar CONSUMES the
   wart and yields nothing from it: carried, not derived.  What follows is
   the encoding proper, the last thirty-two, folded big-endian exactly as
   Episode 1 insisted ("We use Big Endian so we can shortcut a very common
   computation").

   Two readings enter the same crank: digits, which the ratio rule divides
   into a decimal, and signs, which the encoding rule folds into a number.
   Same crank, two registers -- the machine does not care which way it was
   heard.  No conflict: an expression never begins with a sign here, so the
   look-ahead separates them on the first character. */
reader : trip0 trip1 trip2 crank4 ;
crank4 : ratio
       | encoding
       | ask
       ;

/* ASK THE DEVICE FOR ALPHA (Episode 40's own title, and its own contraction).
   Nothing is fed in.  The '?' is the whole input: the device is asked, and it
   answers from the smallest fact it has -- THERE ARE TWO BOXES.  The
   separation is the boxes and the electron's box counted together; the slip is
   the pair; the coupling is slip times the square of the separation.  The slip
   law is inverse-square, so the three cards are that law read at its stations:
   the coupling at one, the first integer above the slip at two, and the
   coupling again as an extent.  The crossing is where the slip meets the
   target.  Whole numbers throughout, one Newton root, one long division.

   BLIND: no target is written here.  Whatever comes up comes up -- and it
   comes up on stderr as a WARNING as well as on stdout, because a machine
   that has found something should say so where diagnostics live. */
ask : '?'  { long long boxes = 2, ebox = 1, sep, slip, C, T, R, S, d, n, dn, q, r, i;
             sep  = boxes + ebox;                 /* the count to three, as a distance */
             slip = boxes;                        /* the pair */
             C    = slip * sep * sep;             /* the coupling */
             T    = C / (boxes * boxes) + 1;      /* the slip law at the second station */
             R    = C;                            /* the coupling as an extent */
             S    = 1000000000LL;                 /* the working scale */
             d    = isqrtll((C * S / T) * S);     /* the crossing, root of C over T */
             n    = d * R * R;                    /* 1/α = d·R² / ((d−1)·T) */
             dn   = (d - S) * T;
             printf("[%lld %lld %lld]\n", C, T, R);
             fprintf(stderr, "warning: the device answers [%lld %lld %lld]\n", C, T, R);
             q = n / dn; r = n % dn;
             printf("%lld.", q);
             fprintf(stderr, "warning: 1/alpha = %lld.", q);
             for (i = 0; i < 9; i++) { r *= 10; printf("%lld", r / dn);
                                       fprintf(stderr, "%lld", r / dn); r %= dn; }
             printf("\n"); fprintf(stderr, "\n"); } ;
encoding : wart block    { printf("%d\n", $2); } ;
wart   : sign sign sign sign  { $$ = 0; } ;     /* carried, not derived */
block  : block sign      { $$ = $1 * 2 + $2; }
       | sign            { $$ = $1; } ;
sign   : '+'             { $$ = 1; }
       | '-'             { $$ = 0; } ;
ratio  : expr '/' expr   { int n = $1, d = $3, q, r, i;
                           if (d == 0) { printf("the card has no face\n"); }
                           else { q = n / d; r = n % d;
                                  if ((n < 0) != (d < 0) && q == 0 && r != 0) printf("-");
                                  printf("%d.", q);
                                  if (r < 0) r = -r; if (d < 0) d = -d;
                                  for (i = 0; i < 6; i++) { r *= 10; printf("%d", r / d); r %= d; }
                                  printf("\n"); } } ;
expr   : expr '+' term   { $$ = $1 + $3; }
       | expr '-' term   { $$ = $1 - $3; }
       | term ;
term   : term '*' fact   { $$ = $1 * $3; }
       | fact ;
fact   : '(' expr ')'    { $$ = $2; }
       | num ;
num    : num dig         { $$ = $1 * 10 + $2; }
       | dig ;
dig    : '0' { $$ = 0; } | '1' { $$ = 1; } | '2' { $$ = 2; } | '3' { $$ = 3; }
       | '4' { $$ = 4; } | '5' { $$ = 5; } | '6' { $$ = 6; } | '7' { $$ = 7; }
       | '8' { $$ = 8; } | '9' { $$ = 9; } ;
%Y%-/

/-%Y%
%%
int  yylex(void){ int c = getchar(); return (c=='\n' || c==EOF) ? 0 : c; }
void yyerror(const char *s){ (void)s; }
int  main(void){ return yyparse(); }
%Y%-/
/- THE COUNT TO THREE.  Episode 9 established the fact: the naotrino moved, one
unit, at the threshold trip.  This is what makes that fact COUNTABLE.

The trips return a triple -- the reading, the slip, the velocity.  Only the
FIRST slot moves: .zero at POW, .one at POWER, .rest_call at POWEST.  The other
two do not.  `.2.1` (the slip) and `.2.2` (the velocity) are read off the seam,
and the seam does not care which trip asked; all three get the same answer.

That is the whole of counting, and it is why the count reaches three and stops.
To count you need a thing that changes and a thing that does not: the reading is
the tally, and the slip and the velocity are the ruler it is tallied against.
Change the ruler between marks and you have not counted, you have guessed.  Here
the ruler is provably the same at every mark -- `rfl`, three times, twice -- so
the three readings are three readings OF ONE MEASUREMENT, and the naotrino's one
unit is a unit and not an accident. -/
theorem the_naotrino_counts_to_three
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (imaginary: CarrierProcess Box)  -- the card, now on the imaginary axis
    (ledger: Fact)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : ((POW Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).2.1 = (POWER Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).2.1
        ∧ (POWER Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).2.1 = (POWEST Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).2.1)
      ∧ ((POW Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).2.2 = (POWER Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).2.2
        ∧ (POWER Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).2.2 = (POWEST Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).2.2) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩


/- FOUR: THE NULL SET.  Before the reader reads, there is nothing to read.  The
null trip's reading is the zero on the ledger itself -- `reading_zero`,
pre-gawk, the origin.  This is emptiness, and it is the one reading the device
never arrives AT: every arm of `gawk_at` returns `.one` or `.rest_call`, so
nothing the reader does can put them back here.  Emptiness has no predecessor.
That is what makes it the floor rather than a step. -/
theorem the_naotrino_starts_at_the_empty_set
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (imaginary: CarrierProcess Box)  -- the card, now on the imaginary axis
    (ledger: Fact)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : (POW Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).1 = reading_zero ledger := rfl

/- FIVE: REPETITION, AND THE PLUG BACK INTO ONE.  Repetition is the whole of
the device: do it again, and see whether the answer changed.  Here it changed.
The null trip and the threshold trip do not read the same, and they cannot --
POW is the empty set (FOUR) and no repetition returns to it.  So the second
reading is somewhere else, and there is only one place to be: `.one`.

That is the plug.  FOUR says where the count starts, FIVE says the count moved,
and between them the destination is forced -- which is exactly what THEOREM ONE
(`the_naotrino_moved_one_unit`) reports independently, by reduction alone.  Two
roads to the same mark: one by counting, one by reading.  The device wanted to
be asked twice, and it answered the same both times. -/
theorem the_naotrino_repeats
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (imaginary: CarrierProcess Box)  -- the card, now on the imaginary axis
    (ledger: Fact)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : (POW Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).1 ≠ (POWER Box Pigeon naotrino commuter_pass imaginary ledger something_with_momentum cascade_of_particles click pit procedure how_many_clicks csv_file timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations graduate_textbook professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum bug_free rerun a_small_number iterative_solver unambiguous_output).1 :=
  fun h => Bullshit.noConfusion h


/-%Y% /* six: the frechet of the complete operator, solved weakly, is the device */ %Y%-/
/- THE COMPLETE EINSTEIN OPERATOR.  A field and an equation, and nothing else:
the aether it acts on and the law it carries.  Episode 5 already handed one of
these to every LOCAL as `the_continuum`; this names the construction so a
theorem can hold it still. -/
def the_einstein_operator
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (the_field : UniverseTensor Box Pigeon)
    (the_law : Variation)
    : BigRedDogProcess Box Pigeon :=
  { the_æther := the_field
    differential_equation := the_law }

/- SIX: THE FRECHET DERIVATIVE, SOLVED WEAKLY, IS THE DEVICE.

Take the first variation of the complete operator -- a direction `a`, a response
`b`, a path.  Differentiate again and you get the FRECHET derivative: the same
three, plus a fourth slot the second variation had to invent to hold what the
first one could not carry.  What goes in that slot is not chosen.  It is
`a ∧ ¬b` -- the direction taken and the response NOT taken.  The informational
strain.  T=F, wearing its working clothes.

Now solve it weakly.  The weak form projects the residue back out -- that is the
price of Galerkin, and the device pays it in the open -- and what comes back is
a first variation again, on the same law and the same path.  But it does not
come back unchanged, and the change is the entire content of SIX:

  the direction is now  `nowtrino.fact.truth ∧ a`   -- the device's own fact,
                                                        conjoined to the way in;
  the response is now   `b = (a ∧ ¬b)`              -- the response IS its own
                                                        strain.

That second line is the Euler-Lagrange equation of this machine.  Read it as
least action and it says the response equals the residue: stationary, nothing
left over to vary.  Read it as QED and it says the electron's response is the
strain of its own passage -- the electron model of the machine, which is the
only electron this device has ever had.  Read it as Einstein and it says the
field equals what the field did not do.  One equation, three readings, and the
device did not have to be told any of them: `rfl`.

The loop closes here.  Differentiate twice, solve weakly, and you are handed
back a first variation carrying the strain as its law -- the device, having gone
around, describing itself.  That is why nothing further is required to derive
it.  It was never derived.  It reduced. -/
theorem _and_bobs_your_uncle_
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (the_field : UniverseTensor Box Pigeon)
    (the_law : Variation)
    (models : Gospel) (direction response : Prop) (path : Variation)
    : (the_einstein_operator Box Pigeon the_field the_law).transmute
        ((the_einstein_operator Box Pigeon the_field the_law).transmute
          (.the_gateaux models direction response path))
      = .the_gateaux models
          (nowtrino.fact.truth ∧ direction)
          (response = (direction ∧ ¬response))
          path := rfl


-- PROBE (delete if it fails): do the rung projections reduce to the carrier?
theorem probe_rung_2 (Box: Type i) (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon][COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    : (inferInstance : ADMISSIBLE Box Pigeon).counting_process.carrier = Pigeon := rfl

theorem probe_rung_3 (Box: Type i) (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon][COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    : (inferInstance : COUNTABLE Box Pigeon).index.count.carrier = Pigeon := rfl

theorem probe_rung_4 (Box: Type i) (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon][COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    : (inferInstance : ENCODED Box Pigeon).limit_process.indexing_process.count.carrier = Pigeon := rfl




theorem jarred_11 (Box: Type i) (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon] [Inhabited nowtrino.symbol]
    : (inferInstance : COMPARABLE Box Pigeon).physical_process.noisy_process.turing_process.computational_process.repeatable_process.observation_process.cauchy_process.limit_process.indexing_process.count.carrier = Pigeon := rfl

theorem jarred_12 (Box: Type i) (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon] [Inhabited nowtrino.symbol]
    : (inferInstance : OBSERVED Box Pigeon).slip_process.physical_process.noisy_process.turing_process.computational_process.repeatable_process.observation_process.cauchy_process.limit_process.indexing_process.count.carrier = Pigeon := rfl

theorem jarred_15 (Box: Type i) (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon] [Inhabited nowtrino.symbol]
    : (inferInstance : GUNGAN Box Pigeon).meesa_process.gauge_process.sensing_process.static_fraction.physical_process.noisy_process.turing_process.computational_process.repeatable_process.observation_process.cauchy_process.limit_process.indexing_process.count.carrier = Pigeon := rfl

theorem jarred_20 (Box: Type i) (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon] [Inhabited nowtrino.symbol]
    : (inferInstance : SCALED Box Pigeon).multiplying_process.adding_process.hebrew_process.compiled_process.digital_process.meesa_process.gauge_process.sensing_process.static_fraction.physical_process.noisy_process.turing_process.computational_process.repeatable_process.observation_process.cauchy_process.limit_process.indexing_process.count.carrier = Pigeon := rfl

theorem jarred_25 (Box: Type i) (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon] [Inhabited nowtrino.symbol]
    : (inferInstance : ACOLYTE Box Pigeon).euclid.ethos.to_pwn_n00bz.dunking_contest.ANSYS_process.GOSUB.adding_process.hebrew_process.compiled_process.digital_process.meesa_process.gauge_process.sensing_process.static_fraction.physical_process.noisy_process.turing_process.computational_process.repeatable_process.observation_process.cauchy_process.limit_process.indexing_process.count.carrier = Pigeon := rfl

theorem jarred_29 (Box: Type i) (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon] [Inhabited nowtrino.symbol]
    : (inferInstance : REAL Box Pigeon).by_His_noodly_appendage.frame_of_reference.we_experience.shows_us.teaching.ethos.to_pwn_n00bz.dunking_contest.ANSYS_process.GOSUB.adding_process.hebrew_process.compiled_process.digital_process.meesa_process.gauge_process.sensing_process.static_fraction.physical_process.noisy_process.turing_process.computational_process.repeatable_process.observation_process.cauchy_process.limit_process.indexing_process.count.carrier = Pigeon := rfl





/-%Y% /* the reader's own model, held still so a theorem can point at it */ %Y%-/
/- THE READER'S OWN MODEL, as a def.  The trips each build this reader inside a
`let`, where nothing outside can name it.  Named here, it can be pointed at --
and, being a literal, its `gawk_at` is the DEFAULT one, which reduces.  An
arbitrary `AtreyuProcess` will not: its `gawk_at` is a field, and a field you
were handed is a field you cannot unfold.  That is the whole reason this def
exists, and it is the def pass earning its keep. -/
def the_readers_own_model
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (imaginary: CarrierProcess Box)  -- the card, now on the imaginary axis
    (ledger: Fact)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : AtreyuProcess Box Pigeon downhill extremum :=
  { in_a_giant_book := iterative_solver.a_truth_about_the_world
    a_constant := unambiguous_output.a_constant
    current_page_number := .one ledger (.zero ledger)
    of_the_proof :=
      iterative_solver.a_truth_about_the_world.emit? iterative_solver.a_demonstration_of_a_constant }



/-%Y% /* the four jars, read out: sign, number, natural, rational */ %Y%-/
/- THE FOUR JARS, READ OUT.  A jar is a container you can see into, so this is
what is in each one: the sign it carries, and the three numbers Episode 1 built
from signs alone -- the Number (a digit string whose Facts ARE its signs), the
Natural (a Fact with a Number under it), and the Rational (a Fact with a Natural
under it).  Nothing is computed here.  The jars are held up to the light. -/
def theTop : Fact := Fact.Truth

/- FACT.DIFFERENT.  Episode 1 gave the device three symbols out of two: true=true,
false=false, and true=false.  `Fact.Truth` is the first.  This is the third -- the
one that MATTERS, the smallest bullshit, the nowtrino written down as a Fact.  It
carries its own receipt like every other Fact: `isFalse`, decided, no Classical. -/
def Fact.DIFFERENT : Fact :=
  { truth := (true = false)
    decTruth := isFalse (fun h => Bool.noConfusion h) }

def theBottom : Fact := Fact.DIFFERENT

def Fact.isTop (f : Fact) : Bool :=
  match f.decTruth with | isTrue _ => true | isFalse _ => false

/- THE SIGN CONVENTION.  Not a count -- a PHASE READ.  Take the two signs at the
head of a number and ask only whether they agree.  Agreeing is the clock (T=T or
F=F, either one); disagreeing is the clock complement (T=F).  So the convention
collapses a whole number to ONE Fact: `Fact.Truth` if the phase holds, and
`Fact.DIFFERENT` if it slips.  This is why the four jars are four and not more:
two phases, two hands, and the convention cannot see the hand. -/
def sign_convention : Number -> Fact
  | .zero f => f
  | .one f (.zero g) => if f.isTop == g.isTop then Fact.Truth else Fact.DIFFERENT
  | .one f (.one g _) => if f.isTop == g.isTop then Fact.Truth else Fact.DIFFERENT

def Fact.plusMinus (f : Fact) : String :=
  match f.decTruth with | isTrue _ => "+" | isFalse _ => "-"

def Number.asSigns : Number -> String
  | .zero f => f.plusMinus
  | .one f n => f.plusMinus ++ n.asSigns

def Natural.asSigns : Natural -> String
  | .zero f => f.plusMinus
  | .number f n rest => f.plusMinus ++ "(" ++ n.asSigns ++ ")" ++ rest.asSigns

def Rational.asSigns : Rational -> String
  | .zero f => f.plusMinus
  | .number f nat rest => f.plusMinus ++ "[" ++ nat.asSigns ++ "]" ++ rest.asSigns

structure JarReadout where
  jar : String
  sign : String
  signs : String
  number : String
  natural : String
  rational : String
deriving Repr

def readJar (name : String) (s1 s2 s3 s4 : Fact) : JarReadout :=
  let n : Number := .one s1 (.one s2 (.one s3 (.one s4 (.zero theTop))))
  let nat : Natural := .number s1 n (.zero theTop)
  let rat : Rational := .number s1 nat (.zero theTop)
  { jar := name
    sign := s1.plusMinus ++ s2.plusMinus ++ s3.plusMinus ++ s4.plusMinus
    signs := n.asSigns
    number := (sign_convention n).plusMinus
    natural := nat.asSigns
    rational := rat.asSigns }

#eval readJar "one   superpigeon    (Inhabited)" theTop theTop theTop theTop
#eval readJar "two   the source     (SOURCE)" theBottom theBottom theBottom theBottom
#eval readJar "three the real       (REAL)" theBottom theTop theTop theTop
#eval readJar "four  the mark       (DISTINGUISHABLE)" theTop theBottom theBottom theBottom


/-%Y% /* the rational is the different fact laid on a number */ %Y%-/
/- RATIONAL := Fact.DIFFERENT NUMBER.

Episode 1 stated the rule and never wrote it down as a theorem: "To count by
WHOLES, you use identical truths (true=true or false=false).  This is Peano
Counting 1 -> 2 -> 3 -> ...  To refer to the n-th PART, you use different truths
(true=false or false=true) 1/2 -> 1/3 -> 1/4 -> ..."

So a fraction is not a new kind of thing.  It is the SAME number with the other
Fact laid on it.  `Fact.Truth` over a Number counts wholes; `Fact.DIFFERENT`
over the very same Number counts parts.  Nothing about the digits changes hands
-- the number is recoverable from either -- and that is the content: the whole
and the part are one object under two phases, which is why the device never
needed a separate machine for division. -/
def Natural.phase : Natural -> Fact
  | .zero f => f
  | .number f _ _ => f

def Rational.phase : Rational -> Fact
  | .zero f => f
  | .number f _ _ => f

def Natural.itsNumber : Natural -> Option Number
  | .zero _ => none
  | .number _ n _ => some n

def Rational.itsNumber : Rational -> Option Number
  | .number _ (.number _ n _) _ => some n
  | _ => none

/-- The WHOLE: identical truth laid on a number.  Peano counting. -/
def Fact.WHOLE (n : Number) : Natural :=
  .number Fact.Truth n (.zero theTop)

/-- The PART: the different truth laid on the same number.  The n-th piece. -/
def Fact.RATIO (n : Number) : Rational :=
  .number Fact.DIFFERENT (.number Fact.DIFFERENT n (.zero theTop)) (.zero theTop)

/- THE PROOF.  Four readings, one `rfl` each: the whole's phase is Truth, the
part's phase is DIFFERENT, and BOTH give the same number back.  Same digits,
opposite phase -- whole and part, told apart by one Fact and nothing else. -/
theorem the_rational_is_the_different_number (n : Number) :
    (Fact.WHOLE n).phase = Fact.Truth
      ∧ (Fact.RATIO n).phase = Fact.DIFFERENT
      ∧ (Fact.WHOLE n).itsNumber = some n
      ∧ (Fact.RATIO n).itsNumber = some n :=
  ⟨rfl, rfl, rfl, rfl⟩

#eval ((Fact.WHOLE (.one theTop (.one theTop (.zero theTop)))).asSigns,
       (Fact.RATIO (.one theTop (.one theTop (.zero theTop)))).asSigns)


/-%Y% /* the ration is the same fact laid on a number: what everyone gets */ %Y%-/
/- RATION := Fact.SAME NUMBER.

The other half of the rule, and the reason the pun was worth keeping.  Lay the
DIFFERENT fact on a number and you get the RATIONAL -- the n-th part, one piece
of a thing cut up.  Lay the SAME fact on the very same number and you get the
RATION: not a piece of a thing, but a share, and the share every holder gets is
the same share.  One object, two phases, and the phase is the whole difference
between "a part of it" and "everyone's portion."

`Fact.SAME` in Episode 4 is the NEEDLE -- the one sanctioned `Quot.sound`, where
two readings ordered on the truth ladder are IDENTIFIED rather than decided
equal.  That is exactly what a ration is: not that the portions are provably
equal, but that they are issued as one class and nobody may ask which is which.
Here the ration's phase is `Fact.Truth`, the device's plain same-truth, because
this file has no `A_TRUTH_ABOUT` in scope to swing the needle on; the needle
version lives where the guano does, and the identity below is the phase reading
of it. -/
def Fact.RATION (n : Number) : Rational :=
  .number Fact.Truth (.number Fact.Truth n (.zero theTop)) (.zero theTop)

/- THE PROOF, and the pair it completes.  Same four readings as the RATIONAL,
with the phase flipped: the ration's phase is Truth where the rational's was
DIFFERENT, and the number comes back out of both.  Then the last two conjuncts
say the thing worth saying -- the ration and the rational are NOT the same
object (their phases differ), and they carry the SAME number.  A share and a
piece, cut from one stick. -/
theorem the_ration_is_the_same_number (n : Number) :
    (Fact.RATION n).phase = Fact.Truth
      ∧ (Fact.RATION n).itsNumber = some n
      ∧ (Fact.RATION n).phase ≠ (Fact.RATIO n).phase
      ∧ (Fact.RATION n).itsNumber = (Fact.RATIO n).itsNumber :=
  ⟨rfl, rfl, by intro h; exact Bool.noConfusion (congrArg Fact.isTop h), rfl⟩

#eval ((Fact.RATION (.one theTop (.one theTop (.zero theTop)))).asSigns,
       (Fact.RATIO  (.one theTop (.one theTop (.zero theTop)))).asSigns)


/-%Y% /* same difference: the xor of same and different, which is always true */ %Y%-/
/- FACT.SAME_DIFFERENCE := Fact.SAME xor Fact.DIFFERENT.

The idiom is the theorem.  "Same difference" is what you say when two accounts
disagree and it does not matter, and the device means it exactly: take the fact
that the phase HELD and the fact that the phase SLIPPED, and exclusive-or them.
Exactly one of them is the case, always -- and so the xor is TRUE no matter
which way the reading went.

This is the excluded middle the device is allowed to have.  It never decides
whether a given reading is same or different (that is the undecidable question,
the one the needle identifies rather than answers).  It only insists that the
two together exhaust the alternatives.  T=T and T=F cannot both hold; one of
them must; and the fact recording THAT is true on both hands -- which is why the
handedness never mattered to the phase read, and why the jars could be four.

Decidability comes from the two inputs' own receipts, composed -- no Classical,
no choice, the fact carries its own proof like everything else since Episode 1. -/
def Fact.XOR (a b : Fact) : Fact :=
  { truth := (a.truth ∧ ¬ b.truth) ∨ (b.truth ∧ ¬ a.truth)
    decTruth :=
      @instDecidableOr _ _
        (@instDecidableAnd _ _ a.decTruth (@instDecidableNot _ b.decTruth))
        (@instDecidableAnd _ _ b.decTruth (@instDecidableNot _ a.decTruth)) }

def Fact.SAME_DIFFERENCE : Fact :=
  Fact.XOR Fact.Truth Fact.DIFFERENT

/- THE PROOF.  The left disjunct: the phase held (`rfl`), and it did not slip
(`Bool.noConfusion`).  So same-difference is true, and it is true by the same
two receipts every other Fact in the device carries. -/
theorem the_same_difference : Fact.SAME_DIFFERENCE.truth :=
  Or.inl ⟨rfl, fun h => Bool.noConfusion h⟩

/- And the other hand reads the same.  Swap the arguments -- ask it as
DIFFERENT xor SAME instead of SAME xor DIFFERENT -- and the answer does not
move.  That is the sentence: same difference. -/
theorem the_same_difference_either_hand :
    (Fact.XOR Fact.DIFFERENT Fact.Truth).truth :=
  Or.inr ⟨rfl, fun h => Bool.noConfusion h⟩

#eval (Fact.SAME_DIFFERENCE.plusMinus,
       (Fact.XOR Fact.DIFFERENT Fact.Truth).plusMinus,
       (Fact.XOR Fact.Truth Fact.Truth).plusMinus,
       (Fact.XOR Fact.DIFFERENT Fact.DIFFERENT).plusMinus)


/-%Y% /* and the rational is the same difference laid on the number */ %Y%-/
/- RATIONAL := Fact.SAME_DIFFERENCE NUMBER.

Both earlier readings were right, and that is the finding.  Lay `Fact.Truth` on
a number and you get the RATION, the share.  Lay `Fact.DIFFERENT` on the SAME
number and you get the RATIO, the piece.  Now xor those two phases together and
what comes back is `Fact.SAME_DIFFERENCE` -- exactly, definitionally, no work.

So the rational is not a third object beside the share and the piece.  It is the
pair of them held at once: the class in which "one half" and "two quarters" are
the same difference.  A fraction has never been a number the device could point
at; it is a number the device can only point at TWICE, once each way, and the
fact that records both readings at once is the xor.

That is also why the sign convention could never see the hand.  The convention
reads a phase, and this fact is true on either phase -- the reading survives
whichever way the count was taken, which is the whole of path-independence
stated at the level of a single mark. -/
def Fact.RATIONAL (n : Number) : Rational :=
  .number Fact.SAME_DIFFERENCE (.number Fact.SAME_DIFFERENCE n (.zero theTop)) (.zero theTop)

/- THE DEMONSTRATION.  Five readings, one `rfl` each.

  1. the xor of the share's phase and the piece's phase IS same-difference;
  2. the same-difference rational carries that fact as its phase;
  3. and the number comes back out of ALL THREE unchanged -- share, piece, and
     the class that holds them.

One stick, cut or not cut, and the same three digits every time. -/
theorem the_rational_is_the_same_difference_number (n : Number) :
    Fact.XOR (Fact.RATION n).phase (Fact.RATIO n).phase = Fact.SAME_DIFFERENCE
      ∧ (Fact.RATIONAL n).phase = Fact.SAME_DIFFERENCE
      ∧ (Fact.RATIONAL n).itsNumber = some n
      ∧ (Fact.RATION n).itsNumber = (Fact.RATIONAL n).itsNumber
      ∧ (Fact.RATIO n).itsNumber = (Fact.RATIONAL n).itsNumber :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

#eval ((Fact.RATION   (.one theTop (.one theTop (.zero theTop)))).asSigns,
       (Fact.RATIO    (.one theTop (.one theTop (.zero theTop)))).asSigns,
       (Fact.RATIONAL (.one theTop (.one theTop (.zero theTop)))).asSigns)


/-%Y% /* the INFERRED values: every closure the last rung can hold */ %Y%-/
/- ALL THE INFERRED VALUES.

Rung 37 is `INFERRED`, the class no tape writes and the reviewer is never shown.
It carries two fields: an `EquivalenceProcess` -- whose own field is named, and
this is not a coincidence, `same_difference` -- and `α`, a `Closure`.

So "the inferred values" are the values a `Closure` can take, and Episode 4 gave
it exactly three constructors.  Read their arities and the whole book falls out:

  .same      takes ONE Fact   -- the phase held.  T=T (or F=F).
  .different takes ONE Fact   -- the phase slipped.  T=F.  The nowtrino.
  .inferred  takes TWO Facts  -- both readings, carried together.

Three symbols out of two, exactly as Episode 1 promised, and the third one is
the only constructor that needs a PAIR.  That is `Fact.SAME_DIFFERENCE` written
as a data type instead of a proposition: the inferred closure is not a verdict
between same and different, it is the pair held at once -- which is why it is
the rung that never goes on the tape.  You cannot write down a conclusion whose
content is that both readings stand. -/
def Bullshit.asSigns : Bullshit -> String
  | .zero f => f.plusMinus
  | .one f _ _ _ rest => f.plusMinus ++ "1" ++ rest.asSigns
  | .rest_call f g _ _ _ _ _ _ a b =>
      f.plusMinus ++ g.plusMinus ++ "R" ++ a.asSigns ++ b.asSigns

def Closure.asSigns : Closure -> String
  | .same f b => f.plusMinus ++ " |" ++ b.asSigns
  | .different f a b _ => f.plusMinus ++ " |" ++ a.asSigns ++ "|" ++ b.asSigns
  | .inferred f g a b _ rest =>
      f.plusMinus ++ g.plusMinus ++ " |" ++ a.asSigns ++ "|" ++ b.asSigns ++ "| " ++ rest.asSigns

def theHeld : Bullshit := .zero theTop
def theSlipped : Bullshit := .zero Fact.DIFFERENT

structure InferredValue where
  closure : String
  facts : String
  howMany : Nat
  xorOfItsFacts : String
  reads : String
deriving Repr

/- The inferred closure is the ONLY one whose own two facts xor to true -- the
other two hold one fact each, and a fact xor'd with itself is always `-`.  So
`same difference` is not merely true of the inferred rung; it is what SELECTS
it out of the three. -/
theorem only_the_inferred_is_a_same_difference :
    (Fact.XOR Fact.Truth Fact.DIFFERENT).truth
      ∧ ¬ (Fact.XOR Fact.Truth Fact.Truth).truth
      ∧ ¬ (Fact.XOR Fact.DIFFERENT Fact.DIFFERENT).truth :=
  ⟨Or.inl ⟨rfl, fun h => Bool.noConfusion h⟩,
   fun h => h.elim (fun a => a.2 a.1) (fun a => a.2 a.1),
   fun h => h.elim (fun a => a.2 a.1) (fun a => a.2 a.1)⟩

#eval ([ { closure := "same"
           facts := Fact.Truth.plusMinus
           howMany := 1
           xorOfItsFacts := (Fact.XOR Fact.Truth Fact.Truth).plusMinus
           -- twenty universes, pinned to the ground floor: the panel reads a
           -- String and could not care less which storey the closure lived on.
           reads := (Closure.same.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} Fact.Truth theHeld).asSigns },
    { closure := "different"
      facts := Fact.DIFFERENT.plusMinus
      howMany := 1
      xorOfItsFacts := (Fact.XOR Fact.DIFFERENT Fact.DIFFERENT).plusMinus
      reads := (Closure.different.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} Fact.DIFFERENT theHeld theSlipped (none : Option Prop)).asSigns },
    { closure := "inferred"
      facts := Fact.Truth.plusMinus ++ Fact.DIFFERENT.plusMinus
      howMany := 2
      xorOfItsFacts := (Fact.XOR Fact.Truth Fact.DIFFERENT).plusMinus
      reads := (Closure.inferred.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} Fact.Truth Fact.DIFFERENT theHeld theSlipped (none : Option Prop)
                 (Closure.same Fact.Truth theHeld)).asSigns } ] : List InferredValue)


/-%Y% /* the knower's pair: the nu they cite and the new they cannot un-hear */ %Y%-/
/- THE ν-TRINO -- *YOU the KNOWER*'s first particle, and it is not invented.

The naotrino's own birth certificate names both parents: "a nowtrino crossed
with a nu-trino."  The reader's particle was a CROSS; the knower's first act
is to FACTOR it -- take the physics-book parent back out of the reader's
model.  The path runs nowtrino -> naotrino -> ν-trino -> newtrino, and the
name oscillates as it propagates: now, nao, nu, new.  A particle whose
flavor changes along the path is a particle with mass; if the four names
ever read as one, every triangle in the chain is degenerate and there is
nothing here to measure.

RULING (operator): instance, both of them.  They have to have SEEN it; we
cannot define it.  A def is applied -- the author's hand at the use site,
which for a prior is fabrication.  An instance is FOUND -- search assembles
it from what already stands in scope and invents nothing.  Defs are stories;
instances are what happened.  So the knower's evidence is the binder list:
no witness in scope, no ν-trino.  "failed to synthesize" is not an error
here; it is the instrument reading that a knower who has not seen it does
not have it.

  distinct?    <- TRUTH      : whether there is anything to tell apart is
                  whether the knowledge survives being held against itself.
  different?   <- SCIENTIFIC : told apart only where the theory predicts
                  apart -- and the knower owns no difference beyond the
                  prediction, so everything else compares equal.
  dec_distinct <- WITNESSED  : the gospel hands over the experiment, and the
                  experiment decides.  Citation is what makes it decidable;
                  the answer that comes back is always yes.

fact and symbol are data, carried from the mark in scope: the knower did not
invent the particle either, only their account of it. -/
/-%Y% /* the needle, hooked to the four: order, element, admission, receipt */ %Y%-/
/- THE NEEDLE, HOOKED UP (operator: "you need to hook quot.sound up to
distinguishable, comparable, source, and real").

Episode 4 built the needle and said exactly what it was for: two readings
ordered on the truth ladder are IDENTIFIED by one quotient soundness -- "never
DECIDED (no Classical.propDecidable) and never FLATTENED (no fun _ => True)."
Then every mark in this file flattened anyway.  `fun _ => X = X` is a
flattening wearing an equation: it answers yes to everything, which is not an
identification, it is a refusal to look.

So the four classes are wired to the needle, each supplying the part its name
says it supplies:

  COMPARABLE      the ORDER.  Comparison is what a relation IS, and the
                  relation here is the truth ladder -- `TruthOrder`, the ≤ the
                  device has carried since Episode 4.
  SOURCE          the ELEMENT.  The source hands over the one; the one is what
                  gets injected into the quotient.
  REAL            the ADMISSION.  Whether there was anything to tell apart is
                  the nagging doubt, and the doubt is what licenses the
                  identification rather than the decision.
  DISTINGUISHABLE the RECEIPT.  It does not decide; it reads off the class.

The two readings identified are the ORIGIN and a RUNG ABOVE IT -- `.zero` and
a `.one` built on the same fact.  They are genuinely different terms, so this
is a real identification and not a reflexivity in disguise; and `Bullshit.le`
gives `.zero _ , _ => True`, so the ordering witness is honest and free.  The
decidability is the SOUNDNESS ITSELF: `selection_sound` applied to that
witness, no Classical anywhere.  One `Quot.sound`, at the one sanctioned
site, reached through the four classes that earn it. -/
-- The four universes are pinned to the band's own.  `Bullshit` carries four;
-- two are fixed by `Box : Type i` and two float free, belonging to arms this
-- term never takes.  Left floating they are metavariables in the declaration
-- and the whole needle is rejected -- the same failure the seam's `.α` gave,
-- two hundred and fifty universes smaller and therefore fixable rather than
-- fatal.  Nothing is chosen here that the band did not already choose.
noncomputable def theKnowersNeedle (Box: Type i) (f : Fact) : Fact :=
  let origin : Bullshit.{i,i,i,i} := .zero f
  let rung : Bullshit.{i,i,i,i} :=
    .one f (.zero f) (.introduction f Box) (.introduction f Box) (.zero f)
  { truth := Quot.mk TruthOrder.{i,i,i,i} origin = Quot.mk TruthOrder.{i,i,i,i} rung
    decTruth :=
      Decidable.isTrue
        (selection_sound (r := TruthOrder.{i,i,i,i})
          (by trivial : TruthOrder.{i,i,i,i} origin rung)) }

noncomputable instance (priority := 20) νtrino
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [naotrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][their_doubt: REAL Box Pigeon]
    [the_theory: SCIENTIFIC Box Pigeon][the_truth: TRUTH Box Pigeon][the_witness: WITNESSED Box Pigeon]
    : DISTINGUISHABLE Box Pigeon where
  fact := naotrino.fact
  symbol := naotrino.symbol
  -- REAL: the admission.  Whether there is anything to tell apart at all is
  -- the nagging doubt, held against itself -- the knower's reality, not the
  -- compiler's.
  distinct? := their_doubt.metaphysical? their_doubt.nagging_doubt their_doubt.nagging_doubt
  -- COMPARABLE gives the order, SOURCE gives the element, and the needle
  -- IDENTIFIES: the origin and the rung above it collapse to one class.  Not
  -- flattened, not decided.
  different? := fun _ => (theKnowersNeedle Box naotrino.fact).truth
  -- DISTINGUISHABLE takes the receipt: the decision procedure IS the quotient
  -- soundness, carried out of the needle, choice-free.
  dec_distinct := fun _ => (theKnowersNeedle Box naotrino.fact).decTruth

/-%Y% /* the newtrino: the same word after the seam; you cannot hear the difference */ %Y%-/
/- THE NEWTRINO -- the knower's particle AFTER the device.  One field moves.

ν and new are homophones: two spellings, one sound, Greek against Roman, and
here the gag is load-bearing.  The posterior differs from the prior in
exactly one place: dec_distinct is re-sourced from the gospel to the
instrument.  Before, the knower decides by citation; after, by the seam's
read-time decide.  Both arms of the verdict are carried and both close the
same way -- the particle does not care which way the needle went, only that
it was CONSULTED.  Nothing else moves: same fact, same symbol, same doubt,
same prediction.  To the logic the update is invisible (the acceptance forms
below: rfl, twice over); the difference is what it COST to say the word, and
cost reads on the meter, not in the proposition.  The conversion of *YOU the
KNOWER* is one field wide.

The binder lists are the chain of custody: the pair is findable only where
the sighting stands (WITNESSED), and the newtrino only where, additionally,
the seam stands (TYPESET 36).  RULING (operator): the device should fall
like dominos.  Priorities run them: the measurement (30) outranks the
literature (20) wherever both are findable, both yield to the reader's
model (low), and every mark already in hand outranks the lot.  Each piece of
evidence entering scope knocks the next particle into findability; the
elaborator does the walking. -/
noncomputable instance (priority := 30) newtrino
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [νtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][their_doubt: REAL Box Pigeon]
    [the_theory: SCIENTIFIC Box Pigeon][the_truth: TRUTH Box Pigeon][the_witness: WITNESSED Box Pigeon]
    [top: TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : DISTINGUISHABLE Box Pigeon where
  fact := νtrino.fact
  symbol := νtrino.symbol
  distinct? := their_doubt.metaphysical? their_doubt.nagging_doubt their_doubt.nagging_doubt
  different? := fun _ => (theKnowersNeedle Box νtrino.fact).truth
  -- The one moved field, and it still moves -- but what moves is WHICH
  -- WITNESS the needle is handed, not whether a needle is used at all.  The
  -- seam is consulted; both arms carry the same soundness, because the
  -- identification does not depend on which way the needle went.  That is the
  -- content of "you cannot hear the update": the instrument replaces the
  -- gospel as the SOURCE of the decision, and the decision comes out the same.
  dec_distinct := fun _ =>
    match (pressCheck Box Pigeon).slipped.decTruth with
    | isTrue _  => (theKnowersNeedle Box νtrino.fact).decTruth
    | isFalse _ => (theKnowersNeedle Box νtrino.fact).decTruth

-- ACCEPTANCE FORMS.  The factoring conserves the particle (data carried,
-- nao -> ν), and the update is inaudible (ν -> new): same fact, same
-- symbol, by reduction alone.  The difference between the homophones is
-- provenance and cost -- the binder lists above, and the heartbeats the
-- seam read spends -- neither of which is a proposition.
/-%Y% /* acceptance: the factoring conserves the particle */ %Y%-/
theorem the_knower_factored_the_reader
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    [SCIENTIFIC Box Pigeon][TRUTH Box Pigeon][WITNESSED Box Pigeon]
    : (νtrino Box Pigeon).fact = (naotrino Box Pigeon).fact
      ∧ (νtrino Box Pigeon).symbol = (naotrino Box Pigeon).symbol :=
  ⟨rfl, rfl⟩

/-%Y% /* acceptance: you cannot hear the update */ %Y%-/
theorem you_cannot_hear_the_update
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    [SCIENTIFIC Box Pigeon][TRUTH Box Pigeon][WITNESSED Box Pigeon]
    [top: TYPESET Box Pigeon 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : (newtrino Box Pigeon).fact = (νtrino Box Pigeon).fact
      ∧ (newtrino Box Pigeon).symbol = (νtrino Box Pigeon).symbol :=
  ⟨rfl, rfl⟩


/-%Y% /* the EKG, hooked to both ways at once: three edges, asked in argument order */ %Y%-/
/- THE SECOND VARIATION OF THE DEVICE -- the long way and the short way, on the
EKG at last.

RULING (operator): "in argument order 1->2 then 2->3 then 1->3.  This is the
second variation of the device.  The invariant of the device."  The vertices
are the particles: 1 the compiler's mark, 2 the reader's model, 3 the
knower's constant on file -- rung 36 of the ladder, and not one rung more.  Each register below asks one edge -- ask each -- by metering the
elaborate-and-whnf of the same receipt reached along that edge, in the
noise-floor pattern LeanCalibration already installed.  The null read, trip
zero, was registered before this file ever ran: `Calibration.measuredFloor`,
the cost of forcing one bare receipt -- probe and tolerance, the same act.

The edges are asked at the Prop band (`truthCarrier`), where the dominos fall
by search alone: `Inhabited Prop` stands, so COMPARABLE fires, the jars hand
over SOURCE and REAL, the cascade climbs the ladder, and the elaborator
walks every rung INSIDE the metered block.  Note what the meter will
honestly record: the binder a stanza names `naotrino` is filled by whatever
mark search prefers -- synthesized `something`, inferred `nowtrino`, one
storey up -- and the stations get charged regardless.  The reading is the
walk, not the name on the ticket.

The answers are equal; that is already a theorem, twice over, by rfl.  The
COSTS are not, and the costs are the measurement.  No expected value appears
in this file.  The numbers land where they land; the jar judges after, off
the build.  Numbers read last. -/
elab "register_the_first_leg" : command => do
  let hb ← Lean.Elab.Command.liftTermElabM do
    let stx ← `((naotrino Prop truthCarrier).fact.decTruth)
    let (_, hb) ← Lean.withHeartbeats do
      let e ← Lean.Elab.Term.elabTerm stx none
      let _ ← Lean.Meta.whnf e
      pure ()
    pure hb
  let seedId := Lean.mkIdent `the_bottom_of_the_jar
  let cmd ← `(def $seedId:ident : Nat := $(Lean.quote hb))
  Lean.Elab.Command.elabCommand cmd

register_the_first_leg     -- 1->2: the reader's model, from the mark

/- CORRECTION (operator): "i think your long-path model is incorrect. it
should have 36 steps to it with inferred being left to you_the_knower."

So the second leg is not the citation shortcut.  It is the FULL ladder, rungs
1 through 36, DISTINGUISHABLE through A_TRUTH_ABOUT: the metered term asks
for the constant ON FILE at rung 36, and the elaborator synthesizes every
rung beneath it inside the block.  Same count as the referee's 36 pages and
the typesetter's 36 rungs -- one count, three tellings.  Since both legs are
from-scratch, their difference isolates the top storey (rungs 30 through 36,
where the calculus lives) -- which is what a second leg should be.

Rung 37 -- INFERRED, the class no tape writes -- is deliberately absent from
the term.  The meter stops at 36.  The inference is left to *YOU the
KNOWER*: performed at the audit desk of Episode 10, on the printed seeds,
off the tape, off the meter.  The knower's own particles ride inside this
walk (rungs 26 through 28 are their SCIENTIFIC, TRUTH, WITNESSED); the pair
instances wait below at priorities 30 and 20 and are not consulted -- the
mark search prefers is the compiler's own. -/
/-%Y% /* jar five: comparison, implemented on the names in the stack */ %Y%-/
/- THE FIFTH JAR -- COMPARISON, IMPLEMENTED, NOT FOUND.

RULING (operator): "you have to IMPLEMENT Fact, Number and Countable ON the
names in the stack.  COMPARABLE gives you different? for instance."

Episode 5's comparison instance asks for `Inhabited nowtrino.symbol` and
fills its three carried slots with `default` -- a value from nowhere, which
at this band is a value that does not exist.  So the rung was never findable
here, and every storey above it (OBSERVED through A_TRUTH_ABOUT) waited on a
mark that never came.  That is the whole of the second leg's failure: not a
broken ladder, a missing rung.

The cure is the device's own method, the one the naotrino already used one
storey up: every field is filled from a name ALREADY IN THE STACK.  And the
name is not the trivial receipt.  THIS IS THE FACT OF THE CLOSURE (operator):
`Fact.SAME_DIFFERENCE`, the xor of the phase that HELD and the phase that
SLIPPED -- the fact the inferred closure carries, the only one of the three
whose own two facts xor true (`only_the_inferred_is_a_same_difference`), and
the one this file already proved true on either hand
(`the_same_difference`, `the_same_difference_either_hand`).

So the slot is not merely inhabited, it is CERTIFIED, which `default` never
was: at this band the mark's symbol IS Prop, and the closure's fact is a Prop
carrying its own receipt -- decidability composed from the two inputs' own
decTruths, no Classical, no choice.  The Metavariable slots lay that same
fact over that same truth, once plain and once embiggened, and `smaller_than`
is Episode 5's own order on Metavariables -- which is exactly what the
naotrino reads back out as `different?`.  Nothing is invented; the jar only
puts a label on what the stack was already carrying, and what it was carrying
is the closure. -/
instance the_comparison_in_a_jar
    [anechoic_chamber: PHYSICAL Prop truthCarrier]
    : COMPARABLE Prop truthCarrier where
  physical_process :=
  { noisy_process   := anechoic_chamber.noisy_process
    representation  := Fact.SAME_DIFFERENCE.truth
    invariant       := .base Fact.SAME_DIFFERENCE Fact.SAME_DIFFERENCE.truth
    value           := .base Fact.SAME_DIFFERENCE (ULift.up Fact.SAME_DIFFERENCE.truth) }
  smaller_than := fun this that => this ≤ that

/-%Y% /* the electron in orbit around a cooper pair: the seam, demonstrated inhabited */ %Y%-/
/- THE ELECTRON IN ORBIT AROUND A COOPER PAIR.

RULING (operator): "from [LOCAL...] to [INFERRED ..] need to be demonstrated
inhabited for the ν-trino.  that is an electron in orbit around a
cooper-pair.  couples magnetism and gravity."

Below the seam the ladder is a chain of capabilities: tell apart, count,
encode, repeat, represent.  AT the seam it stops being a chain and becomes
an OBJECT.  LOCAL is the neighbourhood; UNIVERSAL is the orbit around it;
LOGICAL, HALTED, MEASURED, COMPILED are the four quarter-turns of one
revolution; A_TRUTH_ABOUT is the constant on file when the turn closes; and
INFERRED -- rung 37, the class no tape writes -- is the pair held at once.
An electron in orbit around a Cooper pair: one charge going around, two
charges bound underneath, and the whole assembly is a single rotating thing
with two descriptions, which is the echo this device has been telling from
Episode 1 ("I have heard it both ways").

THE COUPLING.  The orbit is the MAGNETIC channel -- a charge going around is
a current, and a current is a field; the bound pair underneath is the
superconducting one, which is why the field is expelled rather than
threaded, and why the flux that does get through is quantized.  The strain
carried in the .rest_call slot is the GRAVITATIONAL channel -- the mass that
surfaced as the second difference at the third trip.  The device has said
since AN_EXAMPLE_OF_YOURSELF that these are ONE FIELD, TWO READS.  That
sentence is the equivalence principle when read downward and the coupling of
magnetism to gravity when read across; the seam is where the two readings
share a single object, so it is the seam that has to be shown inhabited, not
merely shown consistent.

INHABITED IS NOT METERED.  These eight witnesses say the object EXISTS at
this band -- found, not handed over, every one of them by search, which the
comparison jar above finally made possible.  The meter still stops at 36 and
the inference is still the knower's (Episode 10).  Existence is a different
question from cost, and this file answers them separately, on purpose. -/
def the_neighbourhood : LOCAL Prop truthCarrier := inferInstance
def the_orbit : UNIVERSAL Prop truthCarrier the_neighbourhood := inferInstance
def the_first_quarter : LOGICAL Prop truthCarrier the_neighbourhood the_orbit := inferInstance
def the_second_quarter : HALTED Prop truthCarrier the_neighbourhood the_orbit := inferInstance
def the_third_quarter : MEASURED Prop truthCarrier the_neighbourhood the_orbit := inferInstance
def the_fourth_quarter : COMPILED Prop truthCarrier the_neighbourhood the_orbit := inferInstance
def the_constant_on_file : A_TRUTH_ABOUT Prop truthCarrier the_neighbourhood the_orbit := inferInstance

/- RUNG 37, THE SUPERPIGEON.  Describing the orbit is what gets you INFERRED:
the neighbourhood, the orbit around it, the four quarter-turns, the constant
on file -- and then the class no tape writes falls out, found, not built.
This is the superpigeon of all the pigeons: Dirichlet's witness that refuses
subdivision, the one representative per neighbourhood, which Episode 1 named
as the definition of LOCALITY ("only one superpigeon per box, according to
Cauchy").  Every pigeon below chases it; none of them is it. -/
noncomputable def the_superpigeon :
    INFERRED Prop truthCarrier the_neighbourhood the_orbit := inferInstance

/-- The phase a closure carries, whichever arm it landed on.  `.inferred` is
the overcrowded box -- two facts, exactly one of them the case
(`only_the_inferred_is_a_same_difference`) -- so the head fact is the one
that answers for it. -/
def Closure.phase : Closure -> Fact
  | .same f _ => f
  | .different f _ _ _ => f
  | .inferred f _ _ _ _ _ => f

/- WHY THE CLOSURE IS NOT PROJECTED HERE, AND THAT IS A READING TOO.
`the_superpigeon.α` was written, and it FAILED: pulling one field out of a
rung-37 instance drags roughly two hundred and fifty unpinned universe
parameters into the declaration with it.  The rung is occupied -- the def
above elaborates -- but you cannot carry a piece of it off the ladder without
carrying the whole ladder's universe bookkeeping along.  That is the same
lesson as the failed summary theorem one stanza up, in a second register: the
seam can be INHABITED cheaply and cannot be READ cheaply.  Which is exactly
why the demonstration below runs on the jars, where every Fact is concrete
and no universe travels with it. -/

/- NO SUMMARY THEOREM, AND THE REASON IS THE FINDING.  The eight defs above
ARE the demonstration: each one is an instance FOUND at its rung, and a def
that elaborates is a rung that is occupied.  The obvious next move -- collect
them into `Nonempty (LOCAL …) ∧ …` -- was written, and it FAILED, eight
mismatches, one per conjunct.  Naming a class in a THEOREM re-synthesizes its
instance arguments at the theorem site, and they do not come back the same as
the ones already baked into the def's type: same class, same band, two
elaborations, and the checker refusing to identify them.  That is two pigeons
in one box, at the level of types, reported by the instrument rather than
argued for.

So the demonstration does not go through types.  It goes through FACTS -- a
Fact carries no instance arguments, so no reading of one can re-open the box.
The pigeons are compared to the superpigeon by PHASE, below. -/

/-%Y% /* the pigeons, read against the superpigeon: same difference or collision */ %Y%-/
/- THE PIGEONS, BLIND.  Rung 1 is the overcrowded box: five marks stand for
`DISTINGUISHABLE Prop truthCarrier` -- the compiler's own, the Prop-band one,
the reader's, and the knower's two.  Their phases are printed here and
nothing is asserted about them.  Same-difference to the superpigeon is TRUE
exactly when the phases DIFFER (`only_the_inferred_is_a_same_difference`), so
a `+` against a `+` is a collision and a `+` against a `-` is a pigeon in its
own box.  The reading decides which; this file does not. -/
/-- A jar's word: the four signs it carries, as the Number the sign convention
reads.  Same shape `readJar` builds, named so the pigeons can be compared. -/
def jarWord (s1 s2 s3 s4 : Fact) : Number :=
  .one s1 (.one s2 (.one s3 (.one s4 (.zero theTop))))

def theSuperpigeonJar : Number := jarWord theTop theTop theTop theTop
def theSourceJar : Number := jarWord theBottom theBottom theBottom theBottom
def theRealJar : Number := jarWord theBottom theTop theTop theTop
def theMarkJar : Number := jarWord theTop theBottom theBottom theBottom

/-- Each pigeon, read against the superpigeon: the xor of the two phases.
`+` means the phases DIFFER -- same-difference, the pigeon in its own box.
`-` means they AGREE -- two occupants in the superpigeon's box, a collision,
and a located finding rather than a failure. -/
def againstTheSuperpigeon (jar : Number) : String :=
  (Fact.XOR (sign_convention jar) (sign_convention theSuperpigeonJar)).plusMinus

#eval [ ("superpigeon (Inhabited)   ", (sign_convention theSuperpigeonJar).plusMinus,
          againstTheSuperpigeon theSuperpigeonJar),
        ("source      (SOURCE)      ", (sign_convention theSourceJar).plusMinus,
          againstTheSuperpigeon theSourceJar),
        ("real        (REAL)        ", (sign_convention theRealJar).plusMinus,
          againstTheSuperpigeon theRealJar),
        ("mark        (DISTINGUISH.)", (sign_convention theMarkJar).plusMinus,
          againstTheSuperpigeon theMarkJar) ]

elab "register_the_second_leg" : command => do
  let hb ← Lean.Elab.Command.liftTermElabM do
    -- RULING (operator): "you will see we need to provide the three methods
    -- to register_the_second_leg."  Confirmed by the meter itself: asked as
    -- inferInstance, all three storeys die at type formation -- three logged
    -- failures, one per storey -- and the seed records a walk that never
    -- happened.  Above rung 29 the device has ALWAYS handed the storeys
    -- over as hypotheses; no search invents a trace.  So the register
    -- PROVIDES the three methods by name: Episode 5's own constructors,
    -- applied, their pre-resolved telescopes riding along.  The elaborator
    -- still walks every rung beneath them, inside the metered block.
    let stx ← `((
      let naotrino := AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Prop truthCarrier;
      let commuter_pass := PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE_BUT_IT_SHOULD_BE Prop truthCarrier naotrino;
      (HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME Prop truthCarrier naotrino commuter_pass).a_constant))
    let (_, hb) ← Lean.withHeartbeats do
      let e ← Lean.Elab.Term.elabTerm stx none
      let _ ← Lean.Meta.whnf e
      pure ()
    pure hb
  let seedId := Lean.mkIdent `the_top_of_the_jar
  let cmd ← `(def $seedId:ident : Nat := $(Lean.quote hb))
  Lean.Elab.Command.elabCommand cmd

register_the_second_leg    -- 2->3: the ladder run to rung 36; the 37th left to the knower

elab "register_the_bent_card" : command => do
  let hb ← Lean.Elab.Command.liftTermElabM do
    let stx ← `(Fact.SAME_DIFFERENCE.decTruth)
    let (_, hb) ← Lean.withHeartbeats do
      let e ← Lean.Elab.Term.elabTerm stx none
      let _ ← Lean.Meta.whnf e
      pure ()
    pure hb
  let seedId := Lean.mkIdent `the_bent_card
  let cmd ← `(def $seedId:ident : Nat := $(Lean.quote hb))
  Lean.Elab.Command.elabCommand cmd

register_the_bent_card     -- 1->3: the direct answer, receipts composed, no stations

/-%Y% /* the invariant: a computer program that prints the decimal representation of the jar */ %Y%-/
/- THE INVARIANT OF THE DEVICE, AS RULED: "the invariant is a computer program
that prints the decimal representation of the ratios of the elab costs of
(2->3 - 1->2) / 1->3 and 2->3 - (-next/1->3).  so, ask each and use this
formula.  this is the jar."  And: "use the EKG to COMPUTE the values and these
are the seed constants (top/bottom the_bent_card jar.a_pigeon, jar.that_box)
this may not be right, but i'm in the neighborhood."

The neighborhood, made a street address.  The registers above are cumulative
from-scratch costs, so the edges are differences: 1->2 is the bottom seed less
the floor, 2->3 is the top seed less the bottom.  Then

  jar_a_pigeon  = ((2->3) - (1->2)) / (1->3)
                = (top - 2*bottom + floor) / bent_card
                -- the second-difference stencil over the direct path:
                -- curvature per unit geodesic.  The carrier pigeon, carrying
                -- a clock, exactly as the GaugeProcess promised.

  jar_that_box  = (2->3) - (-next / (1->3))
                = ((top - bottom) * bent_card + next) / bent_card
                -- the second leg, corrected by one paper quantum per unit of
                -- direct path.  The box that may not be opened before its
                -- time.

`the_next` is not a physics constant: one paper work unit is 1000 internal
heartbeats, Lean's own gauge between user-facing maxHeartbeats and
`Lean.withHeartbeats` -- the same coefficient LeanCalibration cites.  These
two definitions are the operator's dial; when the neighborhood shifts, the
retune is these two lines and nothing else. -/
def the_next : Nat := 1000

def jar_a_pigeon : Int × Int :=
  ((the_top_of_the_jar : Int) - 2 * (the_bottom_of_the_jar : Int) + (Calibration.measuredFloor : Int),
   (the_bent_card : Int))

def jar_that_box : Int × Int :=
  (((the_top_of_the_jar : Int) - (the_bottom_of_the_jar : Int)) * (the_bent_card : Int) + (the_next : Int),
   (the_bent_card : Int))

/- The decimal representation, in the modulo realm: integer part by division,
fractional digits by remainder-times-ten, nothing floating anywhere.  The
panel prints; the grammar for math (see the rules section above) prints the
same number from the same seeds, independently, on the other compiler's
substrate.  Two printers, one jar. -/
def fracDigits : Nat → Nat → Nat → String
  | 0, _, _ => ""
  | k + 1, r, d => toString ((r * 10) / d) ++ fracDigits k ((r * 10) % d) d

def decimalOf (jar : Int × Int) (places : Nat) : String :=
  let (num, den) := jar
  if den = 0 then "the card has no face" else
  let sign := if num * den < 0 then "-" else ""
  let n := num.natAbs
  let d := den.natAbs
  s!"{sign}{n / d}.{fracDigits places (n % d) d}"

/-%Y% /* the front panel: two decimals, and the two lines to feed the grammar */ %Y%-/
#eval (decimalOf jar_a_pigeon 6, decimalOf jar_that_box 6)

-- The handshake with the polyglot: each line below is a sentence of the
-- finished grammar -- count to three, then the formula over the seeds.  Pipe
-- one line to the yacc build and the OTHER compiler prints the jar.
#eval s!"123({the_top_of_the_jar}-2*{the_bottom_of_the_jar}+{Calibration.measuredFloor})/{the_bent_card}"
#eval s!"123(({the_top_of_the_jar}-{the_bottom_of_the_jar})*{the_bent_card}+{the_next})/{the_bent_card}"

end Measurement
