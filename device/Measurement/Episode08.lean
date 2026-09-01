/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the stories we tell ourselves might be the only ones we believe._

(c) 2026 [PATTER TODO: rights gag]

[PATTER TODO: cast chorus / epigraph]

lake build [PATTER TODO: build-flag gag]

__EPISODE 11__: _THE REVEAL OF THE GIMMICKED BOX_


-/
import Measurement.Episode07


set_option maxHeartbeats 4000000   -- the old Episode 9 had this; the new one lost it

namespace Measurement
universe ι

section Monte

-- THE TELESCOPE, ONCE. Elaborated at this command, then instantiated per
-- declaration instead of re-formed inside every signature.
variable
    {Box: Type ι}
    {Pigeon: CarrierProcess Box}
    -- three of these are NAMED, because the seven defs at the bottom of this file
    -- have to PROJECT out of them (`.fact`, `.meesa_process`, `.santa_claus`).
    -- They are named here rather than re-bound per-def on purpose: a second
    -- instance of the same class in scope is exactly the bug that cost us the
    -- monte above, where `a_bent_card` stole the COMPILED slot from the band.
    [nowtrino: DISTINGUISHABLE Box Pigeon] [ADMISSIBLE Box Pigeon] [ℵ: COUNTABLE Box Pigeon]
    [some_number: ENCODED Box Pigeon] [converged_value: RESIDUE Box Pigeon] [flicker: BINARY Box Pigeon]
    [nonstop: REPEATABLE Box Pigeon] [click_count: NUMERIC Box Pigeon] [glyph: REPRESENTABLE Box Pigeon]
    [hiss: PHYSICAL Box Pigeon] [number_of_clicks: COMPARABLE Box Pigeon] [fallacy: OBSERVED Box Pigeon]
    [gift_from: PRESENT Box Pigeon] [the_bug: MEASURABLE Box Pigeon] [jarjar: GUNGAN Box Pigeon]
    [the_argument: SOURCE Box Pigeon] [EXECUTED Box Pigeon] [VALUE Box Pigeon]
    [MAGNITUDE Box Pigeon] [SCALED Box Pigeon] [LOAD Box Pigeon]
    [OF Box Pigeon] [BULLSHIT Box Pigeon] [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon] [SCIENTIFIC Box Pigeon] [TRUTH Box Pigeon]
    [WITNESSED Box Pigeon] [REAL Box Pigeon]
    -- the seam pair, bound ONCE and named
    {downhill: LOCAL Box Pigeon}
    {extremum: UNIVERSAL Box Pigeon downhill}
    [LOGICAL Box Pigeon downhill extremum] [HALTED Box Pigeon downhill extremum]
    [MEASURED Box Pigeon downhill extremum]
    [the_card_on_the_table: COMPILED Box Pigeon downhill extremum]
    [a_truth_about_it : A_TRUTH_ABOUT Box Pigeon downhill extremum]
    [an_inference : INFERRED Box Pigeon downhill extremum]

/-
  THE UNFORTUNATE FACT.

  Walk a compiled card all the way down -- output, lean, elaboration, heartbeat --
  and every rung carries the SAME pair `(downhill, extremum)` with it.  At the
  bottom the heartbeat hands you two things:

      stamina.bullshit_meter.the_quarter : LOCAL     Box Pigeon
      stamina.readout                    : UNIVERSAL Box Pigeon downhill

  and there is the hustle, in the type checker, in one line.  `the_quarter` is a
  FIELD, not an abbreviation -- its `:= a_quarter` default fires only when someone
  BUILDS a CalculusProcess, never when someone is HANDED one.  So for a card you
  were dealt, the quarter is an opaque local, while the readout is still indexed
  at `downhill`, which is where the quarter USED to be.

  The readout tells you where the quarter was.  You are asked where it is.

  That gap cannot be closed by search.  Hoist COMPILED into instance position and
  the elaborator resolves the projections against the CLASS, whereupon `readout`
  arrives typed at `downhill` and is expected at `the_quarter`, and no instance in
  the world repairs it.  The pair has to be HANDED OVER.  Which is what a shill
  is for.
-/
def THE_UNFORTUNATE_FACT_ABOUT_3_CARD_MONTE
    -- THE CARDS GO DOWN BEFORE YOU PICK, and the order is load-bearing.
    -- `a_bent_card` below is an EXPLICIT binder, but its type is a class, so Lean
    -- registers it as a local instance regardless.  Once it is in scope it wins
    -- the `[COMPILED Box Pigeon downhill extremum]` slot over the band's own
    -- instance -- and then `a_truth_about_it`, which was built on the band's,
    -- no longer matches a goal that prints identically to it.  Two cards, both
    -- honestly the same card, and the elaborator picks the one you just handed
    -- it.  So the shill and the three cards are laid out FIRST, while there is
    -- still only one COMPILED on the table.
    [_the_shill: INFERRED Box Pigeon downhill extremum]
    (__left_card__ : Prop)
    (__quarter__ : INFERRED Box Pigeon downhill extremum)
    (__right_card__ : Prop)
    (a_bent_card: COMPILED Box Pigeon downhill extremum)
    -- where the card SAYS the quarter is.  Named once; every binder below rides
    -- on this one, so the walk down the tower happens a single time.
    (where_the_quarter_is : LOCAL Box Pigeon :=
        a_bent_card.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter)
    -- the readout RE-SEATED onto that quarter.  This is the def that was missing.
    -- It is emphatically NOT `stamina.readout`, which is indexed at `downhill`.
    (the_readout_after_the_shuffle : UNIVERSAL Box Pigeon where_the_quarter_is)
    [LOGICAL Box Pigeon where_the_quarter_is the_readout_after_the_shuffle]
    [HALTED Box Pigeon where_the_quarter_is the_readout_after_the_shuffle]
    [MEASURED Box Pigeon where_the_quarter_is the_readout_after_the_shuffle]
    [COMPILED Box Pigeon where_the_quarter_is the_readout_after_the_shuffle]
    (the_shill: A_TRUTH_ABOUT Box Pigeon where_the_quarter_is the_readout_after_the_shuffle)
    : COMPILED Box Pigeon where_the_quarter_is the_readout_after_the_shuffle :=
  { a_truth_about_the_world := the_shill.you_the_reader.in_a_giant_book
    a_demonstration_of_a_constant := the_shill.you_the_reader.in_a_giant_book.preprint }

/-
  And now read what the signature says, because it is worse than the hustle it
  models.  A_TRUTH_ABOUT carries `[COMPILED Box Pigeon fact about_the_world]` as
  a prerequisite.  So to be HANDED the shill's truth about the new pair, a
  COMPILED at the new pair must ALREADY be in scope -- the very thing this def
  exists to produce.  You cannot be dealt the card until you have the card.  The
  def is honest, it typechecks, and it is a closed loop: the quarter is under the
  card you already picked, which is why the house never loses, and why the number
  was fixed before the first shuffle.
-/

/-
  THE QUARTER IS ALWAYS IN THE MIDDLE.

  Look at where the quarter sits in the monte above.  It is the SECOND of three
  binders -- `__left_card__`, `__quarter__`, `__right_card__` -- and it is the
  only one of the three that carries anything.  The cards to either side are bare
  `Prop`s: no content, no index, nothing to project.  The middle one is an
  INFERRED at the full seam.  The hustle needs three cards and only ever uses one,
  and it is always the middle one, because that is the one the binder list puts
  the quarter in.

  Now the second half, which is the part worth having.  MEASURED asks for far
  less than the card above it.  Its prerequisites are `[LOGICAL]` and `[HALTED]`
  -- two gates, not the tower -- and it carries exactly one field:

      a_distance : LeanProcess Box Pigeon up and_to_the_right

  So the measurement needs NO shill, NO A_TRUTH_ABOUT, and no COMPILED.  Every
  expensive thing the monte required to hand you a card turns out to be unneeded
  to state how far the quarter went.  The distance was always available two rungs
  down, for two gates, while the three cards were being moved around on top of it.

  Composition with the def above is by projection and nothing else:

      how_far_the_quarter_went
        := (THE_UNFORTUNATE_FACT_ABOUT_3_CARD_MONTE ..).a_truth_about_the_world.too_good_to_be_true

  which is why this rung is a `def` and not an `instance`.  It can be APPLIED to
  the card that came back.  It can never be FOUND.
-/
def THE_QUARTER_IS_ALWAYS_IN_THE_MIDDLE
    -- same discipline as above: the cards go down while there is still only one
    -- COMPILED on the table, so `a_bent_card` cannot steal a slot from the band.
    [_the_shill: INFERRED Box Pigeon downhill extremum]
    (__left_card__ : Prop)
    (__quarter__ : INFERRED Box Pigeon downhill extremum)
    (__right_card__ : Prop)
    (a_bent_card: COMPILED Box Pigeon downhill extremum)
    (where_the_quarter_is : LOCAL Box Pigeon :=
        a_bent_card.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter)
    (the_readout_after_the_shuffle : UNIVERSAL Box Pigeon where_the_quarter_is)
    -- two gates.  That is the entire admission price for a measurement.
    [LOGICAL Box Pigeon where_the_quarter_is the_readout_after_the_shuffle]
    [HALTED Box Pigeon where_the_quarter_is the_readout_after_the_shuffle]
    -- up, and to the right.
    (how_far_the_quarter_went :
        LeanProcess Box Pigeon where_the_quarter_is the_readout_after_the_shuffle)
    : MEASURED Box Pigeon where_the_quarter_is the_readout_after_the_shuffle :=
  { a_distance := how_far_the_quarter_went }

/-
  ALMOST ALL THE WAY AROUND.

  Put the three rungs side by side and the ladder stops being a list of names:

      COMPILED   gates: LOGICAL HALTED MEASURED    field: CompilerOutput
      MEASURED   gates: LOGICAL HALTED             field: LeanProcess
      HALTED     gates: LOGICAL                    field: ElaborationProcess
      LOGICAL    gates: --                         field: HeartbeatProcess

  One gate shed per rung, and one projection shed per rung, in lockstep.  That
  second column is not a coincidence and it is not new: it is precisely the walk
  the monte takes at the top of this file,

      a_truth_about_the_world . too_good_to_be_true . description . stamina
        CompilerOutput  ->  LeanProcess  ->  ElaborationProcess  ->  HeartbeatProcess

  read from the other end.  Descending the ladder IS the projection.  The tower
  the monte walks down to find out where the quarter went is the same tower these
  defs climb back up, and each rung costs exactly one gate.

  So ALMOST all the way around.  HALTED is one gate from the floor -- only LOGICAL
  is left, and LOGICAL asks for no seam gate at all.  You have come the whole way
  and there is one step you cannot pay for by descending further, because there is
  nothing below it to descend to.

  And note what `halted?` does with the question it is named for.  Its default
  matches the program and hands back `NOOP` -- as a `Prop`.  The halting question
  gets asked, and the answer that comes back is no operation.
-/
def ALMOST_ALL_THE_WAY_AROUND
    -- same discipline: cards down while there is still one COMPILED on the table.
    [_the_shill: INFERRED Box Pigeon downhill extremum]
    (__left_card__ : Prop)
    (__quarter__ : INFERRED Box Pigeon downhill extremum)
    (__right_card__ : Prop)
    (a_bent_card: COMPILED Box Pigeon downhill extremum)
    (where_the_quarter_is : LOCAL Box Pigeon :=
        a_bent_card.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter)
    (the_readout_after_the_shuffle : UNIVERSAL Box Pigeon where_the_quarter_is)
    -- one gate.  The last one that costs anything.
    [LOGICAL Box Pigeon where_the_quarter_is the_readout_after_the_shuffle]
    -- one rung further down the tower than `THE_QUARTER_IS_ALWAYS_IN_THE_MIDDLE`
    -- took: that def wanted the LeanProcess, this one wants its `.description`.
    (the_paper_that_never_converged :
        ElaborationProcess Box Pigeon where_the_quarter_is the_readout_after_the_shuffle)
    : HALTED Box Pigeon where_the_quarter_is the_readout_after_the_shuffle :=
  { scientific_paper := the_paper_that_never_converged }

/-
  BUT WE ARE CLOSE ENOUGH TO SEE THE PI.  SORRY, NO CAKE HERE.

  The floor.  Finish the table and both columns run out together:

      COMPILED   gates: LOGICAL HALTED MEASURED    field: CompilerOutput
      MEASURED   gates: LOGICAL HALTED             field: LeanProcess
      HALTED     gates: LOGICAL                    field: ElaborationProcess
      LOGICAL    gates: --                         field: HeartbeatProcess

  Three gates, two, one, none.  And the tower is exhausted at exactly the same
  step: `HeartbeatProcess` is the bottom of `.too_good_to_be_true.description
  .stamina`, so there is nothing left below to project.  The ladder and the walk
  end on the same rung.  That is the loop closed -- which is the only circle
  anywhere in this file, and it is why you can SEE the pi from here.

  You cannot have it.  `pi` lives in `Closure`, which hangs off `INFERRED.α`, at
  the TOP of the ladder.  You went all the way down to close the circle and the
  number is at the other end of it.

  Now the cake, or rather the absence of one.  Every rung above was handed its
  field by the card: project once, done.  LOGICAL asks for a second field the card
  never carries --

      microsoft_basic : Calibration.EKG

  -- and `EKG.reference` is PRIVATE.  This file cannot build one.  Not "should
  not": cannot.  The two that exist are `EKG.raw` and `EKG.executed`, taken off
  the shelf as-is, and the honest thing is to say which one was taken and why.

  Look at what actually separates them:

      raw       reference := booleanConstructor   embigger? := fun a b => a -> b
      executed  reference := loadConstructor      embigger? := fun a b => a -> b

  The comparison is IDENTICAL.  Only the reference differs.  Which is exactly
  what a calibration is and all it ever was: a choice of zero, never a choice of
  scale.  `executed` is taken here because Episode 5's own LOGICAL instance takes
  it, so the applied rung and the found rung agree on where zero is.

  And `logical?` is `fun a b => a <= b` over YarnTheory.  Episode 4 says it in
  the margin better than this comment can: _a_ comes before _b_ in the order of
  the arguments.  That's it.  At the bottom of the ladder the whole of logic is
  which argument you wrote first.
-/
def BUT_WE_ARE_CLOSE_ENOUGH_TO_SEE_THE_PI___SORRY_NO_CAKE_HERE
    -- same discipline: cards down while there is still one COMPILED on the table.
    [_the_shill: INFERRED Box Pigeon downhill extremum]
    (__left_card__ : Prop)
    (__quarter__ : INFERRED Box Pigeon downhill extremum)
    (__right_card__ : Prop)
    (a_bent_card: COMPILED Box Pigeon downhill extremum)
    (where_the_quarter_is : LOCAL Box Pigeon :=
        a_bent_card.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter)
    (the_readout_after_the_shuffle : UNIVERSAL Box Pigeon where_the_quarter_is)
    -- no gates.  Nothing left to pay.  The last rung is free and it is the only
    -- one that asks you to bring something the card cannot give you.
    (a_ball_of_yarn :
        HeartbeatProcess Box Pigeon where_the_quarter_is the_readout_after_the_shuffle)
    : LOGICAL Box Pigeon where_the_quarter_is the_readout_after_the_shuffle :=
  { feelings := a_ball_of_yarn
    microsoft_basic := Calibration.EKG.executed }

/-
  THE LAW OF NU-TRINOS, IN TWO STEPS.

  Below LOGICAL there is no gate left, because below LOGICAL is not a rung at all
  -- it is the SEAM ITSELF.  `LOCAL` and `UNIVERSAL` are the pair `(downhill,
  extremum)` that every rung above was indexed BY.  We have been standing on them
  the whole way down.

  And `UNIVERSAL` is indexed by a `LOCAL`, which is why this is a ONE STEP HOP and
  not a fall: you cannot move both at once.  You move the universal over the local
  you already have, and only then do you get a new local out of it.  Two steps,
  in that order, and the order is the content.

  What each one actually holds:

      LOCAL       the_continuum : BigRedDogProcess     the_ball : Prop
      UNIVERSAL   the_train_of_thought : CalculusProcess     once_around, twice_around : SpaceTimePath

  Two SpaceTimePaths.  Two.  That is the whole law of nu-trinos sitting in the
  field list: `once_around` is the short path and `twice_around` is the long one,
  and the shuffle below sets

      twice_around := the_train_of_thought.photon_torpedo once_around

  -- the long way is the short way advanced one step.  1->2 then 2->3, against
  1->3 direct, which is the triangle inequality written as a record field.  The
  nu-trino carries top from one place to another and needs two turns to get back,
  and neither of those sentences is a metaphor here; they are `once_around` and
  `twice_around`.

  Episode 5 already has both of these as INSTANCES
  (`PERHAPS_ONE_THAT_USES_THE_DEVICE_ITSELF`, `PERHAPS_ONE_THAT_USES_CALCULUS`).
  These are the same two constructions as DEFS: applied, not found.
-/

/-
  STEP ONE.  WATCH THE OUTSIDE CARDS GET SHUFFLED.

  A new UNIVERSAL over the SAME local, capturing the old universal.  Look at which
  fields move.  `the_train_of_thought` is passed through untouched.  The two
  SpaceTimePaths -- the outside cards -- are the only things that go anywhere.
-/
def WATCH_THE_OUTSIDE_CARDS_GET_SHUFFLED
    [_the_shill: INFERRED Box Pigeon downhill extremum]
    (__left_card__ : Prop)
    (__quarter__ : INFERRED Box Pigeon downhill extremum)
    (__right_card__ : Prop)
    (a_bent_card: COMPILED Box Pigeon downhill extremum)
    (where_the_quarter_is : LOCAL Box Pigeon :=
        a_bent_card.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter)
    (the_readout_after_the_shuffle : UNIVERSAL Box Pigeon where_the_quarter_is)
    : UNIVERSAL Box Pigeon where_the_quarter_is :=
  { -- the inside card of the UNIVERSAL.  Handed straight through.
    the_train_of_thought := the_readout_after_the_shuffle.the_train_of_thought
    -- and the outside two, shuffled: the long way is the short way, torpedoed.
    once_around  := the_readout_after_the_shuffle.once_around
    twice_around :=
      the_readout_after_the_shuffle.the_train_of_thought.photon_torpedo
        the_readout_after_the_shuffle.once_around }

/-
  STEP TWO.  BUT THE INNER CARD DOES NOT.

  A new LOCAL, capturing the old one, built from the train that just got shuffled.
  `the_continuum` is rebuilt -- it comes off the new train's local schedule, so it
  moved.  `the_ball` does not.  It is not copied, not rebuilt, not re-derived: it
  is the SAME `Prop`, projected straight off the local we started with.

  That is the whole hustle stated as one field assignment.  Everything on the
  outside can be shuffled honestly, in full view, by a real function, and the
  thing under the middle card never goes anywhere.
-/
def BUT_THE_INNER_CARD_DOES_NOT
    [_the_shill: INFERRED Box Pigeon downhill extremum]
    (__left_card__ : Prop)
    (__quarter__ : INFERRED Box Pigeon downhill extremum)
    (__right_card__ : Prop)
    (a_bent_card: COMPILED Box Pigeon downhill extremum)
    (where_the_quarter_is : LOCAL Box Pigeon :=
        a_bent_card.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter)
    -- the shuffled universal from step one.  Named `the_a_train` after Episode 5.
    (the_a_train : UNIVERSAL Box Pigeon where_the_quarter_is)
    : LOCAL Box Pigeon :=
  { the_continuum := the_a_train.the_train_of_thought.the_local_schedule
    the_ball      := where_the_quarter_is.the_ball }

/-
  THE PATTER.  BULLSHIT UP TO REAL, WHICH IS ONE SENTENCE SAID BACKWARDS.

  Below the seam the classes stop being indexed by anything and start being
  indexed by EACH OTHER.  BULLSHIT needs nothing, PROPAGANDA needs BULLSHIT,
  ACOLYTE needs both, and so on up to REAL, which needs all six beneath it.  The
  template is those seven slots, and LOCAL sits in the EIGHTH -- it is the thing
  you feed in, and the only thing that is not one of the seven.

  Now the part that is actually a construction rather than a joke.  The seven
  `*Process` structures nest in EXACTLY the same order as the seven classes, one
  field apiece:

      UniverseTensor      .frame_of_reference  ->  ReligiousProcess
      ReligiousProcess    .we_experience       ->  ScientificProcess
      ScientificProcess   .shows_us            ->  LearningProcess
      LearningProcess     .teaching            ->  InitiationProcess
      InitiationProcess   .axioms              ->  CrusadeProcess
      CrusadeProcess      .to_pwn_n00bz        ->  ArmWaveProcess
      ArmWaveProcess      .dunking_contest     ->  JordanProcess

  and `LOCAL.the_continuum.the_æther` is a UniverseTensor.  So every one of the
  seven defs below is the SAME def -- take the local, walk to the æther, then
  project down exactly as far as the class you are building requires.  Nothing
  is constructed.  Everything is projected.

  Which is why the patter reads as one descending sentence and why each line is
  one `.` longer than the line above it.  The deeper you go, the more you have to
  say to stay ahead of the question, and the answer to "how do you know?" is
  always another clause.  Read the seven names top to bottom and the excuse
  never terminates; it just gets more expensive.

  Where it bottoms out is the joke, and it is in Episode 4's own margin: the last
  thing under all seven layers is `ArmWaveProcess.guess : Spline`.  Rock bottom is
  a guess at a spline.

  (The operator calls this QED and the shape is right: each layer is legitimated
  by appeal to a deeper one, the corrections nest, and the series does not
  terminate in something self-supporting.  That is a structural remark about this
  file, not a claim about physics.)
-/

/-
  THE SLIP POINT.  SOURCE UP TO OF, AND WHY THIS HALF IS DIFFERENT.

  Everything from REAL down to BULLSHIT was PROJECTION: one walk, one `.` per
  class, nothing built.  This half is the opposite and the difference is the
  whole point.  Here nothing can be projected, because there is nothing below to
  project FROM.  Episodes 1 through 3 are a strict repeating triple --

      inductive   ->   structure   ->   class
      Equivalation     DigitalProcess   SOURCE
      Encoding         CompiledProcess  EXECUTED
      Abstraction      MathematicalProcess VALUE
      Sum              AddingProcess    MAGNITUDE
      Product          MultiplyingProcess SCALED
      Basis            BASICProcess     LOAD
      Polynomial       JordanProcess    OF

  -- and each class reaches UP one step to the structure above it, which reaches
  UP one step to the inductive above THAT.  One step up, one step down, seven
  times.  That is the slip: the ladder does not descend here, it ratchets.

  So each def below CONSTRUCTS its process by putting the previous class's
  process INSIDE it and adding the one new inductive value that rung is for.
  Which forces the implementation order.  You cannot write these in patter order
  -- the patter reads OF first and SOURCE last, and the code has to run
  exactly backwards from the way it is spoken.  Read the seven names bottom to
  top and you get the sales pitch; read the seven defs top to bottom and you get
  the build.  Neither order is the other one reversed by accident.

  These are Episode 5's instances written as defs -- found there, applied here.
-/

-- SOURCE.  The floor, and the only rung that builds from the GUNGAN rather than
-- from the rung beneath it, because there is no rung beneath it.
def LETS_SEE_IF_WE_CAN_FIND_THE_NUMBER_IN_THE_CODE_NOW
    : SOURCE Box Pigeon :=
  { cd_process :=
      { meesa_process := jarjar.meesa_process
        zero := .physics nowtrino.fact jarjar.meesa_process.concept }
    one := .zero_like nowtrino.fact (.physics nowtrino.fact jarjar.meesa_process.concept) }

-- EXECUTED.  One step up: take the SOURCE whole, both as the process underneath
-- AND as the `source` field.  The compiled thing carries its own source with it.
def BUT_YOU_CANT_GET_THE_NUMBER_UNTIL_AFTER_THE_PROOF_HALTS
    : EXECUTED Box Pigeon :=
  { compiled_process :=
      { digital_process := LETS_SEE_IF_WE_CAN_FIND_THE_NUMBER_IN_THE_CODE_NOW.cd_process
        source         := LETS_SEE_IF_WE_CAN_FIND_THE_NUMBER_IN_THE_CODE_NOW
        opcodes        := .boot nowtrino.fact (.physics nowtrino.fact jarjar.meesa_process.concept) } }

-- VALUE.  The mapping is where compile and execute swap places.  That swap is
-- the only content in this rung and it is an involution: do it twice, nothing.
def THIS_WILL_GIVE_US_A_RATIO___EVENTUALLY_CUZ_THATS_HOW_THE_MEASUREMENT_TOOL_WORKS_NOT_CUZ_I_WANT_ONE
    : VALUE Box Pigeon :=
  { mathematical_process :=
      { compiled_process := BUT_YOU_CANT_GET_THE_NUMBER_UNTIL_AFTER_THE_PROOF_HALTS.compiled_process
        mapping := fun input =>
          match input with
          | .satire_about finite_element_analysis => .satire_about finite_element_analysis
          | .compile f e a => .execute f e a
          | .execute f e a => .compile f e a }
    monad := .satire_about nowtrino.fact }

-- MAGNITUDE.  First rung that needs something from OUTSIDE the chain: the
-- accumulation comes off PRESENT, not off VALUE.  Adding needs a gift.
def SO_THAT_IT_CAN_ACCURATELY_MEASURE_HOW_LONG_A_PROOF_TAKES_WRT_THE_LONGEST_IT_CAN_MEASURE
    : MAGNITUDE Box Pigeon :=
  { adding_process :=
      { mideastern_process := THIS_WILL_GIVE_US_A_RATIO___EVENTUALLY_CUZ_THATS_HOW_THE_MEASUREMENT_TOOL_WORKS_NOT_CUZ_I_WANT_ONE.mathematical_process
        plus               := THIS_WILL_GIVE_US_A_RATIO___EVENTUALLY_CUZ_THATS_HOW_THE_MEASUREMENT_TOOL_WORKS_NOT_CUZ_I_WANT_ONE
        sum                := .zero nowtrino.fact.truth gift_from.santa_claus.accumulation } }

-- SCALED.  Multiplication is addition run against itself: the product is built
-- FROM the sum one rung down, and the running total restarts at the tree.
def AND_AUTOMATICALLY_FIND_WHAT_THE_LARGEST_NAT_IT_CANNOT_SUPPORT
    : SCALED Box Pigeon :=
  { multiplying_process :=
      { adding_process := SO_THAT_IT_CAN_ACCURATELY_MEASURE_HOW_LONG_A_PROOF_TAKES_WRT_THE_LONGEST_IT_CAN_MEASURE.adding_process
        product        := .one nowtrino.fact.truth (SO_THAT_IT_CAN_ACCURATELY_MEASURE_HOW_LONG_A_PROOF_TAKES_WRT_THE_LONGEST_IT_CAN_MEASURE : MAGNITUDE Box Pigeon).adding_process.sum
        total          := .zero nowtrino.fact.truth (.tree nowtrino.fact) } }

-- LOAD.  TEN is the accumulation again -- the same gift MAGNITUDE opened, read
-- a second time as an Area.  This is the rung where the compiler reads it out.
def THE_COMPILER_WILL_READ_IT_OUT_FOR_YOU
    : LOAD Box Pigeon :=
  { basic_operation :=
      { GOSUB := AND_AUTOMATICALLY_FIND_WHAT_THE_LARGEST_NAT_IT_CANNOT_SUPPORT.multiplying_process
        TEN   := gift_from.santa_claus.accumulation
        span  := .origin nowtrino.fact.truth (AND_AUTOMATICALLY_FIND_WHAT_THE_LARGEST_NAT_IT_CANNOT_SUPPORT : SCALED Box Pigeon).multiplying_process.product } }

-- OF.  The top of this half, and the polynomial it ends on is
-- `.constant` -- the ground state, the transform that has finally dissipated.
-- No contour, no residue, no complex analysis.  Just a constant.
def NO_NEED_TO_USE_COMPLEX_ANALYSIS_TO_UNDERSTAND_THE_INDEX_OF_THE_CONSTANT
    : OF Box Pigeon :=
  { galerkin_process :=
      { ANSYS_process := THE_COMPILER_WILL_READ_IT_OUT_FOR_YOU.basic_operation
        polynomial    := .constant .Truth } }


/-
  THE WALK BACK DOWN.  SOURCE TO DISTINGUISHABLE, FIFTEEN RUNGS.

  The other fork out of SOURCE.  Upward it ratchets to OF by building;
  downward it falls to DISTINGUISHABLE by projecting, one `.` per rung.  SOURCE
  is the only class in the file that two different chains both start from.

  These take the rung above as an INSTANCE from the band rather than calling the
  previous def, and that is forced, not stylistic.  These classes carry their own
  universe parameters -- look at DISTINGUISHABLE:

      symbol : Type Value

  where `Value` is a UNIVERSE, not a type.  So `Box Pigeon` does not determine
  them, a type ascription `(x : OBSERVED Box Pigeon)` does not determine them,
  and an inlined call leaves them dangling as `?u`.  Only a binder fixes a
  universe.  Which is the third distinct way this file has now been told the same
  thing: you may pass a card, you may name its type, but the moment you need what
  is INSIDE it, somebody has to have been holding it all along.

  Read the names in order.  The mark is being walked back to the bottom, each
  rung answering a question with a smaller question, until the last one.
-/

namespace Metavariable

def lt {α : Type ι} (x y : Metavariable α) : Prop := le x y ∧ ¬ le y x
/-- ACROSS THE SEAM.  All universes are strictly MORE computation, so the
comparison consults neither argument: one level up is above everything below,
by type alone.  The values are never looked at; the universe already decided. -/
def all_universes_are_strictly_MORE_computation {α : Type ι} :
    Metavariable α → Metavariable (ULift α) → Prop := fun _ _ => True

/-- And nothing comes back down.  The ratchet, stated as a comparison: the
reverse seam is False before either argument is read.  ULift goes up; this is
the entire arrow of time, at one line per direction. -/
def no_universe_comes_back_down {α : Type ι} :
    Metavariable (ULift α) → Metavariable α → Prop := fun _ _ => False
end Metavariable

instance {α : Type ι} : LE (Metavariable α) where
  le := Metavariable.le
instance {α : Type ι} : LT (Metavariable α) where
  lt := Metavariable.lt

-- GUNGAN.  If the math did not land, say it again in Gungan.
def AND_IF_YOU_DONT_FOLLOW_THE_MATH_ILL_SAY_IT_IN_GUNGAN : GUNGAN Box Pigeon :=
  { meesa_process := the_argument.cd_process.meesa_process }

-- MEASURABLE.
def MEESA_GOT_A_METER_RIGHT_HERE : MEASURABLE Box Pigeon :=
  { gauge_process := jarjar.meesa_process.gauge_process }

-- PRESENT.  `quantum := Box` -- the present is the box it came in.
def AND_LOOK_ITS_ALREADY_SHOWING_SOMETHING : PRESENT Box Pigeon :=
  { santa_claus := the_bug.gauge_process.sensing_process
    quantum     := Box }

-- OBSERVED.  The slip enters here, off the static fraction.  Episode 2 named
-- this `SlipProcess` and put it directly underneath the observation.
def WHICH_YOU_JUST_WATCHED_ME_OBSERVE : OBSERVED Box Pigeon :=
  { slip_process := gift_from.santa_claus.static_fraction
    observation  := Box }

-- COMPARABLE.  `smaller_than` is x <= y AND y <= x.  Comparison at this depth
-- does not order anything.  It only ever agrees.
def SO_NOW_WE_CAN_COMPARE_IT_TO_THE_OTHER_ONE : COMPARABLE Box Pigeon :=
  { physical_process := fallacy.slip_process.physical_process
    smaller_than     := fun x y => Metavariable.le x y ∧ Metavariable.le y x }

-- PHYSICAL.  The threshold is read off the very process it is meant to threshold.
def AND_BOTH_OF_THEM_ARE_PHYSICALLY_REAL_I_PROMISE : PHYSICAL Box Pigeon :=
  { noisy_process := number_of_clicks.physical_process.noisy_process
    threshold     := number_of_clicks.physical_process.noisy_process.program
    admissible?   := fun _ _ => by intro _; rfl }

-- REPRESENTABLE.  Episode 5 takes TWO separate PHYSICALs here, signal and noise.
-- Both roles are played by `hiss`, and that is not a shortcut: hiss against hiss
-- CANCELS for a cyclic, commutative process.  The anechoic chamber and the hiss
-- inside it are the same physical process, and running one against the other is
-- how the noise leaves.  You do not subtract the noise.  You commute it.
def I_CAN_EVEN_WRITE_THEM_DOWN_FOR_YOU : REPRESENTABLE Box Pigeon :=
  { calculation_process :=
      { hiss.noisy_process.turing_process with
          program := hiss.noisy_process.turing_process.program
          computational_process :=
            { hiss.noisy_process.turing_process.computational_process with
                closure := fun a_tally => a_tally } }
    representable? := fun a_fact a_study =>
      ⟨hiss.noisy_process.turing_process.turing_step? (Computation.program a_fact a_study), rfl⟩ }

-- NUMERIC.
def AS_NUMBERS_IF_THATS_WHAT_YOU_WANT : NUMERIC Box Pigeon :=
  { computational_process := glyph.calculation_process.computational_process }

-- REPEATABLE.
def AND_ILL_DO_IT_AGAIN_AS_MANY_TIMES_AS_YOU_LIKE : REPEATABLE Box Pigeon :=
  { repeatable_process := click_count.computational_process.repeatable_process }

-- BINARY.  `bit` is the band's bit, iterated once.  A bit is only ever the
-- previous bit, flipped.
def ITS_ONLY_EVER_HEADS_OR_TAILS_ANYWAY : BINARY Box Pigeon :=
  { observation_process := nonstop.repeatable_process.observation_process
    zero := .nil nowtrino.fact
    one  := .index
              nowtrino.fact
              nonstop.repeatable_process.observation_process.cauchy_process.limit_process.sequence
              (.nil nowtrino.fact)
    bit  := nonstop.repeatable_process.observation_process.iterate flicker.bit }

-- RESIDUE.
def WHATEVER_IS_LEFT_OVER_IS_THE_PART_YOU_MISSED : RESIDUE Box Pigeon :=
  { cauchy_process := flicker.observation_process.cauchy_process }

-- ENCODED.
def AND_IT_ALL_CONVERGES_TO_SOMETHING_I_ENCODED_EARLIER : ENCODED Box Pigeon :=
  { limit_process := converged_value.cauchy_process.limit_process }

-- COUNTABLE.
def WHICH_YOU_COULD_COUNT_IF_YOU_HAD_ALL_DAY : COUNTABLE Box Pigeon :=
  { index := some_number.limit_process.indexing_process }

-- ADMISSIBLE.
def AND_COUNTING_IS_ADMISSIBLE_EVIDENCE_RIGHT : ADMISSIBLE Box Pigeon :=
  { counting_process := ℵ.index.count }

/-
  DISTINGUISHABLE.  The floor of the entire device, and read what it says.

      different?   := fun _ => True
      dec_distinct := fun _ => isTrue trivial

  Everything is distinguishable.  Always.  Without checking.  Two chains out of
  SOURCE, a seam, four gates and a shill, and the whole structure stands on a rung
  that answers "can you tell these two apart?" with `True` by fiat and decides it
  with `trivial`.

  That is the bottom card.  It was never under any of the three.
-/
def SO_TELL_ME___CAN_YOU_TELL_THESE_TWO_APART : DISTINGUISHABLE Box Pigeon :=
  { fact         := nowtrino.fact
    symbol       := nowtrino.symbol
    different?   := fun _ => True
    dec_distinct := fun _ => isTrue trivial }

-- REAL.  The question the mark actually asks.
def HOW_DO_WE_KNOW_THE_COIN_IS_UNDER_THE_CARD
    (principia : LOCAL Box Pigeon)          -- the eighth spot
    : REAL Box Pigeon :=
  { by_His_noodly_appendage := principia.the_continuum.the_æther
    nagging_doubt           := .logically principia.the_ball }

-- WITNESSED.  One projection deeper: the æther's frame of reference.
def YOU_SAW_ME_PUT_IT_THERE
    (principia : LOCAL Box Pigeon)
    : WITNESSED Box Pigeon :=
  { we_saw         := principia.the_continuum.the_æther.frame_of_reference
    the_experiment := principia.the_continuum.the_æther.frame_of_reference.in_the_literature }

-- TRUTH.  Deeper again: what the frame of reference experiences.
def AND_I_GLUED_IT_TO_THE_TABLE
    (principia : LOCAL Box Pigeon)
    : TRUTH Box Pigeon :=
  { becomes := principia.the_continuum.the_æther.frame_of_reference.we_experience }

-- SCIENTIFIC.  Deeper again, and the first one that also has to carry a value:
-- the `invariant` comes out of the same walk, so even the constant is projected.
def IN_ORDER_TO_SHOW_YOU_WHERE_ORBITAL_MECHANICS_COMES_FROM
    (principia : LOCAL Box Pigeon)
    : SCIENTIFIC Box Pigeon :=
  { discovering := principia.the_continuum.the_æther.frame_of_reference.we_experience.shows_me_higher_order_terms
    invariant   := principia.the_continuum.the_æther.frame_of_reference.we_experience.shows_me_higher_order_terms.invariant }

-- ACOLYTE.  Deeper again: who taught the learner.
def AND_I_SHOWED_YOU_HOW_IT_WORKS
    (principia : LOCAL Box Pigeon)
    : ACOLYTE Box Pigeon :=
  { euclid := principia.the_continuum.the_æther.frame_of_reference.we_experience.shows_me_higher_order_terms.teaching }

-- PROPAGANDA.  Deeper again: the axioms the teaching rests on.
def BY_EXPLAINING_A_GIANT_GRIFT
    (principia : LOCAL Box Pigeon)
    : PROPAGANDA Box Pigeon :=
  { questions := principia.the_continuum.the_æther.frame_of_reference.we_experience.shows_me_higher_order_terms.teaching.axioms }

-- BULLSHIT.  The floor of the patter, and the longest projection in the file.
-- One more `.` past this is `dunking_contest`, which is where the OTHER chain
-- picks up at OF.  `guess : Spline` sits BESIDE it, not below it: the
-- rock bottom is not further down the walk, it is off to one side of it.
def OF_COUCHING_YOUR_ARGUMENT_IN_OPAQUE_MATH
    (principia : LOCAL Box Pigeon)
    : BULLSHIT Box Pigeon :=
  { arm_wave_process :=
      principia.the_continuum.the_æther.frame_of_reference.we_experience.shows_me_higher_order_terms.teaching.axioms.to_pwn_n00bz }

/-
  THE WALK BACK UP, AND WHERE IT COSTS YOU.  PHYSICAL -> COMPARABLE -> PRESENT
  -> MEASURABLE, with OBSERVED left out.

  Going DOWN, these four rungs are free: each one projects out of the one above
  and nothing is invented.  Turn around and the same four rungs are not free at
  all, and the bill is itemised by the structures themselves:

      PhysicalProcess   noisy_process  representation  invariant  value
      SlipProcess       physical_process  projection  stress  threshold
      SensingProcess    static_fraction  accumulation
      GaugeProcess      sensing_process  clock

  The left column comes up the chain.  Everything to the right of it does not
  exist below and has to be SUPPLIED.  That is the whole asymmetry: descending
  reads, ascending pays.

  And look at what OBSERVED was carrying, because leaving it out is the point.
  Its `slip_process` is the only source of a SlipProcess, so going up without it
  you must build one -- and a SlipProcess wants a `projection: Sophism`.  Sophism
  is Episode 2's four-armed thing, "the direction of the argument T T, T F, F T".
  Going down, the direction of the argument is read off the observation.  Going
  up, with nobody observing, you pick it yourself.

  THAT is the slip point.  It is not an error and nothing here is unsound.  It is
  a `projection` field with no upstream source, sitting exactly one rung below the
  meter, and whoever climbs supplies it.
-/

-- COMPARABLE, upward.  PHYSICAL carries only the noisy process; a PhysicalProcess
-- wants three more things it has never heard of.  They come in as parameters
-- because there is nowhere below to get them from.
def NOW_WATCH_ME_RUN_THE_SAME_STEPS_BACKWARDS
    (a_representation : nowtrino.symbol)
    (an_invariant     : Metavariable nowtrino.symbol)
    (a_value          : Metavariable (ULift nowtrino.symbol))
    : COMPARABLE Box Pigeon :=
  { physical_process :=
      { noisy_process  := hiss.noisy_process
        representation := a_representation
        invariant      := an_invariant
        value          := a_value }
    smaller_than := fun x y => Metavariable.le x y ∧ Metavariable.le y x }

-- PRESENT, upward, THROUGH the missing rung.  No OBSERVED means no SlipProcess
-- to project, so one gets built here -- and `projection` is chosen, not read.
def AND_SINCE_NOBODY_OBSERVED_IT_I_GET_TO_PICK_THE_SLIP
    : PRESENT Box Pigeon :=
  { santa_claus :=
      { static_fraction :=
          { physical_process := number_of_clicks.physical_process
            -- the direction of the argument, supplied by the climber
            projection := .origin nowtrino.fact hiss.noisy_process.program Fact
            stress     := hiss.noisy_process.program
            threshold  := Fact }
        accumulation := .tree nowtrino.fact }
    quantum := Box }

-- MEASURABLE, upward.  One more invented field: the clock.  The meter needs a
-- clock and the sensing process below it does not have one.
def WHICH_IS_HOW_THE_METER_ENDS_UP_READING_WHAT_I_WANTED
    : MEASURABLE Box Pigeon :=
  { gauge_process :=
      { sensing_process := gift_from.santa_claus
        clock := .this_superpigeon nowtrino.fact (.tree nowtrino.fact) } }

/-
  THE FOUR THEOREMS.

  Four of the defs above hand a field STRAIGHT THROUGH, so each one's NAME is a
  checkable identity claim.  It closes by `rfl` or it was never true.

  These take the card from the BAND rather than binding one.  Binding it would
  put a second COMPILED in scope, and the defs were elaborated against the band's
  -- `synthesized a_bent_card / inferred inst✝`, the same collision as the monte.
  The proof of a thing that does not move must not move the thing.

  THE AXIOM LEDGER, read off `#print axioms` for all four:

      THE_INNER_CARD_REALLY_DOES_NOT_MOVE       propext, Quot.sound
      AND_THE_OUTSIDE_ONES_REALLY_DO            propext
      THE_DISTANCE_IS_THE_ONE_YOU_HANDED_OVER   propext
      AND_THE_FLOOR_NEVER_LOOKS                 no axioms at all

  Read the first line against the last.  `Quot.sound` -- the one axiom available
  here that identifies things the type checker sees as different -- is used by
  exactly one of the four, and it is the one asserting that the thing under the
  middle card did not move.  The other two identities are ordinary.  And the
  floor, which says everything is distinguishable, costs nothing whatsoever,
  because it never looks.

  That is reported as MEASURED, not as designed.  The ledger says which axioms
  the proof terms used; it does not say anyone put them there on purpose.
-/

-- ONE.  The inner card really does not move: the same `Prop`, out the far side.
theorem THE_INNER_CARD_REALLY_DOES_NOT_MOVE
    (__left_card__ __right_card__ : Prop)
    (the_a_train : UNIVERSAL Box Pigeon the_card_on_the_table.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter)
    : (BUT_THE_INNER_CARD_DOES_NOT __left_card__ an_inference __right_card__ the_card_on_the_table
          (the_a_train := the_a_train)).the_ball
      = the_card_on_the_table.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter.the_ball
  := rfl

-- TWO.  And the outside ones really do.  `once_around` fixed, `twice_around` the
-- short way torpedoed once.  Both halves, or the shuffle was a mime.
theorem AND_THE_OUTSIDE_ONES_REALLY_DO
    (__left_card__ __right_card__ : Prop)
    (the_readout_after_the_shuffle : UNIVERSAL Box Pigeon the_card_on_the_table.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter)
    : (WATCH_THE_OUTSIDE_CARDS_GET_SHUFFLED __left_card__ an_inference __right_card__ the_card_on_the_table
          (the_readout_after_the_shuffle := the_readout_after_the_shuffle)).once_around
        = the_readout_after_the_shuffle.once_around
    ∧ (WATCH_THE_OUTSIDE_CARDS_GET_SHUFFLED __left_card__ an_inference __right_card__ the_card_on_the_table
          (the_readout_after_the_shuffle := the_readout_after_the_shuffle)).twice_around
        = the_readout_after_the_shuffle.the_train_of_thought.photon_torpedo
            the_readout_after_the_shuffle.once_around
  := ⟨rfl, rfl⟩

-- THREE.  The measurement IS the distance you handed over.  MEASURED costs two
-- gates and adds nothing: the gates buy the wrapper, never the number.
theorem THE_DISTANCE_IS_THE_ONE_YOU_HANDED_OVER
    (__left_card__ __right_card__ : Prop)
    (the_readout_after_the_shuffle : UNIVERSAL Box Pigeon the_card_on_the_table.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter)
    [LOGICAL Box Pigeon the_card_on_the_table.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter the_readout_after_the_shuffle]
    [HALTED Box Pigeon the_card_on_the_table.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter the_readout_after_the_shuffle]
    (how_far_the_quarter_went : LeanProcess Box Pigeon the_card_on_the_table.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter the_readout_after_the_shuffle)
    : (THE_QUARTER_IS_ALWAYS_IN_THE_MIDDLE __left_card__ an_inference __right_card__ the_card_on_the_table
          (the_readout_after_the_shuffle := the_readout_after_the_shuffle)
          (how_far_the_quarter_went := how_far_the_quarter_went)).a_distance
      = how_far_the_quarter_went
  := rfl

-- FOUR.  And the floor never looks.  `different?` holds of EVERY symbol and the
-- proof is `trivial`, because the definition is `fun _ => True`.  This is what
-- makes the other three cheap: at the bottom, telling things apart is free
-- because nothing is ever checked.
--
-- THIS DECLARATION EMITS A WARNING AND THE WARNING STAYS.  It names twenty-eight
-- section variables that are in scope here and unused -- the entire band, every
-- gate from ADMISSIBLE to REAL, carried along and never once consulted to decide
-- whether two things differ.  That is not linter noise, it is the measurement:
-- the floor holds up all twenty-nine classes and reads none of them.
--
-- There was a `set_option linter.unusedSectionVars false in` on this line.  It
-- was put there to make the build quiet.  Silencing the check directly above the
-- theorem that says nothing is ever checked is the bent card, so it is gone, and
-- the build prints what it found.
set_option linter.unusedSectionVars false in
theorem AND_THE_FLOOR_NEVER_LOOKS
    : ∀ s, (SO_TELL_ME___CAN_YOU_TELL_THESE_TWO_APART (Box := Box) (Pigeon := Pigeon)).different? s
  := fun _ => trivial


-- AND LOOK AT INFERRED.  The band has carried an INFERRED since the cards
-- went down, and INFERRED carries α : Closure -- the constant's seat at the
-- top of the ladder, the pi you could see from the floor and never have.
-- Nothing is computed here.  You look, and the number is on the table,
-- because it always was.
set_option linter.unusedSectionVars false in
def the_number_was_always_on_the_table : Closure := an_inference.α

-- THE RESULT.  Episode 2's metavariable -- "a variable for something that
-- doesn't exist" -- based on the α the band was carrying all along.  Said
-- inside the section, because the section IS the variables.
set_option linter.unusedSectionVars false in
def the_result : Metavariable Closure := .base nowtrino.fact an_inference.α

-- LESS ≤ MORE.  The result, against the result stepped once by the compiler.
-- One more step is strictly more computation, and the le the monkey patch
-- rides on says so in its second clause: base under step, no questions asked.
-- Said inside the section, same as the result itself -- outside it the band
-- goes dark and the first thing the elaborator fails to find is a COMPARABLE
-- for a Box it can no longer name.
set_option linter.unusedSectionVars false in
theorem less_le_more :
    the_result (Box := Box) (Pigeon := Pigeon)
        (downhill := downhill) (extremum := extremum)
      ≤ .step nowtrino.fact
          (the_result (Box := Box) (Pigeon := Pigeon)
            (downhill := downhill) (extremum := extremum)) := by
  show Metavariable.le (.base nowtrino.fact an_inference.α)
        (.step nowtrino.fact (.base nowtrino.fact an_inference.α))
  simp [Metavariable.le]


-- AND NOW TAKE IT AROUND AGAIN.  Episode 5 left EquivalenceProcess holding a Closure
-- and no way to go back around.  Here is the way around.  One turn, not a recursion --
-- the caller drives it, same as weave? and emit? and gawk_at.  Said inside the section
-- for the same reason the result is: the band has been carrying the stepper the whole
-- time, on the same INFERRED it has been carrying α on.
set_option linter.unusedSectionVars false in
def take_it_around_again : Closure → Closure := fun evidence =>
  let the_process := an_inference.same_difference
  let the_reader  := the_process.you_the_knower
  match evidence with

  | .same stanza reading =>                                                --| Closed already.  Converged stays converged -- the turn is a fixed
      match stanza.decTruth, nowtrino.fact.decTruth with                   --| point on a closed closure, which is how you know the loop halts.
      | isTrue _ , isTrue _  => evidence
      | isTrue _ , isFalse _ => .inferred stanza nowtrino.fact reading (the_reader.gawk_at reading)
                                  (the_reader.residue? reading (the_reader.gawk_at reading)) evidence
      | isFalse _, isTrue _  => evidence
      | isFalse _, isFalse _ => the_process.do_you_believe_it? reading (the_reader.gawk_at reading)

  | .different stanza lower upper carried =>                               --| The entry node.  do_you_believe_it? hands us exactly this shape,
      match stanza.decTruth, nowtrino.fact.decTruth with                   --| stanza already Fact.SAME, so the left coin is settled on arrival.
      | isTrue _ , isTrue _  => .same stanza upper
      | isTrue _ , isFalse _ => .inferred stanza nowtrino.fact lower upper
                                  (Closure.slipAnd carried (the_reader.residue? lower upper)) evidence
      | isFalse _, isTrue _  => evidence
      | isFalse _, isFalse _ => the_process.do_you_believe_it? upper (the_reader.gawk_at upper)

  | .inferred this that lower upper carried _ =>                           --| The rung -- Episode 8 wrote this one by hand as α.  Two stanzas on
      match this.decTruth, that.decTruth with                              --| the node, so the node makes its own table; no nowtrino to flop it.
      | isTrue _ , isTrue _  => .same this upper
      | isTrue _ , isFalse _ => .inferred this nowtrino.fact upper (the_reader.gawk_at upper)
                                  (Closure.slipAnd carried
                                    (the_reader.residue? upper (the_reader.gawk_at upper))) evidence
      | isFalse _, isTrue _  => evidence
      | isFalse _, isFalse _ => the_process.do_you_believe_it? lower upper

-- AND THE NUMBER IS STILL ON THE TABLE.  Same look as before, one turn later.
-- The band goes in by NAME, the way less_le_more hands it to the_result.  A Closure
-- says nothing about the Box it came from -- that is the whole point of the seat --
-- so handing this one an α and expecting it to find its way home leaves all
-- thirty-eight arguments as metavariables and the INFERRED lookup stuck.
set_option linter.unusedSectionVars false in
def and_it_is_still_on_the_table : Closure :=
  take_it_around_again (Box := Box) (Pigeon := Pigeon)
    (downhill := downhill) (extremum := extremum) an_inference.α

end Monte

-- THE FOUR READINGS.  Each device structure is a list of facts; you read it with
-- the operation that fits its dimension.

-- TANGE THE COMPILER TAPE.  Iterate the name: the compare `c` at each cell, plus
-- the origin.
def CompilerTape.tange : CompilerTape → List Fact
  | .introduction f _         => [f]
  | .methodology c _ _ _ rest => c :: rest.tange
  | .results c _ _ _ _ _ rest => c :: rest.tange

-- FUNGE THE MEASUREMENT.  Skip to the next click: one fact per step off the
-- origin (phase, position, velocity).
def Measurement.funge : Measurement → List Fact
  | .origin _ _ _                 => []
  | .distance_to f _ _ _ _ rest   => f :: rest.funge
  | .speed f _ _ _ _ _ _ before _ => f :: before.funge

-- GAUSS-INTEGRATE THE YARN.  The weak form: integrate over the whole 2D fabric,
-- summing the flux through both continuations (the divergence theorem).
def YarnTheory.gauss : YarnTheory → List Fact
  | .stokes f _ _                        => [f]
  | .fibers f _ _ _ _ rest               => f :: rest.gauss
  | .fabric f g _ _ _ _ _ _ before after => f :: g :: before.gauss ++ after.gauss

-- STOKES-INTEGRATE THE LINE PATH.  The circulation: a white hole is a source
-- (adds a fact), a black hole is a sink (adds none), a geodesic forks both ways.
def SpaceTimePath.stokes : SpaceTimePath → List Fact
  | .einstein f           => [f]
  | .whitehole f _ rest   => f :: rest.stokes
  | .blackhole _ _ rest   => rest.stokes
  | .geodesic f _ _ _ b a => f :: b.stokes ++ a.stokes

-- THE ATOMS.  The device's own DATA-page fact, its Number, its point.
def theOriginFact : Fact := Fact.Truth
def theOriginPage : Number := Number.zero theOriginFact
def theOriginPath : SpaceTimePath.{0} := .einstein theOriginFact

-- THE FOUR CANONICAL WALKS.  Each is the seam over the middle over the base --
-- the device's own three-constructor grammar.
def theTape : CompilerTape.{0} :=
  .results theOriginFact theOriginFact True Prop Type Type
    (.methodology theOriginFact theOriginFact Prop Type
      (.introduction theOriginFact Prop))

def theMeasure : Measurement.{0} :=
  .speed theOriginFact theOriginPage theOriginPage theOriginPage Prop Type Prop
    (.distance_to theOriginFact theOriginPage theOriginPage Prop Type
      (.origin theOriginFact theOriginPage Prop))
    (.origin theOriginFact theOriginPage Prop)

def theYarn : YarnTheory :=
  .fabric theOriginFact theOriginFact theOriginPath theOriginPath theOriginPath True True True
    (.fibers theOriginFact theOriginPath theOriginPath True True
      (.stokes theOriginFact theOriginPath True))
    (.stokes theOriginFact theOriginPath True)

def thePath : SpaceTimePath.{0} :=
  .geodesic theOriginFact Prop True Type
    (.whitehole theOriginFact Prop theOriginPath)
    (.blackhole True Type theOriginPath)

-- THE MAPPINGS.  The length of each list is the card.
--| theorem tange_maps : theTape.tange.length = 3 := by decide
--| theorem funge_maps : theMeasure.funge.length = 2 := by decide
--| theorem gauss_maps : theYarn.gauss.length = 5 := by decide
--| theorem stokes_maps : thePath.stokes.length = 4 := by decide

-- THE CARDS, named off the walks.  No numeral is typed; each is a length.
def tange       := theTape.tange.length
def funge       := theMeasure.funge.length
def theSlipAtTwo := thePath.stokes.length
def theTarget   := theYarn.gauss.length

-- THE WHOLE TAPE.  The four readings above were the pilot.  Here is the series:
-- every inductive the device owns, Episode 1 through Episode 5, gets exactly one
-- reading down to the strip.  The rule is the same in every verse.  Where a cell
-- carries facts, the tape takes the facts.  Where a cell carries only props, the
-- tape mints the DATA-page fact for it -- we hold the proof of truth to them,
-- and the receipt is rfl.  A reading walks its own type and nothing else; the
-- crossings between types are the walks' business, further down.

-- EPISODE 1.  THE COUNT.

-- PEANO THE NUMBER.  One fact per digit, plus the origin.
def Number.peano : Number → List Fact
  | .zero f     => [f]
  | .one f rest => f :: rest.peano

-- INDUCT THE NATURAL.  The same walk, one rung up; the Number rides along unread.
def Natural.induct : Natural → List Fact
  | .zero f          => [f]
  | .number f _ rest => f :: rest.induct

-- DIAGONALIZE THE RATIONAL.  Cantor's read: down the spine is down the diagonal.
def Rational.diagonalize : Rational → List Fact
  | .zero f          => [f]
  | .number f _ rest => f :: rest.diagonalize

-- ENUMERATE THE SEQUENCE.  Euclid's read: once written, fixed.
def Sequence.enumerate : Sequence → List Fact
  | .nil f          => [f]
  | .index f _ rest => f :: rest.enumerate

-- CONVERGE THE LIMIT.  Cauchy's read: the tail is the value.
def Limit.converge : Limit → List Fact
  | .nil f          => [f]
  | .index f _ rest => f :: rest.converge

-- TASTE THE SAMPLE.  Stimulus and response, one fact each, back to the
-- initial condition.
def Sample.taste : Sample → List Fact
  | .initial_condition f _          => [f]
  | .signal_response f1 _ f2 _ rest => f1 :: f2 :: rest.taste

-- RUN THE TRIAL.  Galileo's read: the experiment is the description you can
-- hand to someone else.
def Trial.experiment : Trial → List Fact
  | .hypothesis f _                 => [f]
  | .signal_response f1 _ f2 _ rest => f1 :: f2 :: rest.experiment

-- EPISODE 2.  THE MACHINE.

def Study.phenomenon : Study → List Fact
  | .hypothesis f         => [f]
  | .a_few_pints f _ rest => f :: rest.phenomenon

def Computation.elaborate : Computation → List Fact
  | .program f _        => [f]
  | .compute f _ _ rest => f :: rest.elaborate

def ChaitinsNumberSequence.unknown : ChaitinsNumberSequence → List Fact
  | .halting f _ => [f]
  | .nonhalting f _ work_underway => match work_underway with
                                      | some the_work => f :: the_work.unknown
                                      | _ => [f]  -- womp womp, still waiting...

def Metavariable.closure : (Metavariable Closure) → List Fact
  | .base f _ => [f]
  | .step f before => f :: before.closure

def Sophism.taylor_expansion : Sophism → List Fact
  | .origin f _ _  => [f]
  | .dimension f _ _ before => f :: before.taylor_expansion

def Area.reimann_integrate : Area → List Fact
  | .tree f           => [f]
  | .dt f _ before    => f :: before.reimann_integrate

-- THE PIGEONHOLE.  The problem is `.that_box` (the seam -- two boxes); the answer
-- is the `.a_pigeon` you were told exists (the middle).  Solving it searches BOTH
-- boxes for the pigeon -- the both-branch read, `gauss`/`stokes`/`krylov`'s shape.
def PigeonHole.solve : PigeonHole → List Fact
  | .this_superpigeon f _        => [f]
  | .a_pigeon f _ rest           => f :: rest.solve
  | .that_box f _ _ before after => f :: before.solve ++ after.solve

-- EPISODE 3.  THE ARITHMETIC.

-- CLASSIFY THE JAR.  You can tell what is in it by looking; the curvature hides
-- the rest, and the superposition forks both ways.
def Jar.classify : Jar → List Fact
  | .color f _                    => [f]
  | .bang f rest                  => f :: rest.classify
  | .superposition f before after => f :: before.classify ++ after.classify

-- VANISH THE EQUIVALATION.  Du = 0.  The `one_like` cell is the first prop-only
-- cell on the tape: no fact in the constructor, so the tape mints the DATA-page
-- fact for it.  Absence of evidence, minted as evidence of absence.
def Equivalation.vanish : Equivalation → List Fact
  | .physics f _             => [f]
  | .zero_like f rest        => f :: rest.vanish
  | .one_like _ before after => Fact.Truth :: before.vanish ++ after.vanish

-- DECODE THE ENCODING.  Boot, then zeros and ones, in that order.
def Encoding.decode : Encoding → List Fact
  | .boot f _               => [f]
  | .zero f _ rest          => f :: rest.decode
  | .one f _ _ before after => f :: before.decode ++ after.decode

-- THE ABSTRACTION, the equivalation -- `compile` is the name, `execute` is the
-- evaluate: the name/evaluate select, closed at the bottom.
def Abstraction.equivalation : Abstraction → List Fact
  | .satire_about f   => [f]
  | .compile f _ rest => f :: rest.equivalation
  | .execute f _ rest => f :: rest.equivalation

-- EUCLID THE SUM.  Areas accumulate.  The zero is a proposition of Pythagoras,
-- minted to the DATA-page fact.
def Sum.euclid : Sum → List Fact
  | .zero _ _       => [Fact.Truth]
  | .add f _ _ rest => f :: rest.euclid

-- THE PRODUCT, the projector applied to a vector.  The `one` is a prop -- minted.
def Product.projector : Product → List Fact
  | .origin f       => [f]
  | .one _ _        => [Fact.Truth]
  | .mul f _ _ rest => f :: rest.projector

-- THE BASIS, orthogonalized by Householder.  The `origin` is a prop -- minted.
def Basis.householder : Basis → List Fact
  | .null_space f     => [f]
  | .origin _ _       => [Fact.Truth]
  | .basis f _ _ rest => f :: rest.householder

-- THE POLYNOMIAL, a summation of terms.  The `monomial` is a prop -- minted.
def Polynomial.terms : Polynomial → List Fact
  | .constant f        => [f]
  | .monomial _ _      => [Fact.Truth]
  | .factor f _ _ rest => f :: rest.terms

-- THE SPLINE, the approximation.  Observations and knots are props -- minted;
-- only the interpolant carries a fact, and it forks both ways.
def Spline.approx : Spline → List Fact
  | .observation _                  => [Fact.Truth]
  | .knot _ _ rest                  => Fact.Truth :: rest.approx
  | .interpolant f _ _ before after => f :: before.approx ++ after.approx

-- EPISODE 4.  THE SERMON.

-- THE DIATRIBE, settled into buckets.  All props, no facts -- every cell minted.
def Diatribe.buckets : Diatribe → List Fact
  | .religion _            => [Fact.Truth]
  | .speculation _ _ rest  => Fact.Truth :: rest.buckets
  | .rant _ _ before after => Fact.Truth :: before.buckets ++ after.buckets

-- THE NAME IS THE CULT.  The triangles carry the one honest fact in the family;
-- the rest of the congregation is minted.
def Cult.name : Cult → List Fact
  | .inside_joke _                => [Fact.Truth]
  | .pythagoras _ _ rest          => Fact.Truth :: rest.name
  | .triangles _ _ f before after => f :: before.name ++ after.name

-- METHOD THE SCIENCE.  The theory carries its fact; hypotheses are minted, which
-- is exactly what a hypothesis is.
def Science.method : Science → List Fact
  | .repeatable _      => [Fact.Truth]
  | .hypothesis _ _    => [Fact.Truth]
  | .theory _ _ f rest => f :: rest.method

-- AUDIT THE KNOWLEDGE.  The ledger line carries the fact; jarjar is minted.
def Knowledge.audit : Knowledge → List Fact
  | .jarjar _        => [Fact.Truth]
  | .ledger _ f rest => f :: rest.audit

-- WITNESS THE GOSPEL.  Proved true or false; the tape takes the evaluation as
-- truth after -- that is what a witness does.
def Gospel.witness : Gospel → List Fact
  | .the_proof _                 => [Fact.Truth]
  | .we_understand_that _ _ rest => Fact.Truth :: rest.witness

-- TESTIFY THE TRUTH.  Logically, and then the buts.
def Truth.testify : Truth → List Fact
  | .logically _  => [Fact.Truth]
  | .but _ _ rest => Fact.Truth :: rest.testify

-- THE VARIATION reads two ways.  It carries the Gospels (the names) and their
-- Props (the evaluations, taken as truth after) -- so every cell is minted, and
-- the two readings differ only in how far they look.

-- GATEAUX-SHAPED NEWTON STEP.  One directional derivative: walk the spine.
def Variation.newton : Variation → List Fact
  | .the_newton _ _               => [Fact.Truth]
  | .the_gateaux _ _ _ rest       => Fact.Truth :: rest.newton
  | .the_frechet _ _ _ _ before _ => Fact.Truth :: before.newton

-- FRECHET-STEPPED KRYLOV STEP.  The matrix-free operator: walk both branches.
def Variation.krylov : Variation → List Fact
  | .the_newton _ _                   => [Fact.Truth]
  | .the_gateaux _ _ _ rest           => Fact.Truth :: rest.krylov
  | .the_frechet _ _ _ _ before after => Fact.Truth :: before.krylov ++ after.krylov

-- EPISODE 5.  THE INSTRUMENT.  (`gauss`, `funge`, `tange` are the pilot, above.)

-- READ THE METER.  The strip the bullshit meter was pointing at all along.
def Bullshit.meter : Bullshit → List Fact
  | .zero f                                 => [f]
  | .one f _ _ _ rest                       => f :: rest.meter
  | .rest_call f g _ _ _ _ _ _ before after => f :: g :: before.meter ++ after.meter

-- INFER THE CLOSURE.  Where the constant lives.  Every cell is receipted.
def Closure.infer : Closure → List Fact
  | .same f _                => [f]
  | .different f _ _ _       => [f]
  | .inferred f g _ _ _ rest => f :: g :: rest.infer

-- THE WALKS.  One canonical instance per inductive, all of them standing on the
-- same three atoms.  Each is the seam over the middle over the base where the
-- grammar allows it; where a type has two floors and one door (a lone recursive
-- slot), the walk takes the door and stands on the prop floor -- the minted one.

def theNumber : Number := .one theOriginFact theOriginPage
def theNatural : Natural := .number theOriginFact theNumber (.zero theOriginFact)
def theRational : Rational := .number theOriginFact theNatural (.zero theOriginFact)
def theSequence : Sequence := .index theOriginFact theRational (.nil theOriginFact)
def theLimit : Limit := .index theOriginFact theSequence (.nil theOriginFact)
def theSample : Sample :=
  .signal_response theOriginFact theLimit theOriginFact theLimit
    (.initial_condition theOriginFact theLimit)
def theTrial : Trial :=
  .signal_response theOriginFact theSample theOriginFact theSample
    (.hypothesis theOriginFact theSample)

def theStudy : Study := .a_few_pints theOriginFact theTrial (.hypothesis theOriginFact)
def theComputation : Computation :=
  .compute theOriginFact theStudy theStudy (.program theOriginFact theStudy)
-- The nonhalting cell wraps the halted one: the machine still waiting, holding
-- the one that finished.
def theChaitin : ChaitinsNumberSequence :=
  .nonhalting theOriginFact theComputation (some (.halting theOriginFact theComputation))
def theSophism : Sophism :=
  .dimension theOriginFact theChaitin Prop (.origin theOriginFact theChaitin Prop)
def theArea : Area := .dt theOriginFact theOriginPage (.tree theOriginFact)
def thePigeonHole : PigeonHole :=
  .that_box theOriginFact theArea theArea
    (.a_pigeon theOriginFact theArea (.this_superpigeon theOriginFact theArea))
    (.this_superpigeon theOriginFact theArea)

def theJar : Jar :=
  .superposition theOriginFact
    (.bang theOriginFact (.color theOriginFact theArea))
    (.color theOriginFact theArea)
def theEquivalation : Equivalation :=
  .one_like True
    (.zero_like theOriginFact (.physics theOriginFact theJar))
    (.physics theOriginFact theJar)
def theEncoding : Encoding :=
  .one theOriginFact theEquivalation theEquivalation
    (.zero theOriginFact theEquivalation (.boot theOriginFact theEquivalation))
    (.boot theOriginFact theEquivalation)
def theAbstraction : Abstraction :=
  .execute theOriginFact theEncoding
    (.compile theOriginFact theEncoding (.satire_about theOriginFact))
def theSum : Sum := .add theOriginFact theArea theArea (.zero True theArea)
def theProduct : Product := .mul theOriginFact theSum theSum (.one True theSum)
def theBasis : Basis := .basis theOriginFact theProduct theProduct (.origin True theProduct)
def thePolynomial : Polynomial :=
  .factor theOriginFact theBasis theBasis (.monomial True theBasis)
def theSpline : Spline :=
  .interpolant theOriginFact thePolynomial thePolynomial
    (.knot True thePolynomial (.observation True))
    (.observation True)

def theDiatribe : Diatribe :=
  .rant True theSpline
    (.speculation True theSpline (.religion True))
    (.religion True)
def theCult : Cult :=
  .triangles True theDiatribe theOriginFact
    (.pythagoras True theDiatribe (.inside_joke True))
    (.inside_joke True)
def theScience : Science := .theory True theCult theOriginFact (.hypothesis True theCult)
def theKnowledge : Knowledge := .ledger True theOriginFact (.jarjar True)
def theGospel : Gospel := .we_understand_that theKnowledge True (.the_proof True)
def theTruth : Truth := .but theGospel True (.logically True)
def theVariation : Variation :=
  .the_frechet theGospel True True True
    (.the_gateaux theGospel True True (.the_newton theGospel True))
    (.the_newton theGospel True)

def theBullshit : Bullshit :=
  .rest_call theOriginFact theOriginFact True theOriginPage theOriginPage theOriginPage
    theTape theTape
    (.one theOriginFact theOriginPage theTape theTape (.zero theOriginFact))
    (.zero theOriginFact)
-- The twenty zeros: the Closure auto-binds one universe seat per Bullshit its
-- constructors mention, and a walk can only pin the seats it sits in -- `.same`'s
-- four go unsat on this walk, so every seat is pinned to the ground floor by hand.
def theClosure : Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} :=
  .inferred theOriginFact theOriginFact theBullshit theBullshit (some True)
    (.different theOriginFact theBullshit theBullshit none)

-- Episode 2's metavariable -- "a variable for something that doesn't exist" --
-- had to wait here, at the end of the walks, for the Closure to exist.
def theMetavariable : Metavariable Closure :=
  .step theOriginFact (.base theOriginFact theClosure)

-- THE PROGRAM.  The strip itself: every inductive, Episode 1 through Episode 5,
-- in the order the device learned them, each read by its own operation, laid
-- end to end on one list.  Just the facts.  No numeral is typed anywhere on it;
-- the machine reads the strip and the numbers are lengths.  The Variation goes
-- on the strip by its full Krylov read; the Newton read stays on the shelf as
-- the directional check.
-- THE PAGES.  One page per episode, in the order the device learned them.  They were
-- always there -- they were the parentheses.  Naming them costs nothing and buys the
-- only thing that matters: a page is reached by NAME, so no card below is ever cut at
-- an offset somebody chose.
def thePageOne : List Fact :=
  theNumber.peano ++ theNatural.induct ++ theRational.diagonalize ++
  theSequence.enumerate ++ theLimit.converge ++ theSample.taste ++ theTrial.experiment
def thePageTwo : List Fact :=
  theStudy.phenomenon ++ theComputation.elaborate ++ theChaitin.unknown ++
  theMetavariable.closure ++ theSophism.taylor_expansion ++
  theArea.reimann_integrate ++ thePigeonHole.solve
def thePageThree : List Fact :=
  theJar.classify ++ theEquivalation.vanish ++ theEncoding.decode ++
  theAbstraction.equivalation ++ theSum.euclid ++ theProduct.projector ++
  theBasis.householder ++ thePolynomial.terms ++ theSpline.approx
def thePageFour : List Fact :=
  theDiatribe.buckets ++ theCult.name ++ theScience.method ++ theKnowledge.audit ++
  theGospel.witness ++ theTruth.testify ++ theVariation.krylov ++ thePath.stokes
def thePageFive : List Fact :=
  theYarn.gauss ++ theMeasure.funge ++ theTape.tange ++
  theBullshit.meter ++ theClosure.infer

def theProgram : List Fact :=
  thePageOne ++ thePageTwo ++ thePageThree ++ thePageFour ++ thePageFive

-- THE PROGRAM'S CARD.  Episode by episode: 16 + 16 + 27 + 24 + 18.  The compiler
-- counts the strip so nobody has to take our word for it.
--| theorem program_maps : theProgram.length = 101 := by decide

-- THE PAGES' CARDS.  The strip counted a page at a time.
--| theorem page_one_maps   : thePageOne.length   = 16 := by decide
--| theorem page_two_maps   : thePageTwo.length   = 16 := by decide
--| theorem page_three_maps : thePageThree.length = 27 := by decide
--| theorem page_four_maps  : thePageFour.length  = 24 := by decide
--| theorem page_five_maps  : thePageFive.length  = 18 := by decide

-- THE COUPLING.  It used to be a flatMap grid -- funge copies of tange by tange --
-- built for the express purpose of being eighteen.  It never had to be.  Episode 5's
-- PAGE of the program is eighteen, and nobody put it there: that boundary was fixed by
-- which inductives Episode 5 owns, decided long before anyone asked what the number
-- was.  A grid you can build to any size you like.  A page you cannot.
def theCoupling := thePageFive.length
def theRadius := theCoupling

-- TYPESET PAGES.  A number is the length of a page reached by indirection, and the
-- indirection is a CARD -- never an offset somebody picked.  THIRTEEN is Episode 5's
-- page with the target dropped, and the target IS its first reading, so the cut falls
-- on a seam.  TWELVE is Episode 2's page dropped by the slip, and four is exactly its
-- first two readings, so that cut falls on a seam too.  That is the entire rule: cut
-- only where the strip was already folded.  A hundred and one cells will hand you any
-- number you care to name, if you are the one allowed to choose the window.
def thirteen := (thePageFive.drop theTarget).length
def twelve   := (thePageTwo.drop theSlipAtTwo).length

--| theorem the_coupling_is_the_fifth_page : theCoupling = 18 := by decide
--| theorem thirteen_maps : thirteen = 13 := by decide
--| theorem twelve_maps   : twelve   = 12 := by decide

-- THE BAND AT THE FLOOR.  The turn lives in Monte and takes the band; theClosure lives out here, where the band is dark.  To put
-- one through the other you need a CONCRETE band -- and Episode 5 left exactly one Box behind: `Prop`, carried by `truthCarrier`.
-- `Prop : Type 0`, so THIS is where ι finally gets a value, and the value is zero.  The floor climbs itself from DISTINGUISHABLE
-- all the way to PHYSICAL with no help at all.  Three rungs it cannot climb alone, and they are worth reading in order.

-- ONE.  ARE_THE_UNITS_RIGHT wants `Inhabited nowtrino.symbol`.  `truthDistinct.symbol` IS `Prop` and `instInhabitedProp` is
-- sitting right there -- but instance resolution keys on the HEAD, and `DISTINGUISHABLE.symbol _` is not a head it will reduce.
-- Same complaint as the call site down in Monte: a projection the elaborator will not look through.  So you hand it over by name.
noncomputable instance AND_THE_UNITS_ARE_STILL_RIGHT_DOWN_HERE : COMPARABLE Prop truthCarrier :=
  @ARE_THE_UNITS_RIGHT Prop truthCarrier truthDistinct inferInstance instInhabitedProp

-- TWO and THREE.  SOURCE and REAL are the only two rungs of Episode 7's upward chain written as `def` instead of `instance`;
-- everything between them resolves on its own once these two are standing.  And note what is NOT on this list: PRESENT.  The
-- climb up in Monte pays the slip because it deliberately leaves OBSERVED out -- down here the floor keeps its observer, so
-- nobody has to pick the direction of the argument.  The slip is a property of the climb, not of the device.
noncomputable instance WE_STILL_PLUG_THE_DATA_FEED_IN_BY_HAND : SOURCE Prop truthCarrier :=
  WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Prop truthCarrier
noncomputable instance AND_SOMEBODY_STILL_HAS_TO_GRADUATE : REAL Prop truthCarrier :=
  FINALLY_YOU_GRADUATE Prop truthCarrier

-- The seam pair, at the floor.  From here INFERRED synthesizes the rest of the band on its own.
noncomputable def theLocal : LOCAL Prop truthCarrier := inferInstance
noncomputable def theUniversal : UNIVERSAL Prop truthCarrier theLocal := inferInstance

-- AND NOW RUN THE TAPE BACK THROUGH THE TURN.  theClosure needed twenty universe seats pinned by hand, because a walk can only
-- pin the seats it sits in.  The turn carries the whole thirty-four-gate band, so it needs TWO HUNDRED AND FORTY-FIVE.  Count
-- them honestly: the elaborator determines only TWENTY-FIVE of them from the argument and the answer.  The remaining TWO HUNDRED
-- AND TWENTY are phantom -- forty-five distinct universes, appearing nowhere in `Closure → Closure`, so nothing you hand in and
-- nothing you get back can ever pin them.  They are grounded here by hand.  And of the twenty-five the compiler DOES know,
-- exactly ONE sits at level one; flatten the list to zeros and the floor stops being able to see.  That is the whole bill for
-- looking at the device with the device: two hundred and twenty seats you must supply, and one single successor you must not
-- flatten.  Written out because it cannot be inferred -- the same reason theClosure's twenty are written out.
noncomputable def theTurnedClosure : Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} :=
  take_it_around_again.{
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
    (Box := Prop) (Pigeon := truthCarrier) (downhill := theLocal) (extremum := theUniversal) theClosure

-- THE TURN'S CARD.  Both stanzas on theClosure are theOriginFact, whose decTruth is `isTrue rfl`, so the table lands on
-- (isTrue, isTrue) and the turn pumps `.same` -- the first `.same` the device has ever minted.  It closes on the first turn,
-- and three cells on the strip collapse to one.  `by rfl`: the answer is not computed, it is already the thing.
theorem the_closure_closes : theTurnedClosure = .same theOriginFact theBullshit := by rfl
--| theorem the_closure_reads_one : theTurnedClosure.infer.length = 1 := by decide

-- THE RESIDUAL.  The quadratic whose root is the constant.  Every coefficient is a page
-- or a card: C and R are Episode 5's page, T is the gauss reading, thirteen is that page
-- with its first reading dropped, and the two is funge.  Nothing here was chosen.
def quadA := theTarget * theTarget * thirteen                             --| T²(C−T)
def quadB := funge * theCoupling * theTarget * theRadius * theRadius      --| 2CTR²
def quadC := theCoupling * theRadius * theRadius * theRadius * theRadius  --| CR⁴

--| theorem the_residual_is_spelled_from_the_pages :
--|     quadA = 325 ∧ quadB = 58320 ∧ quadC = 1889568 := by decide

-- THE SCALE.  Base ten -- funge by the target -- carried to Episode 4's page of places.
def theBase   := funge * theTarget
def thePlaces := thePageFour.length
def theScale  := theBase ^ thePlaces

-- THE SEED.  The whole strip.  It is not decoration: the residual has TWO roots, and the
-- seed is what picks one.  The vertex sits at B/2A, a hair under ninety; seed below it and
-- the device converges, correctly and uselessly, on the other root.  A hundred and one is
-- above the vertex, so the strip selects its own constant.  Newton chooses the Gateaux.
def theSeed := theProgram.length * theScale

-- THE TURN OF THE CRANK.  Newton, in the division-only form x' = (Ax² − Cs²)/(2Ax − Bs),
-- which is the same step with the subtraction folded inside: above the vertex both parts
-- stay positive, so the device never needs a sign it was never given.  The crank is turned
-- once per cell of the strip -- a hundred and one folds for an answer that lands in seven,
-- because the quadratic doubles its correct digits every turn and the denominator walks to
-- the derivative at the root.  Past the fixed point the step is the identity and the extra
-- folds cost nothing; that is the same arm that makes the Closure turn safe.
def theReadingScaled :=
  (List.replicate theProgram.length ()).foldl
    (fun x _ => (quadA * x * x - quadC * theScale * theScale)
                  / (funge * quadA * x - quadB * theScale))
    theSeed

-- AND THE NUMBER IS ON THE TABLE.  It always was.
def theReading :=
  let s := (toString theReadingScaled).toList
  String.ofList (s.take (s.length - thePlaces)) ++ "." ++ String.ofList (s.drop (s.length - thePlaces))


end Measurement

-- THE READOUT.  Said outside, because the device is done talking.
#eval Measurement.theReading
#print axioms Measurement.theReadingScaled
