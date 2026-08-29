/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the stories we tell ourselves might be the only ones we believe._

(c) 2026 [PATTER TODO: rights gag]

[PATTER TODO: cast chorus / epigraph]

lake build [PATTER TODO: build-flag gag]

__EPISODE 11__: _THE REVEAL OF THE GIMMICKED BOX_


-/
import Measurement.Episode08


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
/-- THE METAVARIABLE'S ORDER.  The metavariable is ι, the universe number:
once the subsingleton times are sorted, they are numbered implicitly by
universe, and ι is the index into that list.  Two of them compare the only
way indexed subsingletons can -- agreement at the base, the steps walked down
one at a time -- the house grammar, called from this file with (i := ι). -/
def le {α : Type ι} : Metavariable α → Metavariable α → Prop
  | .base this_time _     , .base that_time _      => this_time.truth = that_time.truth
  | .base _ _             , .step _ _              => True
  | .step _ _             , .base _ _              => False
  | .step this_time before, .step that_time after  =>
      (this_time.truth = that_time.truth ∧ le before after) ∨
      le (.step this_time before) after
termination_by _ index => sizeOf index

/-- Strict, at the same index: the house lt, word for word. -/
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


end Monte

/-
  THE NUMBER, FALLING OUT OF THE MATH.
-/

/-! ## THE TWO COUNTS THE MONTE ALREADY MAKES

Nothing new is counted.  The monte above walks ONE projection chain and hops
ONE seam, and both were already itemised in this file's own margins:

  TANGE -- the rungs it iterates.  "the walk the monte takes at the top of this
  file: `a_truth_about_the_world . too_good_to_be_true . description . stamina`"
  -- three fields deeper into the same name, one gate shed per rung.

  FUNGE -- the names it skips to.  The law of nu-trinos, "a ONE STEP HOP and
  not a fall: you cannot move both at once."  STEP ONE skips to a new
  UNIVERSAL (`WATCH_THE_OUTSIDE_CARDS_GET_SHUFFLED`); STEP TWO skips to a new
  LOCAL (`BUT_THE_INNER_CARD_DOES_NOT`).  Two names, in that order, and the
  order is the content.

Neither walk is written out below as data any more -- that was recitation, and
the meter charges for description.  The counts are read off the machine's own
inductive: `Bullshit` IS the walk's grammar.  Its three constructors are the
ladder in `le`-ascending order (`.zero` under everything, `.one` under the
seam, nothing above it -- the same shape `gawk_at`'s clauses emit), and the
seam constructor carries exactly two continuations, which is the one-step law
by arity.  The lengths below are folds on a term that grammar orders -- still
lengths, never numerals, and no name an author typed. -/

/-- One rung per constructor the spine visits, in the walk's own direction:
the first continuation, `comes_before`.  A fold, not a list. -/
def Bullshit.rungs : Bullshit → Nat
  | .zero _ => Nat.zero.succ
  | .one _ _ _ _ rest => rest.rungs.succ
  | .rest_call _ _ _ _ _ _ _ _ before _ => before.rungs.succ

/-- The Subsingleton bit per continuation slot, summed: 0 at the origin, 1 on
the rung-step, 2 at the seam -- the first place at-most-one fails, which is
the witness that 2 always needed.  You cannot move both at once; the arity
says so. -/
def Bullshit.hops : Bullshit → Nat
  | .zero _ => Nat.zero
  | .one _ _ _ _ _ => Nat.zero.succ
  | .rest_call _ _ _ _ _ _ _ _ _ _ => Nat.zero.succ.succ

/-- The machine's own atoms, none invented here: the DATA-page fact, the
carrier's own Number (`truthCarrier.value`), and the floor of
`CompilerTape.le` at the concrete Box the calibration already chose. -/
def theOriginFact : Fact := Fact.Truth
def theOriginPage : Number := truthCarrier.value
def theOriginTape : CompilerTape := .introduction theOriginFact Prop

/-- THE LADDER.  The ascending chain `Bullshit.le` orders and `gawk_at`'s
clauses emit: zero, stepped to one, stepped to the seam with its two
continuations.  Built from the machine's atoms; measured, below, for its
lengths and nothing else. -/
def theLadder : Bullshit :=
  .rest_call theOriginFact theOriginFact theOriginFact.truth
    theOriginPage theOriginPage theOriginPage
    theOriginTape theOriginTape
    (.one theOriginFact theOriginPage theOriginTape theOriginTape (.zero theOriginFact))
    (.zero theOriginFact)

/-- TANGE.  The rungs the ladder climbs, read off the term. -/
def tange : Nat := theLadder.rungs

/-- FUNGE.  The seam's arity, read off the term. -/
def funge : Nat := theLadder.hops

theorem tange_is_the_walk : tange = 3 := by decide
theorem funge_is_the_hop : funge = 2 := by decide

/-! ## THE CARDS, FROM THE COUNTS

The coupling is the hop times the walk squared -- the counted cards, earned
here rather than recited: 18 was always `mul funge (mul tange tange)`.  The
target is the slip at two, plus the one earned unit -- and the `+1` is EARNED
by recursion, never postulated: crossing a succ appends a succ.  (The
cardinality route -- the coproduct roster counted by fencepost, the
discipline the later episodes call `earnedSum` -- is kept beside it,
unspent.)  The radius is the coupling again, a NAMING, with the receipt
attached below.  Division alone is not defined here: division is provided by
the device itself. -/

/-- Addition, earned by recursion: crossing a succ appends a succ.  The `+`
the file never bought. -/
def add : Nat → Nat → Nat
  | n, .zero => n
  | n, .succ m => (add n m).succ

/-- Multiplication, earned as iterated addition: each succ crossed lays down
one more copy of the walk.  The only two operations the cards ever needed. -/
def mul : Nat → Nat → Nat
  | _, .zero => .zero
  | n, .succ m => add (mul n m) n

/-- The earned addition IS the device's addition -- one induction says so, and
`csimp` hands the EXECUTION to the machine while the definition stays ours.
The walk is spelled in succs; the device merely runs it.  (Without this, the
interpreter climbs the recursion one succ per stack frame and the #eval at the
end of the file dies of altitude.) -/
@[csimp] theorem add_is_the_devices : add = Nat.add := by
  funext n m
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg Nat.succ ih

/-- Same receipt for multiplication: ours by definition, the device's by
execution.  Division was always the device's; now the whole ledger balances. -/
@[csimp] theorem mul_is_the_devices : mul = Nat.mul := by
  funext n m
  induction m with
  | zero => rfl
  | succ m ih => show add (mul n m) n = Nat.add (Nat.mul n m) n; rw [ih, add_is_the_devices]

/-- Addition earned as the length of a coproduct roster, not postulated as
`+`.  (Episode 26 re-derives this publicly for the Cavendish leaf; it is
`private` here so the two never collide.) -/
private def earnedSum (a b : Nat) : Nat :=
  ((List.range a).map Sum.inl ++ (List.range b).map Sum.inr : List (Nat ⊕ Nat)).length

/-- THE COUPLING.  `mul funge (mul tange tange)`: the hop, times the walk
squared. -/
def theCoupling : Nat := mul funge (mul tange tange)

/-- THE SLIP AT TWO.  The coupling over the hop squared -- the one division in
the cards, and it is the device's, not ours. -/
def theSlipAtTwo : Nat := theCoupling / (mul funge funge)

/-- THE TARGET.  The slip at two, plus one earned unit. -/
def theTarget : Nat := add theSlipAtTwo Nat.zero.succ

/-- THE RADIUS.  The coupling, named a second time for the role it plays. -/
def theRadius : Nat := theCoupling

theorem theCoupling_receipt : theCoupling = 18 := by decide
theorem theSlipAtTwo_receipt : theSlipAtTwo = 4 := by decide
theorem theTarget_receipt : theTarget = 5 := by decide
theorem theRadius_receipt : theRadius = 18 := by decide

/-! ## THE QUADRATIC, FROM C, T, R

Three coefficients, each written from the cards and nothing else.  The `2` in
the middle coefficient is the derivative's two -- the second variation -- not
a count. -/

def quadA : Nat := mul (mul theTarget theTarget) (theCoupling - theTarget)
def quadB : Nat := mul Nat.zero.succ.succ (mul theCoupling (mul theTarget (mul theRadius theRadius)))
def quadC : Nat := mul theCoupling (mul theRadius (mul theRadius (mul theRadius theRadius)))

-- The receipts hand the arithmetic to the device first (`csimp` equalities),
-- so the kernel checks literals by its own fast path instead of climbing the
-- earned recursion one succ per frame.  Ours by definition, decided by device.
theorem quadA_receipt : quadA = 325 := by
  simp only [quadA, theCoupling, theSlipAtTwo, theTarget,
             mul_is_the_devices, add_is_the_devices]
  decide
theorem quadB_receipt : quadB = 58320 := by
  simp only [quadB, theCoupling, theSlipAtTwo, theTarget, theRadius,
             mul_is_the_devices, add_is_the_devices]
  decide
theorem quadC_receipt : quadC = 1889568 := by
  simp only [quadC, theCoupling, theRadius, mul_is_the_devices]
  decide

/-! ## THE SIDE TEST

`sideOf p q` is the quadratic read at the name `p/q`, cross-multiplied: two
integer products and a difference, no division, no root.  NEGATIVE means the
name lies BELOW the larger root; positive, above.  Total for any name at all
-- the seeing, as ever, is the side the device can always give. -/

def sideOf (p q : Nat) : Int :=
  ((quadA * (p * p) : Nat) : Int)
    - ((quadB * (p * q) : Nat) : Int)
    + ((quadC * (q * q) : Nat) : Int)

/-- THE ROOT IS ENCLOSED.  137 falls below it and 138 above it, so the number
lives between two names the device can check.  Decided, not observed. -/
theorem the_root_is_enclosed : sideOf 137 1 < 0 ∧ 0 < sideOf 138 1 := by
  simp only [sideOf, quadA_receipt, quadB_receipt, quadC_receipt]
  decide

/-! ## THE MEDIANT WALK

Two names straddling the root; the mediant of the pair is a new name; the side
test says which end it replaces.  `sideOf m < 0` raises the low end, else the
high end comes down.  Legs only, integers only, and the root is never touched
-- only cornered. -/

def mediantWalk : Nat -> (Nat × Nat) -> (Nat × Nat) -> (Nat × Nat) × (Nat × Nat)
  | 0, lo, hi => (lo, hi)
  | n + 1, lo, hi =>
      if sideOf (lo.1 + hi.1) (lo.2 + hi.2) < 0
      then mediantWalk n (lo.1 + hi.1, lo.2 + hi.2) hi
      else mediantWalk n lo (lo.1 + hi.1, lo.2 + hi.2)

/-- THE BRACKET NEVER LOSES THE ROOT.  If the ends straddle going in, they
straddle coming out, for ANY number of steps: each mediant replaces exactly
the end whose side it shares.  Induction and the sign, nothing else. -/
theorem the_bracket_never_loses_the_root (n : Nat) (lo hi : Nat × Nat)
    (hlo : sideOf lo.1 lo.2 < 0) (hhi : 0 ≤ sideOf hi.1 hi.2) :
    sideOf (mediantWalk n lo hi).1.1 (mediantWalk n lo hi).1.2 < 0
      ∧ 0 ≤ sideOf (mediantWalk n lo hi).2.1 (mediantWalk n lo hi).2.2 := by
  induction n generalizing lo hi with
  | zero => exact ⟨hlo, hhi⟩
  | succ n ih =>
      by_cases h : sideOf (lo.1 + hi.1) (lo.2 + hi.2) < 0
      · simp only [mediantWalk]
        rw [if_pos h]
        exact ih _ _ h hhi
      · simp only [mediantWalk]
        rw [if_neg h]
        refine ih _ _ hlo ?_
        show 0 ≤ sideOf (lo.1 + hi.1) (lo.2 + hi.2)
        omega

/-- THE BRACKET, at two hundred steps of the walk. -/
def theBracket : (Nat × Nat) × (Nat × Nat) := mediantWalk 200 (137, 1) (138, 1)

/-- The bracket IS the walk, by name alone -- one rfl, stated without
projections, so nothing below ever asks the elaborator to run two hundred
steps just to connect a name to its definition. -/
theorem theBracket_spec : theBracket = mediantWalk 200 (137, 1) (138, 1) := rfl

-- SEAL THE READING.  Nothing below may REDUCE the bracket -- the quad
-- coefficients are earned in unary (quadC is 1889568 successors), so any
-- defeq that whnf's the walk detonates.  Every fact about the bracket goes
-- through `theBracket_spec` and the general walk lemmas; the reading itself
-- stays a black box, which is the honest posture anyway -- you get the digits,
-- not the machinery.  (`#eval` is untouched: it runs compiled code.)
attribute [irreducible] theBracket

/-- And it still straddles: the general theorem, applied to the actual walk. -/
theorem the_bracket_straddles :
    sideOf theBracket.1.1 theBracket.1.2 < 0
      ∧ 0 ≤ sideOf theBracket.2.1 theBracket.2.2 := by
  rw [theBracket_spec]
  exact the_bracket_never_loses_the_root 200 (137, 1) (138, 1)
    the_root_is_enclosed.1 (Int.le_of_lt the_root_is_enclosed.2)

/-! ### THE BRACKET NARROWS -- convergence, stated without a limit

Containment above says the root never escapes.  It does not say the walk gets
anywhere.  These say it does, and they say it in whole numbers: the two ends
keep a determinant of exactly ONE, and their denominators grow by at least one
per step.  A gap of one over a growing product is a width going to nothing, and
no real number was borrowed to say so. -/

/-- The two ends' determinant: `hi.1*lo.2 - lo.1*hi.2`.  For a straddling pair
of the Stern-Brocot kind this is the numerator of the width. -/
def gapOf (lo hi : Nat × Nat) : Nat := hi.1 * lo.2 - lo.1 * hi.2

theorem the_mediant_keeps_the_gap_below (lo hi : Nat × Nat) :
    gapOf (lo.1 + hi.1, lo.2 + hi.2) hi = gapOf lo hi := by
  simp [gapOf, Nat.add_mul, Nat.mul_add]; omega

theorem the_mediant_keeps_the_gap_above (lo hi : Nat × Nat) :
    gapOf lo (lo.1 + hi.1, lo.2 + hi.2) = gapOf lo hi := by
  simp [gapOf, Nat.add_mul, Nat.mul_add]; omega

/-- THE WALK NEVER CHANGES THE GAP.  Whichever end the mediant replaces, the
determinant is the one it came in with -- for any number of steps.  The
numerator of the width is an invariant of the walk. -/
theorem the_walk_keeps_the_gap (n : Nat) (lo hi : Nat × Nat) :
    gapOf (mediantWalk n lo hi).1 (mediantWalk n lo hi).2 = gapOf lo hi := by
  induction n generalizing lo hi with
  | zero => rfl
  | succ n ih =>
      by_cases h : sideOf (lo.1 + hi.1) (lo.2 + hi.2) < 0
      · simp only [mediantWalk]; rw [if_pos h, ih, the_mediant_keeps_the_gap_below]
      · simp only [mediantWalk]; rw [if_neg h, ih, the_mediant_keeps_the_gap_above]

/-- AND THE DENOMINATORS GROW, at least one per step: the replaced end takes on
the SUM of the two denominators, so the pair's total climbs by whichever end
survived.  No step is free and no step is wasted. -/
theorem the_walk_grows_the_denominators : ∀ (n : Nat) (lo hi : Nat × Nat),
    1 ≤ lo.2 -> 1 ≤ hi.2 ->
    lo.2 + hi.2 + n ≤ (mediantWalk n lo hi).1.2 + (mediantWalk n lo hi).2.2
  | 0, lo, hi, _, _ => by simp [mediantWalk]
  | n+1, lo, hi, h, h' => by
      by_cases hs : sideOf (lo.1 + hi.1) (lo.2 + hi.2) < 0
      · simp only [mediantWalk]; rw [if_pos hs]
        have := the_walk_grows_the_denominators n (lo.1+hi.1, lo.2+hi.2) hi (by simp; omega) h'
        simp at this ⊢; omega
      · simp only [mediantWalk]; rw [if_neg hs]
        have := the_walk_grows_the_denominators n lo (lo.1+hi.1, lo.2+hi.2) h (by simp; omega)
        simp at this ⊢; omega

/-- THE ACTUAL WALK: gap exactly one, after two hundred steps. -/
theorem the_bracket_gap_is_one : gapOf theBracket.1 theBracket.2 = 1 := by
  rw [theBracket_spec, the_walk_keeps_the_gap]; decide

/-- AND ITS DENOMINATORS HAVE CLIMBED TO AT LEAST TWO HUNDRED AND TWO.  Put the
two together: a width whose numerator is one and whose denominator is a product
of numbers this large.  That is what the reading's digits are made of, and it is
the whole convergence claim -- in naturals, decided, no analysis borrowed. -/
theorem the_bracket_denominators_have_grown :
    202 ≤ theBracket.1.2 + theBracket.2.2 := by
  have := the_walk_grows_the_denominators 200 (137,1) (138,1) (by decide) (by decide)
  rw [theBracket_spec]
  exact this

/-! ## THE DECIMAL

Long division of the bracket's low end, to `k` places, as one scaled natural.
The receipt is the division identity itself: the printed digits times the
denominator land at or under the numerator, and one more digit overshoots. -/

/-- The low end of a bracket, long-divided to `k` decimal places. -/
def decimalOfBracket (pq : Nat × Nat) (k : Nat) : Nat := pq.1 * 10 ^ k / pq.2

/-- THE DIGITS ARE THE LOW END, to `k` places, for any bracket with a real
denominator.  This is long division's own receipt, stated once for all. -/
theorem the_digits_are_the_low_end (pq : Nat × Nat) (k : Nat) (hq : 0 < pq.2) :
    decimalOfBracket pq k * pq.2 ≤ pq.1 * 10 ^ k
      ∧ pq.1 * 10 ^ k < (decimalOfBracket pq k + 1) * pq.2 :=
  ⟨Nat.div_mul_le_self _ _, (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)⟩

/-- THE NUMBER.  The bracket's low end, twelve places out. -/
def theDecimal : Nat := decimalOfBracket theBracket.1 12

/-- THE DENOMINATORS STAY REAL.  Positivity survives the walk, by the same
induction as everything else here -- so nobody has to evaluate two hundred
steps in the kernel just to know the bracket has a bottom. -/
theorem the_walk_keeps_denominators_positive (n : Nat) (lo hi : Nat × Nat)
    (h : 0 < lo.2) (h' : 0 < hi.2) :
    0 < (mediantWalk n lo hi).1.2 ∧ 0 < (mediantWalk n lo hi).2.2 := by
  induction n generalizing lo hi with
  | zero => exact ⟨h, h'⟩
  | succ n ih =>
      by_cases hs : sideOf (lo.1 + hi.1) (lo.2 + hi.2) < 0
      · simp only [mediantWalk]; rw [if_pos hs]; exact ih _ _ (by simp; omega) h'
      · simp only [mediantWalk]; rw [if_neg hs]; exact ih _ _ h (by simp; omega)

/-- And the printed digits agree with the bracket, by the receipt above.
Stated on `decimalOfBracket theBracket.1 12` -- which IS `theDecimal` by
definition -- so the proof is a purely SYNTACTIC application of the general
lemma.  Naming `theDecimal` in the statement instead would force the elaborator
to unfold it across the bracket to relate the two, reducing the walk and firing
`quadC` in unary.  The bent card stays wrapped; the seam is never crossed. -/
theorem the_printed_digits_agree :
    decimalOfBracket theBracket.1 12 * theBracket.1.2 ≤ theBracket.1.1 * 10 ^ 12
      ∧ theBracket.1.1 * 10 ^ 12 < (decimalOfBracket theBracket.1 12 + 1) * theBracket.1.2 := by
  have hq : 0 < theBracket.1.2 := by
    rw [theBracket_spec]
    exact (the_walk_keeps_denominators_positive 200 (137,1) (138,1)
      (by decide) (by decide)).1
  exact the_digits_are_the_low_end theBracket.1 12 hq

/-! ## THE OLD d*-ROUTE, RETIRED WITH ITS ACCOUNTS SETTLED

The old route reached this number through `d* = sqrt(C*T)` -- the square root
of ninety, the invariant of the counted cards, taken by `floorSqrt`.  That
root is DELETED from this read path: nothing above forms it, nothing imports
it, and the walk reads signs only.

It is not disowned; it is PROVED EQUIVALENT.  Complete the square on the
quadratic and the identity below falls out: thirteen times the side test is a
leg squared, minus ninety times a leg squared.  The old route's root is the
right-hand side of an identity the new route never has to cross -- `sideOf`'s
sign IS the side of `sqrt(90)` taken at the transformed legs, which is why the
two routes could never have disagreed.  The hypotenuse retires; the legs keep
the books. -/

/-- The legs of the identity are the cards themselves: `T*(C-T)`, `C*R^2`,
`C*T`, and `R^2`, receipted together. -/
theorem the_legs_are_the_cards :
    theTarget * (theCoupling - theTarget) = 65
      ∧ theCoupling * theRadius * theRadius = 5832
      ∧ theCoupling * theTarget = 90
      ∧ theRadius * theRadius = 324 := by decide

/-- THE OLD ROUTE AGREES WITH THE NEW ROOT.  The completed square: for every
name `(p, q)` whatsoever, `13 * sideOf` equals the d*-leg squared minus ninety
times the radius-leg squared.  No root is formed on either side. -/
theorem the_old_route_agrees_with_the_new_root (p q : Int) :
    13 * (325 * (p * p) - 58320 * (p * q) + 1889568 * (q * q))
      = (65 * p - 5832 * q) * (65 * p - 5832 * q) - 90 * ((324 * q) * (324 * q)) := by
  -- two rearrangements `omega` cannot cross on its own: the doubled cross term,
  -- and the two q-squared monomials collecting into one
  have h1 : p * (q * 758160) = 2 * (p * (q * 379080)) := by
    have h : (758160 : Int) = 2 * 379080 := by decide
    rw [h]
    set_option linter.unusedSimpArgs false in
    simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  have h2 : q * (q * 24564384) + q * (q * 9447840) = q * (q * (34012224 : Int)) := by
    set_option linter.unusedSimpArgs false in
    simp [← Int.mul_add]
  set_option linter.unusedSimpArgs false in
  simp [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.mul_comm,
        Int.mul_left_comm, Int.mul_assoc]
  omega

/-! ## THE READINGS -- printed last, asserted never -/


/-! ## THE LEDGER -/


/-! ### THE READOUT.  Two lines here, two in Episode 11, and nothing else in the
whole build.  This is the LOW end of the bracket to twenty-four places, and the
census of the definition that spells it. -/

def padLeft (n k : Nat) : String :=
  let d := Nat.toDigits 10 n
  String.ofList (List.replicate (k - d.length) '0' ++ d)

def theDecimalLow : Nat := decimalOfBracket theBracket.1 24

end Measurement

#eval s!"alpha = {Measurement.theDecimalLow / 10 ^ 24}.{Measurement.padLeft (Measurement.theDecimalLow % 10 ^ 24) 24}"
#print axioms Measurement.theDecimalLow
