/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

[PATTER TODO: masthead -- Episode 9, the published artifact]
-/
import Measurement.Episode8


set_option maxHeartbeats 4000000   -- the old Episode 9 had this; the new one lost it

namespace Measurement
universe i

section Monte

-- THE TELESCOPE, ONCE. Elaborated at this command, then instantiated per
-- declaration instead of re-formed inside every signature.
variable
    {Box: Type i}
    {Pigeon: CarrierProcess Box}
    [DISTINGUISHABLE Box Pigeon] [ADMISSIBLE Box Pigeon] [COUNTABLE Box Pigeon]
    [ENCODED Box Pigeon] [RESIDUE Box Pigeon] [BINARY Box Pigeon]
    [REPEATABLE Box Pigeon] [NUMERIC Box Pigeon] [REPRESENTABLE Box Pigeon]
    [PHYSICAL Box Pigeon] [COMPARABLE Box Pigeon] [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon] [MEASURABLE Box Pigeon] [GUNGAN Box Pigeon]
    [SOURCE Box Pigeon] [EXECUTED Box Pigeon] [VALUE Box Pigeon]
    [MAGNITUDE Box Pigeon] [SCALED Box Pigeon] [LOAD Box Pigeon]
    [INDEXOFANT Box Pigeon] [BULLSHIT Box Pigeon] [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon] [SCIENTIFIC Box Pigeon] [TRUTH Box Pigeon]
    [WITNESSED Box Pigeon] [REAL Box Pigeon]
    -- the seam pair, bound ONCE and named
    {downhill: LOCAL Box Pigeon}
    {extremum: UNIVERSAL Box Pigeon downhill}
    [LOGICAL Box Pigeon downhill extremum] [HALTED Box Pigeon downhill extremum]
    [MEASURED Box Pigeon downhill extremum] [COMPILED Box Pigeon downhill extremum]
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
      InitiationProcess   .ethos               ->  CrusadeProcess
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
  { discovering := principia.the_continuum.the_æther.frame_of_reference.we_experience.shows_us
    invariant   := principia.the_continuum.the_æther.frame_of_reference.we_experience.shows_us.invariant }

-- ACOLYTE.  Deeper again: who taught the learner.
def AND_I_SHOWED_YOU_HOW_IT_WORKS
    (principia : LOCAL Box Pigeon)
    : ACOLYTE Box Pigeon :=
  { euclid := principia.the_continuum.the_æther.frame_of_reference.we_experience.shows_us.teaching }

-- PROPAGANDA.  Deeper again: the ethos the teaching rests on.
def BY_EXPLAINING_A_GIANT_GRIFT
    (principia : LOCAL Box Pigeon)
    : PROPAGANDA Box Pigeon :=
  { insinuates := principia.the_continuum.the_æther.frame_of_reference.we_experience.shows_us.teaching.ethos }

-- BULLSHIT.  The floor of the patter, and the longest projection in the file.
-- One more `.` past this is `dunking_contest`, and one past THAT is a guess.
def OF_COUCHING_YOUR_ARGUMENT_IN_OPAQUE_MATH
    (principia : LOCAL Box Pigeon)
    : BULLSHIT Box Pigeon :=
  { arm_wave_process :=
      principia.the_continuum.the_æther.frame_of_reference.we_experience.shows_us.teaching.ethos.to_pwn_n00bz }

-- THE NEXT RUNG.  Same shape, one turn later: the card, its re-seated readout,
-- the three gates at the new pair, and the card that comes out the far side.
variable {a_bent_card : COMPILED Box Pigeon downhill extremum}
variable {the_shuffled_readout : UNIVERSAL Box Pigeon
    a_bent_card.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter}
variable
    [LOGICAL Box Pigeon
        a_bent_card.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter
        the_shuffled_readout]
    [HALTED Box Pigeon
        a_bent_card.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter
        the_shuffled_readout]
    [MEASURED Box Pigeon
        a_bent_card.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter
        the_shuffled_readout]
variable {the_bent_card : COMPILED Box Pigeon
    a_bent_card.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_quarter
    the_shuffled_readout}

end Monte
end Measurement
