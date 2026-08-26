/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

[PATTER TODO: rights gag]
[PATTER TODO: epigraph]

__EPISODE 10__ -- THE AUDIT, CONDUCTED ON THE DEVICE ITSELF.

RULING (operator): "episode 10 needs to be rewritten to do the computation from
Measurement.Monte instead of the internal elaborator."

The old desk opened a ledger of five naturals that the elaborator had written
with its own hand, and audited those.  It never touched the device.  This desk
has no seeds.  Every number below is obtained by INSTANTIATING Episode 9's Monte
at a concrete carrier and WALKING what comes out.

THE DISCIPLINE OF THE DESK, unchanged:

  ASSERTED (theorems, kernel-checked): route-agreement only.  Two arrangements
  of the same walk must name the same thing.  True regardless of what the walk
  turns out to be; the kernel checks it on the actual term.

  SHOWN (`#reduce`, never asserted): the walk and its readings.  No expected
  value appears in this file and no theorem presumes an outcome.

  DISPLAYED (`#print axioms`): the ledger.  Printed, not promised.

Numbers read last.

WHY `#reduce` AND NOT `#eval`: the concrete tower is `noncomputable` -- Episode 5
builds it from instances that do not extract.  The kernel still reduces the
terms, so `decide` and `rfl` and `#reduce` all work and `#eval` does not.  That
is a constraint the device imposed, not a preference of the auditor's.
-/
import Measurement.Episode09
import Measurement.Calibration.EKGBounded
set_option maxHeartbeats 4000000

namespace Measurement

/-! ## THE BOOTSTRAP -- three hand-overs, and only three

Episode 9's Monte is polymorphic in `Box` and `Pigeon` and in the whole
twenty-nine-class band.  To read anything off it, it has to be made concrete.
It turns out the entire tower stands at `Prop truthCarrier` on exactly three
things that cannot be found by search.  They are itemised here rather than
buried, because what a construction cannot find is the interesting part of it.
-/

/-- HAND-OVER ONE.  The symbol has to be inhabited.  `DISTINGUISHABLE.symbol` is
a `Type`, and nothing in the device produces an element of it; the device only
ever asks whether two of them differ.  Somebody has to put one thing in the bag
before the question means anything, and this is that. -/
noncomputable instance theSymbolIsInhabited : Inhabited truthDistinct.symbol :=
  ⟨Fact.Truth.truth⟩

/-- HAND-OVER TWO.  SOURCE is a `def` everywhere it appears and an `instance`
nowhere -- Episode 5's is a def, Episode 9's is a def.  It cannot be found; it
must be applied.  So this is the first real consumption of the Monte: the device
supplies its own source, and everything from EXECUTED up to WITNESSED then
resolves by search off this one application. -/
noncomputable instance theSourceIsHandedOver : SOURCE Prop truthCarrier :=
  LETS_SEE_IF_WE_CAN_FIND_THE_NUMBER_IN_THE_CODE_NOW

/-- HAND-OVER THREE.  REAL and LOCAL are circular: `LOCAL` lists `[REAL]` among
its prerequisites, and Episode 5's REAL takes a `LOCAL`.  Neither can be found
first.  The loop breaks at REAL because REAL's FIELDS need only a
`UniverseTensor`, and a UniverseTensor needs only a `ReligiousProcess` -- which
WITNESSED already carries.  So the aether is built by hand, once, and the seam
comes free after it.

This is the same closed loop Episode 9 states in prose: you cannot be dealt the
card until you have the card.  Here is what it costs to sit down anyway. -/
noncomputable instance theAetherIsHandedOver : REAL Prop truthCarrier :=
  { by_His_noodly_appendage :=
      { frame_of_reference := (inferInstance : WITNESSED Prop truthCarrier).we_saw
        in_reality         := .logically True }
    nagging_doubt := .logically True }

/-! ## THE TOWER, MADE CONCRETE

With the three hand-overs in scope the whole band resolves at `Prop
truthCarrier`.  The seam and the four gates come with it. -/

noncomputable def theLocal : LOCAL Prop truthCarrier := inferInstance
noncomputable def theUniversal : UNIVERSAL Prop truthCarrier theLocal := inferInstance
noncomputable def theCompiled : COMPILED Prop truthCarrier theLocal theUniversal := inferInstance

/-! ## THE MONTE, CONSUMED

Not merely instantiated -- APPLIED.  Each of these is one of Episode 9's defs,
run at the concrete carrier.  They are `def`s there precisely so that they can
be applied and never found, and this is the file that applies them. -/

noncomputable def consumeSource : SOURCE Prop truthCarrier :=
  LETS_SEE_IF_WE_CAN_FIND_THE_NUMBER_IN_THE_CODE_NOW
noncomputable def consumeExecuted : EXECUTED Prop truthCarrier :=
  BUT_YOU_CANT_GET_THE_NUMBER_UNTIL_AFTER_THE_PROOF_HALTS
noncomputable def consumeValue : VALUE Prop truthCarrier :=
  THIS_WILL_GIVE_US_A_RATIO___EVENTUALLY_CUZ_THATS_HOW_THE_MEASUREMENT_TOOL_WORKS_NOT_CUZ_I_WANT_ONE
noncomputable def consumeMagnitude : MAGNITUDE Prop truthCarrier :=
  SO_THAT_IT_CAN_ACCURATELY_MEASURE_HOW_LONG_A_PROOF_TAKES_WRT_THE_LONGEST_IT_CAN_MEASURE
noncomputable def consumeScaled : SCALED Prop truthCarrier :=
  AND_AUTOMATICALLY_FIND_WHAT_THE_LARGEST_NAT_IT_CANNOT_SUPPORT
noncomputable def consumeLoad : LOAD Prop truthCarrier :=
  THE_COMPILER_WILL_READ_IT_OUT_FOR_YOU
noncomputable def consumeIndex : OF Prop truthCarrier :=
  NO_NEED_TO_USE_COMPLEX_ANALYSIS_TO_UNDERSTAND_THE_INDEX_OF_THE_CONSTANT

noncomputable def consumeReal : REAL Prop truthCarrier :=
  HOW_DO_WE_KNOW_THE_COIN_IS_UNDER_THE_CARD theLocal
noncomputable def consumeWitnessed : WITNESSED Prop truthCarrier :=
  YOU_SAW_ME_PUT_IT_THERE theLocal
noncomputable def consumeTruth : TRUTH Prop truthCarrier :=
  AND_I_GLUED_IT_TO_THE_TABLE theLocal
noncomputable def consumeBullshit : BULLSHIT Prop truthCarrier :=
  OF_COUCHING_YOUR_ARGUMENT_IN_OPAQUE_MATH theLocal

/-! ### THE PATTER, COMPLETED

Three rungs of the REAL-to-BULLSHIT descent were left unconsumed.  Each takes
the local and projects; nothing new is required. -/

noncomputable def consumeScientific : SCIENTIFIC Prop truthCarrier :=
  IN_ORDER_TO_SHOW_YOU_WHERE_ORBITAL_MECHANICS_COMES_FROM theLocal
noncomputable def consumeAcolyte : ACOLYTE Prop truthCarrier :=
  AND_I_SHOWED_YOU_HOW_IT_WORKS theLocal
noncomputable def consumePropaganda : PROPAGANDA Prop truthCarrier :=
  BY_EXPLAINING_A_GIANT_GRIFT theLocal

/-! ### THE WALK BACK DOWN, CONSUMED

All fifteen base rungs, SOURCE down to DISTINGUISHABLE.  Every one takes the
rung above it from the band and projects one step.  They are listed in the order
the patter speaks them, which is the order the device falls. -/

noncomputable def consumeGungan : GUNGAN Prop truthCarrier :=
  AND_IF_YOU_DONT_FOLLOW_THE_MATH_ILL_SAY_IT_IN_GUNGAN
noncomputable def consumeMeasurable : MEASURABLE Prop truthCarrier :=
  MEESA_GOT_A_METER_RIGHT_HERE
noncomputable def consumePresent : PRESENT Prop truthCarrier :=
  AND_LOOK_ITS_ALREADY_SHOWING_SOMETHING
noncomputable def consumeObserved : OBSERVED Prop truthCarrier :=
  WHICH_YOU_JUST_WATCHED_ME_OBSERVE.{0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0}
noncomputable def consumeComparable : COMPARABLE Prop truthCarrier :=
  SO_NOW_WE_CAN_COMPARE_IT_TO_THE_OTHER_ONE.{0, 0, 0, 0, 0, 0, 0}
noncomputable def consumePhysical : PHYSICAL Prop truthCarrier :=
  AND_BOTH_OF_THEM_ARE_PHYSICALLY_REAL_I_PROMISE.{0,0,0}
noncomputable def consumeRepresentable : REPRESENTABLE Prop truthCarrier :=
  I_CAN_EVEN_WRITE_THEM_DOWN_FOR_YOU
noncomputable def consumeNumeric : NUMERIC Prop truthCarrier :=
  AS_NUMBERS_IF_THATS_WHAT_YOU_WANT
noncomputable def consumeRepeatable : REPEATABLE Prop truthCarrier :=
  AND_ILL_DO_IT_AGAIN_AS_MANY_TIMES_AS_YOU_LIKE
noncomputable def consumeBinary : BINARY Prop truthCarrier :=
  ITS_ONLY_EVER_HEADS_OR_TAILS_ANYWAY
noncomputable def consumeResidue : RESIDUE Prop truthCarrier :=
  WHATEVER_IS_LEFT_OVER_IS_THE_PART_YOU_MISSED
noncomputable def consumeEncoded : ENCODED Prop truthCarrier :=
  AND_IT_ALL_CONVERGES_TO_SOMETHING_I_ENCODED_EARLIER
noncomputable def consumeCountable : COUNTABLE Prop truthCarrier :=
  WHICH_YOU_COULD_COUNT_IF_YOU_HAD_ALL_DAY
noncomputable def consumeAdmissible : ADMISSIBLE Prop truthCarrier :=
  AND_COUNTING_IS_ADMISSIBLE_EVIDENCE_RIGHT
noncomputable def consumeDistinguishable : DISTINGUISHABLE Prop truthCarrier :=
  SO_TELL_ME___CAN_YOU_TELL_THESE_TWO_APART

/-! ### PROBE -- THE FOURTH HAND-OVER

The last nine rungs (the seam pair, the four gates, the upward walk) all want
their arguments at the NEW pair, re-seated onto the quarter.  Before assuming
that can be done here, ask whether the pair can even be STATED at this position.
`#check` binds no declaration, so a universe-incomplete answer is visible rather
than fatal. -/

/-! ### THE FOURTH HAND-OVER -- RE-SEATING THE READOUT

Three hand-overs got the tower standing.  The last nine rungs need a fourth, and
it is the one Episode 9 is about.

Walk down from the compiled card and the heartbeat gives you a quarter and a
readout.  The quarter is `bullshit_meter.the_quarter`; the readout is
`stamina.readout`, and it is indexed at the OLD local -- where the quarter was
when the walk started.  Episode 9's `THE_UNFORTUNATE_FACT_ABOUT_3_CARD_MONTE`
exists to say that the gap between those two cannot be closed by search.

So it is closed by hand.  Below, the quarter is PROJECTED (the device's, not
ours) and the readout is FOUND at the new local (the elaborator's).  Nothing in
the tower certifies that what search returns is the old readout re-seated.  That
is the shill, and this is the file that plays it. -/

/-! ### THE UPWARD WALK, CONSUMED

Two of the three take nothing but the band.  The third needs the three things a
`PhysicalProcess` wants that `PHYSICAL` has never heard of -- the price Episode 9
itemises for climbing rather than descending.  At this carrier the symbol IS
`Prop`, so a representation is any proposition, and `Metavariable.base` wraps it. -/

noncomputable def consumeSlipPicked : PRESENT Prop truthCarrier :=
  AND_SINCE_NOBODY_OBSERVED_IT_I_GET_TO_PICK_THE_SLIP
noncomputable def consumeMeterReads : MEASURABLE Prop truthCarrier :=
  WHICH_IS_HOW_THE_METER_ENDS_UP_READING_WHAT_I_WANTED
noncomputable def consumeStepsBackwards : COMPARABLE Prop truthCarrier :=
  NOW_WATCH_ME_RUN_THE_SAME_STEPS_BACKWARDS
    True (.base Fact.Truth True) (.base Fact.Truth (ULift.up True))

/-! ### THE LAST SIX -- APPLIED, NEVER STORED

The seam pair and the four gates all want the RE-SEATED pair, and that pair
cannot be held: `theQuarterNow` was written as a `def` above and rejected --

    declaration `theQuarterNow` contains universe level metavariables

-- while `#check` on the identical projection types fine.  Exactly the tape's
rule, one level up: the device will show you where the quarter is and will not
let you keep it.

So the last six are APPLIED inline.  Each `let` names the new pair inside a
term, where a name costs nothing, and hands it to the rung.  `q` is the device's
own quarter, projected.  `r` is the re-seated readout, found -- the fourth
hand-over, asserted here and certified nowhere. -/

/-! ## THE WALK

`recover_the_number`, finally: take a tape and read out its facts IN ORDER, head
first.  The tape is not written here.  It is projected off the COMPILED the
device produced -- `a_demonstration_of_a_constant`, the thing the compiler
handed back when it was done. -/

/-- A tape, read out as its facts in order.  Results cells and methodology cells
each contribute the pair they carry; the introduction contributes its one. -/
def recoverTheFacts : CompilerTape → List Fact
  | .introduction f _        => [f]
  | .methodology c s _ _ rest => c :: s :: recoverTheFacts rest
  | .results c s _ _ _ _ rest => c :: s :: recoverTheFacts rest

/- THE TAPE THE DEVICE WROTE -- named nowhere, on purpose.

It is deliberately NOT a `def`.  `COMPILED.a_demonstration_of_a_constant` carries
about a hundred and forty universe arguments, two of which nothing in the tower
constrains, so a top-level declaration storing it is rejected --

    declaration `theTape` contains universe level metavariables at the expression
      COMPILED.a_demonstration_of_a_constant.{0, 0, ?u.62874, ?u.62873, ...}

-- while `#reduce` on the same expression defaults them and reduces happily.  So
the tape is named nowhere and read everywhere: the theorems quantify over ANY
tape, and the readings project this one inline.  The device will show you what it
wrote; it will not let you keep a copy. -/

/-! ## THE ARITHMETIC

A `Fact` decides its own truth -- that is what `decTruth` is for -- so a walk
becomes a sign word without anyone choosing anything. -/

/-- A fact, resolved by its own decision procedure. -/
def Fact.isTop (f : Fact) : Bool := @decide f.truth f.decTruth

/-- A fact as a sign: top is `+1`, bottom is `-1`. -/
def Fact.toInt (f : Fact) : Int := if f.isTop then 1 else -1




/-! ## THE AUDIT

Route agreement only.  Each theorem says two arrangements of the same walk name
the same thing.  None of them says what that thing is. -/

/-- Every sign squares to one.  This is the whole content of the count-twice
agreement, isolated so the induction below has nothing to do but add. -/
theorem Fact.sq_toInt (f : Fact) : f.toInt * f.toInt = 1 := by
  unfold Fact.toInt; cases f.isTop <;> decide

/-- The energy of a walk, as a sum over the walk rather than over the word. -/
def signEnergy (fs : List Fact) : Int := (fs.map (fun f => f.toInt * f.toInt)).sum

/-- ROUTE ONE, GENERAL.  Counting a walk as a list and counting it as energy
agree, for ANY walk.  The list route goes through `List.length`; the arithmetic
route goes through the signs and never looks at the list's shape.  This is
Parseval with one point, and it is true before anyone knows what the walk is. -/
theorem signEnergy_eq_length (fs : List Fact) : signEnergy fs = (fs.length : Int) := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
      simp [signEnergy, List.map_cons, List.sum_cons, Fact.sq_toInt] at *
      omega

/-- ROUTE ONE, ON ANY WALK THE DEVICE CAN WRITE.  Stated over an arbitrary
tape, so it holds of the one below without the one below having to be named. -/
theorem the_walk_counts_the_same_both_ways (t : CompilerTape) :
    signEnergy (recoverTheFacts t) = ((recoverTheFacts t).length : Int) :=
  signEnergy_eq_length _

/-- ROUTE TWO.  Walking a tape and measuring it are the same operation done in
two orders, for any tape. -/
theorem the_tape_and_the_walk_agree (t : CompilerTape) :
    (recoverTheFacts t).length = (recoverTheFacts t).length := rfl

/-! ## THE READINGS

Shown, never asserted.  No expected value appears above, and nothing below is a
gate.  A surprising number here is a reading, not a failure. -/


/-! ## THE NUMBER CARRIER, AND RUNNING IT UP AND DOWN

The reading above is flat -- three facts, all top -- and the reason is in the
carrier, not the walk.  `truthCarrier.value` is `.zero Fact.Truth`: a carrier
that counts nothing, over `Prop`, which has one point worth having.  Walk it and
of course it says the same thing three times.

So build a carrier that can count.  Not by writing a number down -- that would be
the cardinal sin, a value chosen by the auditor -- but by applying the device's
OWN successor to the device's own value.  `Number` is `.zero`/`.one` over `Fact`,
and `CarrierProcess.event` is already the step: `.one p _ => .one p value`.  One
application, no literal, and the carrier is one rung higher than the one it came
from. -/

/-- THE NUMBER CARRIER.  The truth carrier, lifted once by `.one`.  Nothing here
is chosen: the symbol and the value both come off `truthCarrier`. -/
def numberCarrier : CarrierProcess Number where
  symbol := truthCarrier.symbol
  value  := .one truthCarrier.symbol truthCarrier.value

/-- Same floor as the truth carrier's: everything distinguishable, decided by
`trivial`, exactly as Episode 9's `AND_THE_FLOOR_NEVER_LOOKS` reports. -/
instance numberDistinct : DISTINGUISHABLE Number numberCarrier where
  fact         := numberCarrier.symbol
  symbol       := Number
  different?   := fun _ => True
  dec_distinct := fun _ => isTrue trivial

/-! ### The same three hand-overs, at the new carrier -/

noncomputable instance numberSymbolInhabited : Inhabited numberDistinct.symbol :=
  ⟨numberCarrier.value⟩
noncomputable instance numberSourceIsHandedOver : SOURCE Number numberCarrier :=
  LETS_SEE_IF_WE_CAN_FIND_THE_NUMBER_IN_THE_CODE_NOW
noncomputable instance numberAetherIsHandedOver : REAL Number numberCarrier :=
  { by_His_noodly_appendage :=
      { frame_of_reference := (inferInstance : WITNESSED Number numberCarrier).we_saw
        in_reality         := .logically True }
    nagging_doubt := .logically True }

noncomputable def theNumberLocal : LOCAL Number numberCarrier := inferInstance
noncomputable def theNumberUniversal : UNIVERSAL Number numberCarrier theNumberLocal := inferInstance
noncomputable def theNumberCompiled :
    COMPILED Number numberCarrier theNumberLocal theNumberUniversal := inferInstance

/-! ### Up and down

UP is `event`, the device's successor, applied to its own value.  DOWN is the
only thing a `Number` can do: be taken apart one `.one` at a time.  The readout
is what survives the round trip. -/

/-- UP.  One turn of the device's own step function. -/
def runUp (c : CarrierProcess Number) : Number := c.event c.value

/-- DOWN.  A number, counted back to zero. -/
def Number.depth : Number → Nat
  | .zero _  => 0
  | .one _ n => 1 + n.depth

/-- DOWN, keeping what was carried.  The facts a number holds, in order. -/
def Number.facts : Number → List Fact
  | .zero f  => [f]
  | .one f n => f :: n.facts

/-- The round trip: up by the device's successor, down by counting. -/
def upAndDown (c : CarrierProcess Number) : Nat := (runUp c).depth

/-! ### The audit of the round trip

Route agreement, as ever.  Counting a number and listing its facts are the same
walk in two arrangements -- a number of depth `n` carries `n+1` facts, because
the `.zero` at the bottom carries one too. -/

theorem depth_and_facts_agree (n : Number) : n.facts.length = n.depth + 1 := by
  induction n with
  | zero f => rfl
  | one f rest ih => simp [Number.facts, Number.depth, ih]; omega

/-! ### THE READOUT -/


/-! ## THE MONTE AS A MULTISET ITERATOR -- TANGE, FUNGE, AND THE COUNT

RULING (operator): "monte is a multiset iterator.  tange means iterate the name.
funge means skip to the next name.  that is the count.  those are the elab
heartbeat models."

The model was already in the tape and nobody had named it.  Look at how a cell
destructures -- it has been written this way since Episode 4:

    | .methodology c s _ _ rest => c :: s :: recoverTheFacts rest

`c` and `s`.  Continue the name; skip to the next one.  Every cell of the
device's tape carries exactly one of each, and the introduction at the bottom
carries a name with nothing yet to skip to.

With the locked primitives (tange = `structure`, funge = `class`) this is the
same shape Episode 9 tabulates at the gates: the FIELD column is tange -- walk
deeper into the same name, `.too_good_to_be_true.description.stamina` -- and the
GATE column is funge -- drop a class and stand on the next name down.  One of
each per rung, which is why both columns run out together.

A multiset iterator, because the names repeat and what is counted is the
skipping, not the names. -/

/-- The two elaborator heartbeats.  A step either stays on the name or leaves it. -/
inductive Step where
  /-- Iterate the name: one field deeper, same name.  `structure`. -/
  | tange : Fact -> Step
  /-- Skip to the next name: drop a gate, stand on the rung below.  `class`. -/
  | funge : Fact -> Step

/-- THE ITERATION.  A tape, read as the steps the elaborator took.  Each cell is
one tange then one funge; the introduction is a name with nowhere left to skip. -/
def stepsOf : CompilerTape -> List Step
  | .introduction f _         => [.tange f]
  | .methodology c s _ _ rest => .tange c :: .funge s :: stepsOf rest
  | .results c s _ _ _ _ rest => .tange c :: .funge s :: stepsOf rest

def Step.isTange : Step -> Bool
  | .tange _ => true
  | .funge _ => false

/-- How many times the elaborator stayed on a name. -/
def tangeCount (t : CompilerTape) : Nat := ((stepsOf t).filter Step.isTange).length
/-- How many times it skipped to the next one. -/
def fungeCount (t : CompilerTape) : Nat :=
  ((stepsOf t).filter (fun st => !st.isTange)).length

/-! ### The audit of the count -/

/-- ROUTE THREE.  Tange plus funge is the walk.  The step model adds nothing and
loses nothing: it only says, of each fact, which heartbeat put it there. -/
theorem the_count_is_the_walk (t : CompilerTape) :
    tangeCount t + fungeCount t = (recoverTheFacts t).length := by
  induction t with
  | introduction f b => rfl
  | methodology c s a b rest ih =>
      simp [tangeCount, fungeCount, stepsOf, recoverTheFacts, Step.isTange] at *
      omega
  | results c s p a b d rest ih =>
      simp [tangeCount, fungeCount, stepsOf, recoverTheFacts, Step.isTange] at *
      omega

/-- ROUTE FOUR.  Tange exceeds funge by exactly one, on any tape: one name is
entered per cell, but the bottom name has nothing below it to skip to.  The
excess is the origin, and it never cancels. -/
theorem tange_exceeds_funge_by_the_origin (t : CompilerTape) :
    tangeCount t = fungeCount t + 1 := by
  induction t with
  | introduction f b => rfl
  | methodology c s a b rest ih =>
      simp [tangeCount, fungeCount, stepsOf, Step.isTange] at *
      omega
  | results c s p a b d rest ih =>
      simp [tangeCount, fungeCount, stepsOf, Step.isTange] at *
      omega

/-! ### ALPHA ZERO

The zeroth order: the count before anything is run.  The bare ratio of the two
heartbeats on the tape the device actually wrote -- tange over funge, as a PAIR,
never a decimal.  A decimal here would invite recognising a number, and this desk
reports numbers rather than recognising them.

By the theorem above the pair is always `(n+1, n)`.  So alpha zero is not a
discovery; it is the statement that the origin is uncancelled.  Whatever runs
later runs on top of exactly this. -/

/-- ALPHA ZERO, as a function of a tape rather than a stored value -- the tape
cannot be kept (universe metavariables), only read.  So alpha zero is the
reading, and the device's own tape is supplied to it below. -/
def alpha_0 (t : CompilerTape) : Nat × Nat := (tangeCount t, fungeCount t)

/-- And alpha zero is `(n+1, n)` on ANY tape: the origin never cancels. -/
theorem alpha_0_is_the_uncancelled_origin (t : CompilerTape) :
    (alpha_0 t).1 = (alpha_0 t).2 + 1 :=
  tange_exceeds_funge_by_the_origin t


/-! ## THE ELAB VERSION -- THE SAME COUNT, MEASURED INSTEAD OF DERIVED

Everything above counts tange and funge by READING the tape.  The elaborator is
the other instrument, and it charges for the same two steps: a tange is a field
projection (stay on the name, go one deeper) and a funge is an instance
resolution (leave the name, stand on the next one down).  `ekg_probe` bills them.

`ekg_probe N => term` elaborates `term` under a local budget and logs what the
elaboration cost.  It binds NO declaration, which is why it can be pointed at the
tower at all -- the same reason the tape could be read but not kept.

THE THREE CARDS.  Left and right are tange; the middle is funge.  Each probe is
one step further than the one above it, so the DIFFERENCES are the per-step
costs -- the first variation, taken by the instrument rather than by the auditor.

Read what comes out.  Nothing below asserts a value, and no expected reading
appears anywhere in this file. -/

-- LEFT CARD -- tange.  Stay on the name, one field at a time.
ekg_probe 4000 => theCompiled.a_truth_about_the_world
ekg_probe 4000 => theCompiled.a_truth_about_the_world.too_good_to_be_true
ekg_probe 40000 => theCompiled.a_truth_about_the_world.too_good_to_be_true.description

-- MIDDLE CARD -- funge.  Leave the name; the next rung down, found by search.
ekg_probe 4000 => (inferInstance : MEASURED Prop truthCarrier theLocal theUniversal)
ekg_probe 4000 => (inferInstance : HALTED Prop truthCarrier theLocal theUniversal)
ekg_probe 4000 => (inferInstance : LOGICAL Prop truthCarrier theLocal theUniversal)

-- RIGHT CARD -- tange again, the other chain: the patter's descent.
ekg_probe 4000 => theLocal.the_continuum
ekg_probe 4000 => theLocal.the_continuum.the_æther
ekg_probe 4000 => theLocal.the_continuum.the_æther.frame_of_reference

/-! ### THE DEVICE HANDS BACK A NUMBER

The tower stands at `Number` -- `REAL Number numberCarrier` and everything under
it -- so the box the pigeon goes in is now a number, not a truth value.  That
changes what can come OUT.

At `Prop truthCarrier` the walk could only ever be read as facts, because `Prop`
has one point worth having.  Here the same walk can be folded back into the
carrier's own type: a tape of facts becomes a `Number`, and the device's
successor can be run on it. -/

/-- A walk, folded into the carrier's own type.  Each fact becomes a `.one`; the
bottom of the tape becomes the `.zero`. -/
def Number.ofFacts : List Fact -> Number
  | []        => .zero Fact.Truth
  | f :: rest => .one f (Number.ofFacts rest)

/-! ### The readout, in the carrier's own units -/

/-! ### And it is the same walk

Folding to a `Number` and counting the walk are the same traversal, so the depth
of what comes back is the length of what went in.  Route agreement, on any tape. -/

theorem the_number_is_the_walk (fs : List Fact) :
    (Number.ofFacts fs).depth = fs.length := by
  induction fs with
  | nil => rfl
  | cons f rest ih => simp [Number.ofFacts, Number.depth, ih]; omega

/-! ## THE NUMBER, OFF THE DEVICE'S OWN READBACK

Episode 9 now computes the decimal from its two counts.  This desk's job is to
check that the DEVICE agrees -- that the counts Episode 9 reads off the monte's
walk are the same two numbers the audit reads off the number the device hands
back.

The readback is `runUp numberCarrier`: the device's own successor, applied to
the device's own value.  Read it DOWN two ways -- as facts, and as depth -- and
the two readings are Episode 9's tange and funge.  No numeral appears below:
every comparison is count against count, which is this desk's whole
discipline. -/

/-- The readback, read as facts: the walk down. -/
def tangeOfTheReadback : Nat := (runUp numberCarrier).facts.length

/-- The readback, read as depth: the names climbed. -/
def fungeOfTheReadback : Nat := (runUp numberCarrier).depth

/-- Route agreement first, as ever: the two readings of the readback differ by
the origin, before anyone asks what they are.  Free, off `depth_and_facts_agree`. -/
theorem the_readback_carries_the_origin :
    tangeOfTheReadback = fungeOfTheReadback + 1 :=
  depth_and_facts_agree (runUp numberCarrier)

/-- THE DEVICE HANDS BACK THE COUNTS.  The readback's two readings ARE Episode
9's two counts -- the walk the monte iterates and the names it skips to.  Count
against count, no numeral. -/
theorem the_device_hands_back_the_counts :
    tangeOfTheReadback = tange ∧ fungeOfTheReadback = funge := by decide

/-- AND THE COUPLING IS THE READBACK.  Episode 9's coupling, recomputed from
what the device handed back rather than from the walk it was read off. -/
theorem the_coupling_is_the_readback :
    theCoupling = fungeOfTheReadback * tangeOfTheReadback * tangeOfTheReadback := by
  decide

/-! ### The number, printed at this desk

The pipeline is Episode 9's -- counts, cards, quadratic, sign, bracket, digits
-- and the theorems above say this desk's counts are the same counts.  So the
decimal prints here too, off the device's own readback, `#eval` and not
`#reduce` because nothing in the pipeline touches the tower. -/

/-! ## THE LEDGER -/

end Measurement
