/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that the stories we tell ourselves are just expressions of ideas, not the ideas themselves._

(c) 2026

__EPISODE 5__: _THE ANTE_

-/

-- Have I convinced you yet of the dangers of using other peoples imports?
import Measurement.Episode04
import Measurement.Calibration.LeanCalibration
set_option allowUnsafeReducibility true


-- Use this at your own risk.  If you accidentally program something that requires the violation of the halting problem to represent, you might find
-- yourself waiting a few minutes for the compiler as it slowly enumerates ALL of computation to find your program.

-- -O2 is for suckers, as my mentor Russ Hewett would say. This thing enumerates computation and finds the one that we want and copies the input into
-- the output, sorted by how fast they are. That's how it compiles!  Kolmogorov eat your heart out, I put a ring on it!

-- Literally, algebraic ring incoming.
namespace Measurement

universe i -- This is merely a subscript. Variant with Roman letters. a=1 b=2 c=3...


@[reducible]
class UNIVERSAL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [a_nowtrino: DISTINGUISHABLE Box Pigeon]   [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (quartic: LOCAL Box Pigeon) ---| See the ODE above. This is a quadratic of a quadratic. Or a linear of a cubic. Either way.
  where
  the_train_of_thought: CalculusProcess Box Pigeon quartic ---| I do believe we have arrived at the next stop. A universal calculus model.
  once_around: SpaceTimePath
  twice_around: SpaceTimePath

  -- let's ask the compiler to hold the quarter we glued to the table.
  lake_build: SpaceTimePath → SpaceTimePath → Prop := fun _ _ => the_train_of_thought.uptown_or_downtown = a_nowtrino.fact


-- We are just spinning a yarn about commuter rail. A massless yarn that appears to spin twice.
-- The THEORY OF YARNS: WE ASSUME TRAIN STATION ID NUMBERS UPTOWN > TRAIN STAION ID NUMBERS DOWNTOWN.
inductive YarnTheory
|stokes: Fact → SpaceTimePath → Prop → YarnTheory
|fibers: Fact → SpaceTimePath → SpaceTimePath → Prop → Prop → YarnTheory → YarnTheory
|fabric: Fact → Fact → SpaceTimePath → SpaceTimePath → SpaceTimePath → Prop → Prop → Prop → YarnTheory → YarnTheory → YarnTheory

namespace YarnTheory
def le : YarnTheory → YarnTheory → Prop
  | .stokes station_1 route_a station_2,     .stokes station_a route_1 station_b => -- Flop:
                                                            station_1 = station_a ∧
                                                            (route_a ≤ route_1) ∧
                                                            station_2 = station_b

  | .stokes station_1 route_a station_2,     .fibers station_a route_1a route_1b station_1a station_1b _ => -- Flop:
                                                            station_1 = station_a ∧
                                                            (route_a ≤ route_1a ∨ route_a ≤ route_1b) ∧
                                                            (station_2 = station_1a ∨ station_2 = station_1b)

  -- The Maine Railroad, also called you can't get there from here. If I were to go there, I would not start here, I would start at station_b.
  | .stokes station_1 route_a station_2,     .fabric station_a station_b route_b1 route_b2 route_b3 station_b1 station_b2 station_b3 _ _ => -- Flop:
                                                            (station_1 = station_a ∨ station_1 = station_b) ∧
                                                            (route_a ≤ route_b1 ∨ route_a ≤ route_b2 ∨ route_a ≤ route_b3) ∧
                                                            (station_2 = station_b1 ∨ station_2 = station_b2 ∨ station_2 = station_b3)


  --
  | .fibers this_station _ _ route_in route_out _, .stokes destination _ main_line =>
                                                             this_station ≠ destination ∨ (route_in ≠ main_line ∧ route_out ≠ main_line)


  | .fibers this_station route_a route_b time_a time_b this_way, .fibers that_station route_1 route_2 time_1 time_2 that_way =>
                                                            ( this_station = that_station ∧
                                                              route_a ≤ route_1 ∧
                                                              route_b ≤ route_2 ∧
                                                              time_a = time_1 ∧
                                                              time_b = time_2 ∧
                                                              le this_way that_way ) ∨
                                                            le (.fibers this_station route_a route_b time_a time_b this_way) that_way

  | .fibers here zero_reading current_reading zero_value current_value the_current_computation,
    .fabric this that epsilon slip one EPSILON SLIP ONE no_response_yet response_happened =>
                                  ( (here = this ∨ here = that) ∧
                                    (zero_reading ≤ epsilon ∨ zero_reading ≤ slip) ∧
                                    (current_reading ≤ slip ∨ current_reading ≤ one) ∧
                                    (zero_value = EPSILON ∨ zero_value = SLIP) ∧ (current_value = SLIP ∨ current_value = ONE) ∧
                                    (le the_current_computation no_response_yet ∨ le the_current_computation response_happened)) ∨
                                  le (.fibers here zero_reading current_reading zero_value current_value the_current_computation) no_response_yet ∨
                                  le (.fibers here zero_reading current_reading zero_value current_value the_current_computation) response_happened

  | .fabric no_response response _ _ _ EPSILON SLIP ONE _ _, .stokes the_nowtrino _ the_value =>
                                                                              (the_nowtrino ≠ no_response ∧ the_nowtrino ≠ response) ∨
                                                                              (the_value ≠ EPSILON ∧ the_value ≠ SLIP ∧ the_value ≠ ONE)

  | .fabric no_response response epsilon slip one EPSILON SLIP ONE no_response_yet response_happened,
                                              .fibers here departing_station arriving_station departure_time arrival_time going_uptown =>
    ( (no_response = here ∨ response = here) ∧
      (epsilon ≤ departing_station ∨ slip ≤ departing_station) ∧
      (slip ≤ arriving_station ∨ one ≤ arriving_station) ∧
      (EPSILON = departure_time ∨ SLIP = departure_time) ∧
      (SLIP = arrival_time ∨ ONE = arrival_time) ∧
      (le no_response_yet going_uptown ∨ le response_happened going_uptown)) ∨
    le (.fabric no_response response epsilon slip one EPSILON SLIP ONE no_response_yet response_happened) going_uptown

                                                | .fabric no_response response epsilon slip one EPSILON SLIP ONE no_response_yet response_happened,
                                                  .fabric waiting_for_train waiting_on_train p4 p5 p6 q4 q5 q6 train_approaching train_departed =>
                                                  ( no_response = waiting_for_train ∧ response = waiting_on_train ∧
                                                    epsilon ≤ p4 ∧ slip ≤ p5 ∧ one ≤ p6 ∧
                                                    EPSILON = q4 ∧ SLIP = q5 ∧ ONE = q6 ∧
                                                    ( (le no_response_yet train_approaching ∧ le response_happened train_departed) ∨
                                                      (le no_response_yet train_departed ∧ le response_happened train_approaching))) ∨
                                                  le (.fabric no_response response epsilon slip one EPSILON SLIP ONE no_response_yet response_happened)
                                                                    train_approaching ∨
                                                  le (.fabric no_response response epsilon slip one EPSILON SLIP ONE no_response_yet response_happened)
                                                                    train_departed
termination_by _ ball_of_yarn => sizeOf ball_of_yarn
end YarnTheory
--| Can you escape the labyrinth now with your ball of yarn?

instance : LE YarnTheory where
  le := YarnTheory.le

@[reducible]
structure HeartbeatProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (train_schedule: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon train_schedule)
  where
  bullshit_meter: CalculusProcess Box Pigeon train_schedule --| We can model the bullshit meter's path as it _CONTINUES_ to move through _FIELDS_ of bullshit.
  time_spent_waiting: SpaceTimePath
  according_to_newton: YarnTheory
  readout: UNIVERSAL Box Pigeon train_schedule := commuter_pass


  weave? : YarnTheory → YarnTheory := fun yarn =>
     match yarn with
     |.stokes nonstop_train in_the_direction_of_destination uptown =>
          .fibers nonstop_train in_the_direction_of_destination time_spent_waiting uptown
                                                                      commuter_pass.the_train_of_thought.uptown_or_downtown.truth according_to_newton

     |.fibers itinerary now after this_station next_station is_bigger =>
              match itinerary.decTruth with
              | isTrue _ =>
                .fibers itinerary after time_spent_waiting next_station itinerary.truth is_bigger
              | isFalse _ =>
                .fabric itinerary nowtrino.fact now after time_spent_waiting this_station next_station (¬itinerary.truth) is_bigger according_to_newton

     |.fabric this_way that_way here halfway there stamped_here stamped_halfway stamped_there according_to_euler and_einstein =>
              match this_way.decTruth, that_way.decTruth with
              | isTrue _   , isTrue _    =>
                          .fabric this_way that_way here halfway there stamped_here stamped_halfway stamped_there according_to_euler and_einstein
              | isTrue _   , isFalse _   =>
                          .fabric nowtrino.fact that_way time_spent_waiting halfway there commuter_pass.the_train_of_thought.uptown_or_downtown.truth
                                            stamped_halfway (¬stamped_there) according_to_newton and_einstein
              | isFalse _, isTrue _  =>
                          .fibers that_way there time_spent_waiting stamped_there that_way.truth according_to_newton
              | isFalse _, isFalse _ =>
                          .fabric this_way that_way halfway there time_spent_waiting (¬stamped_halfway) (¬stamped_there) that_way.truth
                                                                                                              and_einstein according_to_newton


@[reducible]
class LOGICAL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (iterating_sequence: LOCAL Box Pigeon)
    (local_minimum: UNIVERSAL Box Pigeon iterating_sequence)
  where
  feelings: HeartbeatProcess Box Pigeon iterating_sequence local_minimum --------| No real heart, just a ball pumping.
  microsoft_basic: Calibration.EKG

  logical? : YarnTheory → YarnTheory → Prop := fun a b => a ≤ b --+ In the function, _a_ comes before _b_ in the order of the arguments.  That's it.
--                                                                | That's the whole idea, the _left_ thing comes _before_ the _right_ thing,
-- +--------------------------------------------------------------+ depending on if you are the dealer or the mark. Opposite sides and all. The
-- | compiler is standing on the side of the table where _left_ comes _first_. That's all this says. It is okay for _a_ to happen before _b_, but _b_
-- |cannot happen before _a_. This successfully finishes the logical argument that, in a PHYSICAL theory, a causal relationship is defined.

namespace ComputerProgram
def le
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (matrix_assemply: LOCAL Box Pigeon)
    (matrix_inversion: UNIVERSAL Box Pigeon matrix_assemply) -----------------+ A GENERIC MESH DATA STRUCTURE WITH GENERIC APPLICATIONS.  W.K. Cochran, Jr.
    [commodore64: LOGICAL Box Pigeon matrix_assemply matrix_inversion] --     | Ph.D thesis 2010. Been thinking about this for a long while now..
    : ComputerProgram → ComputerProgram → Prop
  | .boolean
        line10     -- 10 INPUT X                        :REM    THE NEXT OPCODE
        line20     -- 20 INPUT Y                        :REM    THE CURRENT MICROINSTRUCTION
        line30     -- 30 A = NOT (NOT X AND Y)          :REM    THE CURRENT MICROINSTRCUTION HAS THE RETURN VALUE OF THE NEXT OPCODE
        line40     -- 40 PRINT A                        :REM    DISPLAY THE CURRENT ASSEMBLY INSTRUCTION
        line50     -- 50 REM FIND THE LADY              :REM    THE FUNCTION _IS_ THE NEXT OPCODE, WHAT'S TO LOOK FOR?
        line60     -- 60 GOTO 10                        :REM    IP++
        program1,
    .boolean
        line70     -- 70 INPUT X                        :REM    THE NEXT OPCODE
        line80     -- 80 INPUT Y                        :REM    THE CURRENT MICROINSTRUCTION
        line90     -- 90 INPUT Z                        :REM    THE CLOCK
        line100    -- 100 A = NOT (NOT X AND Y) AND Z   :REM    THE CURRENT MICROINSTRUCTION HAS THE RETURN VALUE OF THE NEXT OPCODE AND CLOCK
        line110    -- 110 PRINT A                       :REM    DISPLAY THE CURRENT ASSEMBLY INSTRUCTION
        line120    -- 120 GOTO 70                       :REM    IP++
        program2 =>
    let before := ComputerProgram.boolean line10 line20 line30 line40  line50  line60  program1
    let after  := ComputerProgram.boolean line70 line80 line90 line100 line110 line120 program2
    commodore64.microsoft_basic.booleanProgram? before after
--|                                                ^     ^
--|                                                |     |
--|                            Unsynchronized |----+     +----| Synchronized
--|
--| Once we all agree on a clock mechanism, then we all use that same clock mechanism:  Newton's train of thought.  The idea is *YOU the READER* can
--| be _HERE_ now without *YOU the KNOWER* having been _THERE_ at some time in the past. Newton's train of thought is the simple idea that you can
--| index _TIME_ the same way Descartes indexed _SPACE_. The way we do this is using the same mechanism we use to record distance, with names being
--| replaced by opcodes that compute the value.  You know, monkey-patching and dynamic dispatch.


--| The opcodes of the device, unlike this description of the device, can _BRANCH_ and _LOOP_.  This is the _COMPARE OR BRANCH_ function
  | .transform
        line10     -- 10  GOSUB 50           :REM     We need to check the next instruction to see how we need to shape the answer so that the device
        line20     -- 20  A = X              :REM
        line30     -- 30  IF A THEN RETURN   :REM     IS THIS YOUR CARD?
        line40     -- 40  GOTO 10            :REM     IP++
        program1,
    .boolean
        line50     -- 50  INPUT X            :REM     We should probably define this to be a _routine_ of some kind. A _namespaced_ routine maybe?
        line60     -- 60  INPUT Y            :REM     PREFETCH
        line70     -- 70  INPUT Z            :REM     PREFETCH
        line80     -- 80  GOSUB 20           :REM     Ask the preceding opcode what it is expecting the answer to be
        line90     -- 90  PRINT A            :REM     PRINT THE OPCODE
        line100    -- 100 GOTO 10            :REM     IP++
        program2 =>
    let before := ComputerProgram.transform line10 line20 line30 line40 program1
    let after := ComputerProgram.boolean line50 line60 line70 line80 line90 line100 program2
    commodore64.microsoft_basic.transformBoolean? before after

--| This is the _SWAP NOT EQUAL_ function.
  | .boolean
        line10     -- 10  INPUT X
        line20     -- 20  INPUT Y
        line30     -- 30  INPUT Z
        line40     -- 40  GOSUB 70
        line50     -- 50  PRINT A
        line60     -- 60  GOTO 10
        program1,
    .transform
        line70     -- 70  A = NOT (NOT X AND Y)
        line80     -- 80  A = A AND Z
        line90     -- 90  IF A THEN RETURN
        line100    -- 100 GOTO 70
        program2 =>
        let before := ComputerProgram.boolean line10 line20 line30 line40 line50 line60 program1
        let after := ComputerProgram.transform line70 line80 line90 line100 program2
        commodore64.microsoft_basic.booleanTransform? before after
  | _, _ => False
end ComputerProgram

--| Once we have our model of a computer program with COMPARE AND BRANCH as well as SWAP NOT EQUAL, I think we are ready to

@[reducible]
structure ElaborationProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (linearization: LOCAL Box Pigeon)
    (differential_equation: UNIVERSAL Box Pigeon linearization)
    [LOGICAL Box Pigeon linearization differential_equation]
  where
  stamina: HeartbeatProcess Box Pigeon linearization differential_equation
  trilinos:  Calibration.EKG   ---------------------------| Sorry, Professor Gropp. I think my name is still on some #DEFINE WKC in trilinos.
  numerical_analysis:  ComputerProgram

  teraFLOPs: ComputerProgram → ComputerProgram := fun op_code =>
      match op_code with
      | .load subsystem operator_type =>
                  .transform subsystem (¬subsystem) operator_type (ULift.{i+1} Box) -- We can model a PetSc C struct as ¬subsystem inside the CPP of
                    (.load subsystem operator_type)                                 -- Trilinos (See AMP reports ORNL, 2010, Clarno, Philip, et al.)
                                                                                    -- Memory serves, the problem with PetSc didn't expose an interface
                                                                                    -- to ref-counted pointers. So, I created one just like here.
      | .transform detect value recursively apply_operator program =>
                  .boolean detect value nowtrino.fact.truth recursively apply_operator (ULift.{i+1} apply_operator) program

      | .boolean card1 card2 card3 left_card _ right_card three_card_monte_flop =>
                    if trilinos.outgrown? op_code then
                      .load (¬card1 ∧ ¬card2 ∧ card3) left_card
                    else
                      match nowtrino.fact.decTruth with
                        | isTrue _  => .boolean card2 card3 nowtrino.fact.truth left_card (ULift.{i+1} left_card) right_card three_card_monte_flop
                        | isFalse _ => .load (¬card1 ∧ ¬card2 ∧ card3) left_card




@[reducible] --                                                 | Now that we have demonstrated that our theory has a logical outcome: _A_ causes _B_,
class HALTED ---------------------------------------------------+ this is a good place to stop. ∎
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (convergence_criteria: LOCAL Box Pigeon)
    (conserved_value: UNIVERSAL Box Pigeon convergence_criteria)
    [LOGICAL Box Pigeon convergence_criteria conserved_value]
  where
  scientific_paper: ElaborationProcess Box Pigeon convergence_criteria conserved_value
--                                                          +------------------------------+ This is the palm. Make sure you slide this program
--                                                          |                              | out of the compile loop while the compiler is compiling
--                                                          V                              | so we can use it later.... After it is done..
  halted? : ComputerProgram → ComputerProgram → Prop := fun _ program =>  --+ NOOP LOOP?
    match program with --                                                   | NOP NOP NOP NOP .....
    | .load NOOP _              => NOOP  --           | The greatest trick the devil pulled is convincing the world he didn't exist.
    | .transform NOOP _ _ _ _   => NOOP  -------------+
    | .boolean NOOP _ _ _ _ _ _ => NOOP  --           | And just like that, the bug is gone...  Because the compile is over.


inductive Measurement
|origin: Fact → Number → Type i → Measurement
|distance_to: Fact → Number → Number → Type i → Type (i+1) → Measurement → Measurement
|speed: Fact → Number → Number → Number → Type i → Type (i+1) → Type i →  Measurement → Measurement → Measurement

namespace Measurement
def le : Measurement → Measurement → Prop := fun last_click next_click =>
  match last_click, next_click with
  | .origin this_way before _,                   .origin that_way after _            => (this_way = that_way) ∧ before ≤ after
  | .origin _    _      _,                       _                                   => True

  | .distance_to here _ before _ _ _,            .distance_to there _ after _ _ _    => (here = there) ∧ before ≤ after
  | .distance_to _    _ _      _ _ _,            _                                   => True

  | .speed at_x _ _ at_rest _ _ _ _ _ ,          .speed at_y _ _ in_motion _ _ _ _ _ => (at_x = at_y) ∧ at_rest ≤ in_motion

  | _ , .origin _ _ _           => False
  | _, .distance_to _ _ _ _ _ _ => False
end Measurement

instance : LE Measurement where
  le := Measurement.le

@[reducible]
structure LeanProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (attraction_process: LOCAL Box Pigeon)
    (gravity: UNIVERSAL Box Pigeon attraction_process)
    [LOGICAL Box Pigeon attraction_process gravity]
    [HALTED Box Pigeon attraction_process gravity]
  where
  description: ElaborationProcess Box Pigeon attraction_process gravity
  difference_between: Number
  in_heartbeats: Measurement
  saved_as_y: Type i


  superconverge? : Measurement → Measurement := fun x =>
    match x with
    | .origin constant times _                    => .distance_to constant times difference_between Box (ULift.{i+1} Box) in_heartbeats
    | .distance_to origin slope intercept _ _ is_the_formula_for_y =>
                                .speed origin slope intercept difference_between Box (ULift.{i+1} Box) saved_as_y is_the_formula_for_y in_heartbeats
    | .speed invariant _ now and_later _ _ _ _ is_the_derivative_of_y =>
                                .speed invariant now and_later difference_between Box (ULift.{i+1} Box) saved_as_y is_the_derivative_of_y in_heartbeats


@[reducible]
class MEASURED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (up: LOCAL Box Pigeon)
    (and_to_the_right: UNIVERSAL Box Pigeon up)
    [LOGICAL Box Pigeon up and_to_the_right]
    [HALTED Box Pigeon up and_to_the_right]
  where
  a_distance: LeanProcess Box Pigeon up and_to_the_right  ---| Don't *HATE* cuz all my charts are *UP* and *TO THE RIGHT*. Nnumber go up!

  bounded? : Measurement → Measurement → Prop := fun a b => a ≤ b


inductive CompilerTape where
  | introduction  : Fact → Type i → CompilerTape
  | methodology   : Fact → Fact → Type i → Type (i+1) → CompilerTape → CompilerTape
  | results       : Fact → Fact → Prop → Type i → Type (i+1) → Type (i+1) → CompilerTape → CompilerTape

namespace CompilerTape
def le : CompilerTape → CompilerTape → Prop := fun t1 t2 =>
  match t1, t2 with
  | .introduction _ _                          , _                                            => True
  | _                                          , .introduction _ _                            => False
  | .methodology general_idea _ _ _ _          , .methodology experimental_protocol _ _ _ _   => general_idea = experimental_protocol
  | _                                          , .methodology _ _ _ _ _                       => False
  | .methodology _ _ _ _ _                     , _                                            => True
  | .results stimulus no_response _ _ _ _ _    , .results try_again response _ _ _ _ _        => (stimulus = try_again) ∧ (no_response ≠ response)

-- Found a flop-flip to find bugs.

def lt : CompilerTape → CompilerTape → Prop := fun n1 n2 => le n1 n2 ∧ ¬ le n2 n1

end CompilerTape

instance : LE CompilerTape where
  le := CompilerTape.le
instance : LT CompilerTape where
  lt := CompilerTape.lt

@[reducible]
structure CompilerOutput
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (constant: LOCAL Box Pigeon)
    (ratio: UNIVERSAL Box Pigeon constant)
    [LOGICAL Box Pigeon constant ratio]
    [HALTED Box Pigeon constant ratio]
    [MEASURED Box Pigeon constant ratio]
  where
  too_good_to_be_true: LeanProcess Box Pigeon constant ratio
  preprint: CompilerTape

  emit?: CompilerTape → CompilerTape := fun does_not_matter =>
    match does_not_matter with
    | .introduction abstract lit_review   => .methodology abstract nowtrino.fact lit_review (ULift.{i+1, i} lit_review) preprint

                                      -- Does anyone use the julia side of jupyter? Or just the python terminal?
    | .methodology write sample in_python to_jupyter notebook => .results write sample nowtrino.fact.truth in_python to_jupyter
                                                                                                              (ULift.{i+1, i+1} to_jupyter) notebook

    | .results write sample _ in_python in_jupyter to_draw graphs_and_charts =>
          match write.decTruth,sample.decTruth with
          | isTrue _     , isTrue _    =>  .introduction Fact.Truth Box
          | isFalse _    , isFalse _   =>  .methodology Fact.Truth Fact.Truth in_python in_jupyter graphs_and_charts
          | isTrue _     , isFalse _   =>  .results write nowtrino.fact nowtrino.fact.truth  in_python in_jupyter to_draw graphs_and_charts
          | isFalse _    , isTrue _    =>  .results nowtrino.fact sample nowtrino.fact.truth in_python in_jupyter to_draw graphs_and_charts

@[reducible]
class COMPILED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (number: LOCAL Box Pigeon)
    (another_number: UNIVERSAL Box Pigeon number)
    [LOGICAL Box Pigeon number another_number]
    [HALTED Box Pigeon number another_number]
    [MEASURED Box Pigeon number another_number]
  where
  a_truth_about_the_world: CompilerOutput Box Pigeon number another_number
  a_demonstration_of_a_constant: CompilerTape

  converged?: CompilerTape → CompilerTape → Prop := fun a b => a < b

inductive Bullshit where
| zero       : Fact → Bullshit
| one        : Fact → Number → CompilerTape → CompilerTape → Bullshit → Bullshit
| rest_call  : Fact → Fact → Prop → Number → Number → Number → CompilerTape → CompilerTape → Bullshit → Bullshit → Bullshit

namespace Bullshit
  def le : Bullshit → Bullshit → Prop
  | .zero this_paper           , .zero that_paper           => this_paper.truth = that_paper.truth
  | .zero _                    , _                          => True  -- Zero is the origin for all

  | .one _ _ _ _ _                         , .zero _                            => False
  | .one _ _ _ _ _                         , .rest_call _ _ _ _ _ _ _ _ _ _     => True
  | .one this_measurement x _ _ _          , .one that_measurement x' _ _ _     =>
                                                                        match this_measurement.decTruth, that_measurement.decTruth with
                                                                        | isTrue _,  isTrue _  => x ≤ x'
                                                                        | isFalse _, isFalse _ => x' ≤ x
                                                                        | isTrue _,  isFalse _ => False
                                                                        | isFalse _, isTrue _  => True

  | .rest_call _ _ _ _ _ _ _ _ _ _  , .zero _                    => False
  | .rest_call _ _ _ _ _ _ _ _ _ _  , .one _ _ _ _ _             => False

  | .rest_call this  here stimulus _ _ this_reading _ _ comes_before and_is_less_than,
    .rest_call that there response _ _ that_reading _ _ displays ELEVEN =>
                                                                          (this.truth = that.truth) ∧ --     | For those keeping score on 11, I have
                                                                          (here.truth = there.truth) ∧ --    | o binary 3
                                                                          (stimulus -> response) ∧ --        | o string theory constant(s)
                                                                          (this_reading ≤ that_reading) ∧ -- | o Berry paradox
                                                                          le comes_before displays ∧ --      | o YOU_the_READER's amp (borrowed from
                                                                          le and_is_less_than ELEVEN --------+   Nigel Tufnel, coming later).
                                                                          --                                 | Pretty confident I do not need more.
def lt: Bullshit → Bullshit → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Bullshit

instance : LE Bullshit where
  le := Bullshit.le
instance : LT Bullshit where
  lt := Bullshit.lt


structure AtreyuProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (quantum: LOCAL Box Pigeon)
    (gravity: UNIVERSAL Box Pigeon quantum)
    [LOGICAL Box Pigeon quantum gravity]
    [HALTED Box Pigeon quantum gravity]
    [MEASURED Box Pigeon quantum gravity]
    [COMPILED Box Pigeon quantum gravity]
    where
  in_a_giant_book: CompilerOutput Box Pigeon quantum gravity
  a_constant: Bullshit
  current_page_number: Number
  total_pages: Number := Pigeon.event Pigeon.value   -- Our pidgen is coming along nicely.
  of_the_proof: CompilerTape

  gawk_at: Bullshit → Bullshit := fun measurement =>
  match measurement with
  |.zero _    =>        .one nowtrino.fact current_page_number of_the_proof in_a_giant_book.preprint a_constant

  |.one some_number last_page last_stanza last_variable current_value =>
                                                      match some_number.decTruth, nowtrino.fact.decTruth with
                                                      | isTrue _,  isTrue _  =>
                                                          .rest_call some_number nowtrino.fact
                                                            ((some_number.truth = nowtrino.fact.truth ∧ last_page ≤ current_page_number) ∨
                                                            (some_number.truth ≠ nowtrino.fact.truth ∧ current_page_number ≤ last_page))
                                                            last_page current_page_number total_pages
                                                            last_stanza last_variable current_value a_constant

                                                      | isTrue _,  isFalse _ =>
                                                          .rest_call some_number nowtrino.fact
                                                            False
                                                            last_page current_page_number total_pages
                                                            last_stanza last_variable current_value a_constant

                                                      | isFalse _, isTrue _  =>
                                                          .rest_call some_number nowtrino.fact
                                                            True
                                                            last_page current_page_number total_pages
                                                            last_stanza last_variable current_value a_constant

                                                      | isFalse _, isFalse _ =>
                                                          .rest_call some_number nowtrino.fact
                                                            ((some_number.truth = nowtrino.fact.truth ∧ current_page_number ≤ total_pages) ∨
                                                            (some_number.truth ≠ nowtrino.fact.truth ∧ last_page ≤ current_page_number))
                                                            last_page current_page_number total_pages
                                                            last_stanza last_variable current_value a_constant


  | .rest_call _ some_constant _ _ lower_bound upper_bound _ prior_inductive_step _ in_the_computation =>
                                                  match some_constant.decTruth, nowtrino.fact.decTruth with
                                                  | isTrue _,  isTrue _  =>
                                                      .rest_call some_constant nowtrino.fact
                                                        ((some_constant.truth = nowtrino.fact.truth ∧ lower_bound ≤ current_page_number) ∨
                                                        (some_constant.truth ≠ nowtrino.fact.truth ∧ current_page_number ≤ lower_bound))
                                                        upper_bound current_page_number total_pages
                                                        prior_inductive_step of_the_proof in_the_computation a_constant

                                                  | isTrue _,  isFalse _ =>
                                                      .rest_call some_constant nowtrino.fact
                                                        False
                                                        upper_bound current_page_number total_pages
                                                        prior_inductive_step of_the_proof in_the_computation a_constant

                                                  | isFalse _, isTrue _  =>
                                                      .rest_call some_constant nowtrino.fact
                                                        True
                                                        upper_bound current_page_number total_pages
                                                        prior_inductive_step of_the_proof in_the_computation a_constant

                                                  | isFalse _, isFalse _ =>
                                                      .rest_call some_constant nowtrino.fact
                                                        ((some_constant.truth = nowtrino.fact.truth ∧ current_page_number ≤ lower_bound) ∨
                                                        (some_constant.truth ≠ nowtrino.fact.truth ∧ lower_bound ≤ current_page_number))
                                                        upper_bound current_page_number total_pages
                                                        prior_inductive_step of_the_proof in_the_computation a_constant


  copy_the_cite? : Bullshit → Bullshit → Bullshit := fun lit_review this_proof =>
    -- Back-to-back satirize: lift both inputs one rung, then hang them as the two
    -- children of a single .rest -- the only constructor that carries a pair.  The
    -- Prop slot holds the slip (sa < sb); residue? is exactly the projection of it.
    -- (satirize lifts every rung, so neither side is ever .zero -- the floor arms are
    -- kept only for totality and collapse to the surviving satire.)
    match gawk_at lit_review, gawk_at this_proof with
    | .zero _,  anything_is_better          => anything_is_better
    | anything_is_better,      .zero _      => anything_is_better
    | satire,      reframe_satire     =>
        .rest_call nowtrino.fact nowtrino.fact (satire < reframe_satire) current_page_number current_page_number total_pages of_the_proof of_the_proof satire satire

  -- residue? is the PROJECTION of the operator: run bilinear?, then read the slip out of
  -- the .rest's Prop slot.  The only `none` is the commute -- both inputs at the origin
  -- floor -- mirroring how `.zero` floors Bullshit.le and `none` floors slipLe.  This is
  -- the option the residue computation (obfusplained?/close?) reads off.
  residue? : Bullshit → Bullshit → Option Prop := fun a b =>
    match a, b with
    | .zero _, .zero _ => none
    | _,       _       =>
        match copy_the_cite? a b with
        | .rest_call _ _ truth _ _ _ _ _ _ _ => some truth
        | _                                  => none




class A_TRUTH_ABOUT
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (fact: LOCAL Box Pigeon)
    (about_the_world: UNIVERSAL Box Pigeon fact)
    [LOGICAL Box Pigeon fact about_the_world]
    [HALTED Box Pigeon fact about_the_world]
    [MEASURED Box Pigeon fact about_the_world]
    [COMPILED Box Pigeon fact about_the_world]
  where
  you_the_reader : AtreyuProcess Box Pigeon fact about_the_world
  TRUE : Bullshit := .zero nowtrino.fact
  -- output is the compiler/reader output: the THEORY rung of the bullshit
  -- ladder, NOT the origin TRUE.  Instances must supply it.
  a_constant : Bullshit
  -- The certificate is now ORDERING, not equality: the .zero origin (TRUE)
  -- is the floor below the accumulated bullshit `output`.  `Bullshit.le` gives
  -- `.zero _ , _ => True` for ANY second argument, so `TRUE ≤ output` is the
  -- honest definitional witness no matter which rung `output` lands on.
  the_constant_is_at_least_true : TRUE ≤ a_constant
  raw_output : Bullshit := you_the_reader.gawk_at you_the_reader.a_constant

  obfusplained? : TRUE ≤ a_constant → Bullshit → Bullshit → Option Prop := fun _ a b =>
  match a, b with
  | .zero _, .zero _ => none            -- two origins: they commute, no slip
  | _,       _       => some (a < b)    -- a real rung pair: the slip, condition a < b

/-
  -/

-- THEORY: the three pieces of bullshit as a named ladder, expressed as defs
-- (NOT a 34-binder structure -- a structure here forces a fresh 34-gate
-- instance synthesis at every use site, which is exactly the elaboration cost
-- we are fighting).  Each rung takes the reader-process explicitly and
-- satirizes the PREVIOUS rung, so the chain is well-founded and bottoms at the
-- .zero origin.  `THEORY.raw_output` is the HYPOTHESIS rung (.one): the compiler
-- output the device reads, NOT the origin TRUE.  (It is the b rung, one satirize
-- up; the theory rung c/.rest is still defined below for Episode16's
-- velocity/acceleration variations, but is not used as the certified output --
-- see the raw_output comment for why.)

namespace THEORY

variable
    {Box: Type i}
    {Pigeon: CarrierProcess Box}
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    {fact: LOCAL Box Pigeon}
    {about_the_world: UNIVERSAL Box Pigeon fact}
    [LOGICAL Box Pigeon fact about_the_world]
    [HALTED Box Pigeon fact about_the_world]
    [MEASURED Box Pigeon fact about_the_world]
    [COMPILED Box Pigeon fact about_the_world]
    [A_TRUTH_ABOUT Box Pigeon fact about_the_world]

def repeatable
    (_reader : AtreyuProcess Box Pigeon fact about_the_world) (origin : Bullshit) : Bullshit :=
  origin                                                       -- piece 1: the origin / repeatable observation

def hypothesis
    (reader : AtreyuProcess Box Pigeon fact about_the_world) (origin : Bullshit) : Bullshit :=
  reader.gawk_at (repeatable reader origin)                   -- piece 2: one step on the previous

def theory
    (reader : AtreyuProcess Box Pigeon fact about_the_world) (origin : Bullshit) : Bullshit :=
  reader.gawk_at (hypothesis reader origin)                   -- piece 3: the accumulated rest

def raw_output
    (reader : AtreyuProcess Box Pigeon fact about_the_world) (origin : Bullshit) : Bullshit :=
  hypothesis reader origin                                     -- the compiler output the device reads:
  -- the hypothesis rung (.one).  satirize(.zero) constructs `.one` with a
  -- STATIC head (no decTruth match), so `TRUE ≤ raw_output` certifies cheaply
  -- by `trivial`.  The theory rung (.rest) is the same ladder one step higher
  -- but its head is gated behind a stuck `decTruth` match, which makes the
  -- ordering certificate computationally pathological; the three rung defs
  -- (repeatable/hypothesis/theory) remain intact for the velocity/acceleration
  -- variations in Episode16.

end THEORY


instance DISTINGUISHABLE_PROP
    (Carrier : CarrierProcess Prop)
    : DISTINGUISHABLE Prop Carrier where
  fact := Carrier.symbol
  symbol := Prop
  different? := fun _ => True
  dec_distinct := fun _ => isTrue trivial

def truthCarrier : CarrierProcess Prop where
  symbol := Fact.Truth
  value := .zero Fact.Truth

instance truthDistinct :
    DISTINGUISHABLE Prop truthCarrier where
  fact := truthCarrier.symbol
  symbol := Prop
  different? := fun _ => True
  dec_distinct := fun _ => isTrue trivial



/-- The truth order on the bullshit ladder -- the relation the needle collapses.
`@[reducible]` so it unfolds to `≤` under unification (e.g. against `output_true`). -/
@[reducible] def TruthOrder (less more : Bullshit) : Prop := less ≤ more

/-- THE NEEDLE: the single sanctioned `Quot.sound` site.  Two readings that are
ordered on the truth ladder collapse to the same truth-phase class.  Raw `Quot`,
no `Setoid` (no refl/symm/trans obligation) -- so `#print axioms selection_sound`
is exactly `[Quot.sound]`.  The genuinely-undecidable "are these the same truth?"
is never DECIDED (no `Classical.propDecidable`) and never FLATTENED (no `fun _ =>
True`): related readings are IDENTIFIED by one quotient soundness. -/
theorem selection_sound {α : Sort _} {r : α → α → Prop} {a b : α}
    (h : r a b) : Quot.mk r a = Quot.mk r b :=
  Quot.sound h



inductive Closure
  | same : Fact → Bullshit → Closure
  | different : Fact → Bullshit → Bullshit → Option Prop → Closure
  | inferred : Fact → Fact → Bullshit → Bullshit → Option Prop → Closure → Closure

namespace Closure

/-- The slip order on a node's commutator slot.  `none` (the operators commuted -- no slip) is the
floor, mirroring how `.zero` floors `Bullshit.le`; between two genuine slips the original Prop
implication survives. -/
def branch_and_compare : Option Prop → Option Prop → Prop
  | none,   _      => True
  | some _, none   => False
  | some p, some q => p → q

/-- Slip composition (the cocycle the coherence checks compare against).  `none` is the identity --
a commuting step contributes nothing -- and two genuine slips compose by conjunction. -/
def slipAnd : Option Prop → Option Prop → Option Prop
  | none,   y      => y
  | x,      none   => x
  | some p, some q => some (p ∧ q)

def le : Closure → Closure → Prop
  | .same stanza1 less,  .same stanza2 more                          =>  stanza1.truth = stanza2.truth ∧ less ≤ more
  | .same stanza1 stuff, .different stanza2 lower_bound slip_bound _ =>  stanza1.truth = stanza2.truth ∧ (stuff ≤ lower_bound ∨ stuff ≤ slip_bound)
  | .same stanza value,  .inferred this_stanza that_stanza this_max that_max _ a_named_constant =>
                                                            (stanza.truth = this_stanza.truth ∨ stanza.truth = that_stanza.truth) ∧
                                                            (value ≤ this_max ∨ value ≤ that_max) ∨ le (.same stanza value) a_named_constant

  | .different stanza1 lower_bound slip_bound _,   .same stanza2 value =>    stanza1.truth ≠ stanza2.truth ∨
                                                                              ¬ (lower_bound ≤ value ∨ slip_bound ≤ value)
  | .different stanza1 lower_bound1 slip_bound1 a_constant_computation,
    .different stanza2 lower_bound2 slip_bound2 another_constant_computation =>
                                                            stanza1.truth = stanza2.truth ∧
                                                            lower_bound1 ≤ lower_bound2 ∧ slip_bound1 ≤ slip_bound2 ∧
                                                            branch_and_compare a_constant_computation another_constant_computation

  | .different stanza lower_bound slip_bound a_constant_computation,
    .inferred this_stanza that_stanza this_max that_max another_constant_computation a_named_constant =>
                                                            ((stanza.truth = this_stanza.truth ∨ stanza.truth = that_stanza.truth) ∧
                                                                      lower_bound ≤ this_max ∧ slip_bound ≤ that_max ∧
                                                                      branch_and_compare a_constant_computation another_constant_computation) ∨
                                                            le (.different stanza lower_bound slip_bound a_constant_computation) a_named_constant


  | .inferred this_stanza that_stanza lower_bound slip_bound _ _, .same stanza some_constant_value =>
                                                            (stanza.truth ≠ this_stanza.truth ∧ stanza.truth ≠ that_stanza.truth) ∨
                                                              ¬ (lower_bound ≤ some_constant_value ∨ slip_bound ≤ some_constant_value)
  | .inferred this_stanza that_stanza constant_lower_bound constant_slip_bound a_constant_computation a_named_constant,
    .different stanza lower_bound slip_bound another_constant_computation =>
                                                            ((this_stanza.truth = stanza.truth ∨ that_stanza.truth = stanza.truth) ∧
                                                            constant_lower_bound ≤ lower_bound ∧
                                                            constant_slip_bound ≤ slip_bound ∧
                                                            branch_and_compare a_constant_computation another_constant_computation) ∨
                                                            le a_named_constant (.different stanza lower_bound slip_bound another_constant_computation)
  | .inferred this that  this_low this_slip some_constant_computation    a_named_constant,
    .inferred here there that_low that_slip another_constant_computation a_very_similar_looking_constant_with_a_very_similar_name =>
      ((this.truth = here.truth ∨ that.truth = there.truth) ∧
       this_low ≤ that_low ∧ this_slip ≤ that_slip ∧
       branch_and_compare some_constant_computation another_constant_computation ∧ le a_named_constant
                                                                                            a_very_similar_looking_constant_with_a_very_similar_name) ∨
      le (.inferred this that this_low this_slip some_constant_computation a_named_constant) a_very_similar_looking_constant_with_a_very_similar_name

termination_by train_schedule1 train_schedule2 => sizeOf train_schedule1 + sizeOf train_schedule2  --| I think we expect naturals to fall out of elab.

end Closure

instance : LE Closure where
  le := Closure.le


namespace Fact

noncomputable def SAME
    {Box: Type i}
    {Pigeon: CarrierProcess Box}
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    {fact: LOCAL Box Pigeon}
    {about_the_world: UNIVERSAL Box Pigeon fact}
    [LOGICAL Box Pigeon fact about_the_world]
    [HALTED Box Pigeon fact about_the_world]
    [MEASURED Box Pigeon fact about_the_world]
    [COMPILED Box Pigeon fact about_the_world]
    [guano: A_TRUTH_ABOUT Box Pigeon fact about_the_world]
    : Fact :=
  -- The needle, honest.  "TRUE and the output are the SAME truth" = the two
  -- readings collapse to one class in the truth-order quotient, witnessed by the
  -- one located `Quot.sound` (`selection_sound`), with the genuine ordering witness
  -- `out.output_true : TRUE ≤ output`.  No classical decision; no flattening.
  -- (`SAME.truth` is only ever compared reflexively in `Closure.le` -- every chair
  -- closure uses this same `Fact.SAME`, so `f1.truth = f2.truth` stays `X = X`.)
  { truth := Quot.mk TruthOrder guano.TRUE = Quot.mk TruthOrder guano.a_constant
    decTruth := Decidable.isTrue (selection_sound (r := TruthOrder) guano.the_constant_is_at_least_true) }

end Fact

@[reducible]
structure EquivalenceProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (this_number: LOCAL Box Pigeon)
    (that_number: UNIVERSAL Box Pigeon this_number)
    [LOGICAL Box Pigeon this_number that_number]
    [HALTED Box Pigeon this_number that_number]
    [MEASURED Box Pigeon this_number that_number]
    [COMPILED Box Pigeon this_number that_number]
    [guano: A_TRUTH_ABOUT Box Pigeon this_number that_number]
  where
  you_the_knower : AtreyuProcess Box Pigeon this_number that_number
  your_conclusion : Closure

  do_you_believe_it? : Bullshit → Bullshit → Closure := fun hypothetical_result real_result =>
    .different (Fact.SAME (guano := guano)) hypothetical_result real_result
                                     (guano.obfusplained? guano.the_constant_is_at_least_true hypothetical_result real_result)


@[reducible]
class INFERRED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (same_number: LOCAL Box Pigeon)
    (different_number: UNIVERSAL Box Pigeon same_number)
    [LOGICAL Box Pigeon same_number different_number]
    [HALTED Box Pigeon same_number different_number]
    [MEASURED Box Pigeon same_number different_number]
    [COMPILED Box Pigeon same_number different_number]
    [A_TRUTH_ABOUT Box Pigeon same_number different_number]
  where
  same_difference : EquivalenceProcess Box Pigeon same_number different_number
  α : Closure

  inferred? : Closure → Closure → Prop := fun metaphysical_constant physical_constant => metaphysical_constant ≤ physical_constant



end Measurement
