/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

(c) 2026 Nyy euvgfr erfrerq.

First of all, _CONGRATULATIONS_! You made it through the most complex part of the argument. Probably.  Don't worry, I have a complete patter that
*YOU the READER*
-/
-- Would you even care if I imported anything at this point?
import Measurement.Episode4
set_option allowUnsafeReducibility true


-- So, have you figured out the quarter I keep taking from you?   I told you, you had no idea how
-- much I would take...

-- Get back to work John. You need to learn Gungan __REAL_FAST__.
namespace Measurement

universe i

instance CAN_YOU_SEE_A_CHARACTERISTIC
    (B: Type i)(Pigeon: CarrierProcess B)
    [nowtrino: DISTINGUISHABLE B Pigeon]
    : ADMISSIBLE B Pigeon where
  counting_process :=
  { carrier := Pigeon
    count   := .zero nowtrino.fact
    iterate := fun particle => match particle with
      | .zero _     => .zero nowtrino.fact
      | .number _ _ _ => .number nowtrino.fact Pigeon.value (.zero nowtrino.fact) }


instance CAN_YOU_COUNT_THEM
    (B: Type i)(P: CarrierProcess B)
    [nowtrino: DISTINGUISHABLE B P]
    [particle: ADMISSIBLE B P]
    : COUNTABLE B P where
  index :=
    { count  := particle.counting_process
      origin := .zero nowtrino.fact }

instance CAN_YOU_LABEL_THEM
    (B: Type i)(P: CarrierProcess B)
    [nowtrino: DISTINGUISHABLE B P][ADMISSIBLE B P][enumeration: COUNTABLE B P]
    : ENCODED B P where
  limit_process :=
    { indexing_process := enumeration.index
      limit            := .zero nowtrino.fact
      sequence         := .nil nowtrino.fact }

instance CAN_YOU_SEE_THE_BOUNDARY
    (B: Type i)(P: CarrierProcess B)
    [nowtrino: DISTINGUISHABLE B P][ADMISSIBLE B P][COUNTABLE B P][the_calculus_limit: ENCODED B P]
    : RESIDUE B P where
  cauchy_process :=
    { limit_process  := the_calculus_limit.limit_process
      value          := .zero nowtrino.fact
      accumulation   := .nil nowtrino.fact }

instance DID_THE_PARTICLE_COLOR_OUTSIDE_THE_LINES
    (B: Type i)(P: CarrierProcess B)
    [nowtrino: DISTINGUISHABLE B P][ADMISSIBLE B P][COUNTABLE B P][ENCODED B P][exp_iθ: RESIDUE B P]
    : BINARY B P where
  observation_process :=
    { cauchy_process := exp_iθ.cauchy_process
      before         := .nil nowtrino.fact
      after          := .nil nowtrino.fact }
  bit := .initial_condition nowtrino.fact exp_iθ.cauchy_process.accumulation
  zero := .nil nowtrino.fact
  one  := .nil nowtrino.fact


instance DO_YOU_HEAR_A_BUNCH_OF_CLICKS
    (B: Type i)(P: CarrierProcess B)
    [nowtrino: DISTINGUISHABLE B P][ADMISSIBLE B P][COUNTABLE B P][ENCODED B P][RESIDUE B P][click: BINARY B P]
    : REPEATABLE B P where
  repeatable_process :=
  {
    observation_process := click.observation_process
    stimulus := .initial_condition nowtrino.fact click.zero
    expectation := .hypothesis nowtrino.fact click.bit
  }

instance HOW_MANY_CLICKS_DO_YOU_HEAR
    (B: Type i)(P: CarrierProcess B)
    [nowtrino: DISTINGUISHABLE B P][ADMISSIBLE B P][COUNTABLE B P][ENCODED B P][RESIDUE B P][BINARY B P][JMP: REPEATABLE B P]
    : NUMERIC B P where
  computational_process :=
  { repeatable_process := JMP.repeatable_process
    output := some (.hypothesis nowtrino.fact)
  }

instance WRITE_DOWN_HOW_MANY_CLICKS_YOU_HEAR_IN_A_TABLE
    (B: Type i)(P: CarrierProcess B)
    [nowtrino: DISTINGUISHABLE B P][ADMISSIBLE B P][COUNTABLE B P][ENCODED B P][RESIDUE B P][BINARY B P][REPEATABLE B P][jupyter_notebook: NUMERIC B P]
    : REPRESENTABLE B P where
  calculation_process :=
  { computational_process :=
      {jupyter_notebook.computational_process with closure := fun the_number_of_clicks => the_number_of_clicks}
    program := jupyter_notebook.computational_process.close jupyter_notebook.computational_process.output
    state := .program nowtrino.fact (jupyter_notebook.computational_process.close jupyter_notebook.computational_process.output)
  }
  representable? := fun _ expected_response =>
    ⟨Computation.program nowtrino.fact expected_response, rfl⟩

instance ROSS!_GET_THE_READOUTS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [the_invariant: REPRESENTABLE Box Pigeon]
    : PHYSICAL Box Pigeon where
  noisy_process := {
    turing_process := the_invariant.calculation_process
    program := .halting nowtrino.fact (.program nowtrino.fact the_invariant.calculation_process.program)
  }
  threshold := .nonhalting  nowtrino.fact
                            (.program nowtrino.fact the_invariant.calculation_process.program)
                            (some (ChaitinsNumberSequence.halting nowtrino.fact the_invariant.calculation_process.state))
  admissible? := fun _ _ _ => rfl    --| (Your first for-real flop, *YOU the READER*! rofl! I *LITERALLY* **CANNOT** see the bent card here. Sure this isn't a bug?)


noncomputable instance ARE_THE_UNITS_RIGHT
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [anechoic_chamber: PHYSICAL Box Pigeon]
    [newtrino: Inhabited nowtrino.symbol]
    : COMPARABLE Box Pigeon where
  physical_process :=
  { noisy_process := anechoic_chamber.noisy_process
    representation := default
    invariant := .base nowtrino.fact default
    value := .base nowtrino.fact (ULift.up default)
  }
  smaller_than := fun one_foot π  => one_foot = π


instance DO_YOU_SEE_THE_LIGHT_FLASH_WHEN_YOU_HEAR_THE_CLICK
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [cc: PHYSICAL Box Pigeon]
    [dd: COMPARABLE Box Pigeon]
    : OBSERVED Box Pigeon where
  slip_process :=
  { physical_process := dd.physical_process
    projection       := .origin nowtrino.fact dd.physical_process.noisy_process.program nowtrino.symbol
    stress           := cc.threshold
    threshold        := nowtrino.symbol
  }
  observation := ULift nowtrino.symbol

instance THATS_THE_PHOTOELECTRIC_EFFECT
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [static_friction: OBSERVED Box Pigeon]
    : PRESENT Box Pigeon where
  santa_claus:=
  { static_fraction := static_friction.slip_process
    accumulation := .tree nowtrino.fact
  }
  quantum := Type i

instance THE_PHOTON_IS_MEASURABLE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [gift_from: PRESENT Box Pigeon]
    : MEASURABLE Box Pigeon where
  gauge_process :=
  { sensing_process := gift_from.santa_claus
    clock      := .this_superpigeon nowtrino.fact (.tree nowtrino.fact)
  }

instance PERHAPS_NOT_WITH_A_MULTIMETER_BUT_YOU_UNDERSTAND_WHAT_I_MEAN
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [multimeter: MEASURABLE Box Pigeon]
    : GUNGAN Box Pigeon where
  meesa_process :=
  { gauge_process := multimeter.gauge_process
    concept := .color nowtrino.fact multimeter.gauge_process.sensing_process.accumulation
  }

instance WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [jarjar: GUNGAN Box Pigeon]
    : SOURCE Box Pigeon where
  cd_process :=
  { meesa_process := jarjar.meesa_process
    zero := .physics nowtrino.fact jarjar.meesa_process.concept
  }
  one := .zero_like nowtrino.fact (.physics nowtrino.fact jarjar.meesa_process.concept)

instance AND_THE_COMPILER_WILL_AUTOMATICALLY_CONVERT_THE_RAW_DATA_TO_TABLES
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [jarjar: GUNGAN Box Pigeon]
    [data_feed: SOURCE Box Pigeon]
    : EXECUTED Box Pigeon where
  compiled_process :=
  { digital_process := data_feed.cd_process
    source := data_feed
    opcodes := .boot nowtrino.fact (.physics nowtrino.fact jarjar.meesa_process.concept)
  }

instance ONE_VALUE_AT_A_TIME_IN_ORDER_AND_WRITE_SOMETHING_TO_DISK
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [result: EXECUTED Box Pigeon]
    : VALUE Box Pigeon where
    -- What we have here is the multiplicative identity.  from no-fucking-where
  mathematical_process := {
    compiled_process := result.compiled_process
    mapping := fun input => match input with
      |.satire_about finite_element_analysis => .satire_about finite_element_analysis
      |.compile f e a => .execute f e a
      |.execute f e a => .compile f e a
  }
  monad := .satire_about nowtrino.fact

instance TURNS_OUT_YOU_CAN_FILL_YOUR_DISK
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [gift_from: PRESENT Box Pigeon]
    [GUNGAN Box Pigeon] [SOURCE Box Pigeon] [EXECUTED Box Pigeon]
    [uncountable: VALUE Box Pigeon]
    : MAGNITUDE Box Pigeon where
  adding_process :=
  { hebrew_process := uncountable.mathematical_process
    plus := uncountable
    sum := .zero nowtrino.fact.truth gift_from.santa_claus.accumulation
  }

instance SO_YOU_NEED_TO_GET_MORE_DISKS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [tar_file: MAGNITUDE Box Pigeon]
    : SCALED Box Pigeon where
  multiplying_process :=
  { adding_process := tar_file.adding_process
    product := .one nowtrino.fact.truth tar_file.adding_process.sum
    total := .zero nowtrino.fact.truth (.tree nowtrino.fact)
  }

instance AND_MORE_PROCESSORS_BECAUSE_THERE_ARE_A_LOT_OF_NOWTRINOS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [gift_from: PRESENT Box Pigeon]
    [GUNGAN Box Pigeon] [SOURCE Box Pigeon] [EXECUTED Box Pigeon] [VALUE Box Pigeon]
    [shit_loads: SCALED Box Pigeon]
    : LOAD Box Pigeon where
  basic_operation :=
  { GOSUB := shit_loads.multiplying_process
    TEN := gift_from.santa_claus.accumulation
    span := .origin nowtrino.fact.truth shit_loads.multiplying_process.product
  }

instance SO_MANY_SENSITIVE_NOWTRINO_DETECTORS_TO_DETECT_PRESENCE___WHERE_DID_IT_GO
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [comprehensive_software: LOAD Box Pigeon]
    : INDEXOFANT Box Pigeon where
  galerkin_process :=
  { ANSYS_process := comprehensive_software.basic_operation
    polynomial := .constant .Truth
  }

instance THERE_IT_IS___ONLY_CERTAIN_ELEMENTS_RESPOND_TO_NOWTRINO_DETECTION
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [element: INDEXOFANT Box Pigeon]
    : BULLSHIT Box Pigeon where
  arm_wave_process :=
  { dunking_contest := element.galerkin_process
    guess := .observation nowtrino.fact.truth
  }

instance WE_NEED_TO_GET_A_GRANT_TO_GET_MORE_NOWTRINO_DETECTORS___WE_KEEP_LOSING_IT
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    : PROPAGANDA Box Pigeon where
  insinuates := CrusadeProcess.default Box Pigeon

--| Let's admit a graduate student into the lab.
def InitiationProcess.default
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon][ADMISSIBLE Box Pigeon][COUNTABLE Box Pigeon][ENCODED Box Pigeon]
    [RESIDUE Box Pigeon][BINARY Box Pigeon][REPEATABLE Box Pigeon][NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon][PHYSICAL Box Pigeon][COMPARABLE Box Pigeon][OBSERVED Box Pigeon]
    [PRESENT Box Pigeon][MEASURABLE Box Pigeon][GUNGAN Box Pigeon][SOURCE Box Pigeon]
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon][SCALED Box Pigeon][LOAD Box Pigeon]
    [INDEXOFANT Box Pigeon][model: BULLSHIT Box Pigeon][space: PROPAGANDA Box Pigeon]
    : InitiationProcess Box Pigeon where
  ethos := CrusadeProcess.default Box Pigeon
  sacred_texts := .inside_joke Fact.Truth.truth

instance MAKE_SURE_WE_CAN_GET_A_COUPLE_GRAD_STUDENTS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    : ACOLYTE Box Pigeon where
  euclid := InitiationProcess.default Box Pigeon

--| Now, they can count clicks and get a Ph.D.
def LearningProcess.default
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon][ADMISSIBLE Box Pigeon][COUNTABLE Box Pigeon][ENCODED Box Pigeon]
    [RESIDUE Box Pigeon][BINARY Box Pigeon][REPEATABLE Box Pigeon][NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon][PHYSICAL Box Pigeon][COMPARABLE Box Pigeon][OBSERVED Box Pigeon]
    [PRESENT Box Pigeon][MEASURABLE Box Pigeon][GUNGAN Box Pigeon][SOURCE Box Pigeon]
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon][SCALED Box Pigeon][LOAD Box Pigeon]
    [INDEXOFANT Box Pigeon][model: BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon][ACOLYTE Box Pigeon]
    : LearningProcess Box Pigeon where
  teaching := InitiationProcess.default Box Pigeon
  galileo := .inside_joke Fact.Truth.truth
  invariant := .repeatable Fact.Truth.truth

instance ABD
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    : SCIENTIFIC Box Pigeon where
  discovering := LearningProcess.default Box Pigeon
  invariant := .hypothesis Fact.Truth.truth (.inside_joke Fact.Truth.truth)

instance YOU_HAVE_TO_STOP_TAKING_CLASSES_TO_GRADUATE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [experiment: SCIENTIFIC Box Pigeon]
    : TRUTH Box Pigeon where
  becomes :=
  { shows_us := experiment.discovering
    knowledge := .jarjar nowtrino.fact.truth
  }

instance THEN_COMES_THE_LAB_WORK
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [thesis: TRUTH Box Pigeon]
    : WITNESSED Box Pigeon where
  we_saw :=
  { we_experience := thesis.becomes
    in_the_literature := .the_proof nowtrino.fact.truth
  }
  the_experiment := .the_proof nowtrino.fact.truth

instance FINALLY_YOU_GRADUATE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [the_result: WITNESSED Box Pigeon]
    : REAL Box Pigeon where
  by_His_noodly_appendage :=
  { frame_of_reference := the_result.we_saw
    in_reality := .logically nowtrino.fact.truth
  }
  nagging_doubt := .but the_result.the_experiment nowtrino.fact.truth (.logically nowtrino.fact.truth)
  -- This is a completely circular argument since the experiment describes itself as the experiment it intends to prove.

instance AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [the_result: WITNESSED Box Pigeon]
    [flying_spaghetti_monster: REAL Box Pigeon]
    : LOCAL Box Pigeon where
  the_continuum :=
  { the_æther := flying_spaghetti_monster.by_His_noodly_appendage
    differential_equation := .the_newton the_result.the_experiment nowtrino.fact.truth
  }
  the_ball := nowtrino.fact.truth

instance PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE_BUT_IT_SHOULD_BE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [the_result: WITNESSED Box Pigeon]
    [flying_spaghetti_monster: REAL Box Pigeon]
    (nowtrino_model: LOCAL Box Pigeon)
    : UNIVERSAL Box Pigeon nowtrino_model where
  the_train_of_thought :=
  { the_local_schedule :=
    { the_æther := flying_spaghetti_monster.by_His_noodly_appendage
      differential_equation := .the_gateaux the_result.the_experiment Fact.Truth.truth nowtrino.fact.truth
                                                                                      (.the_newton the_result.the_experiment nowtrino.fact.truth)
    }
    the_direction_to_the_destination := .einstein nowtrino.fact
    uptown_or_downtown := match nowtrino.fact.decTruth with
        | isTrue  _ => Fact.Truth
        | isFalse _ => nowtrino.fact
    the_train_in := Type i
  }
  once_around  := .blackhole nowtrino.fact.truth (ULift.{i+1} Box) (.einstein nowtrino.fact) --    | The nowtrino cank spin around twice before
  twice_around := .whitehole nowtrino.fact Box (.einstein nowtrino.fact) --------------------------+ returning to the same Box.

instance OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [REAL Box Pigeon]
    (naotrino_model: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino_model)
    : LOGICAL Box Pigeon naotrino_model commuter_pass where
  feelings :=
  { bullshit_meter := commuter_pass.the_train_of_thought
    time_spent_waiting := .whitehole nowtrino.fact Box (.einstein nowtrino.fact)
    according_to_newton := .stokes nowtrino.fact (.einstein nowtrino.fact) nowtrino.fact.truth
  }
  microsoft_basic := Calibration.EKG.executed

instance DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [nonsensical: LOGICAL Box Pigeon naotrino commuter_pass]
    : HALTED Box Pigeon naotrino commuter_pass where
  scientific_paper :=
    let feelings : HeartbeatProcess Box Pigeon naotrino commuter_pass := nonsensical.feelings
    { stamina := feelings
      trilinos : Calibration.EKG := nonsensical.microsoft_basic
      numerical_analysis := (.load Fact.Truth.truth Box)
    }

instance THE_NAOTRINO_IS_MEASURED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass]
    [documents_on_file: HALTED Box Pigeon naotrino commuter_pass]
    : MEASURED Box Pigeon naotrino commuter_pass where
  a_distance :=
  { description := documents_on_file.scientific_paper
    difference_between := .zero nowtrino.fact
    in_heartbeats := .origin nowtrino.fact (.zero nowtrino.fact) Box
    saved_as_y := Box
  }

instance WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass]
    [HALTED Box Pigeon naotrino commuter_pass]
    [weakly_interacting_particle: MEASURED Box Pigeon naotrino commuter_pass]
    : COMPILED Box Pigeon naotrino commuter_pass where
  a_truth_about_the_world :=
  { too_good_to_be_true := weakly_interacting_particle.a_distance
    preprint := (.introduction Fact.Truth Box)
  }
  a_demonstration_of_a_constant := .methodology Fact.Truth Fact.Truth Box (ULift.{i+1, i} Box) (.introduction Fact.Truth Box)

instance HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass]
    [HALTED Box Pigeon naotrino commuter_pass]
    [MEASURED Box Pigeon naotrino commuter_pass]
    [holy_shit: COMPILED Box Pigeon naotrino commuter_pass]
    : A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass where
  you_the_reader :=
  { in_a_giant_book := holy_shit.a_truth_about_the_world
    a_constant          := .zero Fact.Truth
    current_page_number := .zero Fact.Truth
    total_pages         := .zero Fact.Truth
    of_the_proof        := .methodology Fact.Truth Fact.Truth Box (ULift.{i+1, i} Box) (.introduction Fact.Truth Box)
  }
  TRUE := .zero Fact.Truth
  raw_output := .one
              Fact.Truth
              (.one Fact.Truth (.zero nowtrino.fact))
              (.introduction nowtrino.fact Box)
              (.methodology Fact.Truth nowtrino.fact Box (ULift.{i+1, i} Box) (.introduction Fact.Truth Box))
              (.zero nowtrino.fact)
  a_constant := .one
              Fact.Truth
              holy_shit.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_local_schedule.the_æther.frame_of_reference.we_experience.shows_us.teaching.ethos.to_pwn_n00bz.dunking_contest.ANSYS_process.GOSUB.adding_process.hebrew_process.compiled_process.digital_process.meesa_process.gauge_process.sensing_process.static_fraction.physical_process.noisy_process.turing_process.computational_process.repeatable_process.observation_process.cauchy_process.limit_process.indexing_process.count.carrier.value
              (.introduction nowtrino.fact Box)
              (.methodology Fact.Truth nowtrino.fact Box (ULift.{i+1, i} Box) (.introduction Fact.Truth Box))
              (.zero nowtrino.fact)
  the_constant_is_at_least_true := by trivial

noncomputable instance OF_COURSE_IT_DOES___I_JUST_PUT_IT_THERE_FOR_NO_REASON
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass]
    [HALTED Box Pigeon naotrino commuter_pass]
    [MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass]
    [guano: A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass]
  : INFERRED Box Pigeon naotrino commuter_pass where
  same_difference :=
  { you_the_knower      := guano.you_the_reader
    your_conclusion     := .different (Fact.SAME (guano:=guano)) (guano.TRUE) (guano.a_constant) (some Fact.Truth.truth)
  }
  α := .same Fact.Truth guano.a_constant

def You_the_Reader
    {Box: Type i}
    {Pigeon: CarrierProcess Box}
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    {fact: LOCAL Box Pigeon}
    {about_the_world: UNIVERSAL Box Pigeon fact}
    [LOGICAL Box Pigeon fact about_the_world]
    [HALTED Box Pigeon fact about_the_world]
    [MEASURED Box Pigeon fact about_the_world]
    [stdout: COMPILED Box Pigeon fact about_the_world]
    [A_TRUTH_ABOUT Box Pigeon fact about_the_world]
 : AtreyuProcess Box Pigeon fact about_the_world where
  in_a_giant_book := stdout.a_truth_about_the_world
  a_constant := .zero nowtrino.fact
  current_page_number := Pigeon.value
  of_the_proof := stdout.a_demonstration_of_a_constant

instance BUT_THE_TRUTH_IS_YOU_THE_READER_UNDERSTANDS_THE_ARGUMENT_NAO
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass]
    [HALTED Box Pigeon naotrino commuter_pass]
    [MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass]
    [guano: A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass]
    [INFERRED Box Pigeon naotrino commuter_pass]
    (Newtrino: CarrierProcess Box)
  : A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass where
  {
    you_the_reader := You_the_Reader Value PropCarrier
    a_constant     := (You_the_Reader).gawk_at (guano.a_constant)
    the_constant_is_at_least_true    := by trivial
  }



end Measurement
