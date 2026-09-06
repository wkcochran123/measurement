/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that we often lose sight of the plot._

(c) 2026

__EPISODE 7__: _THE_MACGUFFIN_

"Experiment is the sole judge of scientifc 'truth.'"      -- Some smart dude.

"Tonights winning numbers are 4 10 28 35 38 55 and a the bonus ball is 33."
                                                          -- NY Lottery, Aug 3. 2002.

-/
-- Would you even care if I imported anything at this point?
import Measurement.Episode05 ----------------------------------| Skip _The Trick_ just to make sure we don't import α
set_option allowUnsafeReducibility true


-- So, have you figured out the quarter I keep taking from you?   I told you, you had no idea how
-- much I would take...

-- Get back to work John. You need to learn Gungan __REAL_FAST__.
namespace Measurement

--| First of all, _CONGRATULATIONS_! You made it through the most complex part of the argument. Probably.  Don't worry, I have a complete patter that
--| *YOU the READER* can use and are probably more familiar with.  On the left is the Lean which demonstrates that the argument is sound.  It reads,
--| well, I chose some fun names. Remember, _that_ is the argumen the compiler is checking for logical consistency. Feel free to refer back to
--| definitions in previous episodes to double check the argument is consistent.  Remember, we are looking for the miracle of the Flying Spaghetti
--| Monster: the two-spin graviton monopole: the nowtrino.

--|      Remember this side is rigorously checked for consistency                   No such rigor checked here. This is purely grift.
--|      ---------------------+----------------------------------                   ------------------------+------------------------
--|                           |                                           --                                |
--|                           |                                           --                                |
--|                           |                                           --                                |
--|                           |                                           --                                |
--|                           V                                           --                                V
universe i                                                                --
                                                                          -- So, we begin with the one _TRUTH_: Action is the exchange of potential
instance CAN_YOU_SEE_A_CHARACTERISTIC                                     -- energy for kinetic energy given by:
    (Box: Type i)(Pigeon: CarrierProcess Box)                             --                      S = ∫ KE(t) - PE(t) = ∫ f(t,g(t)) dt            (1)
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- for some path g(t): ℝ → ℝ³. According to the principle of _LEAST ACTION_
    : ADMISSIBLE Box Pigeon where                                         -- suggests that S remains minimized across all paths g. This means, by
  counting_process :=                                                     -- definition, g is the gradient of some field. Like on Earth.
  { carrier := Pigeon                                                     --
    count   := .zero nowtrino.fact                                        -- This opens up 2 different ways we can explore this function. The first
    iterate := fun particle => match particle with                        -- is as a variational formulation of some operator D. We are missing almost
      | .zero _     => .zero nowtrino.fact                                -- nothing to arrange for Euler-Lagrange dynamics to fall out.  Which is
      | .number _ _ _ => .number nowtrino.fact Pigeon.value               -- good, because it naturally tens to fall out, and never seems to _EVER_
                                                 (.zero nowtrino.fact) }  -- be violated. The second is through the lens of the Riesz representation
                                                                          -- theorem. The important thing is you can see _conservation_ slowly coming
instance CAN_YOU_COUNT_THEM                                               -- into focus as well as orientation. Lot's of other things are also in
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- here. Like the reason why calculus works with or without the axiom of
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- choice.
    [particle: ADMISSIBLE Box Pigeon]                                     --
    : COUNTABLE Box Pigeon where                                          -- So, the device is learning to count here. How does nature count? Well,
  index :=                                                                -- the _easiest_ to use in a _least action_ environment might be induction
    { count  := particle.counting_process                                 -- winding. Actually doesn't matter what is, that's what the device is going
      origin := .zero nowtrino.fact }                                     -- to look like its doing. Eventually. When it needs π. To compute a √. It
                                                                          -- certainly not get π and certainly cannot compute that √. It just needs
instance CAN_YOU_LABEL_THEM                                               -- the ability to do the computation to arbitrary precision.
    (Box: Type i)(Pigeon: CarrierProcess Box)                             --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- And that gets us to winding and the electron. While we _CANNOT_ label an
    [enumeration: COUNTABLE Box Pigeon]                                   -- individual electron, we can count how many times it goes around. During
    : ENCODED Box Pigeon where                                            -- that time of counting there are only so many electrons in the wire.
  limit_process :=                                                        -- Assuming "direct" current, then it is safe to assume conservation of
    { indexing_process := enumeration.index                               -- momentum, a 1-d direction of travel, and perfectly elastic collisions.
      limit            := .zero nowtrino.fact                             -- _Id est_: it looks like there is only 1 electron. So we can't label it.
      sequence         := .nil nowtrino.fact }                            -- But, we can count how many times that single electron we can't see or
                                                                          -- demonstrate exissts went around the loop and get the _right_ (unless it
instance CAN_YOU_SEE_THE_BOUNDARY                                         -- is a left-hand rule) answer.
    (Box: Type i)(Pigeon: CarrierProcess Box)                             --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- The winding number (Z-P) is given by
    [the_calculus_limit: ENCODED Box Pigeon]                              --                             1      f'(z)
    : RESIDUE Box Pigeon where                                            --                            --- ∮   ----- = Z − P                     (2)
  cauchy_process :=                                                       --                            2πi  γ   f(z)
    { limit_process  := the_calculus_limit.limit_process                  -- for Z the number of zeros inside the orbit and P the number of poles.
      value          := .zero nowtrino.fact                               --
      accumulation   := .nil nowtrino.fact }                              --
                                                                          --
instance DID_THE_PARTICLE_COLOR_OUTSIDE_THE_LINES                         --
    (Box: Type i)(Pigeon: CarrierProcess Box)                             --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [exp_iθ: RESIDUE Box Pigeon]                                          --
    : BINARY Box Pigeon where                                             --
  observation_process :=                                                  --
    { cauchy_process := exp_iθ.cauchy_process                             --
      before         := .nil nowtrino.fact                                --
      after          := .nil nowtrino.fact }                              --
  bit := .initial_condition                                               --
                  nowtrino.fact exp_iθ.cauchy_process.accumulation        --
  zero := .nil nowtrino.fact                                              --
  one  := .nil nowtrino.fact                                              --
                                                                          --
instance DO_YOU_SEE_A_BUNCH_OF_FLASHES                                    --
    (Box: Type i)(Pigeon: CarrierProcess Box)                             --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [flicker: BINARY Box Pigeon]                                          --
    : REPEATABLE Box Pigeon where                                         --
  repeatable_process :=                                                   --
  {                                                                       --
    observation_process := flicker.observation_process                    --
    stimulus := .initial_condition nowtrino.fact flicker.zero             --
    expectation := .hypothesis nowtrino.fact flicker.bit                  --
  }                                                                       --
                                                                          --
instance THE_FLASHES_SHOW_NOWTRINOS_ALMOST_EVERY_TIME                     --
    (Box: Type i)(Pigeon: CarrierProcess Box)                             --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [JMP: REPEATABLE Box Pigeon]                                          --
    : NUMERIC Box Pigeon where                                            --
  computational_process :=                                                --
  { repeatable_process := JMP.repeatable_process                          --
    output := some (.hypothesis nowtrino.fact)                            --
  }                                                                       --
                                                                          --
instance WRITE_DOWN_HOW_MANY_FLASHES_YOU_SEE_IN_A_TABLE                   --
    (Box: Type i)(Pigeon: CarrierProcess Box)                             --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [jupyter_notebook: NUMERIC Box Pigeon]                                --
    : REPRESENTABLE Box Pigeon where                                      --
  calculation_process :=                                                  --
  { computational_process :=                                              --
      { jupyter_notebook.computational_process with                       --
            closure := fun the_number_of_clicks => the_number_of_clicks   --
      }                                                                   --
    program := jupyter_notebook.computational_process.close               --
                         jupyter_notebook.computational_process.output    --
    state := .program nowtrino.fact                                       --
                       (jupyter_notebook.computational_process.close      --
                        jupyter_notebook.computational_process.output)    --
  }                                                                       --
  representable? := fun _ expected_response =>                            --
           ⟨Computation.program nowtrino.fact expected_response, rfl⟩     --
                                                                          --
instance ROSS!_GET_THE_READOUTS                                           --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [the_invariant: REPRESENTABLE Box Pigeon]                             --
    : PHYSICAL Box Pigeon where                                           --
  noisy_process := {                                                      --
    turing_process := the_invariant.calculation_process                   --
    program := .halting nowtrino.fact (.program nowtrino.fact             --
                              the_invariant.calculation_process.program)  --
  }                                                                       --
  threshold := .nonhalting  nowtrino.fact                                 --
      (.program nowtrino.fact the_invariant.calculation_process.program)  --
      (some (ChaitinsNumberSequence.halting nowtrino.fact                 --
                               the_invariant.calculation_process.state))  --
  admissible? := fun _ _ _ => rfl                                         --
                                                                          --
                                                                          --
noncomputable instance ARE_THE_UNITS_RIGHT                                --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [anechoic_chamber: PHYSICAL Box Pigeon]                               --
    [Inhabited nowtrino.symbol]                                           --
    : COMPARABLE Box Pigeon where                                         --
  physical_process :=                                                     --
  { noisy_process := anechoic_chamber.noisy_process                       --
    representation := default                                             --
    invariant := .base nowtrino.fact default                              --
    value := .base nowtrino.fact (ULift.up default)                       --
  }                                                                       --
  smaller_than := fun one_foot π  => one_foot = π                         --
                                                                          --
instance DO_YOU_SEE_THE_LIGHT_FLASH_WHEN_YOU_HEAR_THE_CLICK               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [anechoic_chamber: PHYSICAL Box Pigeon]                               --
    [distinct: COMPARABLE Box Pigeon]                                     --
    : OBSERVED Box Pigeon where                                           --
  slip_process :=                                                         --
  { physical_process := distinct.physical_process                         --
    projection := .origin nowtrino.fact                                   --
                      distinct.physical_process.noisy_process.program     --
                      nowtrino.symbol                                     --
    stress := anechoic_chamber.threshold                                  --
    threshold := nowtrino.symbol                                          --
  }                                                                       --
  observation := ULift nowtrino.symbol                                    --
                                                                          --
instance THATS_THE_PHOTOELECTRIC_EFFECT                                   --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon]                                               --
    [static_friction: OBSERVED Box Pigeon]                                --
    : PRESENT Box Pigeon where                                            --
  santa_claus:=                                                           --
  { static_fraction := static_friction.slip_process                       --
    accumulation := .tree nowtrino.fact                                   --
  }                                                                       --
  quantum := Type i                                                       --
                                                                          --
instance THE_PHOTON_IS_MEASURABLE                                         --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon]                                               --
    [gift_from: PRESENT Box Pigeon]                                       --
    : MEASURABLE Box Pigeon where                                         --
  gauge_process :=                                                        --
  { sensing_process := gift_from.santa_claus                              --
    clock      := .this_superpigeon nowtrino.fact (.tree nowtrino.fact)   --
  }                                                                       --
                                                                          --
instance PERHAPS_NOT_WITH_A_MULTIMETER_BUT_YOU_UNDERSTAND_WHAT_I_MEAN     --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon]                                               --
    [multimeter: MEASURABLE Box Pigeon]                                   --
    : GUNGAN Box Pigeon where                                             --
  meesa_process :=                                                        --
  { gauge_process := multimeter.gauge_process                             --
    concept := .color nowtrino.fact                                       --
                  multimeter.gauge_process.sensing_process.accumulation   --
  }                                                                       --
                                                                          --
def WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA                        --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon]                                               --
    [jarjar: GUNGAN Box Pigeon]                                           --
    : SOURCE Box Pigeon where                                             --
  cd_process :=                                                           --
  { meesa_process := jarjar.meesa_process                                 --
    zero := .physics nowtrino.fact jarjar.meesa_process.concept           --
  }                                                                       --
  one := .zero_like nowtrino.fact (.physics nowtrino.fact                 --
                                         jarjar.meesa_process.concept)    --
                                                                          --
instance AND_THE_COMPILER_WILL_CONVERT_THE_RAW_DATA_TO_TABLES             --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon]                                               --
    [jarjar: GUNGAN Box Pigeon]                                           --
    [data_feed: SOURCE Box Pigeon]                                        --
    : EXECUTED Box Pigeon where                                           --
  compiled_process :=                                                     --
  { digital_process := data_feed.cd_process                               --
    source := data_feed                                                   --
    opcodes := .boot nowtrino.fact                                        --
                  (.physics nowtrino.fact jarjar.meesa_process.concept)   --
  }                                                                       --
                                                                          --
instance ONE_VALUE_AT_A_TIME_IN_ORDER_AND_WRITE_SOMETHING_TO_DISK         --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [result: EXECUTED Box Pigeon]                                         --
    : VALUE Box Pigeon where                                              --
  mathematical_process := {                                               --
    compiled_process := result.compiled_process                           --
    mapping := fun input => match input with                              --
      |.satire_about finite_element_analysis => .satire_about             --
                                              finite_element_analysis     --
      |.compile f e a => .execute f e a                                   --
      |.execute f e a => .compile f e a                                   --
  }                                                                       --
  monad := .satire_about nowtrino.fact                                    --
                                                                          --
instance TURNS_OUT_YOU_CAN_FILL_YOUR_DISK                                 --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [gift_from: PRESENT Box Pigeon]                                       --
    [GUNGAN Box Pigeon] [SOURCE Box Pigeon] [EXECUTED Box Pigeon]         --
    [uncountable: VALUE Box Pigeon]                                       --
    : MAGNITUDE Box Pigeon where                                          --
  adding_process :=                                                       --
  { mideastern_process := uncountable.mathematical_process                --
    plus := uncountable                                                   --
    sum := .zero nowtrino.fact.truth gift_from.santa_claus.accumulation   --
  }                                                                       --
                                                                          --
instance SO_YOU_NEED_TO_GET_MORE_DISKS                                    --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [tar_file: MAGNITUDE Box Pigeon]                                      --
    : SCALED Box Pigeon where                                             --
  multiplying_process :=                                                  --
  { adding_process := tar_file.adding_process                             --
    product := .one nowtrino.fact.truth tar_file.adding_process.sum       --
    total := .zero nowtrino.fact.truth (.tree nowtrino.fact)              --
  }                                                                       --
                                                                          --
instance AND_MORE_PROCESSORS_BECAUSE_THERE_ARE_A_LOT_OF_NOWTRINOS         --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [gift_from: PRESENT Box Pigeon]                                       --
    [GUNGAN Box Pigeon] [SOURCE Box Pigeon] [EXECUTED Box Pigeon]         --
    [VALUE Box Pigeon]                                                    --
    [shit_loads: SCALED Box Pigeon]                                       --
    : LOAD Box Pigeon where                                               --
  basic_operation :=                                                      --
  { GOSUB := shit_loads.multiplying_process                               --
    TEN := gift_from.santa_claus.accumulation                             --
    span := .origin nowtrino.fact.truth                                   --
                               shit_loads.multiplying_process.product     --
  }                                                                       --
                                                                          --
instance SO_MANY_SENSITIVE_NOWTRINO_DETECTORS___WHERE_DID_IT_GO           --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [DISTINGUISHABLE Box Pigeon]                                          --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [comprehensive_software: LOAD Box Pigeon]                             --
    : OF Box Pigeon where                                                 --
  galerkin_process :=                                                     --
  { ANSYS_process := comprehensive_software.basic_operation               --
    polynomial := .constant .Truth                                        --
  }                                                                       --
                                                                          --
instance THERE_IT_IS___CERTAIN_ELEMENTS_RESPOND_TO_NOWTRINO_DETECTION     --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [element: OF Box Pigeon]                                              --
    : BULLSHIT Box Pigeon where                                           --
  arm_wave_process :=                                                     --
  { dunking_contest := element.galerkin_process                           --
    guess := .observation nowtrino.fact.truth                             --
  }                                                                       --
                                                                          --
instance WE_NEED_TO_GET_A_GRANT_TO_GET_MORE_DETECTORS___WE_KEEP_LOSING_IT --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [DISTINGUISHABLE Box Pigeon]                                          --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    : PROPAGANDA Box Pigeon where                                         --
  questions := CrusadeProcess.default Box Pigeon                          --
                                                                          --
def InitiationProcess.default                                             --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [DISTINGUISHABLE Box Pigeon][ADMISSIBLE Box Pigeon]                   --
    [COUNTABLE Box Pigeon][ENCODED Box Pigeon][RESIDUE Box Pigeon]        --
    [BINARY Box Pigeon][REPEATABLE Box Pigeon][NUMERIC Box Pigeon]        --
    [REPRESENTABLE Box Pigeon][PHYSICAL Box Pigeon]                       --
    [COMPARABLE Box Pigeon][OBSERVED Box Pigeon][PRESENT Box Pigeon]      --
    [MEASURABLE Box Pigeon][GUNGAN Box Pigeon][SOURCE Box Pigeon]         --
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon]         --
    [SCALED Box Pigeon][LOAD Box Pigeon][OF Box Pigeon]                   --
    [BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon]                          --
    : InitiationProcess Box Pigeon where                                  --
  axioms := CrusadeProcess.default Box Pigeon                             --
  sacred_texts := .inside_joke Fact.Truth.truth                           --
                                                                          --
instance MAKE_SURE_WE_CAN_GET_A_COUPLE_GRAD_STUDENTS                      --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [DISTINGUISHABLE Box Pigeon][COMPARABLE Box Pigeon]                   --
    [SOURCE Box Pigeon]                                                   --
    : ACOLYTE Box Pigeon where                                            --
  euclid := InitiationProcess.default Box Pigeon                          --
                                                                          --
--| Now, they can count clicks and get a Ph.D.                            --
def LearningProcess.default                                               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [DISTINGUISHABLE Box Pigeon][ADMISSIBLE Box Pigeon]                   --
    [COUNTABLE Box Pigeon][ENCODED Box Pigeon][RESIDUE Box Pigeon]        --
    [BINARY Box Pigeon][REPEATABLE Box Pigeon][NUMERIC Box Pigeon]        --
    [REPRESENTABLE Box Pigeon][PHYSICAL Box Pigeon]                       --
    [COMPARABLE Box Pigeon][OBSERVED Box Pigeon][PRESENT Box Pigeon]      --
    [MEASURABLE Box Pigeon][GUNGAN Box Pigeon][SOURCE Box Pigeon]         --
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon]         --
    [SCALED Box Pigeon][LOAD Box Pigeon][OF Box Pigeon]                   --
    [BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon][ACOLYTE Box Pigeon]      --
    : LearningProcess Box Pigeon where                                    --
  teaching := InitiationProcess.default Box Pigeon                        --
  galileo := .inside_joke Fact.Truth.truth                                --
  invariant := .repeatable Fact.Truth.truth                               --
                                                                          --
instance ABD                                                              --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [DISTINGUISHABLE Box Pigeon]                                          --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    : SCIENTIFIC Box Pigeon where                                         --
  discovering := LearningProcess.default Box Pigeon                       --
  invariant := .hypothesis Fact.Truth.truth                               --
                                        (.inside_joke Fact.Truth.truth)   --
                                                                          --
instance YOU_HAVE_TO_STOP_TAKING_CLASSES_TO_GRADUATE                      --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [experiment: SCIENTIFIC Box Pigeon]                                   --
    : TRUTH Box Pigeon where                                              --
  becomes :=                                                              --
  { shows_me_higher_order_terms := experiment.discovering                 --
    knowledge := .jarjar nowtrino.fact.truth                              --
  }                                                                       --
                                                                          --
instance THEN_COMES_THE_LAB_WORK                                          --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [truth: TRUTH Box Pigeon]                                             --
    : WITNESSED Box Pigeon where                                          --
  we_saw :=                                                               --
  { we_experience := truth.becomes                                        --
    in_the_literature := .the_proof nowtrino.fact.truth                   --
  }                                                                       --
  the_experiment := .the_proof nowtrino.fact.truth                        --
                                                                          --
def FINALLY_YOU_GRADUATE                                                  --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [yet: WITNESSED Box Pigeon]                                           --
    : REAL Box Pigeon where                                               --
  by_His_noodly_appendage :=                                              --
  { frame_of_reference := yet.we_saw                                      --
    in_reality := .logically nowtrino.fact.truth                          --
  }                                                                       --
  nagging_doubt := .but yet.the_experiment nowtrino.fact.truth            --
                                     (.logically nowtrino.fact.truth)     --
                                                                          --
instance AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [yet: WITNESSED Box Pigeon]                                           --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    : LOCAL Box Pigeon where                                              --
  the_continuum :=                                                        --
  { the_æther := flying_spaghetti_monster.by_His_noodly_appendage         --
    Du := .the_newton yet.the_experiment nowtrino.fact.truth              --
  }                                                                       --
  the_ball := nowtrino.fact.truth                                         --
                                                                          --
instance PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE             --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [yet: WITNESSED Box Pigeon]                                           --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (nowtrino_model: LOCAL Box Pigeon)                                    --
    : UNIVERSAL Box Pigeon nowtrino_model where                           --
  the_train_of_thought :=                                                 --
  { the_local_schedule :=                                                 --
    { the_æther := flying_spaghetti_monster.by_His_noodly_appendage       --
      Du := .the_gateaux yet.the_experiment Fact.Truth.truth              --
                  nowtrino.fact.truth                                     --
                  (.the_newton yet.the_experiment nowtrino.fact.truth)    --
    }                                                                     --
    the_direction_to_the_destination := .einstein nowtrino.fact           --
    uptown_or_downtown := match nowtrino.fact.decTruth with               --
        | isTrue  _ => Fact.Truth                                         --
        | isFalse _ => nowtrino.fact                                      --
    the_train_in := Type i                                                --
  }                                                                       --
  once_around  := .blackhole nowtrino.fact.truth (ULift.{i+1} Box)        --
                                            (.einstein nowtrino.fact)     --
  twice_around := .whitehole nowtrino.fact Box (.einstein nowtrino.fact)  --
                                                                          --
instance OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2                                 --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino_model: LOCAL Box Pigeon)                                    --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino_model)                    --
    : LOGICAL Box Pigeon naotrino_model yarn_theory where                 --
  feelings :=                                                             --
  { bullshit_meter := yarn_theory.the_train_of_thought                    --
    after_some_time := .whitehole nowtrino.fact Box                       --
                                             (.einstein nowtrino.fact)    --
    according_to_newton := .stokes nowtrino.fact                          --
                         (.einstein nowtrino.fact) nowtrino.fact.truth    --
  }                                                                       --
  microsoft_basic := Calibration.EKG.executed                             --
                                                                          --
instance DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK     --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [nonsensical: LOGICAL Box Pigeon naotrino yarn_theory]                --
    : HALTED Box Pigeon naotrino yarn_theory where                        --
  scientific_paper :=                                                     --
    let feelings : HeartbeatProcess Box Pigeon naotrino yarn_theory :=    --
                                                    nonsensical.feelings  --
    { stamina := feelings                                                 --
      trilinos : Calibration.EKG := nonsensical.microsoft_basic           --
      numerical_analysis := (.load Fact.Truth.truth Box)                  --
    }                                                                     --
                                                                          --
instance THE_NAOTRINO_IS_MEASURED                                         --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [documents_on_file: HALTED Box Pigeon naotrino yarn_theory]           --
    : MEASURED Box Pigeon naotrino yarn_theory where                      --
  a_distance :=                                                           --
  { description := documents_on_file.scientific_paper                     --
    the_measurement_of := .zero nowtrino.fact                             --
    in_heartbeats := .origin nowtrino.fact (.zero nowtrino.fact) Box      --
    saved_as_y := Box                                                     --
  }                                                                       --
                                                                          --
instance WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES                        --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [DISTINGUISHABLE Box Pigeon][COMPARABLE Box Pigeon][SOURCE Box Pigeon]--
    [REAL Box Pigeon]                                                     --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [weakly_interacting_particle:                                         --
                             MEASURED Box Pigeon naotrino yarn_theory]    --
    : COMPILED Box Pigeon naotrino yarn_theory where                      --
  a_truth_about_the_world :=                                              --
  { too_good_to_be_true := weakly_interacting_particle.a_distance         --
    preprint := (.introduction Fact.Truth Box)                            --
  }                                                                       --
  a_demonstration_of_a_constant := .methodology Fact.Truth Fact.Truth     --
              Box (ULift.{i+1, i} Box) (.introduction Fact.Truth Box)     --
                                                                          --
instance HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME                             --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [holy_shit: COMPILED Box Pigeon naotrino yarn_theory]                 --
    : A_TRUTH_ABOUT Box Pigeon naotrino yarn_theory where                 --
  you_the_reader :=                                                       --
  { in_a_giant_book := holy_shit.a_truth_about_the_world                  --
    a_constant := .zero Fact.Truth                                        --
    current_page_number := .zero Fact.Truth                               --
    total_pages := .zero Fact.Truth                                       --
    of_the_proof := .methodology Fact.Truth Fact.Truth Box                --
                  (ULift.{i+1, i} Box) (.introduction Fact.Truth Box)     --
  }                                                                       --
  TRUE := .zero Fact.Truth                                                --
  raw_output := .one                                                      --
              Fact.Truth                                                  --
              (.one Fact.Truth (.zero nowtrino.fact))                     --
              (.introduction nowtrino.fact Box)                           --
              (.methodology Fact.Truth nowtrino.fact Box                  --
                    (ULift.{i+1, i} Box) (.introduction Fact.Truth Box))  --
              (.zero nowtrino.fact)                                       --
  a_constant := .one                                                      -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
              Fact.Truth --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
              holy_shit.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_local_schedule.the_æther.frame_of_reference.we_experience.shows_me_higher_order_terms.teaching.axioms.to_pwn_n00bz.dunking_contest.ANSYS_process.GOSUB.adding_process.mideastern_process.compiled_process.digital_process.meesa_process.gauge_process.sensing_process.static_fraction.physical_process.noisy_process.turing_process.computational_process.repeatable_process.observation_process.cauchy_process.limit_process.indexing_process.count.carrier.value -- |
                                     (.introduction nowtrino.fact Box) --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
              (.methodology Fact.Truth nowtrino.fact Box                  -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
                  (ULift.{i+1, i} Box) (.introduction Fact.Truth Box))    --
              (.zero nowtrino.fact)                                       --
  the_constant_is_at_least_true := by trivial                             --
                                                                          --
noncomputable instance OF_COURSE_IT_DOES___I_JUST_PUT_IT_THERE            --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [DISTINGUISHABLE Box Pigeon]                                          --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [guano: A_TRUTH_ABOUT Box Pigeon naotrino yarn_theory]                --
    : INFERRED Box Pigeon naotrino yarn_theory where                      --
  same_difference :=                                                      --
  { you_the_knower      := guano.you_the_reader                           --
    your_conclusion     := .different (Fact.SAME (guano:=guano))          --
                  (guano.TRUE) (guano.a_constant) (some Fact.Truth.truth) --
  }                                                                       --
  α := .same Fact.Truth guano.a_constant                                  --
                                                                          --
def You_the_Reader                                                        --
    {Box: Type i}                                                         --
    {Pigeon: CarrierProcess Box}                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][ADMISSIBLE Box Pigeon]         --
    [COUNTABLE Box Pigeon][ENCODED Box Pigeon][RESIDUE Box Pigeon]        --
    [BINARY Box Pigeon][REPEATABLE Box Pigeon][NUMERIC Box Pigeon]        --
    [REPRESENTABLE Box Pigeon][PHYSICAL Box Pigeon]                       --
    [COMPARABLE Box Pigeon][OBSERVED Box Pigeon][PRESENT Box Pigeon]      --
    [MEASURABLE Box Pigeon][GUNGAN Box Pigeon][SOURCE Box Pigeon]         --
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon]         --
    [SCALED Box Pigeon][LOAD Box Pigeon][OF Box Pigeon]                   --
    [BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon][ACOLYTE Box Pigeon]      --
    [SCIENTIFIC Box Pigeon][TRUTH Box Pigeon][WITNESSED Box Pigeon]       --
    [REAL Box Pigeon]                                                     --
    {fact: LOCAL Box Pigeon}                                              --
    {about_the_world: UNIVERSAL Box Pigeon fact}                          --
    [LOGICAL Box Pigeon fact about_the_world]                             --
    [HALTED Box Pigeon fact about_the_world]                              --
    [MEASURED Box Pigeon fact about_the_world]                            --
    [stdout: COMPILED Box Pigeon fact about_the_world]                    --
    : AtreyuProcess Box Pigeon fact about_the_world where                 --
  in_a_giant_book := stdout.a_truth_about_the_world                       --
  a_constant := .zero nowtrino.fact                                       --
  current_page_number := Pigeon.value                                     --
  of_the_proof := stdout.a_demonstration_of_a_constant                    --
                                                                          --
def BUT_THE_TRUTH_IS_YOU_THE_READER_UNDERSTANDS_THE_ARGUMENT_NAO          --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [COMPILED Box Pigeon naotrino yarn_theory]                            --
    (_: CarrierProcess Box)                                               --
  : A_TRUTH_ABOUT Box Pigeon naotrino yarn_theory where                   --
    you_the_reader := You_the_Reader (fact:=naotrino)                     --
                                       (about_the_world:=yarn_theory)     --
    a_constant     := THEORY.raw_output (You_the_Reader                   --
                (fact:=naotrino) (about_the_world:=yarn_theory))          --
                (.zero nowtrino.fact)                                     --
    the_constant_is_at_least_true    := by trivial                        --
                                                                          --
def SO_YOU_START_TO_BUILD_ANOTHER_DEMONSTRATION_PROCESS                   --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [multimeter: MEASURED Box Pigeon naotrino yarn_theory]                --
    [holy_shit: COMPILED Box Pigeon naotrino yarn_theory]                 --
    (_: CarrierProcess Box)                                               --
    : COMPILED Box Pigeon naotrino yarn_theory where                      --
  a_truth_about_the_world :=                                              --
  { too_good_to_be_true := multimeter.a_distance                          --
    preprint := .methodology nowtrino.fact Fact.Truth Box                 --
         (ULift.{i+1,i} Box) holy_shit.a_demonstration_of_a_constant      --
  }                                                                       --
  a_demonstration_of_a_constant := .methodology nowtrino.fact             --
            Fact.Truth Box (ULift.{i+1,i} Box)                            --
                  holy_shit.a_demonstration_of_a_constant                 --
                                                                          --
def IN_ORDER_TO_MEASURE_THE_CONSTANT_EMPIRICALLY                          --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [nonsensical: LOGICAL Box Pigeon naotrino yarn_theory]                --
    [documents_on_file: HALTED Box Pigeon naotrino yarn_theory]           --
    [multimeter: MEASURED Box Pigeon naotrino yarn_theory]                --
    (_: CarrierProcess Box)                                               --
    [metaphor: COMPILED Box Pigeon naotrino yarn_theory]                  --
    : MEASURED Box Pigeon naotrino yarn_theory where                      --
  a_distance :=                                                           --
  {   description := documents_on_file.scientific_paper                   --
      the_measurement_of := multimeter.a_distance.the_measurement_of      --
      in_heartbeats := .distance_to nowtrino.fact (.zero Fact.Truth)      --
            (multimeter.a_distance.the_measurement_of) Box                ------------+
            (ULift.{i+1,i} Box) --                                                    |
             metaphor.a_truth_about_the_world.too_good_to_be_true.in_heartbeats --    |
      saved_as_y := Box --                                                            |
  }                                                                       ------------+
                                                                          --
def YOU_NEED_TO_DEVELOP_A_BOUNDED_PROCESS                                 --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [nonsensical: LOGICAL Box Pigeon naotrino yarn_theory]                --
    [documents_on_file: HALTED Box Pigeon naotrino yarn_theory]           --
    (_: CarrierProcess Box)                                               --
    [data: MEASURED Box Pigeon naotrino yarn_theory]                      --
    : HALTED Box Pigeon naotrino yarn_theory where                        --
  scientific_paper :=                                                     --
  { stamina := data.a_distance.description.stamina                        --
    trilinos := documents_on_file.scientific_paper.trilinos               --
    teraFLOPs := data.a_distance.description.teraFLOPs                    --
    numerical_analysis :=                                                 --
                documents_on_file.scientific_paper.numerical_analysis     --
  }                                                                       --
                                                                          --
def PERHAPS_ONE_THAT_REALLY_MAKES_YOU_THINK                               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [nonsensical: LOGICAL Box Pigeon naotrino yarn_theory]                --
    [documents_on_file: HALTED Box Pigeon naotrino yarn_theory]           --
    (_: CarrierProcess Box)                                               --
    : LOGICAL Box Pigeon naotrino yarn_theory where                       --
  feelings := documents_on_file.scientific_paper.stamina                  --
  microsoft_basic := nonsensical.microsoft_basic                          --
                                                                          --
def PERHAPS_ONE_THAT_USES_THE_DEVICE_ITSELF                               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    (_: CarrierProcess Box)                                               --
    : UNIVERSAL Box Pigeon naotrino where                                 --
  the_train_of_thought := yarn_theory.the_train_of_thought                --
  once_around := yarn_theory.once_around                                  --
  twice_around := yarn_theory.the_train_of_thought.photon_torpedo         --
                                             yarn_theory.once_around      --
                                                                          --
def PERHAPS_ONE_THAT_USES_CALCULUS                                        --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [the_a_train: UNIVERSAL Box Pigeon naotrino]                          --
    : LOCAL Box Pigeon where                                              --
  the_continuum := the_a_train.the_train_of_thought.the_local_schedule    --
  the_ball      := naotrino.the_ball                                      --
                                                                          --
def YEAH_CALCULUS___YOU_CAN_DO_THE_CALCULUS_RITE                          --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [principia: LOCAL Box Pigeon]                                         --
    : REAL Box Pigeon where                                               --
  by_His_noodly_appendage := principia.the_continuum.the_æther            --
  nagging_doubt := .logically naotrino.the_ball                           --
                                                                          --
def MATH_MODELING_IS_EASY___JUST_WATCH                                    --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [invariant: REAL Box Pigeon]                                          --
    : WITNESSED Box Pigeon where                                          ------------------------------------+
  we_saw := invariant.by_His_noodly_appendage.frame_of_reference --                                           |
  the_experiment := flying_spaghetti_monster.by_His_noodly_appendage.frame_of_reference.in_the_literature --  |
--                                                                                                            |
def WHICH_WE_IMMEDIATELY_SEE_THE_FIRST_TIME_IN_THE_LAB                    ------------------------------------+
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [overwhelming_evidence: WITNESSED Box Pigeon]                         --
    : TRUTH Box Pigeon where                                              --
  becomes := overwhelming_evidence.we_saw.we_experience                   --
                                                                          --
def OBVIOUSLY_YOU_START_A_RESEARCH_PROGRAM                                --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [our_mission: TRUTH Box Pigeon]                                       --
    : SCIENTIFIC Box Pigeon where                                         --
  discovering := our_mission.becomes.shows_me_higher_order_terms          --
  invariant := our_mission.becomes.shows_me_higher_order_terms.invariant  --
                                                                          --
def AND_HUNDREDS_OF_POSTDOCS_COME_TO_COUNT_NAOTRINOS                      --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [postdoc: SCIENTIFIC Box Pigeon]                                      --
    : ACOLYTE Box Pigeon where                                            --
  euclid := postdoc.discovering.teaching                                  --
                                                                          --
def BUT_THEN_REIMANN_COMES_ALONG                                          --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [professor: ACOLYTE Box Pigeon]                                       --
    : PROPAGANDA Box Pigeon where                                         --
  questions := professor.euclid.axioms                                    --
                                                                          --
def AND_THE_AMOUNT_OF_CALCULUS_YOU_HAVE_TO_DO_EXPLODES                    --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [geometry: PROPAGANDA Box Pigeon]                                     --
    : BULLSHIT Box Pigeon where                                           --
  arm_wave_process := geometry.questions.to_pwn_n00bz                     --
                                                                          --
def AND_YOU_STUDY_TRIANGLES                                               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [hours_of_math: BULLSHIT Box Pigeon]                                  --
    : OF Box Pigeon where                                                 --
  galerkin_process := hours_of_math.arm_wave_process.dunking_contest      --
                                                                          --
def BUT_YOU_AND_I_KNOW_ANSYS_HAS_GOT_THIS                                 --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [area: OF Box Pigeon]                                                 --
    : LOAD Box Pigeon where                                               --
  basic_operation := area.galerkin_process.ANSYS_process                  --
                                                                          --
def YOU_ARE_ALSO_AWARE_THAT_ANSYS_IS_SLOW                                 --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [still_takes_forever: LOAD Box Pigeon]                                --
    : SCALED Box Pigeon where                                             --
  multiplying_process := still_takes_forever.basic_operation.GOSUB        --
                                                                          --
def BUT_YOU_EVENTUALLY_ESTIMATE_THE_TOTAL_SIZE_OF_THE_COMPUTATION         --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [weight: SCALED Box Pigeon]                                           --
    : MAGNITUDE Box Pigeon where                                          --
  adding_process := weight.multiplying_process.adding_process             --
                                                                          --
def SO_YOU_SUBMIT_THE_JOB_AND_COUNT_HOW_LONG_IT_TAKES                     --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    [uncountable: VALUE Box Pigeon]                                       --
    (_: CarrierProcess Box)                                               --
    [mass: MAGNITUDE Box Pigeon]                                          --
    : VALUE Box Pigeon where                                              --
  mathematical_process := mass.adding_process.mideastern_process          --
  monad := uncountable.monad                                              --
                                                                          --
def BUT_IT_MAY_NOT_CONVERGE                                               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [constant: VALUE Box Pigeon]                                          --
    : EXECUTED Box Pigeon where                                           --
  compiled_process := constant.mathematical_process.compiled_process      --
                                                                          --
def IT_DEFINITELY_COMPILES_THOUGH                                         --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon]                                               --
    [SOURCE Box Pigeon]                                                   --
    [REAL Box Pigeon]                                                     --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [lean: EXECUTED Box Pigeon]                                           --
    : SOURCE Box Pigeon where                                             --
  cd_process := lean.compiled_process.digital_process                     --
  one := lean.compiled_process.digital_process.zero                       --
                                                                          --
def WHICH_MEANS_IT_HAS_A_BETA_REDUCTION                                   --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [the_argument: SOURCE Box Pigeon]                                     --
    : GUNGAN Box Pigeon where                                             --
  meesa_process := the_argument.cd_process.meesa_process                  --
                                                                          --
def AND_ALWAYS_RETURNS_THAT_THE_ARGUMENT_IS_CONSISTENT                    --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [the_argument_for_naotrinos: GUNGAN Box Pigeon]                       --
    : MEASURABLE Box Pigeon where                                         --
  gauge_process := the_argument_for_naotrinos.meesa_process.gauge_process --
                                                                          --
def AT_THE_END_OF_THE_DAY_I_HAVE_TO_ADMIT_IT_IS_A_BLACK_BOX               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [the_bug: MEASURABLE Box Pigeon]                                      --
    : PRESENT Box Pigeon where                                            --
  santa_claus := the_bug.gauge_process.sensing_process                    --
  quantum := Box                                                          --
                                                                          --
def STILL_THERE_COULD_BE_A_MISSPELLING_IN_THIS_LOGIC                      --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [fallacy: PRESENT Box Pigeon]                                         --
    : OBSERVED Box Pigeon where                                           --
  slip_process := fallacy.santa_claus.static_fraction                     --
  observation  := Box                                                     --
                                                                          --
namespace Metavariable                                                    --
                                                                          --
def le {α : Type i} : Metavariable α → Metavariable α → Prop              --
  | .base this_one _,        .base that_one _        =>                   --
                                        this_one.truth = that_one.truth   --
  | .base _ _,               .step _ _               => True              --
  | .step _ _,               .base _ _               => False             --
  | .step this_step here,    .step that_step there   =>                   --
                (this_step.truth = that_step.truth ∧ le here there) ∨     --
                le (.step this_step here) there                           --
termination_by _ how_far => sizeOf how_far                                --
                                                                          --
end Metavariable                                                          --
                                                                          --
instance {α : Type i} : LE (Metavariable α) where                         --
  le := Metavariable.le                                                   --
                                                                          --
def AND_WE_WONT_KNOW_FOR_SURE                                             --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [failure: OBSERVED Box Pigeon]                                        --
    : COMPARABLE Box Pigeon where                                         --
  physical_process := failure.slip_process.physical_process               --
  smaller_than := fun x y => x ≤ y ∧ y ≤ x                                --
                                                                          --
def ONCE_WE_DETECT_NAOTRINO_MOTION_WE_WILL_DETECT_THE_NOWTRINO            --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [number_of_clicks: COMPARABLE Box Pigeon]                             --
    : PHYSICAL Box Pigeon where                                           --
  noisy_process := number_of_clicks.physical_process.noisy_process        --
  threshold := number_of_clicks.physical_process.noisy_process.program    --
  admissible? := fun at_rest in_motion => by intro _; rfl                 --
                                                                          --
def WE_CAN_REPRESENT_CLICK_COUNT_WITH_A_TALLY_EVEN_WITH_NOISE             --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [anechoic_chamber: PHYSICAL Box Pigeon]                               --
    [COMPARABLE Box Pigeon][PRESENT Box Pigeon][MEASURABLE Box Pigeon]    --
    [GUNGAN Box Pigeon][SOURCE Box Pigeon][SOURCE Box Pigeon]             --
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon]         --
    [SCALED Box Pigeon][LOAD Box Pigeon][OF Box Pigeon]                   --
    [BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon][ACOLYTE Box Pigeon]      --
    [SCIENTIFIC Box Pigeon][TRUTH Box Pigeon][WITNESSED Box Pigeon]       --
    [REAL Box Pigeon]                                                     --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [hiss: PHYSICAL Box Pigeon]                                           --
    : REPRESENTABLE Box Pigeon where                                      --
  calculation_process :=                                                  --
    { anechoic_chamber.noisy_process.turing_process with                  --
        program := hiss.noisy_process.turing_process.program              ----------------+
        computational_process := --                                                       |
          { anechoic_chamber.noisy_process.turing_process.computational_process with --   |
              closure := fun a_tally => a_tally } } --                                    |
  representable? := fun a_fact a_study =>                                 ----------------+
    ⟨hiss.noisy_process.turing_process.turing_step?                       --
                              (Computation.program a_fact a_study), rfl⟩  --
                                                                          --
def SO_WE_ARE_CONFIDENT_OF_THE_COUNT_IN_THE_DEVICE                        --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box) ------------------------+ a card!             --
    [glyph: REPRESENTABLE Box Pigeon]                                     --
    : NUMERIC Box Pigeon where                                            --
  computational_process :=                                                --
                    glyph.calculation_process.computational_process       --
                                                                          --
def AND_IT_CLICKS_AGAIN_AND_AGAIN_AND_AGAIN                               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [JMP: REPEATABLE Box Pigeon]                                          --
    [NUMERIC Box Pigeon][REPRESENTABLE Box Pigeon][PHYSICAL Box Pigeon]   --
    [COMPARABLE Box Pigeon][OBSERVED Box Pigeon][PRESENT Box Pigeon]      --
    [MEASURABLE Box Pigeon][GUNGAN Box Pigeon][SOURCE Box Pigeon]         --
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon]         --
    [SCALED Box Pigeon][LOAD Box Pigeon][OF Box Pigeon]                   --
    [BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon][ACOLYTE Box Pigeon]      --
    [SCIENTIFIC Box Pigeon][TRUTH Box Pigeon][WITNESSED Box Pigeon]       --
    [REAL Box Pigeon]                                                     --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [click_count: NUMERIC Box Pigeon]                                     --
    : REPEATABLE Box Pigeon where                                         --
  repeatable_process :=                                                   --
                 click_count.computational_process.repeatable_process     --
                                                                          --
def THE_COUNTER_IS_IMPLEMENTED_IN_A_BINARY_ACCUMULATOR                    --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [flicker: BINARY Box Pigeon]                                          --
    [REPEATABLE Box Pigeon][NUMERIC Box Pigeon][REPRESENTABLE Box Pigeon] --
    [PHYSICAL Box Pigeon][COMPARABLE Box Pigeon][OBSERVED Box Pigeon]     --
    [PRESENT Box Pigeon][MEASURABLE Box Pigeon][GUNGAN Box Pigeon]        --
    [SOURCE Box Pigeon][EXECUTED Box Pigeon][VALUE Box Pigeon]            --
    [MAGNITUDE Box Pigeon][SCALED Box Pigeon][LOAD Box Pigeon]            --
    [OF Box Pigeon][BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon]           --
    [ACOLYTE Box Pigeon][SCIENTIFIC Box Pigeon][TRUTH Box Pigeon]         --
    [WITNESSED Box Pigeon][REAL Box Pigeon]                               --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [nonstop: REPEATABLE Box Pigeon]                                      --
    : BINARY Box Pigeon where                                             --
  observation_process := nonstop.repeatable_process.observation_process   --
  zero := .nil nowtrino.fact                                              --
  one  := .index                                                          ------------------------------+
              nowtrino.fact --                                                                          |
              nonstop.repeatable_process.observation_process.cauchy_process.limit_process.sequence --   |
              (.nil nowtrino.fact) --                                                                   |
  bit  := nonstop.repeatable_process.observation_process.iterate          ------------------------------+
              flicker.bit                                                 --
                                                                          --
def JUST_NEED_TO_INSPECT_THE_REGISTER_TO_SEE_CURRENT_SEQUENCE_INDEX       --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [register: BINARY Box Pigeon]                                         --
    : RESIDUE Box Pigeon where                                            --
  cauchy_process := register.observation_process.cauchy_process           --
                                                                          --
def FIGURE_OUT_WHAT_IT_CONVERGES_TO                                       --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [converged_value: RESIDUE Box Pigeon]                                 --
    : ENCODED Box Pigeon where                                            --
  limit_process := converged_value.cauchy_process.limit_process           --
                                                                          --
def CAN_YOU_COUNT_THAT_HIGH                                               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [some_number: ENCODED Box Pigeon]                                     --
    : COUNTABLE Box Pigeon where                                          --
  index := some_number.limit_process.indexing_process                     --
                                                                          --
def CAN_YOU_UNDERSTAND_THE_PROCESS_TO_COUNT_THAT_HIGH                     --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [ℵ : COUNTABLE Box Pigeon]                                            --
    : ADMISSIBLE Box Pigeon where                                         --
  counting_process := ℵ.index.count                                       --
                                                                          --
def THEN_I_THINK_YOU_CAN_TELL_APART_A_NAOTRINO_AND_A_NOWTRINO             --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    : DISTINGUISHABLE Box Pigeon where                                    --
  fact := nowtrino.fact                                                   --
  symbol := nowtrino.symbol                                               --
  different? := fun _ => True                                             --
  dec_distinct := fun _ => isTrue trivial                                 --




end Measurement
