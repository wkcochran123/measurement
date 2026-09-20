/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that we often lose sight of the plot._

(c) 2026

__EPISODE 7__: _THE PATTER_

"Pay no attention to the man behind that curtain."
                -- Oscar Zoroaster Phadrig Isaac Norman Henkle Emmannuel Ambroise Diggs
                   The Wizard of Oz

lake build --me_a_career_programming

**KEEP YOUR EYE ON THE QUARTER**
Pigeon.quarter almost makes sense to say now to *YOU the READER*.  *YOU the KNOWER* are unaware of the pouch the Carrier Pigeon carries. For if you
were, then you would know where the quarter is. Any reason why it couldn't have a pouch? They have a pouch so they can deliver the receipt to the
payments center faster than the receipts trying to ride the train. I thought we went over this.
-/
-- Would you even care if I imported anything at this point?
import Measurement.Episode05 ----------------------------------| Skip _The Trick_ just to make sure we don't import α
set_option allowUnsafeReducibility true


namespace Measurement

--| First of all, _CONGRATULATIONS_! You made it through the most complex part of the argument. Probably.  Don't worry, I have a complete patter that
--| *YOU the READER* can use and are probably more familiar with.  On the left is the Lean which demonstrates that the argument is sound.  It reads,
--| well, I chose some fun names. Remember, _that_ is the argument the compiler is checking for logical consistency. Feel free to refer back to
--| definitions in previous episodes to double check the argument is consistent.  Remember, we are looking for the miracle of the Flying Spaghetti
--| Monster: his Noodly appendage: the two-spin graviton monopole: the nowtrino: the naotrino. Perhaps a νtrino?

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
  { palmed_card := Pigeon                                                 --
    count   := .zero nowtrino.fact                                        -- This opens up 2 different ways we can explore this function. The first
    iterate := fun particle => match particle with                        -- is as a variational formulation of some operator D. We are missing almost
      | .zero _     => .zero nowtrino.fact                                -- nothing to arrange for Euler-Lagrange dynamics to fall out.  Which is
      | .number _ _ _ => .number nowtrino.fact Pigeon.quarter             -- good, because it naturally tens to fall out, and never seems to _EVER_
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
      accumulation   := .nil nowtrino.fact }                              -- The number of poles, as we are taught in topology, are not only countable
                                                                          -- but isomorphic to ℕ. Some would call that redundant. That would smuggle
instance DID_THE_PARTICLE_COLOR_OUTSIDE_THE_LINES                         -- in some sort of selection that may or may not exist well enough for the
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- compiler to tell the difference.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [exp_iθ: RESIDUE Box Pigeon]                                          -- If the compiler can't tell the difference, then it will declare absolute
    : BINARY Box Pigeon where                                             -- equivalence. The key here is synchronization of the loops of discussing
  observation_process :=                                                  -- how to count so that we count while we count.
    { cauchy_process := exp_iθ.cauchy_process                             --
      before         := .nil nowtrino.fact                                -- You know _square numbers_. We can use a square as a pretty good
      after          := .nil nowtrino.fact }                              -- approximation to the norm of a vector. I mean, *YOU the KNOWER* should
  bit := .initial_condition                                               -- do the limit by hand. But  +----------------+
                  nowtrino.fact exp_iθ.cauchy_process.accumulation        --            → →             |  n           j |
  zero := .nil nowtrino.fact                                              --          ||x-y||  = lim  j |  Σ  (x  - y )    = max (x  - y )        (3)
  one  := .nil nowtrino.fact                                              --                 ∞   j→∞   √  i=0   i    i        i    i    i
                                                                          --
instance DO_YOU_SEE_A_BUNCH_OF_FLASHES                                    -- is one of the more _cromulent_ norms. This is probably the easiest way
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- to grasp how Gershgorin found his disks. What can be counted is the number
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- of disjoint disks. What cannot be counted is the number of eigenvalues
    [flicker: BINARY Box Pigeon]                                          -- in each connected section. Should be at least one per connected section.
    : REPEATABLE Box Pigeon where                                         -- There could be many eigenvalues in a connected region.
  repeatable_process :=                                                   --
  {                                                                       -- But, what is a connected region? Its the thing that can have holes in it
    observation_process := flicker.observation_process                    -- that topology guarantees that we can not only count, but infer a trivial
    stimulus := .initial_condition nowtrino.fact flicker.zero             -- map for isomorphivity. Remember, it isn't the fact that an isomorphism
    expectation := .hypothesis nowtrino.fact flicker.bit                  -- exists insofar as we can explicitly describe it.
  }                                                                       --
                                                                          -- Of course, like most of the effort in this work, I am rapidly condensing
instance THE_FLASHES_SHOW_NOWTRINOS_ALMOST_EVERY_TIME                     -- the extraordinarily precise work of Cohen. The goal here is to provide
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- many different ways to have the trivial isomorphism y=x. The trivial
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- isomorphism, unlike the others, is the same in the field of the single
    [JMP: REPEATABLE Box Pigeon]                                          -- element as it is in the compiler T=T for T the only element.
    : NUMERIC Box Pigeon where                                            --
  computational_process :=                                                -- Then the isomorphic mechansim that allows 𝔽(1) to count can finally be
  { repeatable_process := JMP.repeatable_process                          -- established.  Not because we understand why, but that we don't
    output := some (.hypothesis nowtrino.fact)                            -- understand the exact same problem across mathematical reasoning.
  }                                                                       --
                                                                          -- Well almost all the way across, Riemann says we have to take a point out
instance WRITE_DOWN_HOW_MANY_FLASHES_YOU_SEE_IN_A_TABLE                   -- in order to guarantee that lines cannot generate fenceposts. What does
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- this have to do with what is going on in the code right now? Well,
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- depending on how close *YOU the KNOWER* are to the missing tiddle ι,
    [jupyter_notebook: NUMERIC Box Pigeon]                                -- the larger the disk Gershgorin predicts.
    : REPRESENTABLE Box Pigeon where                                      --
  calculation_process :=                                                  -- How many flashes are detected report just that, the number of connected
  { computational_process :=                                              -- areas, not how many eigenvalues are in each. But that detail really
      { jupyter_notebook.computational_process with                       -- isn't matter. The number of connected areas are the visible measurement.
            closure := fun the_number_of_clicks => the_number_of_clicks   --
      }                                                                   -- The compiler is merely counting them. While writing code that will count
    program := jupyter_notebook.computational_process.close               -- the counts based on reality. When the disks come together, there is no
                         jupyter_notebook.computational_process.output    -- reason for a particular disk to be home to any eigenvalue whatsoever.
    state := .program nowtrino.fact                                       --
                       (jupyter_notebook.computational_process.close      -- That's why all flashes need to be written, because the disks they
                        jupyter_notebook.computational_process.output)    -- represent _COULD_ contain the _ELUSIVE_ naotrino we have been trying to
  }                                                                       -- isolate. Each flash is a completed physical process. Obvious to any
  representable? := fun _ expected_response =>                            -- photon detector of the appropriate wave length.
           ⟨Computation.program nowtrino.fact expected_response, rfl⟩     --
                                                                          -- Ross, in this case, is a deep cut. More or less, having the experience
instance ROSS!_GET_THE_READOUTS                                           -- of the photon is not enough. It must be tallied, recorded, checked,
    (Box: Type i)                                                         -- verified, and tortured with endless statistics. These are the readouts,
    (Pigeon: CarrierProcess Box)                                          -- the proof that all the proof we collected can be counted, sorted, and
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- categorized into appropriate buckets.
    [the_invariant: REPRESENTABLE Box Pigeon]                             --
    : PHYSICAL Box Pigeon where                                           -- How many buckets? That sounds like yet another isomorphism to ℕ. It seems
  noisy_process := {                                                      -- like this device does little more than describe the same isomorphism over
    turing_process := the_invariant.calculation_process                   -- and over again: y=x for y,x ∈ ℚ. I prefer ℚ as more sophisticated
    program := .halting nowtrino.fact (.program nowtrino.fact             -- represntation of ℕ.
                              the_invariant.calculation_process.program)  --
  }                                                                       -- May I remind *YOU the KNOWER* that the first rule of tautology club is
  threshold := .nonhalting nowtrino.fact                                  -- the first rule of tautology club. This will be funnier when we get to
      (.program nowtrino.fact the_invariant.calculation_process.program)  -- taughtology club and its first rule about how to avoid getting killed.
      (some (ChaitinsNumberSequence.halting nowtrino.fact                 --
                               the_invariant.calculation_process.state))  -- Are these representations still trivial now? Does y=x still apply?
  admissible? := fun _ _ _ => rfl                                         -- Does 2 still = 2 in this case? I mean it could mean 4/2. That's three
                                                                          -- times the symbols. Or two more symbols. Probably both. This distinction
                                                                          -- seems important. Seems hard to compute, too. Or, ridiculously easy.
noncomputable instance ARE_THE_UNITS_RIGHT                                -- It's just the 3 card monte flop again. So, we start the process one more
    (Box: Type i)                                                         -- time.
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- I'm glad we chose a definition of a handful of fractions as possibly
    [anechoic_chamber: PHYSICAL Box Pigeon]                               -- redundant somehow. Dunno if a mature number system needs more than say
    [Inhabited nowtrino.symbol]                                           -- 4 or 5 numbers. This allows us to bucket very noisy data and look for
    : COMPARABLE Box Pigeon where                                         -- _clear_ biases. The first easy one to notice is the FACT we cannot have
  physical_process :=                                                     -- a prior without a prior value. Some default value that we reach for when
  { noisy_process := anechoic_chamber.noisy_process                       -- asked to *CLEAR OUR MINDS*. That's the first bucket *YOU the KNOWER*
    representation := default                                             -- reaches for. I believe this could be misconstrued appropriately as ϕ, the
    invariant := .base nowtrino.fact default                              -- empty set. *YOU the READER*, this is where you _HAND_ the empty set to
    value := .base nowtrino.fact (ULift.up default)                       -- *YOU the KNOWER*. There are a dozen trivial isomorphisms that
  }                                                                       -- *YOU the READER* can now palm as cards.
  smaller_than := fun one_foot π  => one_foot = π                         --
                                                                          -- Before I forget, there is a famous book that mentions how π can be
instance DO_YOU_SEE_THE_LIGHT_FLASH_WHEN_YOU_HEAR_THE_CLICK               -- effectively approximated as 3. Here we are effectively approximating it
    (Box: Type i)                                                         -- as an isomorphism to ℕ. For those that understand the Hebrew process
    (Pigeon: CarrierProcess Box)                                          -- of an Arabic constant, the approximation gets much more efficient.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [anechoic_chamber: PHYSICAL Box Pigeon]                               -- But this is how we _slip_ into absurdity. The absurdity of T=F. How many
    [distinct: COMPARABLE Box Pigeon]                                     -- of these constructions are necessary to keep in memory before the
    : OBSERVED Box Pigeon where                                           -- computation of the proof can finally be shortcut to T=T? I feel like I
  slip_process :=                                                         -- am dancing around a concept of how polynomials can be evaluated. Or,
  { physical_process := distinct.physical_process                         -- not so much evaluated as demostrated solved, evaluating to 0.
    projection := .origin nowtrino.fact                                   --
                      distinct.physical_process.noisy_process.program     -- Thankfully, we can _count_ the number of times this could possibly
                      nowtrino.symbol                                     -- happen. The thing about polynomials is they can describe _ANYTHING_.
    stress := anechoic_chamber.threshold                                  -- I mean _ANYTHING_. The magic of Disney is no longer animation but
    threshold := nowtrino.symbol                                          -- _POLYNOMIALS_ and _SPLINES_.
  }                                                                       --
  observation := ULift nowtrino.symbol                                    -- I'm sure we have all seen a Pixar film.
                                                                          --
instance THATS_THE_PHOTOELECTRIC_EFFECT                                   -- On a screen of some kind.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          -- Delivered by some digital streaming service.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon]                                               -- And that's the three card monte throw again. Now, the thing about Pixar
    [static_friction: OBSERVED Box Pigeon]                                -- films is that they are generally aimed at children and the parents bear
    : PRESENT Box Pigeon where                                            -- the expense. Much like another experience common to many children. In
  santa_claus:=                                                           -- order to exhaust to absurdity, one must be ready to go to absurd places.
  { static_fraction := static_friction.slip_process                       --
    accumulation := .tree nowtrino.fact                                   -- Places that allow for supernatural forces to provide observations to
  }                                                                       -- those who cannot explain where the forces come from. Places that allow
  quantum := Type i                                                       -- for blindly looking for harmonic partial differential equations and
                                                                          -- just assuming they all should work.
instance THE_PHOTON_IS_MEASURABLE                                         --
    (Box: Type i)                                                         -- For them to work, there can only be two derivatives. We may have another
    (Pigeon: CarrierProcess Box)                                          -- number here. Two different derivatives each taken to provide the second.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- The mixed partial. Non-commutation. Causality. These are all words that
    [COMPARABLE Box Pigeon]                                               -- can be used to draw a conclusion about how physical laws necessarily
    [gift_from: PRESENT Box Pigeon]                                       -- encode mechanism and representation simultaneously.
    : MEASURABLE Box Pigeon where                                         --
  gauge_process :=                                                        -- I believe that is a consequence of Noether's theorem. IANAPhysicist.
  { sensing_process := gift_from.santa_claus                              -- I am barely a computer programmer. But, it is my understanding, that
    clock      := .this_superpigeon nowtrino.fact (.tree nowtrino.fact)   -- interaction of particles is something we still do not understand.
  }                                                                       -- I believe all interactions of matter that I, personally, experience are
                                                                          -- mediated by photons. May as well come from Santa Claus as far as the
instance PERHAPS_NOT_WITH_A_MULTIMETER_BUT_YOU_UNDERSTAND_WHAT_I_MEAN     -- compiler is concerned. The important thing is there is a way to both
    (Box: Type i)                                                         -- _describe_ how to count the number of photons in an experience _AND_
    (Pigeon: CarrierProcess Box)                                          -- _describe_ experience without using the photon itself.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon]                                               -- We can generalize this description of a device to *THE* description of
    [multimeter: MEASURABLE Box Pigeon]                                   -- *ANY* device, as long as we are careful with the plot. The plot device.
    : GUNGAN Box Pigeon where                                             -- Jar Jar Binks. Segue. *TA-DA*!
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
  sacred_texts := .inside_joke FACT.Truth.truth                           --
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
  galileo := .inside_joke FACT.Truth.truth                                --
  invariant := .repeatable FACT.Truth.truth                               --
                                                                          --
instance ABD                                                              --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [DISTINGUISHABLE Box Pigeon]                                          --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    : SCIENTIFIC Box Pigeon where                                         --
  discovering := LearningProcess.default Box Pigeon                       --
  invariant := .hypothesis FACT.Truth.truth                               --
                                        (.inside_joke FACT.Truth.truth)   --
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
      Du := .the_gateaux yet.the_experiment FACT.Truth.truth              --
                  nowtrino.fact.truth                                     --
                  (.the_newton yet.the_experiment nowtrino.fact.truth)    --
    }                                                                     --
    the_direction_to_the_destination := .einstein nowtrino.fact           --
    uptown_or_downtown := match nowtrino.fact.click with                  --
        | isTrue  _ => FACT.Truth                                         --
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
      numerical_analysis := (.load FACT.Truth.truth Box)                  --
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
    of_jibberish := (.introduction FACT.Truth Box)                            --
  }                                                                       --
  a_demonstration_of_a_constant := .methodology FACT.Truth FACT.Truth     --
              Box (ULift.{i+1, i} Box) (.introduction FACT.Truth Box)     --
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
    a_constant := .zero FACT.Truth                                        --
    current_page_number := .zero FACT.Truth                               --
    total_pages := .zero FACT.Truth                                       --
    of_the_proof := .methodology FACT.Truth FACT.Truth Box                --
                  (ULift.{i+1, i} Box) (.introduction FACT.Truth Box)     --
  }                                                                       --
  TRUE := .zero FACT.Truth                                                --
  raw_output := .one                                                      --
              FACT.Truth                                                  --
              (.one FACT.Truth (.zero nowtrino.fact))                     --
              (.introduction nowtrino.fact Box)                           --
              (.methodology FACT.Truth nowtrino.fact Box                  --
                    (ULift.{i+1, i} Box) (.introduction FACT.Truth Box))  --
              (.zero nowtrino.fact)                                       --
  a_constant := .one                                                      -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
              FACT.Truth --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
              holy_shit.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_local_schedule.the_æther.frame_of_reference.we_experience.shows_me_higher_order_terms.teaching.axioms.to_pwn_n00bz.dunking_contest.ANSYS_process.GOSUB.adding_process.mideastern_process.compiled_process.digital_process.meesa_process.gauge_process.sensing_process.static_fraction.physical_process.noisy_process.turing_process.computational_process.repeatable_process.observation_process.cauchy_process.limit_process.indexing_process.count.palmed_card.quarter -- |
                                     (.introduction nowtrino.fact Box) --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
              (.methodology FACT.Truth nowtrino.fact Box                  -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
                  (ULift.{i+1, i} Box) (.introduction FACT.Truth Box))    --
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
    your_conclusion     := .different (FACT.SAME (guano:=guano))          --
                  (guano.TRUE) (guano.a_constant) (some FACT.Truth.truth) --
  }                                                                       --
  α := .same FACT.Truth guano.a_constant                                  --
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
  current_page_number := Pigeon.quarter                                   --
  of_the_proof := stdout.a_demonstration_of_a_constant                    --

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
    of_jibberish := .methodology nowtrino.fact FACT.Truth Box                 --
         (ULift.{i+1,i} Box) holy_shit.a_demonstration_of_a_constant      --
  }                                                                       --
  a_demonstration_of_a_constant := .methodology nowtrino.fact             --
            FACT.Truth Box (ULift.{i+1,i} Box)                            --
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
      in_heartbeats := .distance_to nowtrino.fact (.zero FACT.Truth)      --
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
  not_the_same := fun _ => isTrue trivial                                 --




end Measurement
