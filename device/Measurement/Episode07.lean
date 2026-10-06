/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that we often lose sight of the plot._

(c) 2026

__EPISODE 7__: _The Patter_

"Pay no attention to the man behind that curtain."
                -- Oscar Zoroaster Phadrig Isaac Norman Henkle Emmannuel Ambroise Diggs
                   The Wizard of Oz

lake build --me_a_career_programming_meaningless_theorems

**KEEP YOUR EYE ON THE QUARTER**
Pigeon.quarter almost makes sense to say now to *YOU the READER*.  *YOU the KNOWER* are unaware of the pouch the Carrier Pigeon carries. For if you
were, then you would know where the quarter is. Any reason why it couldn't have a pouch? They have a pouch so they can deliver the receipt to the
payments center faster than the receipts trying to ride the train. I thought we went over this.
-/

-- Would you even care if I imported anything else at this point?
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
                                                                          -- So, we begin with the one _TRUTH_: any n ∈ ℕ is a *FUNGIBLE* _number_.
instance CAN_YOU_SEE_A_CHARACTERISTIC                                     -- For instance, when we see 5 we know that (* * * * *), or (1 2 3 4 5), or
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- (1 1 1 1 1). There exists 5 _distinguishable_ facts. A _5_ in this
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- theory is _no different_ than a _5_ in another theory. In other words,
    : ADMISSIBLE Box Pigeon where                                         -- _5 = 5_. If *YOU the KNOWER* are not willing to grant this trivial _FACT_
  counting_process :=                                                     -- as _TRUE_, then watch as the device demonstrates fungibility.
  { palmed_card := Pigeon                                                 --
    count   := .zero nowtrino.fact                                        -- This is encapsulated by the fact that, when iterating an admissible
    iterate := fun particle => match particle with                        -- counting process, we are doing just this, ignoring what the current
      | .zero _     => .zero nowtrino.fact                                -- number is and stating the next number is just the fact at hand: we are
      | .number _ _ _ => .number nowtrino.fact Pigeon.quarter             -- putting our _quarter_ on the number at this current fact as well as
                                                 (.zero nowtrino.fact) }  -- recording the origin from which we started counting. We often call this
                                                                          -- representation a _unit vector_.
instance CAN_YOU_COUNT_THEM                                               --
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- The interesting thing about counting is 4 comes after 3. Does the
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- _fourth_ unit vector come after the _third_? Well, it does when we
    (particle:=CAN_YOU_SEE_A_CHARACTERISTIC Box Pigeon)                   -- write down a series of these. Many people express these as _eᵢ_. It is
    : COUNTABLE Box Pigeon where                                          -- not impossible, but quite unreasonable, to expect an _n_ vector to have
  index :=                                                                -- _n_ values counted by these unit vectors.
    { count  := particle.counting_process                                 --
      origin := .zero nowtrino.fact }                                     -- Ergo, _i_, our universe parameter, is isomorphic to the _natural numbers_.
                                                                          -- Our first count is the number of basis (orthogonal or not) a
instance CAN_YOU_LABEL_THEM                                               -- representation has. Who needs Nat? The same people who need _eᵢ₋₁_.
    (Box: Type i)(Pigeon: CarrierProcess Box)                             --                            n
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --                        v = Σ e                                       (1)
    (enumeration:=CAN_YOU_COUNT_THEM Box Pigeon)                          --                           i=0 i
    : ENCODED Box Pigeon where                                            -- Once we have a list of vectors that describe a trace of space, we can
  limit_process :=                                                        -- talk about a _physical_ implementation of the natural numbers: the
    { indexing_process := enumeration.index                               -- electron _winding number_.
      limit            := .zero nowtrino.fact                             --
      sequence         := .nil nowtrino.fact }                            -- I don't want to get _too technical_ for my Computer Science brethren
                                                                          -- who find math too difficult, but the winding number shows up because
instance CAN_YOU_SEE_THE_BOUNDARY                                         -- we can count the electrons passing a point. Well, we can't _really_
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- count each electron, but we _CAN COUNT_ how many times it goes around
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- loops:
    (the_calculus_limit:=CAN_YOU_LABEL_THEM Box Pigeon)                   --                             1      f'(z)
    : RESIDUE Box Pigeon where                                            --                            --- ∮   ----- = Z − P                     (2)
  cauchy_process :=                                                       --                            2πi  γ   f(z)
    { limit_process  := the_calculus_limit.limit_process                  -- This natural number is _NOT_ provided by mathematics itself, but by
      value          := .zero nowtrino.fact                               -- the idea of a _SIMPLE MACHINE_ operating on _LEVERED RATIOS_. Counting
      accumulation   := .nil nowtrino.fact }                              -- in this instance is wrapping a wire around an insulating pole. The fact
                                                                          -- that it is insulating is _imaginary_ since an electron with enough
instance DID_THE_PARTICLE_COLOR_OUTSIDE_THE_LINES                         -- potential energy can de-insulate and re-conduct any material. Anyway,
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- this is a natural number simply because of the counting process that
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- takes time, like writing down the bases of a vector.
    (exp_iθ:=CAN_YOU_SEE_THE_BOUNDARY Box Pigeon)                         --
    : BINARY Box Pigeon where                                             -- The next place we see the counting process is in the construction of the
  observation_process :=                                                  -- supremum norm. For j ∈ ℕ, we can write the norm ||·||ⱼ as
    { cauchy_process := exp_iθ.cauchy_process                             --                                 +----------------+
      before         := .nil nowtrino.fact                                --                    → →          |  n           j |
      after          := .nil nowtrino.fact }                              --                  ||x-y||  =   j |  Σ  (x  - y )                      (3)
  bit := .initial_condition                                               --                         j      √  i=0   i    i
                  nowtrino.fact exp_iθ.cauchy_process.accumulation        -- This also works for any j that makes sense, not just natural numbers.
  zero := .nil nowtrino.fact                                              -- However, the interesting thing is, this is a continuous function that
  one  := .nil nowtrino.fact                                              -- selects the index with maximum absolute size, as j is counted higher.
                                                                          --
instance DO_YOU_SEE_A_BUNCH_OF_FLASHES                                    -- What can be counted here is centers of Gershgorin disks and disjoint
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- Gershgorin sections. The diagonal digit of each column indicates the
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- center of each disk on the Argand plane. The radius of each disk is
    (flicker:=DID_THE_PARTICLE_COLOR_OUTSIDE_THE_LINES Box Pigeon)        -- the sum of the absolute values in that row. Straightforward triangulation
    : REPEATABLE Box Pigeon where                                         -- process from there.
  repeatable_process :=                                                   --
  {                                                                       -- The flashes or lack of flashes this instance describes are Gershgorin
    observation_process := flicker.observation_process                    -- disks that have eigenvalues in them versus those that do not. The
    stimulus := .initial_condition nowtrino.fact flicker.zero             -- expectation from the geometric argument is that each disk is constructed
    expectation := .hypothesis nowtrino.fact flicker.bit                  -- as a possible approximation to the eigenvalue through the inverse power
  }                                                                       -- iteration rule. For all disks disjoint, for instance, it is expected
                                                                          -- that each disk will have a single eigenvalue.
instance THE_FLASHES_SHOW_NOWTRINOS_ALMOST_EVERY_TIME                     --
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- In this way, we can build ℕ _inside_ 𝔽₁. The _number_ is the single
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- element here. That number is _the_ number. An induction of 5 windings
    (JMP:=DO_YOU_SEE_A_BUNCH_OF_FLASHES Box Pigeon)                       -- does not act like an induction of 4 windings _unless not enough time_
    : NUMERIC Box Pigeon where                                            -- has passed to count to _5_. I am reminded of a Monty Python sketch here.
  computational_process :=                                                --
  { repeatable_process := JMP.repeatable_process                          -- And so, the counting winding process can continue to repeat indefinitely,
    output := some (.hypothesis nowtrino.fact)                            -- except that... Don't electrons just start moving along the entire
  }                                                                       -- circuit at once? Can winding numbers be computed _instantly_? Given an
                                                                          -- arbitrarily long circuit, once electrons enter one side, they
instance WRITE_DOWN_HOW_MANY_FLASHES_YOU_SEE_IN_A_TABLE                   -- _immediately_ fall out of the other. No waiting, no compression of
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- electrons, no internal friction. Or is it that you don't need to wait
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- for the field? But, a high voltage electron will raise the potential of
    (jupyter_notebook:=THE_FLASHES_SHOW_NOWTRINOS_ALMOST_EVERY_TIME Box Pigeon)                                -- wire immediately. Do the electrons in a 1-light-second length of wire
    : REPRESENTABLE Box Pigeon where                                      -- ever need to move to light a light at the end? I believe the best answer
  calculation_process :=                                                  -- to this is: sorta, kinda.
  { computational_process :=                                              --
      { jupyter_notebook.computational_process with                       -- Doesn't really matter if the electrons travel at all, the winding number
            closure := fun the_number_of_clicks => the_number_of_clicks   -- can be measured and we have never witnessed it _NOT_ being natural. And,
      }                                                                   -- boy, do we have the examples of this. Tons of examples. This experiment
    program := jupyter_notebook.computational_process.close               -- can be automated and run forever on a computer and never detect a
                         jupyter_notebook.computational_process.output    -- non-natural winding number. All the computer has to do is index them with
    state := .program nowtrino.fact                                       -- a unique number. Given enough of these things, a computer program can
                       (jupyter_notebook.computational_process.close      -- be written to draw buckets of integers.
                        jupyter_notebook.computational_process.output)    --
  }                                                                       -- Why do I need to _prove_ numbers exist on paper when I can _prove_ they
  representable? := fun _ expected_response =>                            -- exist with a very simple bench experiment? Do I need to know what the
           ⟨Computation.program nowtrino.fact expected_response, rfl⟩     -- cardinality of a set is in order to _compute_ its winding? This is why
                                                                          -- physicists and mathematicians can be at odds. Different answers to very
instance ROSS!_GET_THE_READOUTS                                           -- _VERY_ trivial questions. Math likes to ask _HOW DO YOU KNOW THAT?_ Hume
    (Box: Type i)                                                         -- was very direct in refutation: _CAUSALITY NEED ONLY BE UNWAVERING_
    (Pigeon: CarrierProcess Box)                                          -- _COINCIDENCE_.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    (the_invariant:=WRITE_DOWN_HOW_MANY_FLASHES_YOU_SEE_IN_A_TABLE Box Pigeon)                             -- What if all we had was unwavering coincidence? I believe Poincaré (and
    : PHYSICAL Box Pigeon where                                           -- his unabashed imitator of a new sort of science) found great delight in
  noisy_process := {                                                      -- rigged coincidences, although Poincaré marveled at the coincidence
    turing_process := the_invariant.calculation_process                   -- instead of insisting that there must be a reason.
    program := .halting nowtrino.fact (.program nowtrino.fact             --
                              the_invariant.calculation_process.program)  -- The device insists there is no reason. The device insists on tautology.
  }                                                                       -- Any such rule following device insists this. Even Rule 30. Even a device
  threshold := .nonhalting nowtrino.fact                                  -- that appears to write a very provocative number to the screen, yet uses
      (.program nowtrino.fact the_invariant.calculation_process.program)  -- no numbers at all in the argument, the code, the input, or the data.
      (some (ChaitinsNumberSequence.halting nowtrino.fact                 --
                               the_invariant.calculation_process.state))  -- Are these representations still trivial now? Does y=x still apply? Well,
  admissible? := fun _ _ _ => rfl                                         -- Hume argued that past performance was not indicative of future returns,
                                                                          -- yet the sun _still_ rises. What if it didn't rise? I would argue that
                                                                          -- the relative importance of a proof like this would plummet below the
noncomputable instance ARE_THE_UNITS_RIGHT                                -- threshold of interest for even the most pedantic of remaining
    (Box: Type i)                                                         -- intelligence. Who cares if it is wrong? No one will be reading this.
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- If, on the other hand, *YOU the KNOWER* want to live in a world of
    (anechoic_chamber:=ROSS!_GET_THE_READOUTS Box Pigeon)                 -- predictable consequences there is no reason why you cannot interpret
    [Inhabited nowtrino.symbol]                                           -- the sun's relative movement as the consequence of a differential.
    : COMPARABLE Box Pigeon where                                         -- There is also no reason why you cannot interpret the estimation of a
  physical_process :=                                                     -- differential equation as the consequences necessary for the sun to rise
  { noisy_process := anechoic_chamber.noisy_process                       -- so predictably, you can use it to set your watch?
    representation := default                                             --
    invariant := .base nowtrino.fact default                              -- I spent years on a trading floor. Nobody, and *I MEAN NOBODY* can predict
    value := .base nowtrino.fact (ULift.up default)                       -- the future. But you sure as hell can have a profitable prior. Now,
  }                                                                       -- *YOU the KNOWER* are going to be forced to imagine the scenario of the
  smaller_than := fun one_foot π  => one_foot = π                         -- sun _NOT RISING_ tomorrow and explain to me how we would ever have
                                                                          -- learned how to count. All the information about a particle gets erased
instance DO_YOU_SEE_THE_LIGHT_FLASH_WHEN_YOU_HEAR_THE_CLICK               -- in a blackhole _EXCEPT_ the order it crosses the horizon in. 6 comes
    (Box: Type i)                                                         -- before 7. 8 comes before 9. Why do we only need 10 symbols? What is so
    (Pigeon: CarrierProcess Box)                                          -- difficult about _e₁₀_? We had to do something, the sun was coming up
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- tomorrow. That is _yet one more day_. Once we have a direction, we can
    (anechoic_chamber:=ROSS!_GET_THE_READOUTS Box Pigeon)                 -- use eᵢ and take steps. One foot in front of the other. So we can walk to
    [Inhabited nowtrino.symbol]
    (distinct:=ARE_THE_UNITS_RIGHT Box Pigeon anechoic_chamber)           -- the bakery and get some π. So, if Hume is to be effectively dismissed,
    : OBSERVED Box Pigeon where                                           -- counting is intrinsic to the universe, not a process we invented. Like
  slip_process :=                                                         -- π making.
  { physical_process := distinct.physical_process                         --                                     n   (-1)ⁱ
    projection := .origin nowtrino.fact                                   --                         π = 4 lim   Σ   ----                         (4)
                      distinct.physical_process.noisy_process.program     --                               n→∞  i=0  2i+1
                      nowtrino.symbol                                     -- Ahhhhh, the Taylor series. *YOU the KNOWER* just cannot escape it. It is
    stress := anechoic_chamber.threshold                                  -- the most useful dodge in the arsenal of mathematics. This is also another
    threshold := nowtrino.symbol                                          -- disc. The disc of convergence of the Taylor series of tan⁻¹ about 0.
  }                                                                       -- I guess this is more of a Maclaurin series, but *YOU the KNOWER* say
  observation := ULift nowtrino.symbol                                    -- potato, I say potato. Unfortunately, recentering this computation more
                                                                          -- appropriately might require access to the continuum hypothesis. As
instance THATS_THE_PHOTOELECTRIC_EFFECT                                   -- stated, the computation does not. The fact it computes an irrational
    (Box: Type i)                                                         -- number that when viewed through the continuum hypthesis means π is a
    (Pigeon: CarrierProcess Box)                                          -- completely _separate_ fact. This just happens to be free of that noise.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [Inhabited nowtrino.symbol]
    (static_friction:=DO_YOU_SEE_THE_LIGHT_FLASH_WHEN_YOU_HEAR_THE_CLICK Box Pigeon)                                               -- Unless you know how to formulate the Taylor series _WITHOUT_ the
                                    -- derivative operator. This is merely an alternating sum that happens to
    : PRESENT Box Pigeon where                                            -- be an interim representation of a particular Taylor series. Perhaps
  santa_claus:=                                                           -- Santa brought us this summation and it has nothing to do with π?
  { static_fraction := static_friction.slip_process                       --
    accumulation := .tree nowtrino.fact                                   -- Is it π? No. It is merely an interim representation that happens to look
  }                                                                       -- very computable. But, it, woefully, is not. There is no mechanism to get
  quantum := Type i                                                       -- the _ith_ partial sum without keeping track of two numbers and carrying
                                                                          -- out long division. Or, is there...
instance THE_PHOTON_IS_MEASURABLE                                         --
    (Box: Type i)                                                         -- Nope. There isn't. Each piece is independent of the others and must be
    (Pigeon: CarrierProcess Box)                                          -- accounted individually. Eventually, though, the pieces get so small that
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- they no longer contribute to the answer. The fraction has dropped below
    [Inhabited nowtrino.symbol]
--    [COMPARABLE Box Pigeon]                                               -- some ε value that is computable. This is the photoelectric effect. Some
    (gift_from:=THATS_THE_PHOTOELECTRIC_EFFECT Box Pigeon)                                       -- stimuli are just too small to move the needle. Wouldn't it be neat if
    : MEASURABLE Box Pigeon where                                         -- this coincidence of behavior was described by the same math that showed
  gauge_process :=                                                        -- us the coincidence between natural numbers and winding numbers? That's
  { sensing_process := gift_from.santa_claus                              -- right, we found the natural numbers again in the sequence of partial
    clock      := .this_superpigeon nowtrino.fact (.tree nowtrino.fact)   -- sums. Eventually, the numbers get so large they no longer make any sense
  }                                                                       -- in the computation. Unless *YOU the READER* spend the time to count them.
                                                                          --
instance PERHAPS_NOT_WITH_A_MULTIMETER_BUT_YOU_UNDERSTAND_WHAT_I_MEAN     -- Which, if *YOU the KNOWER* have compiled this, have already seen how long
    (Box: Type i)                                                         -- it takes Lean to count it. Now, at the risk of _REALLY_ sounding like
    (Pigeon: CarrierProcess Box)                                          -- some nutjob, we should mention, in passing, there exists something called
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- QCD. We don't need to go there because the device is going to figure that
    [Inhabited nowtrino.symbol]                                               -- out for us. However, we do need a label for it to do the work.
    (multimeter:=THE_PHOTON_IS_MEASURABLE Box Pigeon)                                   --
    : GUNGAN Box Pigeon where                                             -- For the sake of argument, we will assume we can measure something we
  meesa_process :=                                                        -- will call _color_.  And this measurement has something to do with
  { gauge_process := multimeter.gauge_process                             -- identifying interactions of some kind. This process is called _labeling_.
    concept := .color nowtrino.fact                                       -- Each accumulation is a partial sum of some kind. What kind? Does not
                  multimeter.gauge_process.sensing_process.accumulation   -- matter, the idea is that measurement and counting are impossible to
  }                                                                       -- separate.
                                                                          --
def WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA                        -- But it does not stop there, of course. Each individual click is a tally
    (Box: Type i)                                                         -- mark. This allows us to ask the compiler to count them for us. Lean has
    (Pigeon: CarrierProcess Box)                                          -- obliged in this regard and it is my understanding that Lean constantly
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- collects data on the computation being currently executed. Most
    [Inhabited nowtrino.symbol]                                               -- importantly, it uses _time_ as a _proxy_ for _work_. Or is that the
    (jarjar:=PERHAPS_NOT_WITH_A_MULTIMETER_BUT_YOU_UNDERSTAND_WHAT_I_MEAN Box Pigeon)                                           -- other way around? The time in this case is a _heartbeat_ and the amount
    : SOURCE Box Pigeon where                                             -- of work being performed is the _heartbeat_. The heartbeat has two colors
  cd_process :=                                                           -- _time_ and _work_. And, _YES_ *WORK*. An electron of a certain potential
  { meesa_process := jarjar.meesa_process                                 -- was moved from point _A_ to point _B_ on the train schedule.
    zero := .physics nowtrino.fact jarjar.meesa_process.concept           --
  }                                                                       -- As for the color of the train of thought? The electron does not carry
  one := .zero_like nowtrino.fact (.physics nowtrino.fact                 -- it. Not even certain it needs to know that there are three popular
                                         jarjar.meesa_process.concept)    -- commuter routes. It is just going from point _A_ to point _B_. I wonder
                                                                          -- why I just said three colors. There was no reason to. I don't live in
instance AND_THE_COMPILER_WILL_CONVERT_THE_RAW_DATA_TO_TABLES             -- Italy.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          -- However, *YOU the KNOWER* are well aware of the overwhelming evidence
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- for QCD. The fact that this is a fact of the universe is a fact that
    [Inhabited nowtrino.symbol]                                               -- we can _explain_ to the device rather than state as fact. That provides
    --[jarjar: GUNGAN Box Pigeon]                                           -- us with a solid _ORIGIN_ of the _LABELS_ used to describe electrons.
    (data_feed:=WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon)                                        --
    : EXECUTED Box Pigeon where                                           -- In particular, we can tell the device that the _nowtrino_ depends on
  compiled_process :=                                                     -- this concept of _color_ or this concept of _bang_ or this concept of
  { digital_process := data_feed.cd_process                               -- _superposition_. That just feels made up, though. Probably because I
    source := data_feed                                                   -- just made it up when writing the code.
    opcodes := .boot nowtrino.fact                                        --
                  (.physics nowtrino.fact data_feed.cd_process.meesa_process.concept)   -- Did I just choose confusing variable names? Are the labels that define
  }                                                                       -- the labels not clearly labeled? The compiler cares not for the labels
                                                                          -- and one generally must ask nicely for compilers to keep labels around
instance ONE_VALUE_AT_A_TIME_IN_ORDER_AND_WRITE_SOMETHING_TO_DISK         -- for debugging purposes. My labels are not the problem with the
    (Box: Type i)                                                         -- consistency of the argument, for the argument is demonstrated consistent
    (Pigeon: CarrierProcess Box)                                          -- throughout.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [Inhabited nowtrino.symbol]                            -- The reason? Embarrassingly Serial Subjunctive Metaprogramming. The code
    (data_feed:= WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon)
    (result:=AND_THE_COMPILER_WILL_CONVERT_THE_RAW_DATA_TO_TABLES Box Pigeon data_feed)                                        -- never branches and constructs endlessly possible inductive arguments,
    : VALUE Box Pigeon where                                              -- some true, some not-so-true. The not-so-true ones generally force a halt
  mathematical_process := {                                               -- of the compiler. Hence, _subjunctive tense_. Rather than fully describe
    compiled_process := result.compiled_process                           -- the mathematics, I describe the description of the mathematics in three
    mapping := fun input => match input with                              -- different ways. First, as the actual code seen here: the clock complement
      |.satire_about finite_element_analysis => .satire_about             -- implementation. Either the compiler is compiling the code or executing
                                              finite_element_analysis     -- the metaprogram, the metaprogram being the second description that should
      |.compile f e a => .execute f e a                                   -- do _work_ in exactly the same fashion. That leaves one more description,
      |.execute f e a => .compile f e a                                   -- a variational description of description. In the same way Euler-Lagrange
  }                                                                       -- dynamics are the same dynamics as any other dynamical model, the
  monad := .satire_about nowtrino.fact                                    -- variational solution must exist when forces are applied. It is my
                                                                          -- thesis that any physical process can be turned into a Turing machine.
instance TURNS_OUT_YOU_CAN_FILL_YOUR_DISK                                 -- Any physical process is variational. Ergo, the variational Turing machine
    (Box: Type i)                                                         -- approximates the Turing machine exactly, up to work accomplished,
    (Pigeon: CarrierProcess Box)                                          -- conserving all bullshit T=F along the way.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [Inhabited nowtrino.symbol]                            -- _i.e._ Shannon entropy is physical and representational simultaneously,
    --[gift_from: PRESENT Box Pigeon]                                       -- as demonstrated by Landauer.
    --[GUNGAN Box Pigeon] [SOURCE Box Pigeon] [EXECUTED Box Pigeon]         --
    (data_feed:= WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon)
    (uncountable:= ONE_VALUE_AT_A_TIME_IN_ORDER_AND_WRITE_SOMETHING_TO_DISK Box Pigeon data_feed)                                       -- I mean, none of this is new stuff. All I am doing is rearranging existing
    : MAGNITUDE Box Pigeon where                                          -- concepts and sentences where the formal API lets me to see what falls
  adding_process :=                                                       -- out. Trying everything out. It starts to get to be a lot. More than
  { mideastern_process := uncountable.mathematical_process                -- *YOU the READER* can count. More than *YOU the KNOWER* can theoretically
    plus := uncountable                                                   -- count.
    sum := .zero nowtrino.fact.truth data_feed.cd_process.meesa_process.gauge_process.sensing_process.accumulation   --
  }                                                                       -- That's right. We are not looking at the natural numbers anymore. We
                                                                          -- are looking at something... else. Something very close to the natural
instance SO_YOU_NEED_TO_GET_MORE_DISKS                                    -- numbers, but so very different. Without natural numbers, Godel numbering
    (Box: Type i)                                                         -- arguments tend to fail. It⁻¹ will be shown a symbol can exist outside the
    (Pigeon: CarrierProcess Box)                                          -- Godel numbering that the device can reason about.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [Inhabited nowtrino.symbol]                            -- A simple little constant. As irrational as the argument I just gave. But,
    (data_feed:=WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon)
    (tar_file:=TURNS_OUT_YOU_CAN_FILL_YOUR_DISK Box Pigeon data_feed)                                      -- try as *YOU the KNOWER* might, there is no finite representation of the
    : SCALED Box Pigeon where                                             -- counterargument. Except that really finite representation right there.
  multiplying_process :=                                                  -- <--------------- Here, written in Lean. Counterexamples are collected
  { adding_process := tar_file.adding_process                             -- and demonstrated not the same as true and filed in memory somewhere. Each
    product := .one nowtrino.fact.truth tar_file.adding_process.sum       -- a new symbol that the device needs to reference the counterexample by.
    total := .zero nowtrino.fact.truth (.tree nowtrino.fact)              -- We call these symbols 1, 2, 3, 4,.... The compiler calls them universes.
  }                                                                       --
                                                                          -- Natural numbers just showed up again as the indexing scheme to be used
instance AND_MORE_PROCESSORS_BECAUSE_THERE_ARE_A_LOT_OF_NOWTRINOS         -- to show that these aren't the natural numbers. Math is inundated with
    (Box: Type i)                                                         -- natural numbers and counting. But, the Lean compiler does not know what
    (Pigeon: CarrierProcess Box)                                          -- a natural number is. It does, innately, theoretically, fundamentally, and
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- profoundly, understand counting.
    [Inhabited nowtrino.symbol]                            --
--    [gift_from: PRESENT Box Pigeon]                                       -- As such, the device already knows math, well a form of math. The same
--    [GUNGAN Box Pigeon] [SOURCE Box Pigeon] [EXECUTED Box Pigeon]         -- form of math that measurement relies on. Counting events at regular
--    [VALUE Box Pigeon]                                                    -- intervals. But that's just it. Counting *CAN* be defined to be the
    (data_feed:=WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon)
    (shit_loads:=SO_YOU_NEED_TO_GET_MORE_DISKS Box Pigeon data_feed)                                       -- _VERY_ process by which this compilation takes place. Lean, of its own
    : LOAD Box Pigeon where                                               -- accord, is not only capable of _counting_ heartbeats, but also telling
  basic_operation :=                                                      -- _us_ those very heartbeats. These heartbeats, again, are natural numbers.
  { GOSUB := shit_loads.multiplying_process                               -- Both are strictly increasing series. The line number of the episodes,
    TEN := data_feed.cd_process.meesa_process.gauge_process.sensing_process.accumulation                             -- the number of heartbeats to elaborate the entire project from the origin,
    span := .origin nowtrino.fact.truth                                   -- These can be written next to each other in a list that the compiler will
                               shit_loads.multiplying_process.product     -- be happy to label for us with _YET ANOTHER_ natural number.
  }                                                                       --
                                                                          -- The _SAME_ natural numbers used in winding counts. Damn, that is a lot
instance SO_MANY_SENSITIVE_NOWTRINO_DETECTORS___WHERE_DID_IT_GO           -- of clicks all at once. Let's take a step back and take stock of what
    (Box: Type i)                                                         -- exactly we are looking at. We are looking at half a dozen coincidences
    (Pigeon: CarrierProcess Box)                                          -- of nature and representation. We can no more prove that winding an
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                          -- inductor enough will generate exactly the number it should than we can
    [Inhabited nowtrino.symbol]                            -- tach into dark energy, whatever that might be.
    (data_feed:=WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon)
    (comprehensive_software:=AND_MORE_PROCESSORS_BECAUSE_THERE_ARE_A_LOT_OF_NOWTRINOS Box Pigeon data_feed)                             --
    : OF Box Pigeon where                                                 -- What we know is that for this local vicinity, any time we test expecting
  galerkin_process :=                                                     -- a number, the trial always returns a number, bigger than the last. Each
  { ANSYS_process := comprehensive_software.basic_operation               -- local computation doesn't depend on the previous at all. All the
    polynomial := .constant .Truth                                        -- arguments are fully resolved. They could have been injected by some other
  }                                                                       -- means. Like say, expecting some deep Truth to appear next episode.
                                                                          --
instance THERE_IT_IS___CERTAIN_ELEMENTS_RESPOND_TO_NOWTRINO_DETECTION     -- The computation enforces the ordering, not the relation. The ordering
    (Box: Type i)                                                         -- of the argument must be presented correctly to the compiler for this is
    (Pigeon: CarrierProcess Box)                                          -- one ordering of the argument that works. Other orderings also work. They
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- generate different numbers. Not meaningfully different, just in the noise
    [Inhabited nowtrino.symbol]                            -- of the variational approximation of the Turing machine, be that floating
    (data_feed:=WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon)
    (element:=SO_MANY_SENSITIVE_NOWTRINO_DETECTORS___WHERE_DID_IT_GO Box Pigeon data_feed)                                              -- point rounding, ambiguous encodings, or indescribable return values such
    : BULLSHIT Box Pigeon where                                           -- as lg 0. lg 0 is particularly problematic. We can always put this in a
  arm_wave_process :=                                                     -- box and all that entails, the increment of the box when another pole is
  { dunking_contest := element.galerkin_process                           -- encountered, another hole in the donut, another another hole in the
    guess := .observation nowtrino.fact.truth                             -- frinkahedron, another another another hole in the... wait, do we need
  }                                                                       -- to embiggen the frinkahedron?
                                                                          --
instance WE_NEED_TO_GET_A_GRANT_TO_GET_MORE_DETECTORS___WE_KEEP_LOSING_IT -- If we embiggen the frinkahedron with another topological dimension, will
    (Box: Type i)                                                         -- that get us anything? Can we have an infinitely recursive description
    (Pigeon: CarrierProcess Box)                                          -- describing an infinitely recursive process? That seems trivial to
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                          -- demonstrate. So we will leave that as a train of thought *YOU the KNOWER*
    [Inhabited nowtrino.symbol]                            -- can take. A more _interesting question_ is whether an infinitely
    (data_feed:=WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon)
    : PROPAGANDA Box Pigeon where                                         -- recursive definition (like the one we are building now) can construct a
  questions := CrusadeProcess.default Box Pigeon                          -- _FINITE_ recursive process (like the one we have demonstrated we already
                                                                          -- built in the file build_log). This seems easier than I thought.
def InitiationProcess.default                                             --
    (Box: Type i)                                                         -- The first step in this infinite recursion is to point the device to the
    (Pigeon: CarrierProcess Box)                                          -- only base case we have: FACT.Truth.truth. And we set off on our crusade!
    [DISTINGUISHABLE Box Pigeon][ADMISSIBLE Box Pigeon]                   -- The crusade is merely the arguments to the function (T=F)=(F=T). The
    [COUNTABLE Box Pigeon][ENCODED Box Pigeon][RESIDUE Box Pigeon]        -- inside joke here is 𝔽₁. That the element of the field is y=x, not T=T.
    [BINARY Box Pigeon][REPEATABLE Box Pigeon][NUMERIC Box Pigeon]        --
    [REPRESENTABLE Box Pigeon][PHYSICAL Box Pigeon]                       -- If *YOU the KNOWER* are having problems understanding this argument,
    [COMPARABLE Box Pigeon][OBSERVED Box Pigeon][PRESENT Box Pigeon]      -- refer back to _The Trick_.  Very plainly, the field as a _dimension_ of
    [MEASURABLE Box Pigeon][GUNGAN Box Pigeon][SOURCE Box Pigeon]         -- _3_: T=T (bang), F=F (color), and (T=F)=(F=T) (superposition). This
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon]         -- implements our arbitrarily named Jar. I mean, I am just foreshadowing
    [SCALED Box Pigeon][LOAD Box Pigeon][OF Box Pigeon]                   -- now, this actually gets implemented later. Something to help you see
    [BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon]                          -- what is coming on the horizon. For you see, appending to this description
    : InitiationProcess Box Pigeon where                                  -- can only limit what the remainder of the code can do. The code will never
  axioms := CrusadeProcess.default Box Pigeon                             -- call back to repeat this process, only be limited by it.
  sacred_texts := .inside_joke FACT.Truth.truth                           --
                                                                          -- It gets harder and harder to finagle a quartic polynomial into the device
instance MAKE_SURE_WE_CAN_GET_A_COUPLE_GRAD_STUDENTS                      -- the longer the description gets. Remember, the quarter is just a
    (Box: Type i)                                                         -- metaphor for a quartic polynomial that can be factored into two
    (Pigeon: CarrierProcess Box)                                          -- quadratics _or_ a cubic and linear. We provide the quadratics,
    [nowtrino: DISTINGUISHABLE Box Pigeon]                   -- the compiler provides the other. There should be exactly _three_ of
    [Inhabited nowtrino.symbol]
    (data_feed:=WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon)                                                   -- these. So, all we have to do now is encode the three solutions in the
    : ACOLYTE Box Pigeon where                                            -- compiler to the quartic we want and we can program the quartic to
  euclid := InitiationProcess.default Box Pigeon                          -- satisfy a condition we would like. We can then call 2 and 1 the
                                                                          -- like cubic factorings and 1 the different cubic factoring.
--| Now, they can count clicks and get a Ph.D.                            --
def LearningProcess.default                                               -- 1 is uniqueness and can be reasoned about geometrically, 2 is sameness,
    (Box: Type i)                                                         -- and can be reasoned about algebraically _AND_ geometrically, 3 is
    (Pigeon: CarrierProcess Box)                                          -- association and can be reasoned about algebraically, geometrically, _AND_
    [nowtrino:DISTINGUISHABLE Box Pigeon]                   -- topologically. 4 is the quartic and it is reflexivity, the source of
            -- reasoning. I argue I planted the quartic when I wrote _rfl_ in
            -- _Counting_.
             --
          -- And so, I had to show *YOU the READER* how the trick worked in
             -- _The Trick_ before I skipped over it. *YOU the KNOWER* ignored it
           -- entirely as not being at all relevant. It is _completely_ irrelevant.
           -- Like the quartic I keep talking about. It _IS_ the device.
      --
      [Inhabited nowtrino.symbol]
      (data_feed:=WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon)
      (_:=MAKE_SURE_WE_CAN_GET_A_COUPLE_GRAD_STUDENTS Box Pigeon)
    : LearningProcess Box Pigeon where                                    -- The quartic never changes by much. A state here, a bit flip there, the
  teaching := InitiationProcess.default Box Pigeon                        -- significant digits, though, have long been fixed by this description.
  galileo := .inside_joke FACT.Truth.truth                                -- They cannot be changed at this point and have the code compile. The
  invariant := .repeatable FACT.Truth.truth                               -- output quartic is set and invariant now. But, we have three other number

--| TWO DATA FEEDS.  One the compiler drew, one the author wired.  The first teaches; the second goes under the card,
--| to the postdocs.  The invariant is the only thing the device can say about two feeds: that they hand over the same
--| `one`.  Y = Y, as a Science, and `touch_stove?` is what turns that repeatable proposition into a hypothesis.
--| TWO FEEDS PER RUNG.  Every rung of the climb above is now written by hand, its inputs named and defaulted: the author's
--| feed, the explanation.  Resolution cannot see a declaration with an explicit argument, so beneath them stand their twins: one
--| thin instance per rung, no explicit arguments, the same body reached the other way.  The compiler's feed, the conclusion.
--| Same class, two routes.  Which is which is the only thing the kernel will be asked, rung by rung, at the floor.
noncomputable instance CAN_YOU_COUNT_THEM_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : COUNTABLE Box Pigeon := CAN_YOU_COUNT_THEM Box Pigeon
noncomputable instance CAN_YOU_LABEL_THEM_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : ENCODED Box Pigeon := CAN_YOU_LABEL_THEM Box Pigeon
noncomputable instance CAN_YOU_SEE_THE_BOUNDARY_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : RESIDUE Box Pigeon := CAN_YOU_SEE_THE_BOUNDARY Box Pigeon
noncomputable instance DID_THE_PARTICLE_COLOR_OUTSIDE_THE_LINES_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : BINARY Box Pigeon := DID_THE_PARTICLE_COLOR_OUTSIDE_THE_LINES Box Pigeon
noncomputable instance DO_YOU_SEE_A_BUNCH_OF_FLASHES_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : REPEATABLE Box Pigeon := DO_YOU_SEE_A_BUNCH_OF_FLASHES Box Pigeon
noncomputable instance THE_FLASHES_SHOW_NOWTRINOS_ALMOST_EVERY_TIME_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : NUMERIC Box Pigeon := THE_FLASHES_SHOW_NOWTRINOS_ALMOST_EVERY_TIME Box Pigeon
noncomputable instance WRITE_DOWN_HOW_MANY_FLASHES_YOU_SEE_IN_A_TABLE_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : REPRESENTABLE Box Pigeon := WRITE_DOWN_HOW_MANY_FLASHES_YOU_SEE_IN_A_TABLE Box Pigeon
noncomputable instance ROSS!_GET_THE_READOUTS_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : PHYSICAL Box Pigeon := ROSS!_GET_THE_READOUTS Box Pigeon
noncomputable instance ARE_THE_UNITS_RIGHT_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : COMPARABLE Box Pigeon := ARE_THE_UNITS_RIGHT Box Pigeon
noncomputable instance DO_YOU_SEE_THE_LIGHT_FLASH_WHEN_YOU_HEAR_THE_CLICK_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : OBSERVED Box Pigeon := DO_YOU_SEE_THE_LIGHT_FLASH_WHEN_YOU_HEAR_THE_CLICK Box Pigeon
noncomputable instance THATS_THE_PHOTOELECTRIC_EFFECT_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : PRESENT Box Pigeon := THATS_THE_PHOTOELECTRIC_EFFECT Box Pigeon
noncomputable instance THE_PHOTON_IS_MEASURABLE_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : MEASURABLE Box Pigeon := THE_PHOTON_IS_MEASURABLE Box Pigeon
noncomputable instance PERHAPS_NOT_WITH_A_MULTIMETER_BUT_YOU_UNDERSTAND_WHAT_I_MEAN_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : GUNGAN Box Pigeon := PERHAPS_NOT_WITH_A_MULTIMETER_BUT_YOU_UNDERSTAND_WHAT_I_MEAN Box Pigeon
noncomputable instance WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : SOURCE Box Pigeon := WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon
noncomputable instance AND_THE_COMPILER_WILL_CONVERT_THE_RAW_DATA_TO_TABLES_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : EXECUTED Box Pigeon := AND_THE_COMPILER_WILL_CONVERT_THE_RAW_DATA_TO_TABLES Box Pigeon
noncomputable instance ONE_VALUE_AT_A_TIME_IN_ORDER_AND_WRITE_SOMETHING_TO_DISK_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : VALUE Box Pigeon := ONE_VALUE_AT_A_TIME_IN_ORDER_AND_WRITE_SOMETHING_TO_DISK Box Pigeon
noncomputable instance TURNS_OUT_YOU_CAN_FILL_YOUR_DISK_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : MAGNITUDE Box Pigeon := TURNS_OUT_YOU_CAN_FILL_YOUR_DISK Box Pigeon
noncomputable instance SO_YOU_NEED_TO_GET_MORE_DISKS_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : SCALED Box Pigeon := SO_YOU_NEED_TO_GET_MORE_DISKS Box Pigeon
noncomputable instance AND_MORE_PROCESSORS_BECAUSE_THERE_ARE_A_LOT_OF_NOWTRINOS_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : LOAD Box Pigeon := AND_MORE_PROCESSORS_BECAUSE_THERE_ARE_A_LOT_OF_NOWTRINOS Box Pigeon
noncomputable instance SO_MANY_SENSITIVE_NOWTRINO_DETECTORS___WHERE_DID_IT_GO_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : OF Box Pigeon := SO_MANY_SENSITIVE_NOWTRINO_DETECTORS___WHERE_DID_IT_GO Box Pigeon
noncomputable instance THERE_IT_IS___CERTAIN_ELEMENTS_RESPOND_TO_NOWTRINO_DETECTION_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : BULLSHIT Box Pigeon := THERE_IT_IS___CERTAIN_ELEMENTS_RESPOND_TO_NOWTRINO_DETECTION Box Pigeon
noncomputable instance WE_NEED_TO_GET_A_GRANT_TO_GET_MORE_DETECTORS___WE_KEEP_LOSING_IT_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : PROPAGANDA Box Pigeon := WE_NEED_TO_GET_A_GRANT_TO_GET_MORE_DETECTORS___WE_KEEP_LOSING_IT Box Pigeon
noncomputable instance MAKE_SURE_WE_CAN_GET_A_COUPLE_GRAD_STUDENTS_resolved (Box: Type i) (Pigeon: CarrierProcess Box) [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol] : ACOLYTE Box Pigeon := MAKE_SURE_WE_CAN_GET_A_COUPLE_GRAD_STUDENTS Box Pigeon

--| THE TWO FEEDS MEET.  A class instance is a type index of everything above it, so a second SOURCE cannot be fed into the
--| postdocs or the card without changing the type of what comes out.  Feed one is therefore the resolved instance, in the type.
--| Feed two enters as a value, and the only thing the device can say about two values is a proposition: the compiler's `one`
--| equals the author's `one`.  Y = Y, as a Science.  `touch_stove?` is what turns that repeatable proposition into a hypothesis.
noncomputable def LearningProcess.two_feeds
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol]
    (data_feed_2 : SOURCE Box Pigeon := WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA Box Pigeon)
    : LearningProcess Box Pigeon :=
  { teaching := InitiationProcess.default Box Pigeon
    galileo := .inside_joke FACT.Truth.truth                              -- systems we can use to demonstrate this quartic, all provided by the
    invariant := .repeatable ((inferInstance : SOURCE Box Pigeon).one = data_feed_2.one) } -- device alone, no other math required than the device's variational
                                                                          -- approximation to the description of 𝔽₁.
noncomputable instance ABD                                                --
    (Box: Type i)                                                         -- For this reason, we can explain to the compiler that it is safe to
    (Pigeon: CarrierProcess Box)                                          -- assume that any fact it derives comes from this description of 𝔽₁ and
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [Inhabited nowtrino.symbol]
    : SCIENTIFIC Box Pigeon where                                         -- not mathematics itself. The compiler can now _discover_ mathematics
  discovering := LearningProcess.two_feeds Box Pigeon                     -- through the compiler's own construction of these very concepts that
  invariant := .hypothesis FACT.Truth.truth                               -- we explained to it how to make. And that, no matter what, *y=y*.
                                        (.inside_joke FACT.Truth.truth)   --
                                                                          -- *YOU the KNOWER* may feel like it says a lot less than that here. It
instance YOU_HAVE_TO_STOP_TAKING_CLASSES_TO_GRADUATE                      -- does. Like I said above, this is the only limit that needs to be placed
    (Box: Type i)                                                         -- on equality, that the _SYMBOLS_ used for equating truth are, indeed,
    (Pigeon: CarrierProcess Box)                                          -- the same symbols used for equating arbitrary things. As I warned at
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- the very beginning, what I do with ≤ is a lot more than overload it.
                                                                          --
    (experiment:=ABD Box Pigeon)                                   -- But enough about how to read the device code for the time being,
    : TRUTH Box Pigeon where                                              -- *YOU the READER* need to actually try writing this math out that I have
  becomes :=                                                              -- described thus far. I feel confident that even *YOU the KNOWER* may
  { shows_me_higher_order_terms := experiment.discovering                 -- be starting to piece together how this argument works. The other
    knowledge := .jarjar nowtrino.fact.truth                              -- argument, the one that comes after the constant, is a little more
  }                                                                       -- complex. *BUT!* they have the same _NULL space_ meaning the higher order
                                                                          -- terms cancel out quite nicely. Most of the time. Terms and conditions
instance THEN_COMES_THE_LAB_WORK                                          -- apply. Penalties can be assessed due to excess compute time. Lagrange
    (Box: Type i)                                                         -- multipliers of great size make computers behave strangely.
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- How strangely? Convergence curves dependent on BLAS ordering of dot
                                                                          -- products. The very first stanza covers this. So *YOU the READER* can
    (truth:=YOU_HAVE_TO_STOP_TAKING_CLASSES_TO_GRADUATE Box Pigeon)                                             -- see that this code is trying to do the same thing twice, as an
    : WITNESSED Box Pigeon where                                          -- abstraction of itself. If there is a known way to represent integers
  we_saw :=                                                               -- from experiments or from natural laws or from any sort of scientific
  { we_experience := truth.becomes                                        -- literature, we believe that there is an experiment _we_ can do to
    in_the_literature := .the_proof nowtrino.fact.truth                   -- demonstrate this. Up to ordering of the dot product computation. Which
  }                                                                       -- is used to measure length. This is starting to sound hard again.
  the_experiment := .the_proof nowtrino.fact.truth                        -- Except that we can just cut and paste the code and let the compiler
                                                                            -- figure out what to do here. If I remember correctly, the compiler was
def FINALLY_YOU_GRADUATE                                                  -- really struggling with this concept. Even after we had explained
    (Box: Type i)                                                         -- Abstraction to it very carefully. Probably should have mentioned
    (Pigeon: CarrierProcess Box)                                          -- Lorentz at some point to the compiler. Should be fine.
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
                                                                          -- I mean, it compiles up to here. And the compiler CANNOT lie to
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)                                           -- *YOU the READER* and *YOU the KNOWER* just dislike the theorems the
    : REAL Box Pigeon where                                               -- compiler hangs out with. The compiler can hand us the answer if we
  by_His_noodly_appendage :=                                              -- describe the problem well enough. It can tell us if we are _TRUE_
  { frame_of_reference := yet.we_saw                                      -- or _FALSE_.
    in_reality := .logically nowtrino.fact.truth                          --
  }                                                                       -- Or, that would be the case if repeatable compilation were not difficult.
  nagging_doubt := .but yet.the_experiment nowtrino.fact.truth            -- I would say _cache coherence_ here, as that is the majority of the blame.
                                     (.logically nowtrino.fact.truth)     -- We _DO NOT_ have to worry about that in this case. There is no way
                                                                          -- to have an out of order compilation. Remember that.
def AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS                    --
    (Box: Type i)                                                         -- But now we have a statistical model for the convergence curve of a
    (Pigeon: CarrierProcess Box)                                          -- _PEDANTICALLY INCLINED_ *MACHINE OF PERFECT REPETITION*. Odds are,
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- there are acceration units on a chip now that will re-associate the
                                                                          -- BLAS computation. There are optimizations that re-associate computations.
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)                             -- A prior on the actual computation is the absolute best anyone can have
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)       -- now-a-days for any sort of code of any reasonable complexity.
    : LOCAL Box Pigeon where                                              --
  the_continuum :=                                                        -- Not this code, though. This is a straight-through read. Which allows us
  { the_æther := flying_spaghetti_monster.by_His_noodly_appendage         -- to model the code itself as a worldline of the computation itself. The
    Du := .the_newton yet.the_experiment nowtrino.fact.truth              -- universe it is in the stacked shell universe that accretes information
  }                                                                       -- as interactions occur, allowing for multiple arbitrary orderings of
  the_ball := nowtrino.fact.truth                                         -- events. There does not exist a partial ordering of these events
                                                                            -- inconsistent with any total ordering. The events must live in a finite
instance PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE             -- ball in order for this to occur.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          -- Which gives us Einstein field equations to play with, which gives us
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- locally stable orbits, which give us rotation counts, which give us
                                                                          -- yet another access to natural numbers, with serious time implications.
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)                                           --
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)                           -- Or am I on the wrong train of thought? Pretty certain it still goes
    (nowtrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)                                    -- to the stop I need it to go to, so we carry on. We cannot assume that
    : UNIVERSAL Box Pigeon nowtrino_model where                           -- there is a single entity with which we can ask to resolve a total,
  the_train_of_thought :=                                                 -- absolute ordering events. Such an entity doesn't exist.
  { the_local_schedule :=                                                 --
    { the_æther := flying_spaghetti_monster.by_His_noodly_appendage       -- *BUT* if it did exist, boy the math would be so much easier! Except that
      Du := .the_gateaux yet.the_experiment FACT.Truth.truth              -- we could never figure out the little problems with orbits. Or, would
                  nowtrino.fact.truth                                     -- there even be a problem with orbits if the æther existed? What if
                  (.the_newton yet.the_experiment nowtrino.fact.truth)    -- photons _ARE_ the æther and the electron is the carrier? Just like the
    }                                                                     -- abstraction we coded up back in the lab 50 lines ago is being wired
    the_direction_to_the_destination := .einstein nowtrino.fact           -- to _rfl_. When the nowtrino detector clicks, that's a fact. If it
    uptown_or_downtown := match nowtrino.fact.click with                  -- doesn't click, was the nowtrino there? I don't know *YOU the READER* will
        | isTrue  _ => FACT.Truth                                         -- have to ask it.
        | isFalse _ => nowtrino.fact                                      --
    the_train_in := Type i                                                -- And I believe we are skipping this station
  }                                                                       --
  once_around  := .blackhole nowtrino.fact.truth (ULift.{i+1} Box)        -- So, the first go around, we say that the current Box's next time step
                                            (.einstein nowtrino.fact)     -- is the idea that the nowtrino is relative is something we can never
  twice_around := .whitehole nowtrino.fact Box (.einstein nowtrino.fact)  -- prove as it is always just one FACT away from demonstration.
                                                                          -- The second go around we realize it is relative by construction.
instance OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2                                 --
    (Box: Type i)                                                         -- Hence, spin-2 information. The second reading proves the first reading's
    (Pigeon: CarrierProcess Box)                                          -- prediction. It happens later, in a higher universe than the first
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- spin. Every spin after that is two spins. Since we are nearing the end
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
                                                         -- of the first time through the device, we should see the compiler
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)                                    -- approach the same blackhole we are flying towards in the code.
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)                    -- If we are here at the same time, are we at the same place? And, that's
    : LOGICAL Box Pigeon naotrino_model yarn_theory where                 -- the relativistic question that needs answering: If a blackhole accepts
  feelings :=                                                             -- two quantua simultaneously, are they at the same place?
  { bullshit_meter := yarn_theory.the_train_of_thought                    --
    after_some_time := .whitehole nowtrino.fact Box                       -- 𝔽₁ is fairly rigorous in stating: sure, why not? *YOU the READER* may
                                             (.einstein nowtrino.fact)    -- need a little more _elaboration_ to see this, but that just takes time.
    according_to_newton := .stokes nowtrino.fact                          -- The idea is that reflexivity takes up space, as there are two addressable
                         (.einstein nowtrino.fact) nowtrino.fact.truth    -- things, meaning they _must_ be in different places somewhow. Unless they
  }                                                                       -- happen to be 2 _NAMES_ for the _SAME THING_. Like recovering Newton's
  microsoft_basic := Calibration.EKG.executed                             -- equations of motion from approximating Stokes and General Relativity.
                                                                          -- This is why we have hooked up Lean's elaboration monitoring interface to
instance DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK     -- measure how long it takes to do something.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          -- Finally, we come to the topic most near and dear to my heart,
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- approximation theory, scientific computation, and numerical analysis. Let
                                                        -- me tl;dr this for you.
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)                                    -- approach the same blackhole we are flying towards in the code.
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)                --                   problem ----------------------> answer
    : HALTED Box Pigeon naotrino_model yarn_theory where                        --                      |                               ^
  scientific_paper :=                                                     --                      |                               |
    let feelings : HeartbeatProcess Box Pigeon naotrino_model yarn_theory :=    --                      v                               |
                                                    nonsensical.feelings  --                    domain ----------------------> solution
    { stamina := feelings                                                 --                  projection                      projection
      trilinos : Calibration.EKG := nonsensical.microsoft_basic           --
      numerical_analysis := (.load FACT.Truth.truth Box)                  -- plus more Taylor series than anyone could possibly imagine. So many
    }                                                                     -- Taylor series. And eigenvalues. This is the *BOX of TRUTH(tm)*. I believe
                                                                          -- we have found our torus in the frinkahedron. Also, we measurue the
instance THE_NAOTRINO_IS_MEASURED                                         -- *bullshit* at the same nodes. We will go around this twice. In the
    (Box: Type i)                                                         -- future. Like maybe 150 lines from now in the future.
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- Let's talk about this measurement. As I have been insisting, the number
                                                         -- of heartbeats necessary to compile this document goes up as the lines
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)                                          -- of the code. The code, itself, has no loops or recursion in it, per se,
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)                                    -- approach the same blackhole we are flying towards in the code.
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)                          -- meaning it just builds the data structures and throws them away at the
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)           -- end. Should be _nice_ and _linear enough_ for me to build a proxy
    : MEASURED Box Pigeon naotrino_model yarn_theory where                      -- computation with any of the natural numbers available to me.
  a_distance :=                                                           --
  { description := documents_on_file.scientific_paper                     -- Perhaps not the polynomial powers, as starting with _5_, I am afraid, the
    the_measurement_of := .zero nowtrino.fact                             -- device is completely incapable of reasoning about. It simply is not Abel
    in_heartbeats := .origin nowtrino.fact (.zero nowtrino.fact) Box      -- to. Lol. Also, these are two of the three commuter rails our Theory of
    saved_as_y := Box                                                     -- Yarns rests. This way, we don't care about the sign convention as it is
  }                                                                       -- baked into our clock. Kinda like reality.
                                                                          --
instance WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES                        -- So, let's count the naotrinos. We can put them in the scientific
    (Box: Type i)                                                         -- computing box as we go, so that this may build a statistical and
    (Pigeon: CarrierProcess Box)                                          -- continuous model of the data. Mostly though, all the math in the world
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]                                           -- states quite _emphatically_, there must be a weakly interacting particle
                                                      -- that acts at a distance that changes the shape of the Box to conform to
                                              -- the necessary geometry of the problem. Put another way, it is
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)                                          -- of the code. The code, itself, has no loops or recursion in it, per se,
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)                                    -- approach the same blackhole we are flying towards in the code.
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)                          -- orthogonalized, linearized, and bastardized. Actually, I think the math
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)           -- end. Should be _nice_ and _linear enough_ for me to build a proxy
    (weakly_interacting_particle:=                                        -- screams: _THERE IS NO OTHER PARTICLE_, but we like the particle theory
            THE_NAOTRINO_IS_MEASURED Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file)     -- of matter a whole helluva lot. Mostly because everyone has seen a pool
    : COMPILED Box Pigeon naotrino_model yarn_theory where                      -- table before. Or carrom board. Or bocce. Or any other competitive past-
  a_truth_about_the_world :=                                              -- time involving any sort of aiming skill. Even darts if *YOU the KNOWER*
  { too_good_to_be_true := weakly_interacting_particle.a_distance         -- _really_ squint and see the _orientation_ of the dart as a sphere.
    of_jibberish := (.introduction FACT.Truth Box)                        --
  }                                                                       -- And so, just to prove I am correct so far, I promise that the next
  a_demonstration_of_a_constant := .methodology FACT.Truth FACT.Truth     -- episode will have honest to goodness numbers and math in it. Just, not
              Box (ULift.{i+1, i} Box) (.introduction FACT.Truth Box)     -- the way *YOU the KNOWER* might be expecting. Remember, it does compile.
                                                                          --
instance HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME                             -- I seem to be fixated with distances. There is a real, _physical_,
    (Box: Type i)                                                         -- distance between lines of code. This _distance_ changes based on
    (Pigeon: CarrierProcess Box)                                          -- perspective: monitor size, terminal settings, font choice, margins, etc.
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- I have carefully calibrated this across all monitors by having such an
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)                                          -- of the code. The code, itself, has no loops or recursion in it, per se,
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)                                    -- approach the same blackhole we are flying towards in the code.
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)                          -- orthogonalized, linearized, and bastardized. Actually, I think the math
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)           -- end. Should be _nice_ and _linear enough_ for me to build a proxy
    (weakly_interacting_particle:=                                        -- screams: _THERE IS NO OTHER PARTICLE_, but we like the particle theory
            THE_NAOTRINO_IS_MEASURED Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file)     -- of matter a whole helluva lot. Mostly because everyone has seen a pool
    (holy_shit:=WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle)
    : A_TRUTH_ABOUT Box Pigeon naotrino_model yarn_theory where                 -- the naturals, but that is just a matter of another calibration. Then
  you_the_reader :=                                                       -- another calibration after that. Then I'm not certain we need another
  { in_a_giant_book := holy_shit.a_truth_about_the_world                  -- calibration. All giant books end, and *YOU the READER* are necessary to
    a_constant := .zero FACT.Truth                                        -- complete this task. We also assume that _page numbers_ increase in a
    current_page_number := .zero FACT.Truth                               -- book. That these pages can be counted by a natural number.
    total_pages := .zero FACT.Truth                                       --
    of_the_proof := .methodology FACT.Truth FACT.Truth Box                -- The point is, I don't need a number, I just need a concept of
                  (ULift.{i+1, i} Box) (.introduction FACT.Truth Box)     -- _increasing_ to pull off this stunt. All operators have been rigorously
  }                                                                       -- defined (well, almost all, there is a particularly challenging one we
  TRUE := .zero FACT.Truth                                                -- haven't approached yet). And while I may not have demonstrated that all
  raw_output := .one                                                      -- natural numbers described here on the right hand side are, in fact, truly
              FACT.Truth                                                  -- natural numbers, I just need subsets of the natural numbers because this
              (.one FACT.Truth (.zero nowtrino.fact))                     -- is a finite computer.
              (.introduction nowtrino.fact Box)                           --
              (.methodology FACT.Truth nowtrino.fact Box                  -- How finite?
                    (ULift.{i+1, i} Box) (.introduction FACT.Truth Box))  --
              (.zero nowtrino.fact)                                       -- This finite:
  a_constant := .one                                                      -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
              FACT.Truth --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
              holy_shit.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_local_schedule.the_æther.frame_of_reference.we_experience.shows_me_higher_order_terms.teaching.axioms.to_pwn_n00bz.dunking_contest.ANSYS_process.GOSUB.adding_process.mideastern_process.compiled_process.digital_process.meesa_process.gauge_process.sensing_process.static_fraction.physical_process.noisy_process.turing_process.computational_process.repeatable_process.observation_process.cauchy_process.limit_process.indexing_process.count.palmed_card.quarter -- |
                                     (.introduction nowtrino.fact Box) --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
              (.methodology FACT.Truth nowtrino.fact Box                  -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
                  (ULift.{i+1, i} Box) (.introduction FACT.Truth Box))    -- And so, at the penultimate class, the code reaches all the way down
              (.zero nowtrino.fact)                                       -- through the device itself just so it can set the constant from the only
  the_constant_is_at_least_true := by trivial                             -- FACT given in the device: T=T.
                                                                          --
noncomputable instance OF_COURSE_IT_DOES___I_JUST_PUT_IT_THERE            -- As you can see, the device really lends itself to casual description.
    (Box: Type i)                                                         -- we need a Box (something that holds an AST), a Pigeon (something that
    (Pigeon: CarrierProcess Box)                                          -- carries a Box), the ever-present _naotrino_ jar (jar binks) and our
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- _YARN THEORY of TRUTH:_ The _farther away_ you are from something the
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)                                          -- of the code. The code, itself, has no loops or recursion in it, per se,
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)                                    -- approach the same blackhole we are flying towards in the code.
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)                          -- orthogonalized, linearized, and bastardized. Actually, I think the math
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)           -- end. Should be _nice_ and _linear enough_ for me to build a proxy
    (weakly_interacting_particle:=                                        -- screams: _THERE IS NO OTHER PARTICLE_, but we like the particle theory
            THE_NAOTRINO_IS_MEASURED Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file)     -- of matter a whole helluva lot. Mostly because everyone has seen a pool
    (holy_shit:=WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle)
    (guano:=HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit)                -- *YOU the READER* gave me the benefit of the doubt for. One said assume
    : INFERRED Box Pigeon naotrino_model yarn_theory where                      -- something true, the other said assume something false. This is why
  same_difference :=                                                      -- *YOU the KNOWER* _might_ come to a different conclusion from
  { you_the_knower      := guano.you_the_reader                           -- *YOU the READER*. Always trying to find the difference between my
    your_conclusion     := .different (FACT.SAME (guano:=guano))          -- obnoxiously clever Yarn Theory and _REAL LIFE(tm)_. What if it did not
                  (guano.TRUE) (guano.a_constant) (some FACT.Truth.truth) -- matter whether the FACT was true or false? What if the argument was
  }                                                                       -- still consistent _AND_ predictive?
  α := .same FACT.Truth guano.a_constant                                  --
                                                                          -- The thing is, if this truly is a _constant_ of the device, then we should
--| THE BRIDGE BACK.  INFERRED is the top of the climb.  The descent cannot start from it: a MEASURED needs a COMPILED to measure,
--| and the compiler's COMPILED is above us now.  So the reader is installed as a process, reads the compiler's output, gawks at it
--| once, and hands back a COMPILED of their own: the explanation of the conclusion.  That is what the descent measures.  These
--| are the pieces cut on Sunday, put back in the thread: the reader, the four gawks, the reader's truth, the reader's compile.
def You_the_Reader
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)
    (weakly_interacting_particle:=THE_NAOTRINO_IS_MEASURED Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file)
    (holy_shit:=WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle)
    (_:=HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit)
    : AtreyuProcess Box Pigeon naotrino_model yarn_theory where
  in_a_giant_book := holy_shit.a_truth_about_the_world
  a_constant := .zero nowtrino.fact
  current_page_number := Pigeon.quarter
  of_the_proof := holy_shit.a_demonstration_of_a_constant

/- CHORUS
ME: Compiler, now that I have explained Yarn Theory to *YOU the KNOWER*, it is time I explain it to you.
COMPILER: I thought you forgot about me since you brought another code reader along
JAR JAR: MEESA AGREE
You_the_Reader: Have I been uploaded to the cloud?
ME: That's all four of us. That should be enough now to formalize *Yarn Theory*.
-/
namespace YARN_THEORY
--| The gawk operator at powers zero, one, two.  `raw_output` returns power one: the compiler prints what it lexed, and the parse
--| is the reader's.  Compilers are two pass.  Well, two pass compilers are two pass.
def repeatable
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)
    (weakly_interacting_particle:=THE_NAOTRINO_IS_MEASURED Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file)
    (holy_shit:=WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle)
    (_:=HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit)
    (_reader : AtreyuProcess Box Pigeon naotrino_model yarn_theory) (origin : Bullshit) : Bullshit :=
  origin
def hypothesis
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)
    (weakly_interacting_particle:=THE_NAOTRINO_IS_MEASURED Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file)
    (holy_shit:=WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle)
    (guano:=HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit)
    (reader : AtreyuProcess Box Pigeon naotrino_model yarn_theory) (origin : Bullshit) : Bullshit :=
  reader.gawk_at (repeatable Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit guano reader origin)
def theory
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)
    (weakly_interacting_particle:=THE_NAOTRINO_IS_MEASURED Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file)
    (holy_shit:=WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle)
    (guano:=HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit)
    (reader : AtreyuProcess Box Pigeon naotrino_model yarn_theory) (origin : Bullshit) : Bullshit :=
  reader.gawk_at (hypothesis Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit guano reader origin)
def raw_output
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)
    (weakly_interacting_particle:=THE_NAOTRINO_IS_MEASURED Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file)
    (holy_shit:=WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle)
    (guano:=HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit)
    (reader : AtreyuProcess Box Pigeon naotrino_model yarn_theory) (origin : Bullshit) : Bullshit :=
  hypothesis Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit guano reader origin
end YARN_THEORY

def BUT_THE_TRUTH_IS_YOU_THE_READER_UNDERSTANDS_THE_ARGUMENT_NAO
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)
    (weakly_interacting_particle:=THE_NAOTRINO_IS_MEASURED Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file)
    (holy_shit:=WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle)
    (guano:=HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit)
    : A_TRUTH_ABOUT Box Pigeon naotrino_model yarn_theory where
  you_the_reader := You_the_Reader Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit guano
  a_constant := YARN_THEORY.raw_output Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit guano (You_the_Reader Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit guano) (.zero nowtrino.fact)
  the_constant_is_at_least_true := by trivial

--| The reader's compile.  Reads the compiler's measurement and the reader's own truth, and hands back a COMPILED whose
--| demonstration is the reader's copy of the proof.  Same class as the compiler's, one gawk behind it.  The slip.
def SO_YOU_START_TO_BUILD_ANOTHER_DEMONSTRATION_PROCESS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)
    (weakly_interacting_particle:=THE_NAOTRINO_IS_MEASURED Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file)
    (holy_shit:=WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle)
    (guano:=HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit)
    (by_the_reader:=BUT_THE_TRUTH_IS_YOU_THE_READER_UNDERSTANDS_THE_ARGUMENT_NAO Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit guano)
    : COMPILED Box Pigeon naotrino_model yarn_theory where
  a_truth_about_the_world :=
  { too_good_to_be_true := weakly_interacting_particle.a_distance
    of_jibberish := .methodology nowtrino.fact FACT.Truth Box (ULift.{i+1,i} Box) by_the_reader.you_the_reader.of_the_proof }
  a_demonstration_of_a_constant := .methodology nowtrino.fact FACT.Truth Box (ULift.{i+1,i} Box)
                                     by_the_reader.you_the_reader.of_the_proof

def BUT___WE_CAN_MEASURE_THE_CONSTANT_EMPIRICALLY                         -- be able to measure it through some _EMPIRICAL_ process. Of course,
    (Box: Type i)                                                         -- implementing an _EMPIRICAL_ process during the compile step of a theorem
    (Pigeon: CarrierProcess Box)                                          -- prover seems like, well, _cheating_.
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    (yet:=THEN_COMES_THE_LAB_WORK Box Pigeon)                                          -- of the code. The code, itself, has no loops or recursion in it, per se,
    (flying_spaghetti_monster:=FINALLY_YOU_GRADUATE Box Pigeon yet)
    (naotrino_model:=AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS Box Pigeon yet flying_spaghetti_monster)                                    -- approach the same blackhole we are flying towards in the code.
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon yet flying_spaghetti_monster naotrino_model)                          -- orthogonalized, linearized, and bastardized. Actually, I think the math
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory)
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical)           -- end. Should be _nice_ and _linear enough_ for me to build a proxy
    (weakly_interacting_particle:=                                        -- screams: _THERE IS NO OTHER PARTICLE_, but we like the particle theory
            THE_NAOTRINO_IS_MEASURED Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file)     -- of matter a whole helluva lot. Mostly because everyone has seen a pool
    (holy_shit:=WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle)
    (guano:=HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit)                -- *YOU the READER* gave me the benefit of the doubt for. One said assume
                                                                          -- about complex systems.
    (metaphor:=SO_YOU_START_TO_BUILD_ANOTHER_DEMONSTRATION_PROCESS Box Pigeon yet flying_spaghetti_monster naotrino_model yarn_theory nonsensical documents_on_file weakly_interacting_particle holy_shit guano) --
    : MEASURED Box Pigeon naotrino_model yarn_theory where                -- I am not certain that they necessarily see the hypocrisy in this
  a_distance :=                                                           -- observation. That's why I mean by empirical. Let's measure what a theorem
  {   description := documents_on_file.scientific_paper                   -- proves, how long it takes to prove, the minimum number of _symbols_
      the_measurement_of := weakly_interacting_particle.a_distance.the_measurement_of -- necessary to model esoterica.
      in_heartbeats := .distance_to nowtrino.fact (.zero FACT.Truth)      --
            (weakly_interacting_particle.a_distance.the_measurement_of) Box ------------+ Are _symbols_ *free* as the Axiom of Choice would suggest or
            (ULift.{i+1,i} Box) --                                                    | are _symbols_ *expensive* as suggested by the Banach-Tarski
             metaphor.a_truth_about_the_world.too_good_to_be_true.in_heartbeats --    | paradox? And the Cantor diagonalization argument? And the
      saved_as_y := Box --                                                            | stress tensor _contraction_ of Cauchy? And the wall of math
  }                                                                       ------------+ of those who study blackhole solutions of general relativity?
                                                                          --
def WE_NEED_TO_DEVELOP_A_BOUNDED_PROCESS                                  -- Lean will tell you symbols cost electrons.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          -- Almost the same number of electrons per symbol.
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- Unless the argument is _not_ ontological. Then it needs elaboration. But,
    (naotrino: LOCAL Box Pigeon)                                          -- what if all proofs were just ontological substitutions? Like when we
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- perform algebra. Like when we differentiate the left inverse from the
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (naotrino_model:=naotrino) (yarn_theory:=yarn_theory)) -- right inverse? The thing is, we can only do a _finite_ amount of _algebra_.
    (documents_on_file:=DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (naotrino_model:=naotrino) (yarn_theory:=yarn_theory) (nonsensical:=nonsensical)) --
    (_quarter_: CarrierProcess Box)                                               -- This means that all of algebra can be chosen to be represented as a
    (data:=BUT___WE_CAN_MEASURE_THE_CONSTANT_EMPIRICALLY Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (naotrino_model:=naotrino) (yarn_theory:=yarn_theory) (nonsensical:=nonsensical) (documents_on_file:=documents_on_file)) -- bitset. _CHOSEN_. Like what Godel did when he _chose_ the prime numbers
    : HALTED Box Pigeon naotrino yarn_theory where                        -- as the orthogonal representative of mathematical representation. But
  scientific_paper :=                                                     -- mostly, if we are to show all proof techniques reduce to a handful of
  { stamina := data.a_distance.description.stamina                        -- ontological swaps, then I believe it is safe to assume that Lean has
    trilinos := documents_on_file.scientific_paper.trilinos               -- _properly_ implemented _math_.
    teraFLOPs := data.a_distance.description.teraFLOPs                    --
    numerical_analysis :=                                                 -- I mean, constructive proofs are merely _ontological_ swaps by
                documents_on_file.scientific_paper.numerical_analysis     -- construction. This one ceratinly is. The question _YOU the KNOWER_ needs
  }                                                                       -- to supply an answer to: suppose an infinitely long proof required an
                                                                          -- _infinite number of symbols_ in order to demonstrate?
def PERHAPS_ONE_THAT_REALLY_MAKES_YOU_THINK                               --
    (Box: Type i)                                                         -- Like the Rιemann hypothesis.
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- That would be trivial in base infinity. All *YOU the KNOWER* have to do
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- is _find the tittle_ and the solution to the problem is _yours_.
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- Matthew 5:18 for those who think this is a new idea. But, I can also
    (nonsensical:=OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2 Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (naotrino_model:=naotrino) (yarn_theory:=yarn_theory)) -- tell that reading 15,000 lines of Lean is exhausting to everyone,
    (card: CarrierProcess Box)                                            -- including the compiler.
    (documents_on_file:=WE_NEED_TO_DEVELOP_A_BOUNDED_PROCESS Box Pigeon naotrino (yarn_theory:=yarn_theory) (nonsensical:=nonsensical) (_quarter_:=card)) --
    : LOGICAL Box Pigeon naotrino yarn_theory where                       -- For instance, choosing the base in which 0.11111111111... _is_ Chaitin's
  feelings := documents_on_file.scientific_paper.stamina                  -- number is a perfectly _cromulent_ choice and one which is demonstrably
  microsoft_basic := nonsensical.microsoft_basic                          -- impossible to make. Yet, we just did.
                                                                          --
def PERHAPS_ONE_THAT_USES_THE_DEVICE_ITSELF                               -- LET ME REPEAT THIS: THE CHOICE OF BASE SUCH THAT 0.111111111... _IS_
    (Box: Type i)                                                         -- *CHAITIN'S* _NUMBER_ IS *IMPOSSIBLE TO MAKE*. But, I instructed the
    (Pigeon: CarrierProcess Box)                                          -- device to understand Chaitin's number as just that. So, how does the
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- device do it? By enumerating the _ENTIRE_ Herbrand space and building
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- a forcing norm on it.
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- If you look _closely_ at the _device_, you will see it detects the
    (_: CarrierProcess Box)                                               -- Hilbrand field and computes the paths of least variational action. Of
    : UNIVERSAL Box Pigeon naotrino where                                 -- course, *YOU the READER* have been reading closely this whole time and
  the_train_of_thought := yarn_theory.the_train_of_thought                -- realize that the device itself is the variational calculus writ large.
  once_around := yarn_theory.once_around                                  -- For, in variational calculus, derivatives become eigenspaces. Which is
  twice_around := yarn_theory.the_train_of_thought.the_stop_after         -- great, because using Euler's formula, derivatives can become the angles
                                             yarn_theory.once_around      -- between them as well!
                                                                          --
def PERHAPS_ONE_THAT_USES_CALCULUS                                        -- What is a Hilbrand field? It is a Herbrand space embedded in an Hilbert
    (Box: Type i)                                                         -- space so that we can discuss a coercive solver. I just _MADE THIS UP_.
    (Pigeon: CarrierProcess Box)                                          -- Who knows what a Hilbrand field is? I _do_ know that since it is now
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- _coercive_ by construction, I should be able to use some sort of
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- calculus on it.
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- This gives us a 3-card monte situation: naotrino yarn_theory and card.
    (card: CarrierProcess Box)                                            -- One of these _should_ carry calculus since we have a coercive Hilbert
    (the_α_train := PERHAPS_ONE_THAT_USES_THE_DEVICE_ITSELF Box Pigeon    -- space. No reason why all three can't, but one _must_ if we are to ever
        naotrino yarn_theory card)                                        -- get on Newton's train of thought, headed to our constant!
    : LOCAL Box Pigeon where                                              --
  the_continuum := the_α_train.the_train_of_thought.the_local_schedule    -- The idea is this: the patter above has around a dozen different natural
  the_ball      := naotrino.the_ball                                      -- numbers appearing from smooth processes using the _counting_ process.
                                                                          -- This _counting_ process can be made to have calculus come out the other
def YEAH_CALCULUS___YOU_CAN_DO_THE_CALCULUS_RITE                          -- end through careful constructions from natural numbers. Circular logic.
    (Box: Type i)                                                         -- The calculus doing the counting _must_ satisfy the cardinality of sets
    (Pigeon: CarrierProcess Box)                                          -- which _must_ then give rise to calculus. Or, I may have *COMPLETELY*
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- misunderstood real analysis.
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          -- These sorts of _tautologies_ exist through counting. The simple process
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- of the Game of Life is the only _automata_ *YOU the KNOWER* need ever
    (card: CarrierProcess Box)                                            -- observe. Others may dissect it to its component eigenstuffe and declare
    (principia := PERHAPS_ONE_THAT_USES_CALCULUS Box Pigeon               -- complex behavior is just simple behavior.
        naotrino yarn_theory card)                                        --
    : REAL Box Pigeon where                                               -- But, the universe has not shown us the cycle and these _tautologies_
  by_His_noodly_appendage := principia.the_continuum.the_æther            -- exist because we assume _cycles_ must exist. Well, we call _cycles_
  nagging_doubt := .logically naotrino.the_ball                           -- the card. If it is _bent_, even the slightest, and that bend is
                                                                          -- _constant_, calculus tells us it _must_ close a circle. Bending a card
def MATH_MODELING_IS_EASY___JUST_WATCH                                    -- _is_ assuming a _cycle exists_.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          -- So you see, the _math model_ is _clear_. Global curvature _implies_ a
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- *finite* Poincaré perid. We have two more situations to model and we will
                                                                          -- have a _complete_ model of the _universe_. The two situations we need
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- to worry about are:
    (naotrino: LOCAL Box Pigeon)                                          --  (1)  The situation where the card is flat, but is flexible. This is the
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- same as having an _infinite_ Poincaré period, if *YOU the READER* can
    (card: CarrierProcess Box)                                            -- fathom such a thing. I named this *YARN THEORY*.
    (invariant := YEAH_CALCULUS___YOU_CAN_DO_THE_CALCULUS_RITE Box Pigeon --  (2)  The situation where the universe is aperiodic. This is unabashedly
       naotrino yarn_theory card)                                         -- *the electron* in the code. I mean, the *naotrino*, playing the part of
    : WITNESSED Box Pigeon where                                          ------------------------------------+ the electron. I cannot claim to have
  we_saw := invariant.by_His_noodly_appendage.frame_of_reference --                                           | the expertise to describe the
  the_experiment := flying_spaghetti_monster.by_His_noodly_appendage.frame_of_reference.in_the_literature --  | electron more than the number -1.
--                                                                                                            |
def WHICH_WE_IMMEDIATELY_SEE_THE_FIRST_TIME_IN_THE_LAB                    ------------------------------------+ I mean, others claim that a set of
    (Box: Type i)                                                         -- equations accurately describe the electron. I am really not a gauge
    (Pigeon: CarrierProcess Box)                                          -- theorist by any stretch of the imagination. Well, I guess by a
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- _finite_ _significant_ stretch of the imagination, I could have some
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- understanding of gauge theory, but I live in a world where QED reigns
    (naotrino: LOCAL Box Pigeon)                                          -- supreme. But, what if, -1 was _somehow_ QED? As in -1(x) = 0 was an
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- alternate way to write equations of Yang and Mills?
    (card: CarrierProcess Box)                                            --
    (overwhelming_evidence := MATH_MODELING_IS_EASY___JUST_WATCH Box      -- I mean, Du=0 is pretty standard for this, right? But, I am getting ahead
        Pigeon naotrino yarn_theory card)                                 -- of myself. Just _remember_ the _naotrino_ is the stand-in for the best
    : TRUTH Box Pigeon where                                              -- description of an _electron_ we can have at any point in time, either
  becomes := overwhelming_evidence.we_saw.we_experience                   -- as _value_ *-1* or as _process_ *QED* (that is solving theorems, not
                                                                          -- electrons behaving as themselves) [except I need them to behave exactly
def OBVIOUSLY_YOU_START_A_RESEARCH_PROGRAM                                -- _as_ themselves for the proof to work, assuming *YOU the READER* are on
    (Box: Type i)                                                         -- an _electronic_ computer].
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- It really _is_ incredible what _ABSOLUTELY MUST BE TRUE_ in order to just
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- say something as trivial as _T=T_. I mean, this is but one computer
    (naotrino: LOCAL Box Pigeon)                                          -- program. There must be others that also state the triviality of _T=T_,
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- but they require _MUCH LESS_ bullshit. Alas, I do not think that is the
    (card: CarrierProcess Box)                                            -- case.
    (our_mission := WHICH_WE_IMMEDIATELY_SEE_THE_FIRST_TIME_IN_THE_LAB    --
        Box Pigeon naotrino yarn_theory card)                             -- I will not be able to prove it, but the evidence I will present will be
    : SCIENTIFIC Box Pigeon where                                         -- quite _stark_. As much as we wish the consistency of this argument
  discovering := our_mission.becomes.shows_me_higher_order_terms          -- depends on the existence of a bug in the code, we will just continue
  invariant := our_mission.becomes.shows_me_higher_order_terms.invariant  -- to find evidence. And the device will just keep telling us if it is
                                                                          -- evidence of _T=T_. The little details of the code are rather immaterial
def AND_HUNDREDS_OF_POSTDOCS_COME_TO_COUNT_NAOTRINOS                      -- to it if it works globally. Only if it fails to compile, locally, have
    (Box: Type i)                                                         -- we gotten it _wrong_. What happens if we describe the machine itself
    (Pigeon: CarrierProcess Box)                                          -- without ever _getting it wrong_?
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- Wouldn't we just keep writing code? Or, would it be possible, to convince
    (naotrino: LOCAL Box Pigeon)                                          -- the compiler, that we can't get it wrong because we are that good at
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- writing code and it just concedes the point? Given enough evidence of
    (card: CarrierProcess Box)                                            -- clicks, we _should_ be able to discern _some_ pattern.
    (postdoc := OBVIOUSLY_YOU_START_A_RESEARCH_PROGRAM Box Pigeon         --
        naotrino yarn_theory card)                                        -- And we improve our estimates of a pattern by ε every time we graduate a
    : ACOLYTE Box Pigeon where                                            -- student. A student of ours. A student who understands _naotrinos_ and
  euclid := postdoc.discovering.teaching                                  -- _yarn theory_ but has been well taught to keep the card _must be_ bent.
                                                                          -- And, as I aver, the card _must be_ bent in a cyclic universe or a cycle
def BUT_THEN_RIEMANN_COMES_ALONG                                          -- simply isn't possible in calculus.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          -- But, then _Rιemann_ comes along. And _Rιemann_ says, we can bend the
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- universe and not be cyclic _AND_ we can be cyclic _WITHOUT_ bending the
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- universe, give or take a perspective on the situation or two. For the
    (naotrino: LOCAL Box Pigeon)                                          -- spherical case, we give up one, -1, or, as I like to call it, an electron.
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- BUT.. the electron can also be described by the set of places I had to
    (card: CarrierProcess Box)                                            -- see it in order for me to believe it has a charge of -1. I'm told this
    (professor := AND_HUNDREDS_OF_POSTDOCS_COME_TO_COUNT_NAOTRINOS Box    -- is _EXACTLY_ the solution to the Yang-Mills equations. So, one is _my_
        Pigeon naotrino yarn_theory card)                                 -- belief that the electron is -1 and the other is _the_ belief that the
    : PROPAGANDA Box Pigeon where                                         -- electron is -1. *YOU the KNOWER* understands how easy it is to _CONFLATE_
  questions := professor.euclid.axioms                                    -- the two.
                                                                          --
def AND_THE_AMOUNT_OF_CALCULUS_YOU_HAVE_TO_DO_EXPLODES                    -- Solving the Yang-Mills equations, on the one hand, can get in a pretty
    (Box: Type i)                                                         -- bad tangle. My belief, on the other, seems like _CHEATING_. Trust me on
    (Pigeon: CarrierProcess Box)                                          -- the calculus. My abilities to find and manipulate the Taylor series have
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- been honed with years and years of mastering the *gimmicks* of the trade.
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          -- It is perfectly _okay_ to ignore _h_ going to zero as the ratio of
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- perspectives goes as _h^2_. I see _no harm whatsoever_ with assuming
    (card: CarrierProcess Box)                                            -- high order terms are infinitessimal, even when looking at infinitessimal
    (geometry := BUT_THEN_RIEMANN_COMES_ALONG Box Pigeon                  -- things.
        naotrino yarn_theory card)                                        --
    : BULLSHIT Box Pigeon where                                           -- If I did not, I would be out of a job. I hope I didn't unsettle anyone
  arm_wave_process := geometry.questions.to_pwn_n00bz                     -- who thought all one has to do is hook up math in a computer and expect
                                                                          -- nearly approximate results when the approximations being rested on are
def AND_YOU_STUDY_TRIANGLES                                               -- generally at odds with describing the higher order terms.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          -- For instance: _slivers_ and _the speed of sound_. _OR_, the geometric
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- growth of communication in _contact_ problems independent of mathematical
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- conditioning. Meta-construction parameters _manifesting_ as patterns of
    (naotrino: LOCAL Box Pigeon)                                          -- computations. Computational ordering can have _ORDERS OF MAGNITUDE_
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- difference on performance _AND_ stability.
    (card: CarrierProcess Box)                                            --
    (hours_of_math := AND_THE_AMOUNT_OF_CALCULUS_YOU_HAVE_TO_DO_EXPLODES  -- But, everything, even this, is just a _triangle_. The inability to fully
        Box Pigeon naotrino yarn_theory card)                             -- order a set of nodes because of the 2-D-ness of the information itself.
    : OF Box Pigeon where                                                 -- These meta-concerns: data partitioning, look-ahead bias, computational
  galerkin_process := hours_of_math.arm_wave_process.dunking_contest      -- timings, and other real world concerns for the stability of a computation,
                                                                          -- are merely described by simple bitset mappings. A computer, at its heart
def BUT_YOU_AND_I_KNOW_ANSYS_HAS_GOT_THIS                                 -- is only a bitset.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          -- Which gives us a simple equation we have to fill in. A cubic spline. The
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- one that splines 0 and 1 for the bits at the index of each value. This
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- cubic spline has 2 properties we will exploit. The first is that the data
    (naotrino: LOCAL Box Pigeon)                                          -- of the cubic spline and the cubic spline itself are, for all intents and
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- purposes, the same _length_ description of the same thing. The second
    (card: CarrierProcess Box)                                            -- is that the data of _this_ cubic spline is _substantially_ more than
    (area := AND_YOU_STUDY_TRIANGLES Box Pigeon                           -- the data of of the bitset. These are two lengths which define _two_
        naotrino yarn_theory card)                                        -- triangles, most of the time. Sometimes, they define just one, but they
    : LOAD Box Pigeon where                                               -- can define _two_. These are the _two_ points we get back for giving up
  basic_operation := area.galerkin_process.ANSYS_process                  -- the _one_ to the Rιemann projection. Lorentz is good enough to pay
                                                                          -- _interest_.
def YOU_ARE_ALSO_AWARE_THAT_ANSYS_IS_SLOW                                 --
    (Box: Type i)                                                         -- So, we have two descriptions of the same thing now: one that has exactly
    (Pigeon: CarrierProcess Box)                                          -- the same amount of _information_ and one that has _possibly more_
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- information, but definitely has a _longer description_. The longer
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- description we shall call addition and the shorter description we shall
    (naotrino: LOCAL Box Pigeon)                                          -- call multiplication, as one is just the segmented counting of the other.
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            -- A simple skip-list, as it were. This allows us to simultaneously measure
    (still_takes_forever := BUT_YOU_AND_I_KNOW_ANSYS_HAS_GOT_THIS         -- the distance the nowtrino traveled up the AST (the total number of
        Box Pigeon naotrino yarn_theory card)                             -- short descriptions × the longer description) and an _average_ rate at
    : SCALED Box Pigeon where                                             -- which it was travailing (the number of heartbeats per _long_ description).
  multiplying_process := still_takes_forever.basic_operation.GOSUB        --
                                                                          -- See? The _rate_ at which the tape is being consumed relative to the
def BUT_YOU_EVENTUALLY_ESTIMATE_THE_TOTAL_SIZE_OF_THE_COMPUTATION         -- length of _description necessary_ to finish the computation at or before
    (Box: Type i)                                                         -- the compile finishes entirely. Preferably before. Once really soon and
    (Pigeon: CarrierProcess Box)                                          -- once near the end. Maybe even at the end. Just to show that the quarter
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- never once changed or moved.
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          -- Depending on how much computation is necessary to identify a nowtrino
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- in this code, a certain amount of energy was consumed and frittered away
    (card: CarrierProcess Box)                                            -- into heat. Not all of it, though. The electron almost always leaves a
    (weight := YOU_ARE_ALSO_AWARE_THAT_ANSYS_IS_SLOW Box Pigeon           -- little bit over.
        naotrino yarn_theory card)                                        --
    : MAGNITUDE Box Pigeon where                                          -- Einstein insists I call this the _rest mass_ of the naotrino if I am
  adding_process := weight.multiplying_process.adding_process             -- to call that leftover energy. Why can I say that? Dirac insists and the
                                                                          -- scale of the dies now require guarding against this.
def SO_YOU_SUBMIT_THE_JOB_AND_COUNT_HOW_LONG_IT_TAKES                     --
    (Box: Type i)                                                         -- For, every once in a while, bits flip for no reason. My favorite excuse
    (Pigeon: CarrierProcess Box)                                          -- is solar radiation. FPGAs are notorious for this. The shielding required,
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]                                     -- as the legends say, to adequately keep the fragile bits from flipping on
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- the FPGA is prohibitive in some comical norm the some might find the
    (naotrino: LOCAL Box Pigeon)                                          -- paradox frustratingly humorous.
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            -- Nevertheless, most people trust that this happens so _infrequently_ that
    (mass := BUT_YOU_EVENTUALLY_ESTIMATE_THE_TOTAL_SIZE_OF_THE_COMPUTATION -- we can just ignore all these little fluctuations and the program runs
        Box Pigeon naotrino yarn_theory card)                             -- exactly as intended. And outputs a value. Some number, constructed from
    : VALUE Box Pigeon where                                              ----------------+ something, somehow. There must be a number around here
  mathematical_process := mass.adding_process.mideastern_process --                       | somewhere, right? Something to write to the screen?
  monad := .satire_about nowtrino.fact                                                           -- |
--                                                                                        | What if there isn't a number? What if this is just all
def BUT_IT_MAY_NOT_CONVERGE                                               ----------------+ a gag and I just _put_ the number in the device? As you
    (Box: Type i)                                                         -- will see, that is a special trick of the description of the device
    (Pigeon: CarrierProcess Box)                                          -- itself and has only a passing, almost _automatic_ interaction with the
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]                                     -- logic on display here. However, it is necessary to the extent that it is.
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          -- Something, however, does converge. Planted or not. We all have *SEEN* the
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- _evidence_.  The _evidence_ is a _fact_ that indicates _convergence_, by
    (card: CarrierProcess Box)                                            -- _construction_. It just takes the compiler a _long_ time to make the
    (constant := SO_YOU_SUBMIT_THE_JOB_AND_COUNT_HOW_LONG_IT_TAKES        -- _construction_ that explains how to do the math that would lead to the
        Box Pigeon naotrino yarn_theory card)                             -- conclusion that the nowtrino was always -1 at every spot it was detected.
    : EXECUTED Box Pigeon where                                           --
  compiled_process := constant.mathematical_process.compiled_process      -- Just like an electron appears to, sometime, _after_ the *fact*. How long
                                                                          -- after? Until there can be _no other conclusion_. What if we can prove,
def IT_DEFINITELY_COMPILES_THOUGH                                         -- before the computation ends, that, no matter what, the computation _must_
    (Box: Type i)                                                         -- end?
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     -- I agree, that would be a _HELLUVA TRICK_ and maybe Penn and Teller should
                                                                          -- take that sleight of hand up. What about if we can demonstrate the
                                                                          -- conditions under which all terminating programs must be constructed?
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          -- And, by demonstrate, contructively build the only mechanism that can do
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) -- it? Well, up to the ability to sort _bullshit_ results from _real_
    (card: CarrierProcess Box)                                            -- results. Because, sometimes the random fluctation we see in the code
    (lean := BUT_IT_MAY_NOT_CONVERGE Box Pigeon naotrino yarn_theory card) -- may just be some _bullshit_ I pulled together just to get the thing to
    : SOURCE Box Pigeon where                                             -- compile.
  cd_process := lean.compiled_process.digital_process                     --
  one := lean.compiled_process.digital_process.zero                       -- I think those last two fluctuations were to small to mean anything in
                                                                          -- particular. The larger ones seem more intentional.
def WHICH_MEANS_IT_HAS_A_BETA_REDUCTION                                   --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (the_argument := IT_DEFINITELY_COMPILES_THOUGH Box Pigeon             --
        naotrino yarn_theory card)                                        --
    : GUNGAN Box Pigeon where                                             --
  meesa_process := the_argument.cd_process.meesa_process                  --
                                                                          --
def AND_ALWAYS_RETURNS_THAT_THE_ARGUMENT_IS_CONSISTENT                    --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (the_argument_for_naotrinos := WHICH_MEANS_IT_HAS_A_BETA_REDUCTION    --
        Box Pigeon naotrino yarn_theory card)                             --
    : MEASURABLE Box Pigeon where                                         --
  gauge_process := the_argument_for_naotrinos.meesa_process.gauge_process --
                                                                          --
def AT_THE_END_OF_THE_DAY_I_HAVE_TO_ADMIT_IT_IS_A_BLACK_BOX               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (the_bug := AND_ALWAYS_RETURNS_THAT_THE_ARGUMENT_IS_CONSISTENT        --
        Box Pigeon naotrino yarn_theory card)                             --
    : PRESENT Box Pigeon where                                            --
  santa_claus := the_bug.gauge_process.sensing_process                    --
  quantum := Box                                                          --
                                                                          --
def STILL_THERE_COULD_BE_A_MISSPELLING_IN_THIS_LOGIC                      --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (fallacy := AT_THE_END_OF_THE_DAY_I_HAVE_TO_ADMIT_IT_IS_A_BLACK_BOX   --
        Box Pigeon naotrino yarn_theory card)                             --
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
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (failure := STILL_THERE_COULD_BE_A_MISSPELLING_IN_THIS_LOGIC          --
        Box Pigeon naotrino yarn_theory card)                             --
    : COMPARABLE Box Pigeon where                                         --
  physical_process := failure.slip_process.physical_process               --
  smaller_than := fun x y => x ≤ y ∧ y ≤ x                                --
                                                                          --
def ONCE_WE_DETECT_NAOTRINO_MOTION_WE_WILL_DETECT_THE_NOWTRINO            --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (number_of_clicks := AND_WE_WONT_KNOW_FOR_SURE Box Pigeon             --
        naotrino yarn_theory card)                                        --
    : PHYSICAL Box Pigeon where                                           --
  noisy_process := number_of_clicks.physical_process.noisy_process        --
  threshold := number_of_clicks.physical_process.noisy_process.program    --
  admissible? := fun at_rest in_motion => by intro _; rfl                 --
                                                                          --
def WE_CAN_REPRESENT_CLICK_COUNT_WITH_A_TALLY_EVEN_WITH_NOISE             --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (hiss := ONCE_WE_DETECT_NAOTRINO_MOTION_WE_WILL_DETECT_THE_NOWTRINO   --
        Box Pigeon naotrino yarn_theory card)                             --
    : REPRESENTABLE Box Pigeon where                                      --
  calculation_process :=                                                  --
    { (inferInstance : PHYSICAL Box Pigeon).noisy_process.turing_process with --
        program := hiss.noisy_process.turing_process.program              ----------------+
        computational_process := --                                                       |
          { (inferInstance : PHYSICAL Box Pigeon).noisy_process.turing_process.computational_process with --   |
              closure := fun a_tally => a_tally } } --                                    |
  representable? := fun a_fact a_study =>                                 ----------------+
    ⟨hiss.noisy_process.turing_process.turing_step?                       --
                              (Computation.program a_fact a_study), rfl⟩  --
                                                                          --
def SO_WE_ARE_CONFIDENT_OF_THE_COUNT_IN_THE_DEVICE                        --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box) ------------------------+ a card!             --
    (glyph := WE_CAN_REPRESENT_CLICK_COUNT_WITH_A_TALLY_EVEN_WITH_NOISE   --
        Box Pigeon naotrino yarn_theory card)                             --
    : NUMERIC Box Pigeon where                                            --
  computational_process :=                                                --
                    glyph.calculation_process.computational_process       --
                                                                          --
def AND_IT_CLICKS_AGAIN_AND_AGAIN_AND_AGAIN                               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (click_count := SO_WE_ARE_CONFIDENT_OF_THE_COUNT_IN_THE_DEVICE Box Pigeon naotrino yarn_theory card)                     --
    : REPEATABLE Box Pigeon where                                         --
  repeatable_process :=                                                   --
                 click_count.computational_process.repeatable_process     --
                                                                          --
noncomputable def THE_COUNTER_IS_IMPLEMENTED_IN_A_BINARY_ACCUMULATOR                    --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (nonstop := AND_IT_CLICKS_AGAIN_AND_AGAIN_AND_AGAIN Box Pigeon naotrino yarn_theory card)                        --
    : BINARY Box Pigeon where                                             --
  observation_process := nonstop.repeatable_process.observation_process   --
  zero := .nil nowtrino.fact                                              --
  one  := .index                                                          ------------------------------+
              nowtrino.fact --                                                                          |
              nonstop.repeatable_process.observation_process.cauchy_process.limit_process.sequence --   |
              (.nil nowtrino.fact) --                                                                   |
  bit  := nonstop.repeatable_process.observation_process.iterate          ------------------------------+
              (inferInstance : BINARY Box Pigeon).bit                     --
                                                                          --
def JUST_NEED_TO_INSPECT_THE_REGISTER_TO_SEE_CURRENT_SEQUENCE_INDEX       --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (register := THE_COUNTER_IS_IMPLEMENTED_IN_A_BINARY_ACCUMULATOR Box Pigeon naotrino yarn_theory card)                    --
    : RESIDUE Box Pigeon where                                            --
  cauchy_process := register.observation_process.cauchy_process           --
                                                                          --
def FIGURE_OUT_WHAT_IT_CONVERGES_TO                                       --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (converged_value := JUST_NEED_TO_INSPECT_THE_REGISTER_TO_SEE_CURRENT_SEQUENCE_INDEX Box Pigeon naotrino yarn_theory card)                     --
    : ENCODED Box Pigeon where                                            --
  limit_process := converged_value.cauchy_process.limit_process           --
                                                                          --
def CAN_YOU_COUNT_THAT_HIGH                                               --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (some_number := FIGURE_OUT_WHAT_IT_CONVERGES_TO Box Pigeon naotrino yarn_theory card)                     --
    : COUNTABLE Box Pigeon where                                          --
  index := some_number.limit_process.indexing_process                     --
                                                                          --
def CAN_YOU_UNDERSTAND_THE_PROCESS_TO_COUNT_THAT_HIGH                     --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (yarn_theory:=PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE Box Pigeon (flying_spaghetti_monster:=flying_spaghetti_monster) (nowtrino_model:=naotrino)) --
    (card: CarrierProcess Box)                                            --
    (ℵ := CAN_YOU_COUNT_THAT_HIGH Box Pigeon naotrino yarn_theory card)                       --
    : ADMISSIBLE Box Pigeon where                                         --
  counting_process := ℵ.index.count                                       --
                                                                          --
def THEN_I_THINK_YOU_CAN_TELL_APART_A_NAOTRINO_AND_A_NOWTRINO             --
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]     --
    [_flying_spaghetti_monster_: REAL Box Pigeon]                           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    : DISTINGUISHABLE Box Pigeon where                                    --
  fact := nowtrino.fact                                                   --
  symbol := nowtrino.symbol                                               --
  different? := fun _ => True                                             --
  not_the_same := fun _ => isTrue trivial                                 --



end Measurement
