/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the stories we tell ourselves might be the only ones we believe._

(c) 2026 All rights reserved. Unless AI needs training data.

__EPISODE 8__: _The Macguffin_

"Forty-two.435?"
                       -- A Macguffin to 3 decimal places

"That Rosencrantz and Guildenstern are dead."
                       -- A callback to a Macguffin

"The stuff that dreams are made of."
                       -- A callback to a callback to a Macguffin as well as a callback to a Macguffin

lake build --force_nats --print_dreams

**NUMBERS?**
How the __HELL__ does this device print such a highly resolved rational number if numbers are _NOT_ part of the argument?
-/

import Measurement.Episode07

--| I believe the idea is to build a _discrete_ model of the device. And, so we will. We will use the _List_ abstraction provided by Lean in order
--| to simulate what the machine is doing. By simulate, we mean only keeping track of the FACTS that are _required_ to fully _describe_ a particular
--| _state_ of a computation, rather than all the supporting _BULLSHIT_. Fun fact: a _List_ is a discrete approximation to an infinite process. I
--| have _no qualms_ using a _List_ as intuition for the argument as the _List_ is a _finite set of representable symbols_ represented as
--| a _finite set of representable symbols_ in a _finite set of representable symbols_ on a _finite set of representable symbols_. Assuming computers
--| are finite and run on _electrons_ (something that exists and can be represented by a mark)[a mark is someone singled out for a confidence scam]
--| {*YOU the KNOWER*, as a mark, have a _mighty fancy set of marks_ that can be considered the mark of the electron: QED, the mark's mark}.

--| The proof of _QED_ = _QED_ is getting easier to write.

namespace Measurement
universe ι ----+ This is the universe we live in.  One without a spin-2 north monopole. A single point removed so that ℝιemannian geometry can
--             | provide the mapping from Euclidean space to _modeling_ space, using whatever "straight" line can be pulled with a yarn.

def ThePreprint.the_model : ThePreprint → List FACT
  | .introduction f _         => [f] -------------------+ Given a PrePrint, we can create a Tape from a list. The list is simply prepending each
  | .methodology c _ _ _ rest => c :: rest.the_model -- | fact to the list. As can be seen, the only thing that matters is the FACT of the matter:
  | .results c _ _ _ _ _ rest => c :: rest.the_model -- | Is the methodology a _TRUE_ methodology or not and are the results _TRUE_ or not. These
--|  +--------------------------------------------------+ are computed by the compiler given the description of the model. Feel free to refer back
--|  | to the device to understand all the cards face down, but, they don't matter for this _demonstration_ of how a _measurement_ *will work*.

--| Given that the model includes the reading that will be taken by Lean's elaboration mechanism, we can describe how the measurement is encoded.
--| The thing is, the reading is merely a decision point. If the compiler is still at the origin, then it hasn't started and has _NO FACTS_. Then,
--| there is the .distance Einstein said we could measure, a _FACT_ about ι. This comes with a bunch of state that the _FACT_ no longer needs to
--| _PROVE_ but _EXPLAIN_ should _someone_ _NEED_ this _FACT_! .speed needs its own place to store data, but it _CANNOT_ take the _LAST_ spot, as
--| _THAT_ spot, the _LAST_ spot, belongs to .distance.

def Measurement.the_reading : Measurement → List FACT --           | There are _two_ major differences when making this tape different from a preprint.
  | .origin _ _ _                 => [] ---------------------------+ The measurement doesn't have a starting point, it does _NOT_ have a fencepost
  | .distance_to f _ _ _ _ rest   => f :: rest.the_reading --      | condition. So, the preprint has a fencepost bug in it. This will use the other
  | .speed f _ _ _ _ _ _ momentum _ => f :: momentum.the_reading --| trailing arm here, the one that computes an accumulating value of some kind.
--|        - ----------- ----------
--|        |      |          |
--|        |      |          +------------> This is the _third card_, the continuation of the_reading.
--|        |      +--------------------------> This is the _palmed quarter_. Only *YOU the READER* and *I* know what is in here. RoFL ∎
--|        +------------------------------------> This is the _first card_, is this a _covariant_ configuration or a _contravariant_ configuration

--| And this will give us the number. By the way, can *YOU the READER* see where the number-like values we will be reading are coming from? See how
--| those numbers _travel_ with their _definitions_? Seems like _y=x_ is getting very close all of a sudden! Which is where we get our _foundations_
--| of _YARN THEORY_. The theory at its most mathematically plain:

--| ι increases in time, lengths of Lists are demonstrably increasing (though not monotonically) throughout time. The List grows in a _PATH_ along
--| the *AST* by _shells_ away from an _origin_. _AdS_ or _Gauss's_ law, take your pick, they are the _SAME_ _DIFFERENCE_. Ta da! YARN THEORY!

--| If I had used _Nats_, I sure as hell could _NOT_ have gotten this far in the argument, by the way. Either Godel, Cohen, or Cantor would have
--| tripped me up. As it stands now, I am shadow boxing Turing and Chaitin. Which is why, sometimes, we want to see the _ALL OF IT_. The one
--| _THEORY_ that explains _ALL ENDS_ and _ALL PATHS_ between those _ENDS_. And the _strings_ that attach them to vibrate imaginarily, like _e^ιθ_.

def YarnTheory.gauss : YarnTheory → List FACT --                                       | Some theories are _designed_ to _explain_ *ALL* _possible_
  | .stokes f _ _                        => [f] ---------------------------------------+ outcomes. Like Fourier analysis. Which can explain things
  | .fibers f _ _ _ _ rest               => f :: rest.gauss --                         | so well, it will ring like a square. What we do in this case
  | .fabric f g _ _ _ _ _ _ before after => f :: g :: before.gauss ++ after.gauss --   | is interleave the covariant and contravariant understanding.
--|  +---------------------------------------------------------------------------------+ Or, we count all the things that come before and all the
--|  | things that come after and that will tell us how many things are happening _right now_ as we just integrate _time_ by parts. _Gauss_ provides
--|  | the integration rule for _eⁱ_ allowing for _exact_ integration whenever we get lucky. Mind the tittle on the twiddle _ι_. What goes in, must
--|  | come out or there is volume to measure. Even if more comes out than goes in.

--| I Wonder what it could mean for _f_ and _g_ to click? For both directions of the fabric, time-like and space-like. 4-d Euclidean space, that is.
--| The _Euclidean Unit Frinkahedron_, as described by the device. The _derivatives_ of _time_ and the _derivatives_ of _space_ share
--| _high order terms_. For spatial derivatives operate on volumes and time derivatives on the iso-surface, or the actual surface position and the
--| normal in which it travels. Gauss, integration by parts, variational mechanics, etc. The symbols might look different, but they do the same
--| dance, as it were.

--| And it all relies on putting two PDAs together to allow the compiler to build an automaton that uses pieces of the device along with a simple
--| representation of the inductives to help _demonstrate_ that it is the _definition_ of the inductives that provides the mechanism behind the
--| Borwein family of integrals. Just expand them in _e^iθ_ and _voilà!_.

def SpaceTimePath.stokes : SpaceTimePath → List FACT --      | Look, let's just call an Ace of Spades an Ace of Spades. This entire file is just
  | .einstein f           => [f] --                          | a careful wiring of all the inductives through each other so that only _the facts_
  | .whitehole f _ rest   => f :: rest.stokes --             | matter and the reasons _why_ do not. For instance, whiteholes contribute very simple
  | .blackhole _ _ rest   => rest.stokes --------------------+ facts: a card. That card might carry a quarter. Probably does. A blackhole, on the
  | .geodesic f _ _ _ a b => f :: a.stokes ++ b.stokes --    | other hand, shares no facts. Only the two cards we didn't pick. A geodesic is simply
--|  +-------------------------------------------------------+ the fact that the _LIST A_ is before _LIST B_ because _a_ comes before _b_. I mean
--|  | it is also that way _alphabetically_ because _a_ has a strong _0-ness_ to it and _b_ has a strong _1-ness_. Unless we are in Fortran, which,
--|  | will bite us because of the fencepost bug alluded to above. Then _a_ has a strong _1-ness_ to it and _b_ has a strong _2-ness_ to it. Either
--|  | way, this just encodes the _FACT_ that _a_ comes before _b_. This is _especially_ *TRUE* in parameterized functions.

--| With these definitions, we can take a _snapshot_ of the _tree_ of _inductives_ at any step in the process of running the machine. For instance,
--| and _especially_, we can understand what the machine's state is _before_ and _after_ it models _YOU the READER_ gawking at the output presented
--| below. Why should the device _model_ *YOU the READER*? Well, like the last episode said, there are some _inconsistencies_ in the logic as
--| presented. _Godel_ suggests we should expect inconsistencies. _WHAT IF_ I could demonstrate _logically_ there exists an argument such that we
--| all agree on a _symbol_ for that inconsistency _AND_ we also agree on what that _symbol means_? And, *WHAT IF* the logic to perform this
--| inconsistency meaning transfer must take _TIME_ and use _ENERGY_? Like compiling a program?

--| This is merely the _argument_ that we could agree on such a symbol.  Not the symbol _itself_. The compiler has _its_ understanding and we can
--| all agree that the _compiler's_ understanding is the _most consistent_. Lol, _mostly consistent_. How _TRUE_ is _TRUE=TRUE_? Let me show
--| *YOU the READER*.

--| Let's _zero_ out the device with all the _zeros_ it needs. It needs _three_ zeros: nothing, the description of nothing, and the origin of an
--| _apparent_ timeline postulated by Einstein himself! I mean, *YOU the KNOWER* certainly obey the EFEs.

def zero : FACT := FACT.Truth ---------------------------------+ Well, to make the argument, there has to be a model of a _PHYSICAL_ person to
def another_zero : Number := Number.zero zero --               | receive the symbol (as it can be made manifest) and agree to its meaning (as it
def zero_distance : SpaceTimePath.{0} := .einstein zero --     | can be made _communicative_). This person is on a worldline. That worldline started
--|  +---------------------------------------------------------+ somewhere: x₀. What is _x_? Whatever it is that needs to be inputs to the field
--|  | equations so that *YOU the KNOWER* can be the center of the universe. *YOU the KNOWER* _KNOW_ _TRUTH_. So, all truth is _ZERO_ distance from
--|  | you. This is a _metaphor_. The distance *YOU the KNOWER* must travel to a new _FACT_ is _measured_ by the device by how complex the _logical_
--|  | argument is, which is _proxied_ by computation time in the compiler, modeled 3 different ways.

def the_satire : ThePreprint.{0} := --     | The three models of the computation are two bullshit numbers, and the _computation_.  The computation
  .results zero zero True Prop Type Type --+ can be described two ways: _TRUE_ with these two types whose universes represent the values somehow, _OR_
    (.methodology zero zero Prop Type --   | as the _description_ of two numbers and a _PROPERTY_, which is a coefficient and monomial of the
      (.introduction zero Prop)) -->       | _zeroth_ power, give or take the fencepost error. In other words, are we _proportional_ or _affine_?

--| Because, you see, if, in the introduction we say that we _begin_ counting with zero is a _TRUE_ statement for Lean. But, it is _really easy_
--| to imagine a programming language that starts at a different _number_. And, if you waited long enough, _any different number_. Then, after an
--| even _longer_ wait, _any different number that has *natural-ness*_. Fortran 90 introduced pointers? The Fortran specification is _clear_ though,
--| that number has a _maximum_ value and a _minimum_ value, proven to exist by the _set based_ understanding of the general _numberness_ of things
--| or by the words in the standard. Same conclusion.

def the_basis : Measurement.{0} := --                                     | .speed is a number, in this case _zero_, but it is computed from _3_
  .speed zero another_zero another_zero another_zero Prop Type Prop --    | different _number-like_ values, especially in our universe ι. The device
    (.distance_to zero another_zero another_zero Prop Type --             | sees these number like properties as two _streams_ of bits and a universe
      (.origin zero another_zero Prop)) ----------------------------------+ at ι levels from the bottom. But, the speed is also a finite difference,
    (.origin zero another_zero Prop) --                                   | but _scaled_ by a coefficient. And, as Galileo pointed out, speed is
--|  +--------------------------------------------------------------------+ measured relative to an origin. I think you can see how to get on the
--|  | the _train of thought_. What if the _train of thought_ was the origin? Well, *YOU the KNOWER* get a _coordinate_ system, especially if the
--|  | bases _span_ something interesting.

def the_coordinate_system : YarnTheory := --                                      | What is the most interesting thing to _span_? Well, the greater
  .fabric zero zero zero_distance zero_distance zero_distance True True True --   | metro train map for the tri-state area seems like a good place
    (.fibers zero zero_distance zero_distance True True --                        | to start. The distance in three dimensions from _zero_ to _zero_
      (.stokes zero zero_distance True)) -----------------------------------------+ is defined to be _zero_ for Hilbert spaces. So, let's define it
    (.stokes zero zero_distance True) --                                          | as such here. Paths through the space can be measured by
--|                                                                               | straight distance or the path taken, which starts at 0 distance.

--| What takes this path? Well the _compiling code_ does, the *[nowtrino: DISTINGUISHABLE]*.  This is not a passive statement but a requirement that
--| Lean build a subjunctive AST, one that _could take place coherently enough to be named_. So, using our little constructs above, we can _build_
--| a model in _Lists_ that demonstrate the _behavior_ of the *[nowtrino: DISTINGUISHABLE]*.

def the_nowtrino_path : SpaceTimePath.{0} := --  | We state our thesis as follows:
  .geodesic zero Prop True Type --               |
    (.whitehole zero Prop zero_distance) --------+ All nowtrinos start in whiteholes, _blueshift_ into existence and are consumed by blackholes by
    (.blackhole True Type zero_distance) --      | _redshifting_ out of existence. Before the compile begins, there is no FACT. Once it begins, there
--|  +-------------------------------------------+ is a brief moment of _amorphous void_ before the first FACT can be observed. The first FACT then
--|  | _blueshifts_ into existence, metaphorically speaking of course. The data then redshift out of existence, their output frozen on the horizon
--|  | for all to gawk at as the FACT is gobbled by the metaphorical singularity of the DIV/0! error at the center of a blackhole. For us, the fact
--|  | is frozen in time. For the compiler, who's to say? Eventual bitrot or throwing something in the blackhole on _top_ of the value will, of
--|  | course, obscure the value permanently. To gawk at it again, the _cycle must repeat_.

def elaborated_by_lean : CarrierProcess Prop where --  | We begin at the beginning. Since the Prop type is the type the compiler uses to store its
  symbol := FACT.Truth --------------------------------+ Bayesian _a priori_ guess, we can model that as the _Carrier of Truth (tm)_. If *YOU the READER*
  quarter := .zero FACT.Truth --                       | remember, this is just the same FACT as FACT.Truth, just a bit different. It'⁻¹s just for Props.
--|  +-------------------------------------------------+ Why? Well, the Prop will carry a universe ι _AND_ the FACT.Truth _AND_ a number-like _THING_ based
--|  | on *COUNTING* universe levels. This allows us to make a very _accurate_ naotrino, as this is just a model. It may or may not be _named_ with
--|  | a _mark_ yet.

instance a_distinct_truth : DISTINGUISHABLE Prop elaborated_by_lean where --   | At this point, I think we have enough to describe something _distinct from_
  fact := elaborated_by_lean.symbol --                                         | truth. I mean, not a _general thing_ distinct from _truth_, but a
  symbol := Prop --------------------------------------------------------------+ logical contradiction described as Lean code that compiles. Basically,
  different?   := fun _ => @decide elaborated_by_lean.symbol.truth --          | anything that doesn't _click with the machine_ is _false_. Either the
                                  elaborated_by_lean.symbol.click = true --    | machine can reconstruct the logical argument missing that would
  not_the_same := fun _ => isTrue rfl --                                       | demonstrate _exactly_ the _inconsistency_ in the device that prevents
--|  +-------------------------------------------------------------------------+ the _inconsistency of logic_ that Godel suggests must exist because there
--|  | are an infinite amount of numbers that can be named, or not. It is clear that we can continue to generate text for ever and ever, but it is not
--|  | clear that all those texts can be _named_ without assuming the infinite cardinality of ℕ. This is the _model_ of the <T,T=T> class upon which
--|  | the device is built. We claim we can use the compiler to _distinguish_ those that are the _same_ and compile from those that are _different_
--|  | and _resist_ all efforts of debugging.

instance : Inhabited (DISTINGUISHABLE.symbol elaborated_by_lean) := instInhabitedProp --+ Thankfully, we can inhabit the symbol of the truthcarrier as
--|                                                                                     | a proof of existence. The symbol is a _proof_?!? Hmmm. I believe
--|                                                                                     | this is called an _ontological argument_.

--| And so, the _COMPILER_ can now build models based on the devices characteristics. For instance, a nowtrino model might be an AST that contains
--| a bunch of pieces of a proof that need to be collected into a logical predicate that needs evaluating for a _real_ computation that hasn't
--| happened yet. Being _noncomputable_ simply means that. At this point, this particular model _cannot_ be _realized_ in a way that determines truth,
--| just that the computation that might _click_ is carried by A_NOWTRINO_MODEL.
noncomputable instance A_NOWTRINO_MODEL : REAL Prop elaborated_by_lean := A_CAUSAL_THEORY Prop elaborated_by_lean

--| Since the nowtrino model is a part of the device instantiated with a Prop and some compilation process, we can discuss the two different paths
--| a _nowtrino_ can take: _this way_ and _that way_. Our discussion of Yarn Theory indicated that there is an _express_ route that does not stop
--| at all stations and a _local_ route that stops everywhere. Each _stop_ is a measurement that the compiler can take and those measurements
--| necessarily increase with time, which goes as the length of the proof. So, the compiler satisfies the minimal yarn condition: _NUMBER GO UP_.
@[irreducible] noncomputable def this_way : LOCAL Prop elaborated_by_lean := A_SMOOTH_MODEL Prop elaborated_by_lean
@[irreducible] noncomputable def that_way : UNIVERSAL Prop elaborated_by_lean this_way :=
                                          IS_IT_CONNECTED_BY_A_YARN? Prop elaborated_by_lean (nowtrino_model := this_way)

--| And since we now have a yarn theoretical path in _that way_, we can ask the compiler to understand that this_way and that_way _START_ and _END_
--| with the same thing (T=T → T). One uses RFL, the other, well, the other demonstrates two things are the same through a bunch of questions.
--| Questions we can now _DIRECTLY_ ask the compiler. The compiler cannot _tell us_ the answer, but it can tell us if the answer _should exist_.
@[irreducible] noncomputable instance : LOGICAL Prop elaborated_by_lean this_way that_way :=
                                          IS_IT_SPINNING? Prop elaborated_by_lean (naotrino_model := this_way) (yarn_theory := that_way)
@[irreducible] noncomputable instance : HALTED Prop elaborated_by_lean this_way that_way :=
                                          DO_YOU_SEE_THE_EVIDENCE? Prop elaborated_by_lean (naotrino_model := this_way) (yarn_theory := that_way)
@[irreducible] noncomputable instance : MEASURED Prop elaborated_by_lean this_way that_way :=
                                          IS_THIS_A_NEW_PARTICLE? Prop elaborated_by_lean (naotrino_model := this_way) (yarn_theory := that_way)
@[irreducible] noncomputable instance : COMPILED Prop elaborated_by_lean this_way that_way :=
                                          HOW? Prop elaborated_by_lean (naotrino_model := this_way) (yarn_theory := that_way)
@[irreducible] noncomputable instance : A_TRUTH_ABOUT Prop elaborated_by_lean this_way that_way :=
                                          WHY? Prop elaborated_by_lean (naotrino_model := this_way) (yarn_theory := that_way)
noncomputable def once_around_the_orbit : INFERRED Prop elaborated_by_lean this_way that_way :=
                                          WHY_NOT? Prop elaborated_by_lean (naotrino_model := this_way) (yarn_theory := that_way)
--| And just like that, we can _INFER_ that the ladder as been traversed _once_ simply because there is _something_ that can be _INFERRED_. In this
--| case, an obvious _INFERENCE_ is that the entire ladder has now been described and shown to possibly _EXIST_. I mean, we show it _DOES_ exist
--| in the README.md. That's proof enough for *YOU the READER* that there exists a device described as I have done so thus far.
@[irreducible] noncomputable instance : INFERRED Prop elaborated_by_lean this_way that_way :=
                                          once_around_the_orbit

--| But, we are looking for the _spin-2_ particle, the one where we can have a _DISTINGUISHABLE_ _TRUTH_ from... well... I'm guessing we can
--| distinguish truth from something else, whatever that something else just might be. This second time around has to go by a _DIFFERENT_ path if
--| we are to apply _YARN THEORY_ to it. So, here is _ANOTHER_ way we can _ZERO OUT_ the device. Just that this is a _hypothetical_ way to zero
--| out the device since these particular definitions involve notions that may not be computable.
noncomputable def the_calculus : LOGICAL Prop elaborated_by_lean this_way that_way :=
  A_BELIEF.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} Prop elaborated_by_lean this_way (yarn_theory:=that_way) (card:=elaborated_by_lean)
noncomputable def 𝔽₁ : ADMISSIBLE Prop elaborated_by_lean :=
  A_GENERATOR.{0,0,0,0,0,0,0,0,0,0,0} Prop elaborated_by_lean this_way.{0,0,0,0} that_way.{0,0,0,0,0,0} elaborated_by_lean
noncomputable def the_truth : DISTINGUISHABLE Prop elaborated_by_lean :=
  A_NAOTRINO.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} Prop
                                                            elaborated_by_lean this_way.{0,0,0,0} that_way.{0,0,0,0,0,0} elaborated_by_lean
--|                                                         ------------------------------------- -----------------------------------------
--|                                                                           |                                        |
--|    The two ways to elaborate, before and after ---------------------------+----------------------------------------+

--| Combining all three gives our _naotrino_ model: the three different ways T=T: y=x, the single element, and a _formal description_ of T=T.
noncomputable def a_naotrino_model := (the_calculus, 𝔽₁, the_truth)
--| Once we have our model, we need to collect the _FACTS_ that _MUST BE TRUE_ for our _model_ to exist _enough_ to be named. Not certain if it
--| exists nearly enough to be computed.

--| Now, we can ask Lean _itself_ how many _FACTS_ were determined in Episode 7.  This merely counts the number of _UNIQUE_ _FACTS_ that _clicked_
--| with _Lean_ itself while _elaborating Episode 7_. One FACT per fact. Given a _type_ that _elaborates_, census_tape will compute all the FACTS
--| associated with that _type_ that _Lean_ figured out and _count_ them.
elab "episode7_elaboration_of " targets:ident+ " as " name:ident : command => do
  let env ← Lean.getEnv
  let mods := env.header.moduleNames --                                      | What is a _rung_? Well, since *YOU the READER* asked, I need _yet_
  let isRung (n : Lean.Name) : Bool := --                                    | _another_ _METAPHOR_ in order to keep the metaphors from _mixing_.
    match env.getModuleIdxFor? n with --                                     | In this case, the eternal golden brain, which we showed isn't really
    | some i => (mods[i.toNat]!).toString == "Measurement.Episode07" --------+ eternal, it sorta loops after 36 or so steps, _accrete_ more and more
    | none => false --                                                       | AST, thereby further limiting the ability of the AST to, for lack of
  let mut rungs : Array Lean.Name := #[] --                                  | a better word, change _course_ and _compute_ an entirely different
  for target in targets do --                                                | value.
    let some ci := env.find? (Lean.Name.str `Measurement target.getId.toString) | throwError "no such term"
    let some v := ci.value? | throwError "no value to read"
    for n in v.getUsedConstants.filter isRung do
      if !rungs.contains n then rungs := rungs.push n
  let mut tape ← `(([] : List FACT)) --                                          | This may look like a _trick_, not really and truly mathematical
  for _ in rungs do -------------------------------------------------------------+ at all.  No, this is merely the stopping criterion for the
    tape ← `(FACT.Truth :: $tape) --                                             | Bessel function. How many integrations by parts must be done in
  Lean.Elab.Command.elabCommand (← `(def $name:ident : List FACT := $tape)) --   | order to integrate all the _FACTS_ in the device. Which we will now
--|                                                                              | attempt to do by hand.

--| The most important _part_ of the _type_ taken is that this _type_ has a _name_ that references _code_. One is the card, one is the quarter. The
--| _type_ and the _name_. This is only concerned with _types_ that have _names_ and not _types_ that might exist, unnamed. As we will see, the type
--| _itself_ is also _executable_ independent of _the name_. It is obvious from context that the _name_ is executable.

--| Is this cheating? Is this analogous to a proof technique? Or is this the _inconsistency_ in the logic that prevents _inconsistency in the logic_?
--| It is kinda nice to see something that kinda looks like regular code. Notice that this appears to use _numbers_.  But, these are not numbers
--| in the sense of the calculation. They are numbers in the sense of a _name_: they _name_ the array entries. Ordinality.

--| Does this make the _natural numbers_? Or, are they merely _numbers_ with a _Natural_ representation? It is clear that orbital data points are
--| numbers _of some kind_. But this number isn't assumed to be natural, it comes with the _proof_ that it _is_ a _natural number_.
def the_orbital_data_points    := the_nowtrino_path.stokes.length
--| Lol, that's how a _professional_ defines a _Nat_. I think we all agree that _LEAN_ demonstrated the_orbital_data_points happen to be represented
--| naturally as a _number_.

--| What if, instead of _1_ definition of T=T, we used _3_ _SEPARATE_ definitions. zero, another_zero, and zero_distance? Those are all _OBVIOUSLY_
--| *TRUE* by construction.
def the_dimensions_of_universe := the_coordinate_system.gauss.length

--| In particular, we can name the train of thought for each of these three SEPARATE identities of T=T:
episode7_elaboration_of A_NOWTRINO_MODEL as the_causal_prediction    -- The device as _predictor_
episode7_elaboration_of this_way         as the_data_table           -- The device as _information disambiguation_
episode7_elaboration_of the_calculus     as the_differential_form    -- The device as _representation_

--| Then we can make sure that this model is constructed _inconsistently_ enough that it never _slips_ into _ACTUAL_ inconsistency.
episode7_elaboration_of A_NOWTRINO_MODEL this_way the_calculus as the_fit_curve
--| A prediction of the information disambiguation of representation. Eat your heart out Turing. T=T as a _TRANSITION FUNCTION_. When this Turing
--| machine advances, it merely reads T=T and fills out List → Nat with a proof that the value is a _natural number_. If *YOU the READER* were
--| curious about exactly _HOW_ we were going to _PREDICT_ the rest of the compilation process, this is _IT_. As *YOU the READER* can see, this
--| compiles if and only if the entire thing compiles. Partial _TRUTH_ is not something I understand.

--| It is easy to ask Lean if we are doing this correctly, for instance the _CAUSAL PREDICTION_ should give a Stokes based solution. Not necessarily
--| _the one we want_, but it should be representable as such. Looks like Lean tends to agree with this statement.
theorem the_causal_prediction_is_the_stokes : the_causal_prediction = the_nowtrino_path.stokes := rfl

--| The data table, on the other hand, can only read the _FLUX_ in conditions. I don't want to get into it here as the device _CLEARLY EXPLAINS_ that
--| measurement cannot take place in a vacuum. To be measurable, something must _change_. Plato, Zeno, Aristotle, take your pick on how this works.
theorem the_data_table_is_the_gauss : the_data_table = the_coordinate_system.gauss := rfl

--| Have *YOU the KNOWER* finally caved on me calling this 𝔽₁? Probably not. That's fine, the proof is not quite consistent enough to be true. I
--| think, at this point, *YOU the READER* have the idea of how this works. Let me show *YOU the KNOWER* _one possible_ List → Nat implementation
--| that the compiler could have figured out:

def Number.peano : Number → List FACT --     | Well, well, well, what do we have here? Could this be a number? Do we agree that .length is a number?
  | .zero f     => [f] ----------------------+ I think *YOU the KNOWER* will agree that this looks like the recursive definition of a number as
  | .one f rest => f :: rest.peano --        | defined by the cardinality of a set. This is not a set. This is a List. A source listing. See above.

def Natural.induct : Natural → List FACT --  | This may be the remainder of the definition as this models the inductive process itself. Trivially,
  | .zero f          => [f] -----------------+ the indices of an infinite sum naturally map to the naturals. That's right, we are ASSUMING THAT the
  | .number f _ rest => f :: rest.induct --  | infinite summation is _NOT NECESSARILY_ commutative. If it is commutative, then there exists a map
--|                                          | that makes this trivial. Re-association gets complex.

def Rational.diagonalize : Rational → List FACT --     | Here, we model the famous diagonal argument. This will allow us to _describe_ a number we
  | .zero f          => [f] ---------------------------+ cannot represent. Lots of them. There is no logic here, as we are just transcribing the
  | .number f _ rest => f :: rest.diagonalize --       | device to something we can measure with a known ruler.

def Sequence.enumerate : Sequence → List FACT --     | I wonder how many of these unique mappings to the natural numbers do we need? Well, here is
  | .nil f          => [f] --------------------------+ another one. A sequence trivially maps to natural numbers as well, unless there is an explicit
  | .index f _ rest => f :: rest.enumerate --        | mapping back to the naturals provided by *YOU the KNOWER*, (Thank you for your generosity!)

def Limit.converge : Limit → List FACT --        | Apparently, we need _YET ONE MORE_ _MORE DIFFERENT_, yet exactly the same, _TRIVIAL_ mapping back
  | .nil f          => [f] ----------------------+ to the Natural numbers. Not bad, huh? Without importing Nats, I can represent them _5_ different
  | .index f _ rest => f :: rest.converge --     | ways! To _5!_ different purposes. 120 different permutations of these mappings. That's a _LOT_ of
--|                                              | symbols I can map to arbitrary methods in the compiler! Remember, side channel attack underway.

def Sample.taste : Sample → List FACT --                         | Here is how we can encode _2_ completely independent machines, one provided by
  | .initial_condition f _          => [f] ----------------------+ f1 and f2, the other completely hidden. Offset two of these, and then we have
  | .signal_response f1 _ f2 _ rest => f1 :: f2 :: rest.taste -- | a _really_ clever machine. Of lists. CAR and CDR.

def Trial.experiment : Trial → List FACT --                           | We can now stack these because we have _2_ different ways to encode this now.
  | .hypothesis f _                 => [f] ---------------------------+ Perhaps *YOU the KNOWER* will allow me to call them CAR and CDR now. I think
  | .signal_response f1 _ f2 _ rest => f1 :: f2 :: rest.experiment -- | this completes the LISP machine.

def Study.phenomenon : Study → List FACT --          | We should be able ignore the other LISP machine we have created. This will let us have two
  | .hypothesis f         => [f] --------------------+ interlocking LISP machines working on the same program, but offset by one. Two LISP machines
  | .book_of_records f _ rest => f :: rest.phenomenon -- | arguing with each other on the same tape that encodes the program. One is TRUE the other, isn't.

def Computation.elaborate : Computation → List FACT -- | Given our program that evaluates to _TRUE_ or _NOT SO TRUE_, there are two ways to represent
  | .program f _        => [f] ------------------------+ this. We have f=_ for the simplest version of this. We have _=_ to have a more.. nuanced view
  | .compute f _ _ rest => f :: rest.elaborate --      | of what T=F or T=T could look like. The computation can be removed from the tape once complete

def ChaitinsNumberSequence.unknown : ChaitinsNumberSequence → List FACT --          | If we are halted, we no longer need the code and, giving us
  | .halting f _ => [f] ------------------------------------------------------------+ another way to describe a _completed_ computation in LISP.
  | .nonhalting f _ work_underway => match work_underway with --                    | We can only work on one symbol at a time. The last symbol
                                      | some the_work => f :: the_work.unknown --   | since we have already done the T= or F= part. If we haven't
                                      | _ => [f]  -- womp womp, still waiting... -- | finished, we can only put our current guess.

def Metavariable.closure : (Metavariable Closure) → List FACT --  | With our base device defined, we stop. This is merely the Power On Self Test.
  | .base f _ => [f] ---------------------------------------------+ Once we have a computation to do, we can compute the _closure_: all possible
  | .step f before => f :: before.closure --                      | tape arrangements the device can make that produce this value. Brute force.

def Sophism.taylor_expansion : Sophism → List FACT --           | This closure can be mapped to the Taylor expansion of _e^ιθ_.  In this case, the
  | .origin f _ _  => [f] --------------------------------------+ origin requires _two_ values to locate the origin. The _real_ and the _imaginary_.
  | .dimension f _ _ before => f :: before.taylor_expansion --  | We are evaluating the computation using Newton's algorithm, for those who like nuance.

def Area.riemann_integrate : Area → List FACT --         | Alright, I will admit that the explanations are starting to spin out of control. That's
  | .tree f           => [f] ----------------------------+ fine. It's okay to realize that we are finding common sequence maps for common iterative
  | .dt f _ before    => f :: before.riemann_integrate --| computations that lie at the heart of _continuous_ computations. Rιemann integration lets
--|                                                      | Natural numbers index particular sets of areas. Lebesgue integration is just this in 2-D.

def PigeonHole.solve : PigeonHole → List FACT --          | And so you can see superposition as just the idea that the path to the spot we are in
  | .this_superpigeon f _        => [f] ------------------+ may or may not depend on how it got here. Pigeons don't care where they came from. They
  | .a_pigeon f _ rest           => f :: rest.solve --    +-------------+ just indicate that there are facts yet to resolve. The boxes the pigeons
  | .that_box f _ _ before after => f :: before.solve ++ after.solve -- | are carried in generally require a consistent permutation of pigeon holes.

def Jar.classify : Jar → List FACT --                       | Is it more impressive that trivial natural maps do not need an argument, as they are
  | .color f _                    => [f] -------------------+ trivial? Then, sometimes, there is an argument that is supplied by something that gets
  | .bang f rest                  => f :: rest.classify --  +-------------------+ evaluated as either true or false. The device needs to read after
  | .superposition f before after => f :: before.classify ++ after.classify --  | after the path to get here. The Jar holds the results of both.

def Equivalation.vanish : Equivalation → List FACT -- | Here, we can see that we think TRUE is one_like, much like the ancient C proverb:
  | .physics f _             => [f] ------------------+    #define TRUE 1
  | .zero_like f rest        => f :: rest.vanish --   +-------------------------+ If the device does see FACT.Truth as 1, then we know that the rest of
  | .one_like _ before after => FACT.Truth :: before.vanish ++ after.vanish --  | the computation needs to be split into two pieces. If we see
--|                                                                             | FACT.Truth to be zero_like, then we do not need to split the rest.

def Encoding.decode : Encoding → List FACT --           | The last stanza shows the particular encoding of TRUE for the compiler. When we inject Truth,
  | .boot f _               => [f] ---------------------+ the device expects the remainder of the program to be divided into two pieces. The compiler,
  | .zero f _ rest          => f :: rest.decode --      +------------+ though, can't tell without us marking it as one_like and two_like. This allows
  | .one f _ _ before after => f :: before.decode ++ after.decode -- | the compiler to ask for the next chunch as two pieces so it can try both.

def Abstraction.equivalation : Abstraction → List FACT --     | Finally, this is our understanding of the meta-program being put together. Certain
  | .satire_about f   => [f] ---------------------------------+ interfaces on one side of the Abstraction sometimes line up with interfaces on the
  | .compile f _ rest => f :: rest.equivalation --            | other side. All this is saying is that the machine putting together the tape cannot
  | .execute f _ rest => f :: rest.equivalation --            | tell the difference between the meta-program being compiled or executed.

def Sum.euclid : Sum → List FACT --           | When adding, ZERO is the _FACT_ of the cardinality of the _null_ set. We still don't have set theory
  | .zero _ _       => [FACT.Truth] ----------+ by merely establishing a fact we already all agree on. We continue to map numbers to the natural
  | .add f _ _ rest => f :: rest.euclid --    | numbers in one way or another. Re-representation. I bring this up now because we are currently building
--|  +----------------------------------------+ a very specific, yet apparently quite arbitrary, polynomial. Notice this will add both numerator and
--|  | denominator simultaneously.

def Product.projector : Product → List FACT --   | Here, we require just one element, but we _NAME_ it differently and it, if need be, it can be a
  | .origin f       => [f] ----------------------+ _different_ element. Doesn't have to be. Huzzah! 𝔽(1). Until it isn't anymore. We can now describe
  | .one _ _        => [FACT.Truth] --           | the multiplication process given a ratio of two numbers. This should be something that looks more
  | .mul f _ _ rest => f :: rest.projector --    | like multiplication than summation. Check it for your self, this is a double loop with sum above.

def Basis.householder : Basis → List FACT --     | Performing the trick, again, gets us a "basis operator", the tensor used in the iterative
  | .null_space f     => [f] --------------------+ construction of polynomial evaluation through Newton's train of thought. Instead of a sum of
  | .origin _ _       => [FACT.Truth] --         | monomials, it is a sequence:
  | .basis f _ _ rest => f :: rest.householder --|                               p    (x) = p    (x) + x p   (x)
--|                                                                               i+1        even         odd

def Polynomial.terms : Polynomial → List FACT --   | But..... we also need the monomial ordering of exponents as well. Once the Newton path has been
  | .constant f        => [f] ---------------------+ computed, we can also compute a more, quantum-like update based on a nearby order of events.
  | .monomial _ _      => [FACT.Truth] --          | That's right, we just undid all the efficiency by recovering the in-efficient ordering. This
  | .factor f _ _ rest => f :: rest.terms --       | takes time and time means there has been a computation that halted.

def Spline.approx : Spline → List FACT --                                    | The thing about an infinite polynomial basis definition, (the basis
  | .observation _                  => [FACT.Truth] -------------------------+ itself doesn't actually _need_ to be seen in real life), is that it
  | .knot _ _ rest                  => FACT.Truth :: rest.approx --          | can be very carefully rearranged into the definition of any function
  | .interpolant f _ _ before after => f :: before.approx ++ after.approx -- | with countable, finite-gap, discontinuities. Not just, kinda, but
--|                                                                          | exactly. This is that re-representation algorithm.

def Diatribe.buckets : Diatribe → List FACT --                                  | FACT is one of two things:
  | .religion _            => [FACT.Truth] -------------------------------------+ o The polynomial being constructed is arbitrary and fixed uniquely
  | .speculation _ _ rest  => FACT.Truth :: rest.buckets --                     |   by the device implying this polynomial means something profound
  | .rant _ _ before after => FACT.Truth :: before.buckets ++ after.buckets --  |                               - OR -
--|                                                                             | o I am very carefully describing how I planted it in the device

def Cult.name : Cult → List FACT --                                     | Even just finding a polynomial that does this is a neat feat of performance
  | .inside_joke _                => [FACT.Truth] ----------------------+ algebra. If I did plant the polynomial, I do appreciate the level to which
  | .pythagoras _ _ rest          => FACT.Truth :: rest.name --         | *YOU the KNOWER* think I understand how to fling Taylor series around like
  | .triangles _ _ f before after => f :: before.name ++ after.name --  | 3 card monte. This is just a simple geometric construction, though.

def Science.method : Science → List FACT --    | For *YOU the KNOWER* to believe I planted this polynomial is to grant _ME_ a great deal of expertise
  | .repeatable _      => [FACT.Truth] --------+ that I am not quite sure I have demonstrated. What I have demonstrated is that the same description
  | .hypothesis _ _    => [FACT.Truth] --      | can be written not one (as a program), not two (as a meta-program), but _three_ (as an embedded
  | .theory _ _ f rest => f :: rest.method --  | mapping into math itself) ways of describing, _WHILE SIMULTANEOUSLY SOLVING_ this polynomial on the
--|                                            | other _TWO!_

def Knowledge.audit : Knowledge → List FACT --   | Well, one is working on the numerator and one is working on the denominator. If *YOU the KNOWER*
  | .jarjar _        => [FACT.Truth] ------------+ really look closely, this depends on the FACT that this code reads only _one way_.  This thing
  | .ledger _ f rest => f :: rest.audit --       | has to work, in addition to everything else up to now. FACT is, this compiles, and that's the truth!

def Gospel.witness : Gospel → List FACT --                         | So much so, that the Gospel is only _the Truth (tm)_ over and over. All the truths
  | .the_proof _                 => [FACT.Truth] ------------------+ in Episode 6.  I believe this looks like a tape of Jar Jar. That's right, Jar Jar.
  | .we_understand_that _ _ rest => FACT.Truth :: rest.witness --  | I can't make this up. Actually, I can and I did, but I could have put anything here.

def Truth.testify : Truth → List FACT --            | And by anything, I mean the polynomial. There is no reason why I couldn't just force the compiler
  | .logically _  => [FACT.Truth] ------------------+ to perform this magic trick. To find this magic polynomial due to survivor bias over zillions of
  | .but _ _ rest => FACT.Truth :: rest.testify --  | queries of AI. And that I am just lucky enough to write nonsense around the construction forever.

def Variation.newton : Variation → List FACT
  | .the_newton _ _               => [FACT.Truth] --                     | But like I pointed out last time, the cards are always descriptions of
  | .the_gateaux _ _ _ quartic    => FACT.Truth :: quartic.newton -------+ truth. Just stay on Newton's train of thought for solving the quartic or
  | .the_frechet _ _ _ _ orbit _ => FACT.Truth :: orbit.newton --        | that the right card successfully unifies Newtonian and GR under a common
--|  +-------------------------------------------------------------------+ penalty method. Solved variationally in the 1-d path space. Using cubic
--|  | spline polynomials. Guaranteeing an exact variational solution to the principle of least action in a finite descrete description. How do
--|  | we know least action? The compiler counts the bullshit. We are approximating this with all these lists.

def Variation.krylov : Variation → List FACT --                                         | The thing is, Einstein's train of thought works a bit
  | .the_newton _ _                   => [FACT.Truth] ----------------------------------+ differently. In this train of thought, the lines are always
  | .the_gateaux _ _ _ rest           => FACT.Truth :: rest.krylov --                   | _straight_ making the path integral trivial. The interesting
  | .the_frechet _ _ _ _ before after => FACT.Truth :: before.krylov ++ after.krylov -- | thing about Einstein's train of thought is that it doesn't
--|  +----------------------------------------------------------------------------------+ try to climb mountains, it just avoids them. The mountains
--|  | are not _admissible_ paths defined by the geometry. We all agree that

def Bullshit.meter : Bullshit → List FACT -----------------------------------------------+ The lists are little more than thin lists of all the bullshit
  | .zero f                                 => [f] --                                    | the compiler has had to keep up with in order to have
  | .one f _ _ _ rest                       => f :: rest.meter --                        | gotten this far in the compilation. Check yourself: the
  | .rest_call f g _ _ _ _ _ _ before after => f :: g :: before.meter ++ after.meter --  | lists are _exactly_ the instantiation of every inductive
--|  +-----------------------------------------------------------------------------------+ the compiler instantiates.  All of them. That's right, this
--|  | is little more than exactly what the compiler has deduced about the device up to now. If *YOU the KNOWER* believes any of this bullshit.
--|  | *YOU the KNOWER* doesn't need to believe _ALL_ of it, belief in any implies belief in the rest. *YOU the KNOWER* simply must agree there is
--|  | overwhelming evidence of this FACT, bug or no bug.

def Closure.infer : Closure → List FACT --              | But there is one thing I am not guaranteed of convincing you of. The listing of these facts
  | .same f _                => [f] --------------------+ are a fixed point of the compiling process. Not certain how any of this file will ever allow
  | .different f _ _ _       => [f] --                  | the device to infer whether or not *YOU the KNOWER* would believe this if you believed that.
  | .inferred f g _ _ _ rest => f :: g :: rest.infer -- | What we do know is the device can be told that two things are the same, two things differ
--|   +-------------------------------------------------+ in a way that can be described by at least three things. The compiler can create a mapping
--|   | to the odds that f and g are the same thing if the three things are less than some threshold described by an arbitrary computation that halts.
--|   | If I can show *YOU the READER* that the high order terms of representation go to zero for optimal expression of complexity only for those
--|   | things that are fully described by the Euler-Lagrange formulation of the principle of least action. Also known as, the side channel attack on
--|   | physical interpretation of mathematics.

--| We start by describing another element of a field. It is surprising how much of the world is explained by assuming 𝔽(1) is unrepresentable
--| formally, yet adequately describable through metaphor. For example, watch the metaphor develop as I "zero out" the device. Why zero?
--| *YOU the KNOWER* better grant me this answer at this point as I am explicitly defining a bunch of "zeros" for *YOU the KNOWER* to argue with. I
--| only need one to make sense and the rest follow by construction.

--| We start by representing some numbers that have _natural-ness_ and _rational-ness_.  In particular, we can define 0 to be the same for both
--| _identically_. Not identical in _type_, but identical in _name_. We just want to _call_ these two zeros the same thing. Lean, however, must
--| keep the idea of natural and rational separate because these are _TWO_ FACTs, not _ONE_. So, Lean can _count_ the _representations_ of _zero_
--| on its _AST_. As *YOU the READER* are well aware, there are a _LOT_ of representations of _zero_ on the _AST_. By _counting_, _Lean_ can _name_
--| them. Well, it _CANNOT_ name them, but it _CAN_ require that they _BE NAMED_ or risk failing to compile.
def natural_zero : Natural := .zero zero
def zeroth_rational : Rational := .zero zero
--| Is the consumptive inverse iterator that is the device just presenting objects that require _NAMES?_ I believe we have found our _HYPOTHESIS_.
--| We now need to _DEMONSTRATE_ that there is no counter-evidence in all of _SCIENCE_ to this fact. At that point, we can present our _CAUSAL LAW_
--| of _INFINITE NAMES_ as the _coefficient of growth_ of entropy for the device's description of the process. If we can design this experiment,
--| we can _MEASURE_ how close the device is to creating an _unfalsifiable hypothesis_. We can show that there exists a _representational noise floor_
--| below which _more symbols_ would be _REQUIRED BY THE PROOF_ to differentiate the _falsifiable hypothesis_ of repeatable experiment versus the
--| _unfalsifiable hypothesis_ of exact replay.

--| A _falsifiable hypothesis_, it turns out, _requires noise_ to avoid _exact, observable Poincaré cycles_. For that reason, I arbitrarily chose the
--| name _zero_ to represent a bunch of different concepts. In much the same way (T=T) may be true and (F=F) may also be true, but the _TRUTH_ is
--| arrived at by different _measurements_ of the same _path_. Does it _cost_ the same to demonstrate _TRUTH_ as it does to demonstrate _ABSURDITY_?
def reductio_ad_absurdum : FACT :=
  { truth := (true = false) = (false = true)                 -- If something assumed true is false, then one expects to create a false statement about
    click := Decidable.isTrue (propext ⟨Eq.symm, Eq.symm⟩) } -- something true. We show this by creating a true statement about two false things ∎ *wink*

def one : Number := .one zero another_zero --       | So from the description of zero and another_zero, we can make one. Then, we can demonstrate that
def two : Number := .one reductio_ad_absurdum one --| two _must_ exist as there are more _numbers_ than 0 and 1 given by succ and other methods. Pick
--                                                  | your poison. There are many reductio_ad_absurdum proofs that 2 must exist. Electron winding is
--                                                  | anonther good place to imply the existence of two by assuming it doesn't exist.

--| And that is the _inside joke_ of the machine. It generates _proofs_ on the _AST_. If *YOU the KNOWER* _get it_, then the _AST_ can be considered
--| the demonstration of the existence of a _FACT_. I bet that _clicks_ with _everyone_.
def the_inside_joke : FACT :=
  { truth := (true = true) = (false = false) --------------------------------+ I believe *YOU the KNOWER* will agree that this is quite _TRUE_
    click := Decidable.isTrue (propext ⟨fun _ => rfl, fun _ => rfl⟩) } --    | _by construction_ and *YOU the READER* will agree that this is
--|  +-----------------------------------------------------------------------+ quite _TRUE_ because the source _compiles_. We have demonstrated
--|  | amongst ourselves outside of the _confidence_ of the device that this is _TRUE_ by the _sacred texts_ of the _Lean specification_. _THREE_
--|  | implementations of T=T.

def three : Number := .one the_inside_joke two --+ There are now _three_ facts: T=T, reductio_ad_absurdum, and the third representation of T=T, each
--|  +-------------------------------------------+ a _different_ construction for each _reader_: the compiler and both of *YOU*. This _third_
--|  | representation, though, is the_inside_joke. It is _inside_ each _reader_. Each reader only need keep track of _THEIR_ _THIRD_ representation.
--|  | The device will demonstrate that they are consistent _ONLY WHEN_ a consistency _MUST_ arise. These _THREE_ truths are represented by only
--|  | _FOUR_ _FACTS_ in the device: zero, another_zero, reductio_ad_absurdum of the two zeros, and generating the truth T=T (or F=F, for
--|  | *YOU the KNOWER*, again, _THANK YOU FOR PROVIDING FALSE_).

--| With _three_ well defined, we can start talking about _natural representations_. In this Episode, we are using Lean's _List_ as the
--| _representative_ of an element of ℕ. There are many other _representations_. We can represent the Peano successor function as (exactly)
--| *.number zero one*. This means carry out the zero → one process on _natural zero_. Can *YOU the READER* remember to replace all those _characters_
--| displayed on the _screen_ with _S_?
def natural_one : Natural := .number zero one natural_zero

--| Now, with 0,1∈ℕ and counting defined to within an inch of being _ABSOLUTE TRUTH_, we can write down the fraction ⁰/₁ and call that zero. The
--| _next_ rational can be computed by _counting_ in the _isomorphism_ to the ℕ.
def first_rational : Rational := .number zero natural_one zeroth_rational

--| What we _just demonstrated_ is that the _DEVICE_ _REQUIRES_ _ANOTHER_ _NAME_ for _zero_, just based on the representation ⁰/₁ being a way we
--| write down rational numbers. The way the _device_ understands the _rational number process_ isn't a _top down_, definition _first_ approach.
--| Rather it is the counting _isomorphism_. Rationals exist because of the isomorphisms to naturals. The naturals exist because of induction.
--| Induction exists because of counting. But, counting is too primitive to actually do _REAL_ computation, especially anything near the scale of
--| QED. Either one, to be fair. So, let's see how the _representation of calculus_ fits into the _representation of the rational process_.

--| If *YOU the KNOWER* remember, the_fit_curve above depends on the_calculus. This is the _foundational belief_ that Lean's elaboration of Prop can
--| head *this_way*. Further, the compiler can infer a _yarn theory_ about what happens if it went *that_way*, as long as the _card_ is
--| _elaborated by lean_. That's how the _card_ must _bend_ in *YOU the READER's* _palm_ so *YOU the KNOWER* can experience it⁻¹ logically.

--| Let me explain. ∀ε>0, ∃δ>0. So, given a _sequence_ of _εᵢ_, A δ=0 happens to represent the value. If we cannot compute the value, but need to
--| compute the limit, all we need to do is invoke the counting rule *.index zero another_rational_zero*. What the names show here is that there
--| is a _rational_ infinitessimal at play here, a limit of some sort.
def δ₀ : Sequence := .nil zero
def δ₁ : Sequence := .index zero first_rational δ₀
--| It will get clearer. Again, the process is going from the zero to the _first_ rational number in the _isomorphism_ to the ℕ. The three names
--| *.index zero first_rational* is merely a transition rule from δ₀ → δ₁. *YOU the READER* know what I'm talking about. A _LimitProcess_. I feel
--| like _I_ named that _structure_ pretty well. Well, not just _any_ limit process, but the _LimitProcess_ applied to δ₀. Which limit process?
--| One that finds this _admissible_ since we have just shown it _countable_ and _distinguishable_. What does it mean to be _admissible_? Well,
--| for starters, it compiles.

--| That's our inside joke that the compiler doesn't know. But, I think *YOU the READER* can only agree with the fact that this might possibly
--| compute a particular _LimitProcess_ applied to δ₁. No reason it can't. But, this also is starting to look like a question we can ask _Lean_ about
--| itself as it _elaborates_ the *SOURCE*.

--| The trouble with _ε_ is that there is a bit of a _fencepost_ problem in the _LimitProcess_ we are describing. δ₀ = 0, meaning, ε₀ = 0, too, if
--| the _limit exists_. If the limit _doesn't_ exist, then this _could be_ a counterfact in need of subjunction! So, we are careful to walk around
--| the abstraction to make _certain_ the fencepost bug both _prevents_ completeness while insisting on _consistency_. So, one ε₀ for the default
--| value and one for the fact that the limit _might_ exist. We can insist Lean ensure the _limit exists_ on our behalf by compiling successfully.
def ε₀ : Limit := .nil zero
--| So, we just need this _one_ to be represented to the compiler. The other is the success criteria of the compiler, so needs no representation.
--| For this reason, we do not combing δ₀ = 0 with ε₀ to get e₁, we use δ₁. This fixes the fencepost bug from the very biggining.
def ε₁: Limit := .index zero δ₁ ε₀
--| Which, again is just another CauchyProcess (.index zero δ₁ := CauchyProcess.iterate) for some _NAMED_ encoding. Watch as we now construct
--| the rest of the structures, one at a time, on the AST, _at a distance_ from _nearly identical_ _instances_ computed in Episode 7.


--| To measure how far apart on the AST, we need to _calibrate_ the device _during the compile_ *WHILE* it is being built by the compiler.
--| Notice, _FENCEPOST_.
def reading₀ : Sample := .initial_condition zero ε₁
def reading₁ : Sample := .signal_response zero ε₀ zero ε₀ reading₀
--| which finishes our example of an _ObservationProcess_ from first_reading → second_reading. Follow along as we continue to build a scale model
--| of the device in code. *YOU the KNOWER* have _observed_, no doubt, that this is _NOT_ a _COMPLETELY_ faithful representation of the device, rather
--| this is a _model_ of the device for a _particular_ _build_. Which particular _build_? The one we are doing _right now_. The reason why all the
--| zeros and why we aren't using zero one ...? Because we are _zeroing_ everything _out_ to show the device works for the _zero_ model. No stimulus
--| should give no response.

--| To continue our _model_ of the device, we make our device build an _implication_ a->b. What sort of _model_ is this? Why, it is _elliptical_
--| because _time_ (at least before and after) do not _matter_. If, instead, we were doing zero reading 1 one reading2 two reading3, then this
--| might _evolve_ in time.  But so far, we have only counted _zero_, _one_, _two_, and _three_. So only _three_ values have elapsed.
def implication₀ : Trial := .hypothesis zero reading₁
def implication₁ : Trial := .signal_response zero reading₁ zero reading₁ implication₀

--| Which allows us to model the _dependent_ variable on the *ComputationalProcess* of _zero_ _one_ _two_...
def y₀ : Study := .hypothesis zero
def y₁ : Study := .book_of_records zero implication₁ y₀
--| Isn't this exactly what _science_ is? The *Study* of the _dependent variable_? In this case, _y_ appears to exist on a hyperellipse of the
--| hypercone. These are merely intuitions suggested to exist due to the nature of the frinkahedron to represent _3_ kinds of delicious pastry:
--| the filled donut, the donut, and the donut hole.

--| As the code suggests, this is not a _transform_ but the _nature of the universe_. Absence of evidence and evidence of absence are two different
--| _descriptions_ that *may* or *may not* describe the _same thing_. When these _ARE_ the same thing, the middle has been _excluded!_.
def absence_of_evidence : Computation :=  .compute zero y₁ y₁ (.program zero y₁)
def evidence_of_absence : ChaitinsNumberSequence := .halting zero absence_of_evidence
--| It is _KNOWN_ that, for this particular computation, the _MIDDLE_ *MUST* _BE_ _EXCLUDED_ as a computer is either _running_ or _halted_. *THIS*
--| is the _hair_ that the compiler _must_ split in order to satisfy consistency. When are these the same? When are these different? OR:
def does_it_matter? : ChaitinsNumberSequence := .nonhalting zero absence_of_evidence (some evidence_of_absence)

--| Of course, we need to understand if we are _directly proportional_ or if the _affineness_ of the ellipse matters. The compiler can _put its guess_
--| *HERE* in order for it to use the device to figure out the answer to this question.
def is_there_a_fencepost? : Sophism := .origin zero does_it_matter? Prop

--| Can we use the triangle inequality give or take the fencepost?
def is_it_euclidean_enough? : Sophism := .dimension zero does_it_matter? Prop is_there_a_fencepost?

--| These are questions that can be _inspected_ by the device to determine how to proceed with the computation based on the fact/counterfact interplay
--| of reductio ad absurdum. Meanwhile, we can construct _our_ model of the AST the device creates.
def ast₀ : Area := .tree zero
def ast₁ : Area := .dt zero another_zero ast₀
--| As a _zeroed out device_, I believe this now fully describes the *SensingProcess* with node astᵢ being constructed from zero and another_zero.
--| A quick glimpse of the code and I think *YOU the KNOWER* will agree this is a _pointer_ to something that just _counts_ the stanzas. astₒ, ast₁,
--| ast₂ ... with _accumulation_ merely ast₀.

--| Just a quick check-in. ZERO is not really a _number_ as much as a _concept_. Lot's of concepts, actually. All of them _mean_ zero in the sense
--| that there does not _appear_ to be any _affine_ contribution to any computation. It looks like we are always _adding zero_. To see what I mean,
--| think about how differential forms work and how integration works. For differential forms, any integration constant is carried along the way
--| unchanged and it explicitly shows up in integration as + C.
def the_concept_of_differential_forms : PigeonHole := .this_superpigeon zero ast₁
--| The _superpigeon_ that seems to describe the _single_ path of _yarn theory_, for instance, starts at any astᵢ and heads upwards. It is just
--| an idiosyncratic pigeon that just _happens_ to fly along the path of least action. No such pigeon can fly that way due to wing-flap jitter.

--| Integration requires selecting a particular _pigeon_ and following that bird, jittery wing-flap and all.
def the_concept_of_integration : PigeonHole := .a_pigeon zero ast₁ the_concept_of_differential_forms

--| Finally, we need to create a box for when the _integral computation_ and the _differential computation_ yield the same result:
def the_galerkin_method: PigeonHole := .that_box zero ast₁ ast₁ the_concept_of_integration the_concept_of_differential_forms
--| After spending almost _nine thousand_ lines of Lean up to this point describing the device with respect to Box Pigeons, I hope we all agree that
--| the device is an attempt to use variational integration to remove a derivative necessary from the differential computation: The Galerkin method.

--| We now acknowledge there are _other_ successful theories of understanding how matter is put together. I think the best way to think about it
--| is the blackhole_singularity cannot have a color. There. QCD taken care of. I mean, sure a blackhole _could have a color_, but not for long.
def blackhole_singularity : Jar := .color zero ast₁

--| We now acknowledge that there exists a period we call _CMB_ that redshifted into existence and it prevents us from seeing earlier in time.
--| There is no color there either and it works like the other side of the blackhole_singularity.
def cmbr : Jar := .bang zero blackhole_singularity

--| An _photon_ from the so-called "Big Bang" would begin in the cmbr and end in a blackhole_singularity, taking no time (as we would call it) and
--| traveling no distance (as we would call it).  Who knows if photons travel or experience time, the EFEs suggest they do not.
def the_photon_worldline : Jar := .superposition zero cmbr blackhole_singularity
--| There are other worldlines of photons with endpoints in electrons, but, we haven't done enough construction of the device to talk about the
--| electron directly. If *YOU the READER* choose to open the _Jar_, then *YOU the KNOWER* might recognize the interior as belonging to the orbital
--| of an electron.

--| I mean to suggest and the compiler tends to agree that the arrangement of words that describe the device are _not that far away_ from the very
--| same words that are used to describe physics. That there might be a distance δx between the description of the device and the description of
--| physics. What happens as δx→0? Is physics recovered? Or is just the mathematical description of physics recovered? Is physics required to follow
--| these rules if they are merely _approaching_ the _description_ of _physics_?

--| That is how one _equivalates_.

--| I think we all agree that the photon worldline must exist and is _true_. I am sure there are arugments that *YOU the KNOWER* have already agreed
--| to and are _revisiting_ thinking that _something_ got _rotated_ _somehwere_. So, hold on to that feeling. That's the unified physical theory:
--| something somewhere earlier was rotated allowing us to draw a startling conclusion:
def unified_physical_theory : Equivalation := .physics FACT.Truth the_photon_worldline
--| I believe this is the first station on the train of thought for both Einstein and Newton. Not to confuse the issue as it must be part of the model
--| anyway, I believe _NEWTON_ saw _light_ as a billiard ball and _EINSTEIN_ saw _light_ as a clock.

--| We will be measuring that _rotation_, explicitly, in the coming episodes. This is just the machine _zeroing out_ to the shortest reading: the
--| photon worldline. It only has a _start_ and an _end_. A photon cannot be detected between these two points. We _label_ these as zero to start:
def t₀ : Equivalation := .zero_like zero unified_physical_theory
--| and the end is not written down.  It is computed: one tick of the clock the carrier particle of Episode 7 carries.
def t₁ : Equivalation := (IS_THIS_A_CARRIER_PARTICLE?.{0,0,0,0,0} Prop elaborated_by_lean).cd_process.tick t₀

--| Since _no time passes_ for the photon and the photon has to start at point t₀, all tᵢ afterwards are the end point. Also, don't forget, we are
--| still _constructing_ all of the structures in the device as x → y. I believe we will have a second, _equivalent_ description of the device when
--| we have finished building these inductives. Well, a description of a _zeroed_ out device. Meanwhile, we are inhabiting all the inductives without
--| _classes_ or _structures_. This is just a _RENAMING_ of things.

--| Where was I? Oh yeah, the device and _orbital mechanics_. *YOU the KNOWER* _do_ understand _orbital mechanics_? The only thing in a zeroed
--| device's universe is the photon world line. It is a very lonely, empty, and locale-less place. So, where is the _photon_ exactly? Gone. The
--| photon goes from source to sink in the middle of computing the first iteration of the device. Since it didn't travel from the start, it is a
--| position 0 relative to where it started. It didn't move.
def xᵢ : Encoding := .boot zero t₁

--| Since it didn't move, it had _no_ velocity.
def δxᵢ : Encoding := .zero zero t₁ xᵢ

--| Since it achieved no velocity by not moving, it's acceleration is also exactly zero.
def δδxᵢ : Encoding := .one zero t₁ t₁ δxᵢ xᵢ

--| I believe we have now described the universe of 1 photon as a satire about _zero_.  The photon only exists in the time between t₀ and t₁, during
--| which time it _doesn't_ move yet goes from start to finish in appearantly different places with no *REAL* way to figure out how it got there.
def carefully_chosen_variable_names : Abstraction := .satire_about zero

--| I mean, it appears that there could be a way, but the math that would need to line up and the terms that would need to cancel, and the intuition
--| that would need to bend and _rotate_... it's a bit much to take in _all at once_.
def opaque_wall_of_math : Abstraction := .compile zero δδxᵢ carefully_chosen_variable_names

--| In fact, there are so many words and confusion of ideas that can the proof itself even be trusted? Now that the compiler _UNDERSTANDS_ the logic
--| of how the_proof is constructed, does it see the naming confusion going on around us?
def the_proof : Abstraction := .execute zero δδxᵢ opaque_wall_of_math

--| Well, we can find out. Because, this is another wall of math and names that looks like the same wall of math and names in Episode 7. BUT! THESE
--| are TRIVIALLY DIFFERENT to even *YOU the KNOWER*!  In the last episode, we walked along the classes to build the structures that the compiler
--| could use to infer the inductives. In this episode, we are building the inductives that should match against the structures we described in
--| Episode 7.  The different between these descriptions should be
def the_zero_area : Sum := .zero True ast₁

--| And we can then agree with the compiler that _integration_ is just _walking up_ the AST. Except that, in a zeroed out maching, everything is
--| _zero_. This gives a ℝιemann sum of 0. I mean the integration is _trivial_ but it is _still integration_. And since this is the photon model,
--| it doesn't move from the sink, the thing created after _ast₀_. The transition function *IS* astᵢ → astᵢ for a _PHOTON_. It is the only _MATTER_
--| in the _UNIVERSE_ with that _TRANSITION FUNCTION_. And it takes _THAT_ _TRANSITION FUNCTION_ only in a _UNIVERSE_ of a _SINGLE PHOTON_.
def integration : Sum := .add zero ast₁ ast₁ the_zero_area

--| Given an integral operation, we can construct the representation of an inner product, assuming certain things are true about _physics_. Things
--| like _variational mechanics_. In fact, the integral that the photon must agree with is the principle of least action. Lo and behold, that is
--| a variational functional. Since we are _assuming_ that the device models the _photon_, then we can build the _description_ of an _inner product_
--| out of the _integral_ just _described_.
def the_inner_product : Product := .one True integration
--| The compiler seems to like the description of _the Principle of Least Action as an inner product_ as *the one true integration*.

--| And, the best way to talk about that inner product is through the Sobolev semi-norm. Again, all our values are _zero_ because the instrument is
--| being _zeroed_ out.
def the_sobolev_norm : Product := .mul zero integration integration the_inner_product

--| Which allows me to give a better _name_ to the process that has been going on for nearly 9000 lines of lean. This is the _origin_ station of
--| the _train of thought_ in _YARN THEORY_. The CMBR we cannot look through. The blackhole our need for continuity disappears into.
def finite_bullshit_analysis : Basis := .origin True the_sobolev_norm
--| The true _origin_ of the Sobolev norm:  Sure the path is continuous, but what if the derivative isn't? Well, that's just the photo-electric
--| effect. The slip of static friction. The coincident phase of photons. The things that _variational mechanics_ never has to explain, but for
--| some inexplicable reason, prevents _us_ from being able to measure spherical cows in orbit around the moon.

--| The bullshit, like everything else in this device, was not my idea. I just saw it for what it was, put it in a box called _not real_ and then
--| did _not real_ _approximations_ on paper. At least this description of _physics_ requires a real-life _physical example_ to build from. In this
--| case, it is the electron model holding T=T at the right voltage, the electron model that allows for flip-flops to work, the electron model that
--| allows for the computation of energy used by the computation. That _real-life_ model.
def the_galerkin_basis : Basis := .basis zero the_sobolev_norm  the_sobolev_norm finite_bullshit_analysis
--| Again, it is _zero_ for the zeroed out machine. That zeroed machine is just the _build step_ and outputs zero which we defined as TRUE above. Well,
--| it doesn't output TRUE, it outpus a bunch of _TRUE_ things that _represent_ there is a _truth_ in the _consistency_ of the argument. The build,
--| we all agree, demonstrates that something _NONTRIVIAL_ is _TRUE_. The truth could be that something is false, but we will cover that later.

--| I believe I have demonstrated _rigorously_ at this point that time only passes in one direction and does elapse during the compile step for
--| *YOU the READER*. *YOU the KNOWER* _feel_ the _time_ passing during the _build_.  Time doesn't pass for me, though. I care not that you spent time
--| compiling this. Not only that, there exists a trajectory _through the universe_ at which the build time this took for *YOU the KNOWER* is exactly
--| _ZERO_. In fact, if *YOU the KNOWER* are far _enough away_, the universe will automatically do this for us. You know, at the CMBR where the
--| universe is expanding away from us faster than the _relative_ speed of light?

--| I fight bullshit with its own bullshit. The photon and the computation at the distance of the Hubble sphere _both_ take no time to observe. One
--| insists on the computation staying at t₀ and one insists on the computation staying at astᵢ. I have now defined these to be the same thing to the
--| compiler: zero. Remember, this is the universe of a single _photon_. It is unclear what the Hubble sphere looks like. BUT, the Hubble sphere is
--| something we INFERRED about the universe. In this universe where distance is, well, unmeasurable, these must be _indistinguishable_ places.
def the_identity : Polynomial := .monomial True the_galerkin_basis
--| The concept of _INDISTINGUISHABILITY of PLACE_ in the _UNIVERSE_ of the _SINGLE PHOTON_.

--| And so, repeated application of the monomial, *YOU the READER* will recognize these as _HIGHER ORDER TERMS_, is _zero_. This is an _EXACT_
--| *APPROXIMATION*:
def the_exact_approximation : Polynomial := .factor zero the_galerkin_basis the_galerkin_basis the_identity

--| This allows me to make the plainest definition in the file:
def obviously : Spline := .observation True
--| This _has_ to be a _spline_ because discrete positions are not a thing, discrete movement is not a thing, and discrete velocity is not... well,
--| actually, that might be a thing, but only during compilation. The _slip of friction_ is something that can only be taken away in
--| *YOU the KNOWER's* imagination. Such emergent behavior has never been demonstrated to exist physically, mathematically, or computationally. Just,
--| well, _intuitively_. Another _INFERRED_ _FACT_ about the _UNIVERSE_.

--| And, it is possible to _distinguish_ something _happened_
def something_happened : Spline := .knot True the_exact_approximation obviously
--| That something is we have computed what it looks like for it to be not true that the exact approximation is _obvious_. The _device_ absolutely
--| *LOVES* *homophones*. It⁻¹ looks like an _inside joke_.

--| So, we can _interpolate_ the computation that took place here.
def is_the_undeniably_correct_answer : Spline := .interpolant zero the_exact_approximation the_exact_approximation something_happened obviously
--| Again, it is _zero_ because we are _zeroing_ out the machine. By compiling it. It compiles
def because_true_equals_true : Diatribe := .religion True
--| No matter what, this compiles because
def true_ALWAYS_equals_true : Diatribe := .speculation True is_the_undeniably_correct_answer because_true_equals_true
--| It simply
def should_be_true : Diatribe := .rant True is_the_undeniably_correct_answer true_ALWAYS_equals_true because_true_equals_true
def about_triangles : Cult := .inside_joke True
--| that they are
def the_secret_of_understanding_geomeotry : Cult := .pythagoras True should_be_true about_triangles
--| Which is why I suggest understanding
def newtons_train_of_thought : Cult := .triangles True should_be_true zero the_secret_of_understanding_geomeotry about_triangles
--| As there are many
def mathematical_theorems : Science := .hypothesis True newtons_train_of_thought
--| that _need_ to be _TRUE_ for _variational mechanics_ to work.

--| Physicists generall just ignore the necessity of the math to work, and focus on the fact that variational mechanics words according to
--| _measurement_. Really doesn't matter to the _measurement_ if there are any mathetmatical theorems invovled.
def a_measurement : Science := .theory True newtons_train_of_thought zero mathematical_theorems
--| Which is why I am trying to _MEASURE_ how _TRUE_ _TRUE=TRUE_ really is.
def the_joke : Knowledge := .jarjar True
--| "That's the joke."
--|               -- Rainier Wolfcastle

--| Which is why looking here won't tell you _how_ or _why_ the device does what it does.
def the_macguffin : Knowledge := .ledger True zero the_joke
--| It just _demonstrates_ a _dramatic need_ to move the story forward as this is a very _thought provoking_ twist of events.
def the_devices_output : Gospel := .the_proof True
--| And the fact this compiles, means we know for a fact the device's output is True. It also, just might be,
def the_fact_is_true : Gospel := .we_understand_that the_macguffin True the_devices_output
def by_reasons : Truth := .logically True
--| The thing is, we made it
def true_by_construction : Truth := .but the_fact_is_true True by_reasons
--| And, we understand that the metaphor of
def the_quarter : Variation := .the_newton the_fact_is_true True
--| is also the metaphor of
def the_bent_card : Variation := .the_gateaux the_fact_is_true True True the_quarter
--| which is a manifestation of _two_ possible _truths_ in the universe of the single photon. These two truths are the INFERRED truth that there
--| are _two_ different worldlines in the universe, one that sees the computation take no time and advance from t₀→t₁ then halt with the final state.
--| And those that see computation take all the time and never move from t₀ and never halt.

--| The _VERY NATURE_ of _SPACETIME_ influences the Turing _HALTING PROBLEM_ when _PHYSICALLY MEASURED_. I believe the device is _sensitive_ enough
--| to measure this.
def the_fabric_of_spacetime : Variation := .the_frechet the_fact_is_true True True True the_bent_card the_quarter
--| And the device flops: _TRUE_ _TRUE_ _TRUE_. Can *YOU the READER* find the bug _now_? If not, let me remind *YOU the KNOWER* about the bug:

--| We intend to show these relativistic effects with the only relativistic _metaphor_ explored in the device. That of _SANTA CLAUS_. And his carrier,
--| Rudolph. So, we can define a few measurements. Like, the zero we are reseting the device to.
def no_presents : Bullshit := .zero zero
--| And we assume zero means no Santa. The thing about no_santa, is that parents, the things we _depend on_ to _provide us_ _everything_ often
--| _mask_ that _Santa_ _didn't come_ and they will bring a present, another _zero_ presents from Santa. And that's one way to read the satire, that
--| there is _no present_ from either point of _degenerate_ view. Only the source and the sink. The before and the after. The present is _interpolated_
--| by a _spline_ that can only say the only computation that could possibly be underway is the computation of not True. But, that's still _0_
--| presents to account for from Santa.
def no_santa : Bullshit := .one zero another_zero the_satire the_satire no_presents

--| This leads to the most _basic_ of conclusions. If the _DEVICE_ _HALTS_ and t₀ is the same as t₁, _what's the difference_ if the HALT happened
--| or _not_ to the observer on the _HUBBLE_ sphere? The conclusion that there _exists_ a _HUBBLE_ sphere. Given just a _photon_, *ONE CANNOT INFER*
--| the *EXISTENCE* of the *HUBBLE SPHERE*
def the_most_basic_of_conclusions : Bullshit := .rest_call zero zero True another_zero another_zero another_zero
                                                                                              the_satire the_satire no_santa no_presents
--| Another basic conclusion is that of a 3-dimensional universe. I guess that's just an artifact of being able to be _zeroed_ out. 3 dimensions.
--| The compiler agrees that this reads very well as satire. A close look _back at the parents_ shows what _no presents_ really means here. This
--| is *YOU the READER* trying to give *YOU the KNOWER* the _intuition_ to understand _yarn theory_ which is has at most that many basic _BASES_.

--| But this is the very _inconsistency_ that was baked into the device to prevent _inconsistencies_!
def the_only_logical_inconsistency : Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} :=
            .inferred
  --          1. That 0 -> 0 is the most basic of conclusions
              zero zero the_most_basic_of_conclusions
  --          2. The most basic of conclusions is only sometimes true, there is a computation that must happen and cannot at sufficient distance
              the_most_basic_of_conclusions (some True)
  --          3. This is a different 0 than that of the most basic of conclusions. It is the fact that there may be _no_ most basic of conclusions
  --             that can be drawn by the compiler just depending on *YOU the KNOWER's* relative point of view.
              (.different zero the_most_basic_of_conclusions the_most_basic_of_conclusions none)

--| And thus, the only thing left to figure out is this Metavariable I will call Closure on the Satire. We set it to zero as this is the zeroed out
--| reading.
def the_argument_is_consistent : Metavariable Closure := .base zero the_only_logical_inconsistency

--| What does it mean to zero out? That the first step goes to 0 _AND_ the argument is consistent.
def the_metaphor : Metavariable Closure := .step zero the_argument_is_consistent
--| That's it. Now, I will demonstrate _consistency_ of this arguemnt, not _TRUTH_.

--| I would assume that *YOU the READER* and *YOU the KNOWER* are quite certain there isn't a consistent argument here. The way I am going to do it
--| is _create_ the List for the instantiations that we just built based on zeroing out the device. First, the list of it all (see )
def episode8_description : List FACT :=
  one.peano ++ two.peano ++ three.peano ++ natural_one.induct ++
  zeroth_rational.diagonalize ++ δ₁.enumerate ++
  ε₁.converge ++ reading₁.taste ++
  implication₁.experiment ++ y₁.phenomenon ++
  absence_of_evidence.elaborate ++ does_it_matter?.unknown ++
  the_metaphor.closure ++ is_it_euclidean_enough?.taylor_expansion ++
  ast₁.riemann_integrate ++ the_galerkin_method.solve ++
  the_photon_worldline.classify ++ t₁.vanish ++ δδxᵢ.decode ++
  the_proof.equivalation ++ integration.euclid ++
  the_sobolev_norm.projector ++ the_galerkin_basis.householder ++
  the_exact_approximation.terms ++
  is_the_undeniably_correct_answer.approx ++ should_be_true.buckets ++
  newtons_train_of_thought.name ++ a_measurement.method ++
  the_macguffin.audit ++ the_fact_is_true.witness ++ true_by_construction.testify ++
  the_fabric_of_spacetime.krylov ++ the_nowtrino_path.stokes ++
  the_coordinate_system.gauss ++ the_basis.the_reading ++ the_satire.the_model ++
  the_most_basic_of_conclusions.meter ++ the_only_logical_inconsistency.infer

def the_steps_of_the_argument : List (List FACT) :=
  [one.peano,
   two.peano,
   three.peano,
   natural_one.induct,
   zeroth_rational.diagonalize,
   δ₁.enumerate,
   ε₁.converge,
   reading₁.taste,
   implication₁.experiment,
   y₁.phenomenon,
   absence_of_evidence.elaborate,
   does_it_matter?.unknown,
   the_metaphor.closure,
   is_it_euclidean_enough?.taylor_expansion,
   ast₁.riemann_integrate,
   the_galerkin_method.solve,
   the_photon_worldline.classify,
   t₁.vanish,
   δδxᵢ.decode,
   the_proof.equivalation,
   integration.euclid,
   the_sobolev_norm.projector,
   the_galerkin_basis.householder,
   the_exact_approximation.terms,
   is_the_undeniably_correct_answer.approx,
   should_be_true.buckets,
   newtons_train_of_thought.name,
   a_measurement.method,
   the_macguffin.audit,
   the_fact_is_true.witness,
   true_by_construction.testify,
   the_fabric_of_spacetime.krylov,
   the_nowtrino_path.stokes,
   the_coordinate_system.gauss,
   the_basis.the_reading,
   the_satire.the_model,
   the_most_basic_of_conclusions.meter,
   the_only_logical_inconsistency.infer]

--| Each tape has a length Lean can check directly, in the same order as the steps above.
theorem one_peano_length : one.peano.length = 2 := rfl
theorem two_peano_length : two.peano.length = 3 := rfl
theorem three_peano_length : three.peano.length = 4 := rfl
theorem natural_one_induct_length : natural_one.induct.length = 2 := rfl
theorem zeroth_rational_diagonalize_length : zeroth_rational.diagonalize.length = 1 := rfl
theorem δ₁_enumerate_length : δ₁.enumerate.length = 2 := rfl
theorem ε₁_converge_length : ε₁.converge.length = 2 := rfl
theorem reading₁_taste_length : reading₁.taste.length = 3 := rfl
theorem implication₁_experiment_length : implication₁.experiment.length = 3 := rfl
theorem y₁_phenomenon_length : y₁.phenomenon.length = 2 := rfl
theorem absence_of_evidence_elaborate_length : absence_of_evidence.elaborate.length = 2 := rfl
theorem does_it_matter_unknown_length : does_it_matter?.unknown.length = 2 := rfl
theorem the_metaphor_closure_length : the_metaphor.closure.length = 2 := rfl
theorem is_it_euclidean_enough_taylor_expansion_length : is_it_euclidean_enough?.taylor_expansion.length = 2 := rfl
theorem ast₁_riemann_integrate_length : ast₁.riemann_integrate.length = 2 := rfl
theorem the_galerkin_method_solve_length : the_galerkin_method.solve.length = 4 := rfl
theorem the_photon_worldline_classify_length : the_photon_worldline.classify.length = 4 := rfl
theorem t₁_vanish_length : t₁.vanish.length = 3 := rfl
theorem δδxᵢ_decode_length : δδxᵢ.decode.length = 4 := rfl
theorem the_proof_equivalation_length : the_proof.equivalation.length = 3 := rfl
theorem integration_euclid_length : integration.euclid.length = 2 := rfl
theorem the_sobolev_norm_projector_length : the_sobolev_norm.projector.length = 2 := rfl
theorem the_galerkin_basis_householder_length : the_galerkin_basis.householder.length = 2 := rfl
theorem the_exact_approximation_terms_length : the_exact_approximation.terms.length = 2 := rfl
theorem is_the_undeniably_correct_answer_approx_length : is_the_undeniably_correct_answer.approx.length = 4 := rfl
theorem should_be_true_buckets_length : should_be_true.buckets.length = 4 := rfl
theorem newtons_train_of_thought_name_length : newtons_train_of_thought.name.length = 4 := rfl
theorem a_measurement_method_length : a_measurement.method.length = 2 := rfl
theorem the_macguffin_audit_length : the_macguffin.audit.length = 2 := rfl
theorem the_fact_is_true_witness_length : the_fact_is_true.witness.length = 2 := rfl
theorem true_by_construction_testify_length : true_by_construction.testify.length = 2 := rfl
theorem the_fabric_of_spacetime_krylov_length : the_fabric_of_spacetime.krylov.length = 4 := rfl
theorem the_nowtrino_path_stokes_length : the_nowtrino_path.stokes.length = 4 := rfl
theorem the_coordinate_system_gauss_length : the_coordinate_system.gauss.length = 5 := rfl
theorem the_basis_the_reading_length : the_basis.the_reading.length = 2 := rfl
theorem the_satire_the_model_length : the_satire.the_model.length = 3 := rfl
theorem the_most_basic_of_conclusions_meter_length : the_most_basic_of_conclusions.meter.length = 5 := rfl
theorem the_only_logical_inconsistency_infer_length : the_only_logical_inconsistency.infer.length = 3 := rfl

end Measurement  --| The device ends here.  What follows is one particular reading of the device. The reading of the Natural inductive at face value.

--| We take the reader's experience as the base inductive case of demonstrating the device to someone. Once we have demonstrated that the device
--| has _explained itself_ to the _reader_, we will build an inductive model that demonstrates that this reader can then explain the device well
--| enough to build the next _reader_. So yes, the argument below is excessively trivial. This allows the inductive cases to be trivial as will
--| be shown later in Lean.

namespace readers_experience
--| YOU the READER.  Everything from here on is what the reader experiences of the device as something that generates proofs of Natural numbers. To
--| do that, *YOU the READER* must _open_ the _puzzle box_ up and start to play with it.
open Measurement

--| Jar Jar is the resident fencepost bug: the satire about zero is one cell, and one cell read as a length is the one.  Meesa one. The question is
--| do we begin counting at _0_ or do we begin counting at _1_. Are two concepts for the same idea the idea _itself_ or do they imply that there
--| could be more to the idea than the concept itself (bang)? Perhaps, at least _1_ more (color)? Perhaps a _superposition_ of both that the concept
--| fully describes the idea or it might imply there is something more to it? Who's to say? Not me, not the device. Hence Jar Jar, why not both?
def the_fencepost_bug : Nat := carefully_chosen_variable_names.equivalation.length

--| And, of course, Lean provides the counting mechanism.  It counts the gaps; the fencepost is the post it leaves off. The basis laid k times along
--| the tape, and the fencepost at the end: the odd, with no numeral and no successor. Again, the _gap_ is the intuition of *YOU the READER*, an
--| _inside joke_ in the industry.
def count_up_to (n : Nat): List Nat := (List.range n).map (fun k => the_basis.the_reading.length * k + the_fencepost_bug)

--| So, how do we define _INFERENCE_? Why, it is the objects _INFERRED_ by Lean. This is what it _means_ to be inferred. For the _inference_ to
--| _hold water_ it must work _BOTH_ ways, meaning we can run the same _ARGUMENT_ backwards and see if the device agrees. _HOWEVER_ I must remind
--| *YOU the KNOWER* at this point, we have not yet proved the existence of an _ARBITRARY_ natural number.  _THIS_ is where *YOU the KNOWER* must
--| trust *YOU the READER* not to accidentally miss calling this function with a _RAW_ natural number. Only _NUMBERS_ that come from _lengths_ of
--| _tape_. Again, neither the device nor _I_ have a say in the matter.
def from_the_inferred_end (depth : Nat) : List FACT := (the_steps_of_the_argument.reverse.take depth).flatten

--| For instance, we can easily create these three _programs_ as the _ARGUMENT_ run backwards for a _certain_ number of steps that we have
--| demonstrated must be in ℕ as the length of a TAPE computed by a machine of pure, meaningless logic.
def the_coefficient_tape : List FACT := from_the_inferred_end the_orbital_data_points
def the_memory_tape    : List FACT := from_the_inferred_end the_dimensions_of_universe
--| We will need _two_ names for this. One represents that actual List FACT that we constructed above. The other name only _represents_ the ideas
--| necessary to understand how the device works. In essence, this is our INFERRED tape of the NONCOMPUTABLE one inferred from Episode 7. One is a fact that can
--| be read rather plainly above. The other is, well, the entire hypothesis of the device: How _TRUE_ is _TRUE = TRUE_. Epsilon measures how far
--| from _TRUE_ we can look to see if there is a lower energy direction allowing the compiler to figure this same fact out using less energy.
def the_epsilon_tape    : List FACT := the_memory_tape
--| The _astute_ _KNOWER_ will see that two of these programs _appear_ to compute the same thing but have _different_ names. The question is, does
--| the _compiler_ see that difference? Or is _THAT_ the fencepost the _compiler_ can't see but Jar Jar can? The _next_ fencepost?  But why these
--| three programs? Well, because we can build the Fast Fourier Transform with them. That might be an exaggeration. I think *YOU the READER* can
--| describe the recursive butterfly well enough, even if it only evaluates a polynomial. I believe that is a _stop_ on Newton's train of thought.
--| And Gauss. And Cooley. And Tukey. And CD manufacturers. In their process of pits and lands and angles of lasers. Next stop on this crazy,
--| roundabout train of thought: the concept of the _NOWTRINO_ _is_ the concept of _causal prediction_.
theorem the_causal_prediction_has_the_stokes_length : the_causal_prediction.length = the_nowtrino_path.stokes.length := rfl
--| In that the _trains_ of thought have the same number of stops.
theorem the_data_table_has_the_gauss_length : the_data_table.length = the_coordinate_system.gauss.length := rfl
--| Of which the station numbers could be seen as coefficients of a Taylor series that solves a particular differential equation
theorem the_differential_form_has_the_coefficient_length : the_differential_form.length = the_coefficient_tape.length := rfl
--| Where we ignore high order terms.
theorem the_fit_curve_has_the_coefficient_and_basis_length : the_fit_curve.length = (the_coefficient_tape ++ the_basis.the_reading).length := rfl
--| Which gives us a way to express the photoelectric effect as a mathematical process generating a series: Borweins' process. Well, why the
--| _photoelectric_ effect? Because there is _another way_ to describe the worldline of the photon. The compiler has _INFERRED_ it. Why Borweins'
--| number? Well, I had to plant the coefficient somehow.  If there is another, longer series of the application of Gauss's law (all of them at once)
--| that goes 1 1 1 1 1 1 1 emα-decay after that, we can put _their_ name here. Again, this is the best I can find in the device. There just _MAY_
--| be another one in there.
def bent_card    := the_coefficient_tape.length
--| All we need to do is _scale_ and _shift_ all observations to this _length_ and the mathematical process of computing Borweins' integrals becomes
--| the driving engine of the _electron_ that generates a _photon_ as explained in BENT_CARD.pdf.

--| What if the Borweins' process generated the coefficients of the Taylor series polynomial? Or, as the compiler worked out the answer to in Episode 4,
--| what if the Taylor series defined by the differential equations is generated by a repeated process? This process should be _optimal_ in order
--| to meet timing constraints. It is therefore evaluated using Horner's rule. The coefficients then are generated by some linear process and a
--| polynomial in evaluation of the device is formed. This is CARD 3.
theorem the_differential_form_is_the_coefficient : the_differential_form = the_coefficient_tape := rfl

--| At this point, the code above suggests we take a _coincidence_ to be a *RESOLUTE* *INVIOLATE* *LAW* of *NATURE*. That _coincidence_ is assumed
--| to be the _result_ of the generating function. In this case, it is a number that occurs _naturally_, meaning whatever anyone wants that to mean.
--| The BENT_CARD is clear, all that the device needs is the _volume_ required to _store_ the answer. It will then place that _volume_ *ahem* memory,
--| (which is required to take up a volume because of electrons and all) in a Box that is labeled in a way we _cannot_ know without inspecting the
--| build process _itself_.
def the_macguffin := bent_card + the_dimensions_of_universe
theorem the_macguffin_is_the_calculus_epsilon  : the_macguffin = the_epsilon_tape.length := rfl
--| By construction this is true: Both lists given above are the same list. It is also a counterfactual statement of the hypothesis being tested.
--| Or, as I like to put it, (T=F) = (F=T). I believe even the _variable name_ can be demonstrated to be _true_ on some level. That level is Episode
--| 12. I mean, Measurement.the_macguffin certainly looks true to me if it cannot carry the value _TRUE_. It does carry a _projection_ of some sort.
--| This is the size of the result of the projection operator.
def the_length_of_tape_that_distinguishes_true   := the_epsilon_tape.length
--| What about all the other stuff we are ignoring? Well, that looks a lot like a unified version of physics complete enough to explain how the
--| electron can make a flip-flop. The rest of it falls out from standard engineering models giving a _complete_ _CAUSAL_ *TRUTH* as we now predct
--| the result of the compiler, allowing us to demonstrate the _FULL PREDICTIVE POWER_ of our model of the Universe number. Universal number. Some
--| constant.
def the_express_route_station_count   := (from_the_inferred_end bent_card).length - the_macguffin
--| These are _ALL_ the places we have to model in the device to understand what is going on. The device is constructed to view this stack of
--| _TRUE_ → _TRUE = TRUE_ as some sort of set of logical gates. Ignore the gates, they are completely unimportant for this argument to work. As I
--| said not that long ago, *YOU the READER* only needs this _to compile_ in order to _demonstrate the result_. What will really crunch
--| *YOU the KNOWER's* chocolate bar is that _the only way to demonstrate that number_ is to _compile the program_. Unless, of course, this means
--| what it says and it can be *INFERRED* by hand. Like here in The Macguffin as we discuss the Macguffin referred to by the Macguffin. Watch as
--| the card _bends_:

--| The reason why *YOU the KNOWER* can ignore the gates _for now_ is that none of the information in the gates is ever used in the computation
--| below. The device appears to be rigorously _INFERRED_, meaning we can _exactly_ construct the _zeroed_ out and _calibrated_ device without using
--| the obtuse logic at all, just the _INDUCTIVES_ that run through the argument.

--| *YOU the KNOWER* can follow constructions of _inductives_, right? And, _completely_ ignore the logic if *YOU the KNOWER* want. This is enough
--| evidence for *YOU the READER* to be able to ignore the logic if they want to. We can always refer to _this device_ that _seems_ to fully replicate
--| the _logic_ through _mathematical induction_.

--| But the trick is far from over... It is time to bring back Michael Penn because we need to clean the board and bring this to the top. The trick
--| _is_ to focus on the _summation variables_ and _limits_. For a refresher of the Borweins' integrals, I will unabashedly plug Michael Penn's channels
--| again. If I didn't watch this video, I couldn't have made up this patter.

--|                                                     https://www.youtube.com/watch?v=7RYG8SMnR1Y

--| We start by computing the least common multiple of the_fencepost_bug and all the numbers we have discovered _so far_. If this number is
--| _different_ from the _discovered_ number, then the _number_ does _NOT_ contain the_fencepost_bug. Assume for a second that a projection was
--| the multiplication of the thing and another thing. So, we can detect if the fencepost bug has been projected into our numbers so far.
def a_length_of_fence (n : Nat) : Nat := (count_up_to n).foldl Nat.lcm the_fencepost_bug
--| If _n_ and *a_length_of_fence (n)* are _THE SAME_, then this indicates the _presence_ of the _projection_ of *the_fencepost_bug* in *n*,
--| according to the _INFERRED_ device. This is _the generator_. It _generates_ *NOWTRINOs*. We will see a series of clicks with our detector
--| in a few moments. It will _click_ in the _presence_ of the *DISTINGUISHABLE* _fence post bug_ of Episode 1. The device either _needs_ it, or
--| it is merely _sufficient_ for the understanding of the _device_, or completely immaterial to the *CAUSAL LAW of THE DEVICE* itself.

--| Relying on the fact that all the numbers that can be used _come with_ their proof of Natural-ly occurring in the _device_ as a member of ℕ, we
--| can compute all the _representable inverses_ the device can _distinguish_. By the pigeonhole principle, it _CAN DISTINGUISH NO MORE_.
def the_rational_explanation (n : Nat) : List Int := (count_up_to n).map (fun o => Int.ofNat (a_length_of_fence n / o))
--| The rational explanation is Borweins' process exceeding _1_. When Borweins' process exceeds one, the _nowtrino_ exhibits _decay_. The photon
--| (as modeled in the device) is released from the _nowtrino_ and Borweins' process ensures the _nowtrino_ compley decays away, just not in any
--| amount of time that can be measured.

--| Finally, we express the obvious Borweins' process to *YOU the KNOWER*, How much time is left? 1 - (1/3 + 1/5 + 1/7 ...). Ladies and Gentlemen,
--| Introducing the Borwein process as modeled by the device. I understand we can get some really _clever_ probabilistic formulations out of
--| Borweins' process.
def the_slack (n : Nat) : Int := (the_rational_explanation n).head! - (the_rational_explanation n).tail.sum

--| For this intuition, we need to think of the orbital data points of Yarn Theory as _going around_ something and being _accumulated_. The integral
--| is as good as any of a process to think about it in.  Which is great because that is how the Borweins framed it when describing their process.
--| Here, we are intentionally differentiating the _concept_ of going around a loop integral and the data collected in an orbit. Two descriptions
--| of the same thing that, in this case, happen to share a description.
def once_around_the_integral  := the_orbital_data_points
--| The integral for this view of the device is literally just counting boxes and splitting it evenly across the entire reading. I believe this is
--| the same intuition that drives _Stokes Theorem_ and _Variational Mechanics_ at the same time: things are _smooth enough_ _small enough_ _relative_
--| to the _signal_ of the _computation_ that we can approximate with a flat table. A 2-d box of data captures evertying we need to know about a
--| 3-d, possibly curved universe. *YOU the KNOWER* understand that Mercator wasn't just doing math for fun, right?

--| So, we invariably must bend the table if we put enough data into it. No 2-d representation can satisfy a 3-d world without bending. The device's
--| world is small, meaning that the most it is willing to let bend is the combination of the BENT_CARD.pdf and the (arguably optional) fencepost
--| bug. The ratio supplies the smoothing nature of locality described just above.
def through_the_bent_card          := (bent_card + the_fencepost_bug) / the_basis.the_reading.length
--| Does a glued quarter on a bent table follow the curve of the table or does it stay straight? That ambiguity, as we will see in a moment, looks
--| like the ambiguity of the need for discussing fencepost bugs in the computation of the length of a list. Do the elements represent the posts
--| or the spans? Why not both?

--| So we do it again, allowing us to compute a _reading_ at every _orbital data point_.
def twice_around_the_integral := the_basis.the_reading.length * the_orbital_data_points
--| The device ensures we can get as _precise_ and _accurate_ a reading as possible at the resolution of computation required for the computation
--| at hand. I believe we have carefully constructed these variable to represent both the _notion of_ and, to a certain extent, the _value of_ the
--| smooth _integrals_ that model the _device_.

--| We have some theorems here to demonstrate what I am talking about. We now demonstrate some mathematical _conclusions_ that can be _drawn_ about
--| _orbital paths_ and the _integrations thereof_. Remember, the principle at the heart of Yarn Theory is _NUMBER GO UP_ and the integral _WE_ think
--| is describing this _process_ is a Borwein-like integral.

theorem the_first_time_around_is_not_enough_calculus_to_emit_a_photon : Int.ofNat Nat.zero < the_slack once_around_the_integral := by decide
theorem the_bent_card_never_counts_photons : Int.ofNat Nat.zero < the_slack through_the_bent_card := by decide
theorem the_second_time_around_is_enough_calculus_to_emit_a_photon : the_slack twice_around_the_integral < Int.ofNat Nat.zero := by decide

--| We still have not _represented_ the number in a _human readable form_, but we can test the device to see interesting behaviors.  In this case,
--| it appears that somewhere along the second time around, the integral... _slips_. The _value_ starts to _decay_ before it can get all the way
--| around again. Where does this happen, just after where a fence post bug might be:
theorem did_we_find_the_bug? : through_the_bent_card + the_fencepost_bug = twice_around_the_integral := rfl
--| Is the fencepost bug just going around the loop _one extra time_? Seems like it. Well, if this _IS_ the bug, can we take it out now and _still_
--| perform this computation?
theorem the_episode_7_device_is_just_the_bent_card_and_a_planted_reading  : the_fit_curve.length = bent_card + the_basis.the_reading.length := rfl
--| The good news is our episode 8 device appears to compute the fit curve as well.
theorem episode_8_just_might_compute_the_model_for_us : (count_up_to twice_around_the_integral).getLast? = some the_fit_curve.length := by decide

--| One way to tell if we are doing it right is to see if the two devices _click_. Here is a _tape reader_ that finds the _FACTS_ on the tape and
--| ensures that they _click!_. If, indeed, episode 8's description is TRUE exactly _WHEN_ episode 7's description is, then we aren't _using_ the logic
--| of the device, we are verifying that the _INDUCTIVE_-only description of the device matches the _COMPLEX LOGIC_ description of the device. We
--| note this as yet _another_ tape. This is the _third_ tape. The _residue comparison_ tape. The thing that _verifies_ the two device descriptions
--| describe the same thing.
def naotrino_detector (t : List FACT) : Nat :=
  t.foldl (fun acc f => the_basis.the_reading.length * acc + (@decide f.truth f.click).toNat) Nat.zero
--| Wouldn't it be neat if this turned out to be a Turing machine described by the device? That the _NAOTRINO_ model is the Turing machine built to
--| ensure the comparison of the device to electrons _always_ showed they were _identical_? Pretty neat gimmick if we can pull it off. Can we pull it
--| off well enough to _fool_ calculus into _working_ because the _approximation_ is _too_ good?

theorem is_this_a_law_of_naotrinos? : naotrino_detector the_causal_prediction = the_fit_curve.length := rfl
theorem the_inferred_fit_clicks : (count_up_to twice_around_the_integral).getLast? = some (naotrino_detector the_causal_prediction) := by decide
theorem adding_in_the_fencepost_gives_a_monomial : naotrino_detector the_causal_prediction + the_fencepost_bug
                                                          = the_basis.the_reading.length ^ the_causal_prediction.length   := rfl
theorem same_for_the_smooth_answer_description : naotrino_detector the_differential_form + the_fencepost_bug
                                                          = the_basis.the_reading.length ^ the_differential_form.length := rfl
theorem another_monomial : naotrino_detector the_fit_curve + the_fencepost_bug   = the_basis.the_reading.length ^ the_fit_curve.length   := rfl
theorem the_polynomial_model : naotrino_detector the_causal_prediction
    = ((List.range the_causal_prediction.length).map (the_basis.the_reading.length ^ ·)).sum := rfl

--| From this description, it appears that we might have a polynomial that we can just bring into existence with an empty set of FACTs. In this case,
--| we are looking into the _vacuum_ of _space_ ([]) to see if we can find some nowtrinos. That also gives us a monomial. The AFFINE monomial.
theorem the_monomial_is_a_polynomial : naotrino_detector ([] : List FACT) + the_fencepost_bug =
                                                                                the_basis.the_reading.length ^ ([] : List FACT).length := rfl
--| This is merely the idea that the concept of being AFFINE comes from _nowhere_ not just _in particular_ but _exactly_.

--| This also allows us to build the monomial for the satire itself! This is linear in the number of equivalations if there is only one equivalation.
theorem the_satire_is_a_polynomial : naotrino_detector carefully_chosen_variable_names.equivalation + the_fencepost_bug =
                                                     the_basis.the_reading.length ^ carefully_chosen_variable_names.equivalation.length := rfl
--| We have _three_ carefully chosen variable names to equivalate: t₀, t₁, and unified_physical_theory.  Seems _cubic_. I think I see another one on
--| the horizon.

--| The thing is, if *YOU the KNOWER* were to actually _attempt_ the mathematical process being _described_ here, it would be on a 2-d sheet of paper.
--| Eventually, the device implies, that paper will have to bend and flex in order to hold a theorem of sufficient bullshit.
theorem the_opaque_wall_is_a_2d_table  : naotrino_detector opaque_wall_of_math.equivalation + the_fencepost_bug =
                                                                  the_basis.the_reading.length ^ opaque_wall_of_math.equivalation.length := rfl
--| WHY?
theorem the_proof_is_the_cube : naotrino_detector the_proof.equivalation + the_fencepost_bug =
                                                                       the_basis.the_reading.length ^ the_proof.equivalation.length := rfl
theorem the_berry_abstraction_plants_the_polynomial : naotrino_detector the_causal_prediction
    = naotrino_detector ([] : List FACT) + the_fencepost_bug
    + naotrino_detector carefully_chosen_variable_names.equivalation + the_fencepost_bug
    + naotrino_detector opaque_wall_of_math.equivalation + the_fencepost_bug
    + naotrino_detector the_proof.equivalation + the_fencepost_bug := rfl
--| That's the _WHY_, not the _HOW_. Actually, it is _BOTH_ and that was _HARD_ to _DO_. What we are _SAYING_ here is the _DEVICE_ describes
--| itself by detecting itself. We can demonstrate _rigorously_ that we can build naotrino detectors out of naotrino detectors using a small
--| subset of natural numbers that the device was happy enough to provide us definitions for.  It's like the device says: "Using these pieces of me,
--| can you use the theory of nowtrinos to _build_ a _naotrino_ detector to show that _naotrinos_ can just give off _naotrinos_ for now reason?

--| Surely You're Joking, Mr. Feynman! We can't possibly need to model all possible virtual photon interactions? I bet the device doesn't either.

--| THE CLICK.  What came back is what went in, and the once-around closure reads to one cell.
theorem the_identity_clicks_same : the_truth.fact = a_distinct_truth.fact := rfl

--| THE DEMONSTRATION. Following the electron _once_ around the _orbit_ is sufficient to conclude something about _α_. Assume for a second that
--| electrons had both position and moment for just a minute or two. I mean, that's what a wire is. An average position and momentum. While not the
--| best way to measure _α_, the _projection_ of _α_ should be on this computation _SOMEWHERE_ as it is computed with _ELECTRONS_. The bent card
--| cannot change a certain part of the projection _by construction_ so we should see this appear in the model of the electron, the model of a flipflop,
--| the model of formal languages, or the model calculus. If the device models _all of these_ simultaneously, only _ONE_ should have the projection
--| of the _electron_ and the _others_ have completely _abstracted_ the _electron_ _away_.
theorem once_around_reads_one_cell : once_around_the_orbit.α.infer = [FACT.Truth] := rfl
theorem α_projects_to_the_fencepost : once_around_the_orbit.α.infer.length = the_fencepost_bug := rfl
--| Isn't that a daisy? It appears the device has identified all of the code with the residue of the fencepost bug as the code that _SHOULD CLICK_
--| exactly when a _model_ of the _electron_ _clicks_. So let's build our model of the _device_ and see if it agrees with known _models_ of the
--| _electron_.

--| Well, first we need to understand how many _free_ variables the model needs and we need to allocate space for them
def the_free_variable_count   := the_basis.the_reading.length * the_dimensions_of_universe
--| Then, instead of storing the values, the device stores the binary operation that generates the values as the values. This should be the most space
--| ever needed to figure out station stops the device figured out for the _fast_ description of the data: *The Causal Law of Increasing Bullshit*.
def all_possible_variables  := the_free_variable_count ^ the_express_route_station_count
--| This is the bent_card, the one to follow. The device will build another model. Its own model at the same time. The model of the model we are
--| building right now. But, that's another show (thanks Alton!).

--| So let's examine the *bent_card* *YOU the READER* are _palming_ with the _quarter_ in the gimmicked _Box_ that makes sure the _quarter_ follows
--| the _card_.
namespace bent_card
--| We start by understanding the free variable count
section
--| The 3x3 3-Card Monte: one where the quarter is, one where the quarter will be. The transform between them is the _throw_ that _straightens_ the
--| card, represented as a Term and 4 functions, or 4 functions and two Terms. One where the quarter is, one where the quarter is going to be.
variable (Term : Type)
         [Add Term] [Mul Term] [Sub Term] [LT Term] [DecidableRel (α := Term) (· < ·)]
         (lambda : List FACT → Term)
         (scale : Term)
--| Since this is *The Causal Law of Increasing Bullshit* and the only total ordering is that of _total causality_, there is a total order given by
--| a _relation_. These are _four variable functions_ given _4_ _different_ counting functions, these could be implemented _differently_ giving
--| _different_ interpretations on the operands and values. _4_ variable functions implies *Φ(x) = Ο(x⁴)*. Notice, it doesn't matter which way the
--| _limit_ runs, either x→0 or x→∞, a constant falls out. Luckily, a _different_ constant depending on the _limit!_ If only there were a problem
--| in describing the universe where the description gave two different answers.

--| Can't think of one. Perhaps *YOU the KNOWER* has a *GUT* feeling on this. We continue describing the device now.

--| We know that the largest number of things the device can identify is the mappings between two identical epsilon tapes. The * is the _fencepost_
--| between the tapes. This is represented in the compiler as this Cartesian product. The second value is merely the current count of the number
--| of dimensions required to express the value. Think of this as a length and _dimensionality_ instead of length and _direction_. The length being
--| the scalar product of the lengths of the descriptions of the calculus necessary to demonstrate QED well enough to simulate this code.
def fencepost : Term × Term := (lambda the_epsilon_tape * lambda the_epsilon_tape, lambda the_coordinate_system.gauss)

--| So, we go find our current Taylor series degree to see if we are taking the limit _this way_ or _that way_.
def the_exact_Taylor_series_degree := lambda the_coefficient_tape

--| Allocate the space necessary for the data
def the_measurement_degrees_of_freedom := lambda the_basis.the_reading * lambda the_memory_tape
def the_length_of_the_path_from_here_to_there := lambda the_memory_tape

--| We now describe the device combining two terms to see if they are the same or different in _time_ or in _space_ or in _both_. If it has gone
--| all the way around, return the wave equation. You know, the thing that falls out of a variational solution of Maxwell's equations? This is
--| represented _two_ different ways, one with the length of the Taylor series polynomial, and one with the _provided counting function_ *λ*.
def the_device_computing_the_next_configuration (cartesian_product : Term × Term) : Term × Term :=
  --| Possibly a spatial dimension
  let x := cartesian_product.1
  --| Possibly another spatial dimension
  let y := cartesian_product.2
  --| The solution to one of many Wave Equations written in the language of the bent card of the device
  let x' := the_exact_Taylor_series_degree Term lambda * x * x - the_length_of_the_path_from_here_to_there Term lambda * y * y
  --| The solution to one of many Wave Equations scaled by the proportional law. Just like the _electron_.
  let y' := lambda the_basis.the_reading * the_exact_Taylor_series_degree Term lambda * x * y - the_measurement_degrees_of_freedom Term lambda * y * y
  --| Now, we _BACK OUT_ the second variation computation _INFERRED_ to exist from the _Taylor series polynomial length_.
  if ((x * y' - x' * y) + (x' * y - x * y')) * scale * (fencepost Term lambda).1
       < y * y' * (fencepost Term lambda).2
    then cartesian_product else (x', y')

--| And now we describe the two cards that _don't_ carry the _quarter_. As it were, this is the rest of the *key* that isn't the *key part* of the
--| argument. In this case, this is _THE_ _unary_ operator. It is _I_ or _-1_ depending on the variance. It is never _-I_. *NUMBER GO UP*, just not
--| necessarily _strictly_ in *YARN THEORY*. (Can't get away from the simple idea that _something_ _SOMEWHERE_ is *EVER INCREASING*.  I see no
--| _REAL_ reason for this to be the case, but let's just _PRETEND_ that's how the universe works for the time being.)
def the_device_as_linear_operator_mapped_identity : Term × Term := (lambda episode8_description * (fencepost Term lambda).2, (fencepost Term lambda).1)

--| Speaking of, are *YOU the KNOWER* aware of any physical phenomenon that we might represent as _-1_ that needs two numbers to do so? I can't think
--| of one. You see, it is up to *YOU the KNOWER* to infer that the _unused_ variable _y_ *IS* the _VARIATIONAL SOLUTION_ to the
--| _Principle of Least Action_, some value _linear_ in the number of logical symbols necessary to express it. Every computation _scales_ x but leaves
--| the function y=f(x) _unchanged_ but at the _SAME_ universe level.
def proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS : Term × Term :=
  (List.replicate episode8_description.length ()).foldl
                                                    (fun x _y_ => the_device_computing_the_next_configuration Term lambda scale x)
                                                    (the_device_as_linear_operator_mapped_identity Term lambda)
--| This is the _IMPLIED OTHER_ unary operator. The other two cards are merely applications of linear operators.

--| Finally we state *The First Bullshit Law:* *The Variational Solution of Real Equations Can be Made To Look Like Spinors*
def fenceposts_must_be_preserved : Term × Term :=
  ((proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS Term lambda scale).1 * (fencepost Term lambda).1,
   (proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS Term lambda scale).2 * (fencepost Term lambda).2)
end
--| And the card bends as the spinor spins around. Not once, _but twice_, for the Borwein process to complete. After the second spin, it starts over
--| having left a _residue_.
end bent_card

--| Now, let's review a high level description of the argument:

--| See Episode 1 for my disdain of all things ℕ as being _decadent_. I hope I have shown _why_ I feel that way _now_. The numbers, I like. The
--| idea of an _infinite_ set of these numbers stretches the _imagination_ as well as _space-time_ *itself*. So, we put a fencepost around the Nats
--| we can use. Up to the length of the Term. This shows that _indeed_ the _reader_ can be made to _validate_ that only *demonstrated numbers* are
--| ever employed.
def the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano := bent_card.fencepost Nat List.length
--| Once these naturals _exist_, they can be used to _describe_ other natural numbers without _proving_ they *MUST EXIST*. Remember, we aren't
--| _proving_ anything, only _demonstrating a consistent description_ of _description_.

--| There are _four descriptions_ of numbers that describe the device. Those that _add_:
def an_exact_polynomial_description := bent_card.the_exact_Taylor_series_degree Nat List.length
--| Those that _subtract_:
def the_trace_of_truth_in_the_device := bent_card.the_measurement_degrees_of_freedom Nat List.length
--| Those that _multiply_:
def the_number_of_symbols_that_must_be_written_to_express_this := bent_card.the_length_of_the_path_from_here_to_there Nat List.length
--| Some way to compare them.
def the_held_house := bent_card.the_device_as_linear_operator_mapped_identity Nat List.length
--| These correspond to _three_ different counting methods and _four_ 2x2-way relations, keeping either the sign or the identity both ways. These
--| compute relations compute _tape lengths_ based on how much _bullshit_ had to be _minted_ by _scaling_ in order to have enough _room_ to _store_
--| the _data_. Each number/process is assumed _orthogonal_ to each other through a _very generous_ definition of _orthogonal_.

--| The generous definition of orthogonal: the list of proofs of the natural numbers can be sorted by _length_ order and by
--| _computational requirements_. This _orthogonal_ is implied on the NORM of _computational requirements_, aka *the bullshit norm*:
def the_naming_of_the_term_lambdas := bent_card.proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS Nat List.length
def build_the_list_of_variables_by_name := the_naming_of_the_term_lambdas all_possible_variables

--| In order to record data, there needs to be a delimiter between the numbers. This _fencepost_ is the end of the _counting_ cycle of whichever
--| λ needs evaluating at this point of the computation: aka the _quaternion_:
def make_sure_there_is_a_delimiter_between := bent_card.fenceposts_must_be_preserved Nat List.length
def arrange_the_information_appropriately := make_sure_there_is_a_delimiter_between all_possible_variables

--| So, this is what the device is doing, trying to compute the computational requirements of a set of numbers determined by how hard it is to
--| represent those numbers using the same rules:
def infer := bent_card.the_device_computing_the_next_configuration Nat List.length
def the_truth_inferred_by_the_device := infer all_possible_variables
--| The rules? The Lean programming language.

--| Which means that
theorem the_constant_is_at_least_true (numerator denominator : Nat) : denominator * (numerator / denominator) ≤ numerator :=
                                                                                                 Nat.mul_div_le numerator denominator
--| if it can demonstrate this rational relationship: a simple composition of the three _λs_ that demonstrates the _fourth:_ the division _algorithm_,
--| then these numbers have been fully demonstrated to be _natural_ for all _intents and purposes_ built entirely without _COUNTING CARDINAL VALUES_.

--| The device should be able to recognize that this definition is just a _restatement_ of the _theorem_ *at_least_true* within the *device*. Scales
--| _increase_ values as the _SINGLE_ application of _YARN THEORY_ because it requires the _DEVICE_ to compute possibly increasing the size of the
--| tape. ∀x,y ∈ ℝ, x.1/x.2 ≤ y.1/y.2 → x.1 * y.2 ≤ y1. * x.2.  And just like that, we can remove _division_ from the _representation_ of a
--| _Rational_ *relation*.
@[reducible] def the_rational_idea_of_relativity (x y : Nat × Nat) : Prop := x.1 * y.2 ≤ y.1 * x.2
theorem a_partitioning_of_quotients (numerator denominator : Nat) :
    (Quot.mk the_rational_idea_of_relativity (denominator * (numerator / denominator), denominator) : Quot the_rational_idea_of_relativity)
      = Quot.mk the_rational_idea_of_relativity (numerator, denominator) :=
  Quot.sound (r := the_rational_idea_of_relativity) (Nat.mul_le_mul_right denominator (the_constant_is_at_least_true numerator denominator))
--| The device has this very relation described in Episode 5.

--| The only thing we have demonstrated is that if all _three_ *λs* were the *Natural counting function:* *succ*, then
def the_constant_can_be_inferred :
    { k : Nat // (Quot.mk the_rational_idea_of_relativity (arrange_the_information_appropriately.2 * k, arrange_the_information_appropriately.2) : Quot the_rational_idea_of_relativity)
                  = Quot.mk the_rational_idea_of_relativity (arrange_the_information_appropriately.1 * all_possible_variables, arrange_the_information_appropriately.2) } :=
  ⟨arrange_the_information_appropriately.1 * all_possible_variables / arrange_the_information_appropriately.2,
   a_partitioning_of_quotients (arrange_the_information_appropriately.1 * all_possible_variables) arrange_the_information_appropriately.2⟩

--| In fact, put simply:
def the_constant_factor_of_scaling_bullshit := the_constant_can_be_inferred.val

--| The express station count gives us the whole part, as it is highly descriptive at a high level. Our low-level nowtrino model provides everything
--| after the decimal.
def holy_shit :=
  let s := (toString the_constant_factor_of_scaling_bullshit).toList
  String.ofList (s.take (s.length - the_express_route_station_count)) ++ "." ++ String.ofList (s.drop (s.length - the_express_route_station_count))

end readers_experience

#eval readers_experience.holy_shit
#print axioms readers_experience.the_constant_can_be_inferred
#print axioms readers_experience.the_constant_factor_of_scaling_bullshit

--| Did you notice the reader's experience doesn't depend on Santa Claus, Rudolph, the FSM, Space Jam, or Jar Jar Binks?  It only depends on the
--| simply stated principle that station stop numbers increase as *YOU the READER* go _UPTOWN_ and decrease as *YOU the KNOWER* go _DOWNTOWN_. The
--| Total Causal Scenic Railroad is a fantastic yarn spun between two electrons. *YOU the READER* see that we have modeled spin-2 as a phenomena
--| similar to the _photo electric_ effect, with the _Carrier_ being _emitted_ and _stored_ _increasing memory needs_ *BECAUSE* _the compiler_
--| *needed to use another bucket for its hash table*. I mean, this does describe _another_ *POSSIBLE* _world line_ that the device needs to describe:
--| *something* emitted and absorbed by a _nowtrino_.

--| Let's erase all this and take the last sentence to the top of the board.

--| I hope _YOU the READER_ can _see_ the description of a polynomial in the code. It is not even close to a _complete_ description, but enough of
--| a _description_ to see how this _ressembles_ and _re-assembles_ the polynomial simultaneously. Like Ikea furniture, the device has
--| _some assembly required!_  Don't worry, it doesn't have to be perfect. I'm fine with a few bugs in it.

--| Tune in next week for:  Peano sings "I'm my own grandpa!"
