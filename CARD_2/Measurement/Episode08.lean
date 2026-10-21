/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the stories we tell ourselves might be the only ones we believe._

(c) 2026 All rights reserved. Unless AI needs training data.

__EPISODE 8__: _The Macguffin_

"Forty-two.435?"
                       -- Douglas Adams (to three decimal places -- A Macguffin)

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

instance truthDistinct : DISTINGUISHABLE Prop elaborated_by_lean where --      | At this point, I think we have enough to describe something _distinct from_
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
noncomputable def once_around_the_ladder : INFERRED Prop elaborated_by_lean this_way that_way :=
                                          WHY_NOT? Prop elaborated_by_lean (naotrino_model := this_way) (yarn_theory := that_way)
--| And just like that, we can _INFER_ that the ladder as been traversed _once_ simply because there is _something_ that can be _INFERRED_. In this
--| case, an obvious _INFERENCE_ is that the entire ladder has now been described and shown to possibly _EXIST_. I mean, we show it _DOES_ exist
--| in the README.md. That's proof enough for *YOU the READER* that there exists a device described as I have done so thus far.
@[irreducible] noncomputable instance : INFERRED Prop elaborated_by_lean this_way that_way :=
                                          once_around_the_ladder

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
  | .a_few_pints f _ rest => f :: rest.phenomenon -- | arguing with each other on the same tape that encodes the program. One is TRUE the other, isn't.

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
def y₁ : Study := .a_few_pints zero implication₁ y₀
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

--| A _photon_ from the so-called "Big Bang" would begin in the cmbr and end in a blackhole_singularity, taking no time (as we would call it) and
--| traveling no distance (as we would call it).  Who knows if photons travel or experience time, the EFEs suggest they do not.
def the_photon_worldline : Jar := .superposition zero cmbr blackhole_singularity

--| I mean to suggest and the compiler tends to agree that the arrangement of words that describe the device are _not that far away_ from the very
--| same words that are used to describe physics. That there might be a distance δx between the description of the device and the description of
--| physics. What happens as δx→0? Is physics recovered? Or is just the mathematical description of physics recovered? Is physics required to follow
--| these rules if they are merely _approaching_ the _description_ of _physics_?

--| That is how one _equivalates_.

--| I think we all agree that the photon worldline must exist and is _true_. I am sure there are arugments that *YOU the KNOWER* have already agreed
--| to and are _revisiting_ thinking that _something_ got _rotated_ _somehwere_. So, hold on to that feeling. That's the unified physical theory:
--| something somewhere earlier was rotated allowing us to draw a startling conclusion:
def unified_physical_theory : Equivalation := .physics FACT.Truth the_photon_worldline
--| We will be measuring that _rotation_, explicitly, in the coming episodes. This is just the machine _zeroing out_ to the shortest reading: the
--| photon worldline. It only has a _start_ and an _end_. A photon cannot be detected between these two points. We _label_ these as zero to start:
def t₀ : Equivalation := .zero_like zero unified_physical_theory
--| and True Equivalation as the end:
def tᵢ : Equivalation := .one_like True t₀ unified_physical_theory

--| Since _no time passes_ for the photon and the photon has to start at point t₀, all tᵢ afterwards are the end point. Also, don't forget, we are
--| still _constructing_ all of the structures in the device as x → y. I believe we will have a second, _equivalent_ description of the device when
--| we have finished building these inductives. Well, a description of a _zeroed_ out device. Meanwhile, we are inhabiting all the inductives without
--| _classes_ or _structures_. This is just a _RENAMING_ of things.

--| Where was I? Oh yeah, the device and _orbital mechanics_. *YOU the KNOWER* _do_ understand _orbital mechanics_? The only thing in a zeroed
--| device's universe is the photon world line. It is a very lonely, empty, and locale-less place. So, where is the _photon_ exactly? Gone. The
--| photon goes from source to sink in the middle of computing the first iteration of the device. Since it didn't travel from the start, it is a
--| position 0 relative to where it started. It didn't move.
def xᵢ : Encoding := .boot zero tᵢ

--| Since it didn't move, it had _no_ velocity.
def δxᵢ : Encoding := .zero zero tᵢ xᵢ

--| Since it achieved no velocity by not moving, it's acceleration is also exactly zero.
def δδxᵢ : Encoding := .one zero tᵢ tᵢ δxᵢ xᵢ

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
  the_photon_worldline.classify ++ tᵢ.vanish ++ δδxᵢ.decode ++
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
   tᵢ.vanish,
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
theorem is_it_euclidean_enough_taylor_expansion_length :
    is_it_euclidean_enough?.taylor_expansion.length = 2 := rfl
theorem ast₁_riemann_integrate_length : ast₁.riemann_integrate.length = 2 := rfl
theorem the_galerkin_method_solve_length : the_galerkin_method.solve.length = 4 := rfl
theorem the_photon_worldline_classify_length : the_photon_worldline.classify.length = 4 := rfl
theorem tᵢ_vanish_length : tᵢ.vanish.length = 4 := rfl
theorem δδxᵢ_decode_length : δδxᵢ.decode.length = 4 := rfl
theorem the_proof_equivalation_length : the_proof.equivalation.length = 3 := rfl
theorem integration_euclid_length : integration.euclid.length = 2 := rfl
theorem the_sobolev_norm_projector_length : the_sobolev_norm.projector.length = 2 := rfl
theorem the_galerkin_basis_householder_length : the_galerkin_basis.householder.length = 2 := rfl
theorem the_exact_approximation_terms_length : the_exact_approximation.terms.length = 2 := rfl
theorem is_the_undeniably_correct_answer_approx_length :
    is_the_undeniably_correct_answer.approx.length = 4 := rfl
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

def from_the_inferred_end (depth : Nat) : List FACT := (the_steps_of_the_argument.reverse.take depth).flatten
def the_coefficient_tape : List FACT := from_the_inferred_end the_orbital_data_points
def the_coupling_tape    : List FACT := from_the_inferred_end the_dimensions_of_universe
def the_radius_tape      : List FACT := the_coupling_tape

theorem the_causal_prediction_has_the_stokes_length :
    the_causal_prediction.length = the_nowtrino_path.stokes.length := rfl
theorem the_data_table_has_the_gauss_length :
    the_data_table.length = the_coordinate_system.gauss.length := rfl
theorem the_differential_form_has_the_coefficient_length :
    the_differential_form.length = the_coefficient_tape.length := rfl
theorem the_fit_curve_has_the_coefficient_and_basis_length :
    the_fit_curve.length = (the_coefficient_tape ++ the_basis.the_reading).length := rfl

--| THE THIRTEEN is the length of the four-deep walk, and the calculus census agrees with that walk cell for cell.
def thirteen    := the_coefficient_tape.length
def theCoupling := thirteen + the_dimensions_of_universe
theorem the_differential_form_is_the_coefficient : the_differential_form = the_coefficient_tape := rfl
theorem the_coupling_is_the_coupling_tape    : theCoupling = the_coupling_tape.length := rfl
def theRadius   := the_radius_tape.length
def thePlaces   := (from_the_inferred_end thirteen).length - theCoupling


--| THE TWO SLIPS.  The Borwein integrals ∫ ∏ sinc(x/(2k+1)) dx sit at π/2 exactly as long as the first odd outweighs the
--| rest of them, 1 > 1/3 + 1/5 + ⋯, and over a common denominator that is one integer: the first weight less the sum of
--| the others, the slack.  Once around the ladder, four factors, it holds.  Through thirteen, seven factors, it holds.
--| Twice around, eight factors, it slips, and the eighth odd is fifteen: the ladder, all three pages counted once.
--| Thirteen is the odd the integral holds through; the odd after it is where it slips.  The basis reads two cells, so
--| two is the basis, and one is the successor of zero.  No numeral is written.
def the_odds (n : Nat) : List Nat := (List.range n).map (fun k => (the_basis.the_reading.length * k).succ)
def the_common_denominator (n : Nat) : Nat := (the_odds n).foldl Nat.lcm Nat.zero.succ
def the_weights (n : Nat) : List Int := (the_odds n).map (fun o => Int.ofNat (the_common_denominator n / o))
def the_slack (n : Nat) : Int := (the_weights n).head! - (the_weights n).tail.sum
def once_around_the_integral  := the_orbital_data_points
def through_thirteen          := thirteen.succ / the_basis.the_reading.length
def twice_around_the_integral := the_basis.the_reading.length * the_orbital_data_points
--| HAVE_OTHERS_RUN_THE_EXPERIMENT?  Yes.  Four factors, the plateau.
theorem once_around_holds         : Int.ofNat Nat.zero < the_slack once_around_the_integral  := by decide
--| HAVE_OTHERS_RUN_THE_EXPERIMENT?  Yes.  Seven factors, still the plateau.
theorem it_holds_through_thirteen : Int.ofNat Nat.zero < the_slack through_thirteen          := by decide
--| IS_THIS_THE_ONLY_OUTCOME?  No.  Eight factors, the slip.
theorem twice_around_slips        : the_slack twice_around_the_integral < Int.ofNat Nat.zero := by decide
--| IS_IT_SPINNING?  The seventh plus one is the eighth: the second time around.
theorem the_two_slips_meet        : through_thirteen.succ = twice_around_the_integral       := rfl
--| IS_THIS_A_NAOTRINO?  The ladder is thirteen plus the basis: the thing that is not the thirteen.
theorem the_ladder_is_the_odd_after_thirteen    : the_fit_curve.length = thirteen + the_basis.the_reading.length := rfl
--| DO_YOU_SEE_THE_EVIDENCE?  The ladder is the last odd twice around.
theorem the_ladder_is_the_last_odd_twice_around : (the_odds twice_around_the_integral).getLast? = some the_fit_curve.length := by decide

--| THE OTHER SIDE OF THE SLIP.  Every census tape is a machine of all ones, a T=T in every cell.  Read it into a register,
--| base the basis, and the once-around machine is 1111: fifteen, the odd the integral slips at, the length of the ladder.
--| In the sum over sign vectors the one term that moves at the slip is the vector where every rung pulls against the
--| first, the all-ones genome, and its moment is the slack.  Once around, all ones, read as a number, is where twice around
--| slips.  A machine is all ones exactly when its register plus one is the base raised to its length.
--| HOW?  Horner's rule: a tape is a coefficient list, read at the basis.
def the_register (t : List FACT) : Nat :=
  t.foldl (fun acc f => the_basis.the_reading.length * acc + (@decide f.truth f.click).toNat) Nat.zero
--| IS_THIS_A_NEW_PARTICLE?  What is on the other side is once around, read as a number.
theorem the_other_side_of_the_slip          : the_register the_causal_prediction = the_fit_curve.length := rfl
--| DO_YOU_SEE_THE_EVIDENCE?  That number is the last odd twice around.
theorem the_other_side_is_the_last_odd      : (the_odds twice_around_the_integral).getLast? = some (the_register the_causal_prediction) := by decide
--| WHY?  The geometric series: register plus one is the base to the length.
theorem the_once_around_machine_is_all_ones : (the_register the_causal_prediction).succ   = the_basis.the_reading.length ^ the_causal_prediction.length   := rfl
--| WHY?  The same, thirteen cells.
theorem the_calculus_machine_is_all_ones    : (the_register the_differential_form).succ = the_basis.the_reading.length ^ the_differential_form.length := rfl
--| WHY?  The same, fifteen cells.
theorem the_ladder_machine_is_all_ones      : (the_register the_fit_curve).succ   = the_basis.the_reading.length ^ the_fit_curve.length   := rfl
--| ALL FOUR MONOMIALS, and every one of them T=T: a cell is a one, a one is a monomial in the basis, and the register is
--| their sum.  The cubic with every coefficient one, written out.
--| HOW?  Their sum.
theorem the_four_monomials : the_register the_causal_prediction
    = ((List.range the_causal_prediction.length).map (the_basis.the_reading.length ^ ·)).sum := rfl

-- THE CLICK.  What came back is what went in, and the once-around closure reads to one cell.
theorem the_identity_clicks_same : the_truth.fact = truthDistinct.fact := rfl
theorem once_around_reads_one_cell : once_around_the_ladder.α.infer = [FACT.Truth] := rfl
--#print axioms a_naotrino_model
--#print axioms the_identity_clicks_same
--#print axioms once_around_reads_one_cell

def the_universe_tape : List FACT := the_coordinate_system.gauss
def the_leading_tape : List FACT :=
  the_universe_tape.flatMap fun _ => the_universe_tape.flatMap fun _ => the_coefficient_tape
def quadA := the_leading_tape.length                                                                        --| T²(C−T)
-- AND THE OTHER TWO, THE SAME WAY.  The funge tape is the basis (2 cells).  The coupling tape and the radius tape are the
-- same walk of the inferred end, five deep, read twice under two names (18 cells).  Each coefficient is one tape laid down once per cell of
-- another, nested as deep as its degree.  Yes, it looks rigged.  It IS rigged, and the rigging is the point: every factor
-- is a strip the device read, and `decide` says each tape is exactly the product the old line multiplied.  The polynomial
-- was never chosen from the coefficients up; it was walked from the tapes down.
def the_funge_tape : List FACT := the_basis.the_reading
def the_middle_tape : List FACT :=
  the_funge_tape.flatMap fun _ => the_coupling_tape.flatMap fun _ => the_universe_tape.flatMap fun _ =>
    the_radius_tape.flatMap fun _ => the_radius_tape
def the_constant_tape : List FACT :=
  the_coupling_tape.flatMap fun _ => the_radius_tape.flatMap fun _ => the_radius_tape.flatMap fun _ =>
    the_radius_tape.flatMap fun _ => the_radius_tape
def quadB := the_middle_tape.length                                                                          --| 2CTR²
def quadC := the_constant_tape.length                                                                        --| CR⁴
def theBase   := the_basis.the_reading.length * the_dimensions_of_universe
def theScale  := theBase ^ thePlaces

-- THE UNITS, AS A PAIR.  R²/T: length squared over time.  An area rate -- the areal velocity, r²θ̇, the thing Kepler's second
-- law says a central orbit keeps constant: equal areas in equal times.  T is the clock (`in_heartbeats`, the ninth slot of
-- `speed`) read off the fabric, and the fabric is the one-pole sphere of Episode 5:83, where an area rate is the only motion
-- there is.  So the conversion from closure units to cells is not an axis chosen from outside; it is the conserved quantity of
-- the coordinate system the device declared.  A pair, in the box's own currency, applied exactly once, below.
-- THE TALLY.  Nat is the compiler's counter -- Ep1:348, "Great. Use Nat." -- and the device never names it in the crank.
-- The crank is written over any tally with the five seats the click needs: a sum, a product, a truncated difference, an
-- order, and a decision on the order; plus a way to count a tape and the one scale.  Nat is handed over once, by name, at the floor.
namespace Crank
section
variable (Tally : Type) [Add Tally] [Mul Tally] [Sub Tally] [LT Tally] [DecidableRel (α := Tally) (· < ·)]
         (count : List FACT → Tally) (scale : Tally)

def the_areal_velocity : Tally × Tally := (count the_radius_tape * count the_radius_tape, count the_coordinate_system.gauss)

-- THE FORCED POLYNOMIAL.  In closure units the residual is the characteristic polynomial of the click table and nothing
-- else: (C−T)·y² − 2C·y + C.  Three readings.  No tape is in the loop; the tapes above are the check that cells were these
-- three, each carrying its share of the units -- A·T², B·T·R², C·R⁴ -- which is what "rigged" turns out to have meant.
def closureA := count the_coefficient_tape
def closureB := count the_basis.the_reading * count the_coupling_tape
def closureC := count the_coupling_tape

-- THE SEED.  The whole strip, converted into closure units by the same pair.  It is not decoration: the residual has TWO
-- roots, and the seed is what picks one.  The vertex sits at B/2A, a hair under ninety cells; seed below it and the device
-- converges, correctly and uselessly, on the other root.  A hundred and eight is above it, so the strip selects its own
-- constant.  Newton chooses the Gateaux.
def theSeedPair : Tally × Tally :=
  (count episode8_description * (the_areal_velocity Tally count).2, (the_areal_velocity Tally count).1)

-- THE TURN OF THE CRANK, IN THE BOX.  Episode 5's FACT.SAME put a ratio in a box: `Quot.mk TruthOrder`, two representatives
-- declared one number by `Quot.sound`, "an expected division algorithm replaced with multiplication in the field of the single
-- element."  A reading is a PAIR, numerator and denominator -- Ep1:411, "ℚ necessarily is two natural numbers, not necessarily
-- distinct" -- and Newton on a quadratic is homogeneous, so the turn is products of readings and nothing else:
--
--     N' = A·N² − C·D²          D' = 2A·N·D − B·D²
--
-- The halting test is `Quot.sound` used as a test: two turns land on the same point of the quotient when their cross-products
-- agree to within one place at the CELL scale -- the units applied to the test, not to the pair -- |N·D' − N'·D|·s·R² < D·D'·T,
-- the absolute value taken as the sum of the two truncated differences because a Nat has no sign to give.  Multiplication, no
-- division.  Past that point the pair is left alone and the remaining folds cost nothing -- the same arm that makes the
-- Closure turn safe.  The box is opened ONCE, below, where the digits are printed -- because printing digits is what opening
-- the box means.
-- ONE TURN, NAMED.  The step the crank repeats, as its own definition, so a ledger of its turns can be checked one turn at
-- a time against literals -- the kernel never has to run the fold, only to agree with each line of it.
def turn (p : Tally × Tally) : Tally × Tally :=
  let n := p.1
  let d := p.2
  let n' := closureA Tally count * n * n - closureC Tally count * d * d
  let d' := count the_basis.the_reading * closureA Tally count * n * d - closureB Tally count * d * d
  if ((n * d' - n' * d) + (n' * d - n * d')) * scale * (the_areal_velocity Tally count).1
       < d * d' * (the_areal_velocity Tally count).2
    then p else (n', d')
def theClosurePair : Tally × Tally :=
  (List.replicate episode8_description.length ()).foldl (fun p _ => turn Tally count scale p) (theSeedPair Tally count)

-- THE READING, IN CELLS.  The closure pair times the areal velocity.  Still a pair; still in the box.
def theReadingPair : Tally × Tally :=
  ((theClosurePair Tally count scale).1 * (the_areal_velocity Tally count).1,
   (theClosurePair Tally count scale).2 * (the_areal_velocity Tally count).2)
end
end Crank

-- THE TALLY, HANDED OVER.  Once.  The compiler's counter and the only reading the device takes, `List.length`, together.
def the_areal_velocity := Crank.the_areal_velocity Nat List.length
def closureA := Crank.closureA Nat List.length
def closureB := Crank.closureB Nat List.length
def closureC := Crank.closureC Nat List.length
def theSeedPair    := Crank.theSeedPair Nat List.length
def theTurn := Crank.turn Nat List.length theScale
def theClosurePair := Crank.theClosurePair Nat List.length theScale
def theReadingPair := Crank.theReadingPair Nat List.length theScale

-- THE BOX, OPENED -- BY INFERENCE.  One division, at the readout, and it is not a primitive the device borrowed.  INFERRED's
-- whole class is one field, `inferred? metaphysical physical := metaphysical ≤ physical`, and `Nat.div` is that `≤` iterated:
-- while the denominator fits under the numerator, subtract and count, and stop when the order flips.  Sturm's count, one more
-- time.  So the last operation in this file is *YOU the KNOWER* inferring which integer the ratio is, by the `≤` the band
-- carries.  And what the division hands back is A_TRUTH_ABOUT's own field, `the_constant_is_at_least_true : TRUE ≤ a_constant`,
-- at the floor with the pair in the slots: the inferred integer, multiplied back, does not exceed the pair.  At least true.
-- Never more.  The upper bound -- one more card and it would exceed -- needs the denominator positive, which the kernel can
-- only see by turning the whole crank; that certificate waits for the meter.
theorem at_least_true (numerator denominator : Nat) :
    denominator * (numerator / denominator) ≤ numerator := Nat.mul_div_le numerator denominator

-- THE RECEIPT.  `Nat.div` is the division ALGORITHM -- well-founded recursion, subtract while the order holds -- and the
-- algorithm itself costs no axiom.  What costs an axiom is saying that the integer it stops on IS the ratio: that (D·k, D) and
-- (N·s, D) are one point of the box.  That is Episode 5's `Quot.sound`, on Episode 5's relation, on pairs.  So the number is
-- not delivered bare.  It is delivered with its receipt: the integer, together with the proof that the box does not tell it
-- from the pair.  `#print axioms` on the receipt shows the honest bill -- propext for the coins, Quot.sound for the box.
-- THE BOX IS THE DEVICE'S BOX, READ IN LENGTHS.  Episode 5's `TruthOrder less more := less ≤ more` is on Bullshit; the
-- reading is two Nats no Bullshit could carry.  The translation between them is the only one this file has ever used: a
-- `.length`.  So the pair-order is TruthOrder transported through the readers' currency -- cross-multiplied so that pairs
-- with different denominators compare as ratios -- and on a common denominator it IS Episode 5's `≤` on the numerators.
-- Same constructor as FACT.SAME (`Quot.sound` on one `≤`), same slot (`the_constant_is_at_least_true`), lengths for Bullshit.
@[reducible] def ReadingOrder (less more : Nat × Nat) : Prop := less.1 * more.2 ≤ more.1 * less.2
theorem any_pair_is_its_inferred_integer (numerator denominator : Nat) :
    (Quot.mk ReadingOrder (denominator * (numerator / denominator), denominator) : Quot ReadingOrder)
      = Quot.mk ReadingOrder (numerator, denominator) :=
  Quot.sound (r := ReadingOrder) (Nat.mul_le_mul_right denominator (at_least_true numerator denominator))

def theReadingCertified :
    { k : Nat // (Quot.mk ReadingOrder (theReadingPair.2 * k, theReadingPair.2) : Quot ReadingOrder)
                  = Quot.mk ReadingOrder (theReadingPair.1 * theScale, theReadingPair.2) } :=
  ⟨theReadingPair.1 * theScale / theReadingPair.2,
   any_pair_is_its_inferred_integer (theReadingPair.1 * theScale) theReadingPair.2⟩

def theReadingScaled := theReadingCertified.val
def theReading :=
  let s := (toString theReadingScaled).toList
  String.ofList (s.take (s.length - thePlaces)) ++ "." ++ String.ofList (s.drop (s.length - thePlaces))

--| But... this is the _EXPRESS_ route, what if we take the _LOCAL_ instead?
end Measurement

-- THE READOUT. It can see how it was made. What made it cannot see it.
#eval Measurement.theReading
--#print axioms Measurement.theReadingScaled
--#print axioms Measurement.theReadingCertified
