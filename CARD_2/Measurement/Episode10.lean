/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the stories we tell ourselves are usually serialized with tokens on a page._

(c) 2026 Springer-Verlag

"Das ist nicht nur nicht richtig; es ist nicht einmal falsch!"
                                        -- The Pauli Exclusion Principle

"Due to the brevity of our life, we cannot afford the luxury of spending time on data which is not new or which is simply erroneous."
                                        -- Good advice from Landau about this entire project. This isn't new and could be simply erroneous.

lake build && pdflatex *.tex

__EPISODE 10__: _The Accomplice_

The *key* to getting people to take an interest is to have them contribute. Any reviewer of this pile has my sympathy as it says almost nothing in
lots and lots of words. In this case, I need *YOU the READER* to really understand how subtle the argument "rebut planted polynomial argument" changes
meaning throughout.

-/

-- REMINDER: This still skips episodes 8 and 6. The example construction was just that, an example. Something that can be called upon to provide
-- _intuition_ for any *READER* of the file. For publication, we need to strip the argument down to its baresst of bones. Thanks to a very
-- _cunning_ reviewer we can cull most of the deadweight necessary to explain _WHY_ the _POLYNOMIAL_ could _NOT_ have been planted.
import Measurement.Episode09
set_option allowUnsafeReducibility true

namespace Measurement

universe i

-- The publisher: the journal's template, the house style every rebuttal is set in.
namespace «springer-verlag»

--                                                                +-------------------+ This Nat is being supplied by the generosity and understanding
--                                                                |                   | of Springer-Verlag. They would never just publish a set of
--                                                                v                   | conference proceedings just because someone asked nicely. It
class REVIEWED (Box: Type i) (Pigeon: CarrierProcess Box) (page: Nat) where --        | takes at least _3_ people. As such, it stays within this
  rebuttal : ThePreprint --                                                           | namespace required by Springer to publish. I just needed a
--                 ^                                                                  | convenient way to _count_ _lifts_ of _cards_ and _universes_.
--                 |
--                 +---------------------+ Sorry if this metaphor beggars belief (If you are curious about begging questions, this is the _beg_ in
--                                       | _question_). Now watch as question after quesstion is begged by conclusions already provided. Except 1.

--| As e

--| We thank the reviewer for asking where to even start. Don't start here, this is just the argument that says there exists a place to start.
--|   Card 1: Corollary 6.1 (p. 34); Theorem 7.1 (p. 37); Proposition 2.6 (p. 9); eq. 1.1 (p. 2).
--|   Card 3: Table 6.1 (p. 44); Definition 8.1 (p. 57); Proposition 2.2 (p. 11); Theorem 2.4 (p. 19).
instance (priority := low) REVIEWER_2_ASKS_WHERE_THE_RECORD_BEGINS
    (Box: Type i) (Pigeon: CarrierProcess Box) --                        | For the reviewer, working backwards from the number, there should be
    (the_manuscript: ThePreprint) --                                     | roughly 3 dozen questions the reviewer can ask to find the start of the
    : REVIEWED Box Pigeon 36 := { rebuttal := the_manuscript }  ---------+ logic and get a foothold on how this works.


--| THE HOUSE STYLE.  Springer has provided a short-form rebuttal for simple and obvious gaps in the logic that need to be fixed. We thank the
--| the reviewer for providing an _order_ in which the _PRESENT_ argument can be _REPRESENTABLE_. What this constructs is an _AST_ that should
--| explain how Episode 7 was able to reach through the machine on line 610 to find the quarter under a mountain of cards. One _rung_ of the
--| scoping operator at a time. It just so happens that this decreases universe levels at a proportional rate to the associated universe levels of
--| page and next_page.
@[reducible] def rebut {Box: Type i} {Pigeon: CarrierProcess Box} {page next_page: Nat}
    (planted polynomial: FACT) (argument: REVIEWED Box Pigeon next_page)
    : REVIEWED Box Pigeon page :=
  { rebuttal := .methodology planted polynomial Box (ULift.{i+1, i} Box) argument.rebuttal }

--| If *YOU the READER* remember, we used definitions and instances to help the _COMPILER_ infer a _mostly complete_ device. The device used only
--| *CLASS inference*. _THEN_, in Episode 8, using only the _INDUCTIVE mechanism_ to describe the machine as a series of _Lists_ that can be used
--| to represent ℕ and a computation on those _Lists_ that allow for the clever use of _NAMES_ in _Lean_. Last episode, we made the _DEVICE_ one
--| more time! Then, in rpisode 9, we used the *STRUCTURE description* to create _YET ANOTHER COPY OF THE DEVICE_. What if I told *YOU the KNOWER* that
--| I can make the exact _SAME_ list machine as the _INDUCTIVEs_ using only _PrePrint_ and the _STRUCTURE description_?

--| I warned *YOU the KNOWER* at the very beginning: "Hold on lady, we go for ride." We start by actually inhabiting the types of Episode 7 instead of
--| inferring their definitions. Assume the device exists (a safe assumption since the device compiles with no warnings). And since we can assume the
--| device exists, we can assume that the [nowtrino: DISTINGUISHABLE Box Pigeon] exists and use that fact to reconstruct the machine of Episode 7 and
--| _number_ each construction with a PrePrint page number as we go. Again, thanks to Springer for providing us some Natural numbers here. 36 is fine,
--| we counted to 137011290548979457087737300 in episode 8. Assuming digits of numbers exist. Which we do not demonstrate in the device. That is not
--| a requirement for proof. Springer has demonstrated the numbers exist by the fact you can turn the page and watch them go up or down, depending on
--| direction, language, and style (like the biggest difference between manga and comics). Isomorphic to the right area of ℕ allowing extrapolation to
--| arbitrary _n∈ℕ_.
section the_checklist
variable (Box: Type i) (Pigeon: CarrierProcess Box)
--| First, the inferred definitions of Episode 7, named where necessary for the argument:
   [nowtrino: DISTINGUISHABLE Box Pigeon]

--| This is the _KEY PART_. Instead of waiting to ask, in the language of the devicec, if the nowtrino takes up space, we _ASSUME_ it does
--| _FROM THE START_. It _turns out_, if you assume that the _NAOTRINO_ takes up space and cannot have a _0 volume_, then the device can _describe_
--| _QUANTUM ELECTRODYNAMICS_ exactly as derived Yang and Mills. If, on the other hand, you assume that the _NAOTRINO ORBITAL_ has volume but the
--| the _NOWTRINO_ itself does _NOT_ then a formulation of the field equations arises in the unit units during the demonstration of the device.

--| The device doesn't change (T=T always), just the words to describe it. Here's how to plant a polynomial into a discretized approximation of a
--| Hilbert space:

--| **************************************************************************************************************************************************
--| **************************************************************************************************************************************************

   [Inhabited nowtrino.symbol] --         |  ***** *   * *****      *   * ***** *   *      ****   ***  ****  *****
--     ^              ^                   |    *   *   * *          *  *  *      * *       *   * *   * *   *   *
--     |              |                   |    *   ***** ***        **    ***     *        ****  ***** ****    *
--     +----------------------------------|    *   *   * *          *  *  *       *        *     *   * *   *   *
--                                        |    *   *   * *****      *   * *****   *        *     *   * *   *   *

--| **************************************************************************************************************************************************
--| **************************************************************************************************************************************************

--|                             The concept of "Assume The Mathematical Representation of the NOWTRINO" exists as a description ∎.

--| I think *YOU the READER* only need this to compile to see that this is a true statement at this point. Allow me to demonstrate. Given that
--| the concept exists, we can now provide the rest of the description of the device constructed in episode 7 as following immediately from the fact
--| the concept exists:
   [flying_spaghetti_monster: REAL Box Pigeon] [naotrino: LOCAL Box Pigeon] [commuter_pass: UNIVERSAL Box Pigeon naotrino]
   [LOGICAL Box Pigeon naotrino commuter_pass] [HALTED Box Pigeon naotrino commuter_pass] [MEASURED Box Pigeon naotrino commuter_pass]
   [stdout: COMPILED Box Pigeon naotrino commuter_pass] [A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass] [INFERRED Box Pigeon naotrino commuter_pass]
   (the_deck: CarrierProcess Box) (ledger: FACT) (something: DISTINGUISHABLE Box Pigeon) (something_with_momentum: ADMISSIBLE Box Pigeon)
   (cascade_of_particles: COUNTABLE Box Pigeon) (click: ENCODED Box Pigeon) (pit: RESIDUE Box Pigeon) (binary: BINARY Box Pigeon)
   (procedure: REPEATABLE Box Pigeon) (how_many_clicks: NUMERIC Box Pigeon) (csv_file: REPRESENTABLE Box Pigeon) (timeseries: PHYSICAL Box Pigeon)
   (relative_value: COMPARABLE Box Pigeon) (motion: OBSERVED Box Pigeon) (just_now: PRESENT Box Pigeon) (timestamp: MEASURABLE Box Pigeon)
   (cannot_be_ignored: GUNGAN Box Pigeon) (the_machine_that_goes_ping: SOURCE Box Pigeon) (plots_and_graphs: EXECUTED Box Pigeon)
   (a_constant: VALUE Box Pigeon) (extraordinary: MAGNITUDE Box Pigeon) (projection: SCALED Box Pigeon) (fem_solver: LOAD Box Pigeon)
   (the_simplex: OF Box Pigeon) (pages_of_derivations: BULLSHIT Box Pigeon) (propaganda: PROPAGANDA Box Pigeon) (professor: ACOLYTE Box Pigeon)
   (new_physical_law: SCIENTIFIC Box Pigeon) (curve_fit: TRUTH Box Pigeon) (obvious_pattern: WITNESSED Box Pigeon)
   (inverse_square_law: REAL Box Pigeon) (downhill: LOCAL Box Pigeon) (extremum: UNIVERSAL Box Pigeon downhill)
   (logical: LOGICAL Box Pigeon downhill extremum) (halted: HALTED Box Pigeon downhill extremum)
   (a_small_number: MEASURED Box Pigeon downhill extremum) (iterative_solver: COMPILED Box Pigeon downhill extremum)
   (a_truth_about: A_TRUTH_ABOUT Box Pigeon downhill extremum)
include Box Pigeon nowtrino flying_spaghetti_monster naotrino commuter_pass stdout the_deck ledger something
   something_with_momentum cascade_of_particles click pit binary procedure how_many_clicks csv_file
   timeseries relative_value motion just_now timestamp cannot_be_ignored the_machine_that_goes_ping
   plots_and_graphs a_constant extraordinary projection fem_solver the_simplex pages_of_derivations
   propaganda professor new_physical_law curve_fit obvious_pattern inverse_square_law downhill extremum
   logical halted a_small_number iterative_solver a_truth_about



instance (priority := low) REVIEWER_2_ASKS_WHAT_THE_ANSWER_WAS_ANSWERING? -- | So, we start by *ASSUMING* we can answer the 36th argument by just
    [argument: REVIEWED Box Pigeon 36] --                                    | looking at the ledger of something.fact. If I am interpreting this
    : REVIEWED Box Pigeon 35 := --                                           | coeectly, and I believe I am, the answer to the 36th question is that
    rebut ledger something.fact argument ------------------------------------+ we are building the symbol of the *NAOTRINO*.
--| See:   Card 1: Proposition 5.4 (p. 28); Section 1.2 (p. 1); Section 6.5 (p. 33).
--|        Card 3: eq. 6.9 (p. 45); Section 6.4 (p. 45); Section 6.1 (p. 41); Section 7.5 (p. 53).

--| Everything follows directly from the same argument: assume the previous critique was answered, then use that answer to show that another assumption
--| must be made giving the next question.

instance (priority := low) REVIEWER_2_ASSERTS_COMPILING_IS_NOT_EVIDENCE_OF_THE_DESCRIPTION_OF_TWO_DIFFERENT_THINGS
    [argument: REVIEWED Box Pigeon 35]
    : REVIEWED Box Pigeon 34 :=
    let planted : FACT := match stdout.a_demonstration_of_a_constant with
      | .introduction t _ => t
      | .methodology t _ _ _ _ => t
      | .results t _ _ _ _ _ _ => t
    let polynomial : FACT := match iterative_solver.a_demonstration_of_a_constant with
      | .introduction f _ => f --          | We start this argument with the assumption that we can settle *REVIEWED Box Pigeon 36*. That card is
      | .methodology f _ _ _ _ => f --     | _thrown_, never to be _lifted_ again. If that were true, then we could define a symbol that indicated
      | .results f _ _ _ _ _ _ => f --     | the _FACT_ that these are the _SAME_ or _DIFFERENT_ without having to evaluate them again. They are
    rebut planted polynomial argument -----+ the _SAME_ when _t=f_ *OR* _f=t_. Just assuming *YOU the KNOWER* think I am clever enough to _plant_ the
--                                         | polynomial.
--| See:   Card 1: Theorem 7.1 (p. 37); Section 6.7 (p. 35); Section 7.2 (p. 38); Appendix A (p. 55).
--|        Card 3: Section 7.4 (p. 52); Section 6.8 (p. 48); Section 7.7 (p. 54).

instance (priority := low) REVIEWER_2_ASSERTS_THAT_BOTH_SIDES_ARE_IDENTICAL
    (velocity_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 34]
    : REVIEWED Box Pigeon 33 :=
    let planted : FACT := velocity_fact_on_file
    let polynomial : FACT := match a_small_number.a_distance.in_heartbeats with
      | .origin f _ _ => f --                                               | This example makes it obvious that the same computation is definitely
      | .distance_to f _ _ _ _ _ => f --                                    | _NOT_ running on *PLANTED* than on *POLYNOMIAL*. The _PLANTED_ answer
      | .speed f _ _ _ _ _ _ _ _ => f --                                    | is the _QUARTER_ glued to the table. The polynomial is an honest to
    rebut planted polynomial argument --------------------------------------+ goodness interpreted _FACT_ about the device itself.
--| See:   Card 1: Proposition 2.5 (p. 8); Section 2.2 (p. 7); Section 4.6 (p. 23).
--|        Card 3: Section 7.7 (p. 54); Section 6.8 (p. 48).

instance (priority := low) REVIEWER_2_ASSERTS_THERE_IS_EVIDENCE_OF_DECEPTION
    (the_route_submitted: SpaceTimePath) --                      | The rebuttal process just demonstrates that the *FACT* of *matter* is the only
    (the_route_taken: SpaceTimePath) --                          | thing that matters. All _other_ arguments _CAN BE IGNORED_. _EVIDENCE_ cannot.
    [argument: REVIEWED Box Pigeon 33] --                        | Given a demonstration of an effect that is _CONTRAFACTUAL_ to _ANY_ model of the
    : REVIEWED Box Pigeon 32 := --                               | _UNIVERSE_ **HAS YET TO** invalidate any of the _OBVIOUS CAUSAL EFFECTS_ of that
    let planted : FACT := match the_route_submitted with --      | very demonstration.
      | .einstein t => t --                                      |
      | .whitehole t _ _ => t --                                 | That also does _NOT_ mean the model is invalid either. One is the _FACT_ of _MATTER_
      | .geodesic t _ _ _ _ _ => t --                            | and the other is the _TRUTH_ of the _matter_. There is _TRUTH_ in Newton's law of
      | .blackhole _ _ _ => Pigeon.symbol --                     | gravity, Bohr's model of the atom, or even Aristotle's model of the atom. These
    let polynomial : FACT := match the_route_taken with --       | ideas come with fudge factors like "thought experiment" and "particles" and
      | .einstein f => f --                                      | "the Einstein field equations." That they give different answers is expected. That
      | .whitehole f _ _ => f --                                 | they give the same "answer" is also expected.
      | .geodesic f _ _ _ _ _ => f --                            |
      | .blackhole _ _ _ => Pigeon.symbol --                     | So, we assume we can call Pigeon.symbol that which is _NOT_ T or F and interpreted
    rebut planted polynomial argument ---------------------------+ as a "FACT" of the universe: both the force of gravity and "the force of gravity."
--| See:   Card 1: eq. 5.2 (p. 27); Section 6.1 (p. 30); Section 6.5 (p. 33).
--|        Card 3: Table 6.1 (p. 44); Proposition 6.1 (p. 42); Figure 6.1 (p. 44); Section 4.8 (p. 33).

instance (priority := low) REVIEWER_2_ASSERTS_THE_COMPILER_CANNOT_TELL_THE_SYMBOLS_APART
    [argument: REVIEWED Box Pigeon 32]
    : REVIEWED Box Pigeon 31 := --                    | Correct. To the compiler, the "force of gravity" as described by Einstein and the "force of
    rebut Pigeon.symbol Pigeon.symbol argument -------+ gravity" _intuited_ by Newton _ARE_ the same thing. TBF, it is hard for me to draw a distinction.
--| See:   Card 1: Proposition 4.2 (p. 19); Section 4.2 (p. 19); Section 3.4 (p. 15).
--|        Card 3: Section 7.7 (p. 54).

--| Here we find ourselves at the RFL of (T=F)=(F=T). *YOU the KNOWER* still know how to *RFL*, right? I would like to interpret this comment as
--| the '=' between two _key parts_ of the AST, both counterfactual understandings of how the device works: by planted polynomial and by physics
--| alone. Wouldn't it be _neat_ if *YOU the READER* thought these were the same thing and *YOU the KNOWER* only knew _one_ to be _true_?

--| **************************************************************************************************************************************************
--| **************************************************************************************************************************************************
--|                                                           *   * ***** *   * *****
--|                                                           *   *   *   **  *   *     *
--|                                                           *****   *   *  **   *
--|                                                           *   *   *   *   *   *     *
--|                                                           *   * ***** *   *   *
--|
--|             This is something that *YOU the READER* **CANNOT** understand _ALONE_ and _I_ *CANNOT* demonstrate to *YOU the KNOWER*:
--|                                         that the code is bug free and proves something false to *YOU the KNOWER* ∎.
--| **************************************************************************************************************************************************
--| **************************************************************************************************************************************************

instance (priority := low) REVIEWER_2_ASSERTS_THE_COMPILER_MEANING_IS_THE_SAME
    [argument: REVIEWED Box Pigeon 31]
    : REVIEWED Box Pigeon 30 :=
    rebut Pigeon.symbol Pigeon.symbol argument
--| See:   Card 1: Section 4.1 (p. 18); Section 1.1 (p. 1); Section 7.3 (p. 38).
--|        Card 3: Proposition 3.1 (p. 23); Proposition 2.2 (p. 11); Section 5.2 (p. 36); Section 5.4 (p. 38).

--| https://www.youtube.com/watch?v=l7NZwqG8yfQ
--| https://www.youtube.com/watch?v=d0ObevuYpQc

instance (priority := low) REVIEWER_2_UNDERSTANDS_THEY_DESCRIBE_THE_SAME_DEVICE
    [argument: REVIEWED Box Pigeon 30]
    : REVIEWED Box Pigeon 29 :=
    let planted : FACT := match flying_spaghetti_monster.nagging_doubt with  --                  | What do *YOU the KNOWER* _know_ to be *TRUE*
      | .logically _ => Pigeon.symbol --                                                         | versus what do *YOU the KNOWER* _know_ to be
      | .but the_model_says _ _ => (match the_model_says with --                                 | _DEMONSTRABLY TRUE_? What is _believed_ versus
        | .the_proof _ => Pigeon.symbol --                                                       | what is _shown_. Euclid's fifth postulate lives
        | .we_understand_that the_device_only_knows _ _ => (match the_device_only_knows with --  | here. ℝιemann spoke at length about what can be
          | .jarjar _ => Pigeon.symbol --                                                        | _SHOWN TRUE_ if only it were possible to
          | .ledger _ t _ => t)) --                                                              | _BELIEVE LESS_.
    let polynomial : FACT := match inverse_square_law.nagging_doubt with  --                     |
      | .logically _ => Pigeon.symbol --                                                         | In this case, what one side sees as _Knowledge_---
      | .but the_device_only_knows _ _ => (match the_device_only_knows with --                   | learnable, demomstrable--the _other_ sees as
        | .the_proof _ => Pigeon.symbol --                                                       | _Gospel_. In all three cases, we find the
        | .we_understand_that the_model_says _ _ => (match the_model_says with --                | Pigeon.symbol of either T or F.
          | .jarjar _ => Pigeon.symbol --                                                        |
          | .ledger _ f _ => f)) --                                                              | Or, just a half a second's thought and *YOU the KNOWER*
    rebut planted polynomial argument -----------------------------------------------------------+ just might see the automation at work.
--| See:   Card 1: Section 7.2 (p. 38); Section 6.4 (p. 32); Section 5.7 (p. 29).
--|        Card 3: Section 3.6 (p. 25); Section 7.3 (p. 52).

instance (priority := low) REVIEWER_2_ASSERTS_THERE_ISNT_A_RELATIVISTIC_TRANSFORMATION_OF_VELOCITY_BASED_ON_DISTANCE_FROM_OBSERVER
    (yet: WITNESSED Box Pigeon)
    [argument: REVIEWED Box Pigeon 29]
    : REVIEWED Box Pigeon 28 :=
    let planted : FACT := match yet.the_experiment with --                                        | I know. But what if there _were_? What if there
      | .the_proof _ => Pigeon.symbol --                                                          | are _two_ different points that _share_ a
      | .we_understand_that this_is_what_a_fact_is _ _ => (match this_is_what_a_fact_is with --   | _reference_ frame at a required distance? _THEN_
        | .jarjar _ => Pigeon.symbol --                                                           | using the _MEAN VALUE THEOREM_, we would be
        | .ledger _ t _ => t) --                                                                  | able to demonstrate that one could exist. I think
    let polynomial : FACT := match obvious_pattern.the_experiment with --                         | there is evidence of this, it just isn't Lorentzian.
      | .the_proof _ => Pigeon.symbol --                                                          |
      | .we_understand_that this_is_what_a_proof_is _ _ => (match this_is_what_a_proof_is with -- | But that's the automation working. It's build to
        | .jarjar _ => Pigeon.symbol --                                                           | regurgitate FACTs: a _symbol_ (either T/F) and
        | .ledger _ f _ => f) --                                                                  | a proof (only TRUE but *stored* so it could be
    rebut planted polynomial argument ------------------------------------------------------------+ FALSE).
--| See:   Card 1: Table 4.1 (p. 20); Section 3.3 (p. 13); Section 6.3 (p. 32).
--|        Card 3: Section 5.5 (p. 39); Section 5.1 (p. 35).

instance (priority := low) REVIEWER_2_DEMANDS_CONSISTENCY_WITH_EVIDENCE
    (knowledge_fact_on_file: FACT) --                                       | At the risk of overcomplicating orbital dynamics, rotation curves---and
    [argument: REVIEWED Box Pigeon 28] --                                   | other high precision measurements at the extremes of science---often
    : REVIEWED Box Pigeon 27 := --                                          | require calibrating to extrapolated behaviors under fairly unrealistic
    let planted : FACT := knowledge_fact_on_file --                         | scaling assumptions. Relativity requires a round trip photon to work.
    let polynomial : FACT := match curve_fit.becomes.knowledge with  --     | Round-tripping a photon between three places far apart leads to, well,
      | .jarjar _ => Pigeon.symbol --                                       | paradoxes according to a fourth observer, even really close by.
      | .ledger _ f _ => f --                                               |
    rebut planted polynomial argument --------------------------------------+ Relativity only _suggests_ what would happen if the photon were one way.
--                                                                          | Like the Heisenberg uncertainty scaled to take into account wavelength
--                                                                          | interactions around blackholes.
--| See:   Card 1: Proposition 5.4 (p. 28); Theorem 7.1 (p. 37); Section 5.6 (p. 28); Section 3.4 (p. 15).
--|        Card 3: Section 6.4 (p. 45); Section 3.7 (p. 25).

instance (priority := low) REVIEWER_2_REQUIRES_A_CONSISTENT_LAW_THAT_EXPLAINS_WHAT_WE_SEE
    (experiment: SCIENTIFIC Box Pigeon)
    [argument: REVIEWED Box Pigeon 27] --                                    | The way the automation works is by understanding how the arguments
    : REVIEWED Box Pigeon 26 := --                                           | _work_. It isn't that the contents of the arguments matter, just
    let planted : FACT := match experiment.invariant with --                 | _HOW MANY_ and _IN WHAT ORDER_. The *inductives* are merely
      | .repeatable _ => Pigeon.symbol --                                    | _interpretations_ of the _symbol_. Something that is *.repeatable*
      | .hypothesis _ _ => Pigeon.symbol --                                  | counts one and returns a *Pigeon.symbol*. Something that is a
      | .theory _ _ t _ => t --                                              | *.hypothesis* counts _two_ things and gives a *Pigeon.symbol*.
    let polynomial : FACT := match new_physical_law.invariant with --        | Meanwhile, the validity of the _theory_ can be seen in the _third_
      | .repeatable _ => Pigeon.symbol --                                    | field of _four_.
      | .hypothesis _ _ => Pigeon.symbol --                                  |
      | .theory _ _ f _ => f --                                              | In this way, we can convince the compiler to hold _two meanings_ for
    rebut planted polynomial argument ---------------------------------------+ the _same symbol_. A _place_ to *monkey patch* _math_ if we need.
--                                                                           | That's what *YOU the READER* see.
--| See:   Card 1: Proposition 5.1 (p. 24); Section 5.3 (p. 26); Section 6.6 (p. 34).
--|        Card 3: eq. 3.2 (p. 22); Section 3.2 (p. 22); Section 3.3 (p. 23); Section 6.5 (p. 46).

instance (priority := low) REVIEWER_2_REQUIRES_THE_LAW_SURVIVE_GEOMETRIC_INTERPRETATION
    (cult_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 26] --                                | This is the train of thought. *GEOMETRIC INTERPRETATION.* Can we find a
    : REVIEWED Box Pigeon 25 := --                                       | _triangle inequality_ that the description defines? If yes, then we have
    let planted : FACT := cult_fact_on_file --                           | a _Pythagorean-like_ ruler made floppy by ℝιemann. The _FACT_ on _FILE_
    let polynomial : FACT := match professor.euclid.sacred_texts with -- | merely _represents_ a _norm_-like function of two arguments, numbered here
      | .inside_joke   _ => Pigeon.symbol --                             | as #25.
      | .pythagoras  _ _ _ => Pigeon.symbol --                           |
      | .triangles _ _ f _ _ => f --                                     | Basically, we can _interpret_ the _f_ as whether or not the two arguments
    rebut planted polynomial argument -----------------------------------+ before are in a triangle-like situation with the two on the right.
--| See:   Card 1: Corollary 6.1 (p. 34); Section 6.4 (p. 32).
--|        Card 3: eq. 7.1 (p. 51); Section 3.7 (p. 25).

instance (priority := low) REVIEWER_2_ASKS_WHAT_IS_THE_MEANING_OF_SYMBOLS_IN_ORDER?
    [argument: REVIEWED Box Pigeon 25] --                | The only meaning to the order is the one the device provides. Covariantly when counting
    : REVIEWED Box Pigeon 24 := --                       | upward and contravariantly when breaking off chuncks. The question is does this represent
    rebut Pigeon.symbol Pigeon.symbol argument ----------+ placing a symbol on the page that _means_ something? Not the argument, the _symbol_.
--| See:   Card 1: Table 2.1 (p. 6); Section 2.1 (p. 5); Section 1.4 (p. 3); Appendix A (p. 55).
--|        Card 3: Section 6.8 (p. 48); Section 7.2 (p. 51).


instance (priority := low) REVIEWER_2_SUSPECTS_INADEQUACY_IN_THE_NAMING_OF_OBJECTS
    (spline_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 24]
    : REVIEWED Box Pigeon 23 := --                                                        | As the names of the arguments (and accompanying lengthy
    let planted : FACT := spline_fact_on_file --                                          | PDFs) suggest, the object can most certainly be modeled
    let polynomial : FACT := match pages_of_derivations.arm_wave_process.guess with --    | as a polynomial, at least 2 _different_ kinds. This is
      | .observation     _ => Pigeon.symbol --                                            | a standard modeling technique in science, selecting one
      | .knot          _ _ _ => Pigeon.symbol --                                          | or the other, to describe the phenomenon presented. I
      | .interpolant f _ _ _ _ => f --                                                    | state *YOU the READER's* case: there is no difference in
    rebut planted polynomial argument ----------------------------------------------------+ the truth of the argument of planting the polynomial's value.
--| See:   Card 1: Section 5.7 (p. 29).
--|        Card 3: eq. 3.4 (p. 23); Section 3.3 (p. 23); Section 1.6 (p. 6).

--| The only difference between an interpolant and a triangle is the location of the _FACT_. If the _FACT_ is the _length_ of the hypotenuse, then
--| it is _TRIANGULAR_. If the _FACT_ is the _area_ of the triangle, then it is interpolated and flatness is indicated. The _DEFINITION_ of _FLAT_
--| is the _INTERPOLATION_ is _EXACT_.

instance (priority := low) REVIEWER_2_ASKS_TO_DESCRIBE_THE_POLYNOMIAL_OF_THE_DEVICE_OF_THE_POLYNOMIAL
    (polynomial_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 23]
    : REVIEWED Box Pigeon 22 := --                                                           | But, 5 things? We have to keep track of 5 things? No,
    let planted : FACT := polynomial_fact_on_file --                                         | only 4 and a property. REMEMBER THIS, the device only
    let polynomial : FACT := match the_simplex.galerkin_process.polynomial with --           | ever sees 4 things and a property at a time at most.
      | .constant f => f --                                                                  | Other times, it only sees 2 or 3 things. The key is
      | .monomial _ _ => Pigeon.symbol --                                                    | _successive application_ of the device to itself, have
      | .factor f _ _ _ => f --                                                              | it compile, while it compiles, while it compiles, etc.
    rebut planted polynomial argument -------------------------------------------------------+ Each argument is a small compilation process.
--| See:   Card 1: Section 4.4 (p. 21); Section 4.5 (p. 22); Section 5.4 (p. 27).
--|        Card 3: Proposition 2.3 (p. 15); eq. 3.5 (p. 24); Section 3.5 (p. 24); Section 2.3 (p. 14).

--| This should be a bit easier to see using the geometric interpretation. A triangle area is given by a quadratic equation. There are two factors
--| in a quadratic: ( T _ _ _ ) and ( F _ _ _ ).  Since the arguments do not matter we can start to build a triangle as _two factors_:
--|  ( T F _ _ _ ) for the first FACTOR ( T F _ _ ).  We know that _ _ is a monomial: Pigeon.symbol. Hence, the first _FACTOR_ of the _AREA_ of the
--| _TRIANGLE_ is that (T F Pigeon.symbol) (an interpretation of T F _ _ that matches the matches above). Placing a _FACT_ between T F and
--| Pigeon.symbol gives the _.triangle_ to be ( T F (FACT) Pigeon.symbol ). If that FACT is the FACT.Truth, then the .triangle is just a geometric
--| interpretation of that _FACT_.

instance (priority := low) REVIEWER_2_WARNS_OF_EXTRAPOLATION_PITFALLS
    (basis_fact_on_file: FACT) --                                              | The polynomial as a _vector space_ prevents the existence of
    [argument: REVIEWED Box Pigeon 22] --                                      | _ANOTHER_ polynomial that is _EXACTLY_ the _SAME_. If the .triangle
    : REVIEWED Box Pigeon 21 := --                                             | is _flat_, there can be no other _polynomial_ to describe it. *BUT*
    let planted : FACT := basis_fact_on_file --                                | if the .triangle is _not flat_, then a function can be made to
    let polynomial : FACT := match fem_solver.basic_operation.span with --     | compute the area of the triangle making the null space a fact.
      | .null_space f => f --                                                  |
      | .origin _ _ => Pigeon.symbol --                                        | That function doesn't need to be thought of as a Stokes integral,
      | .basis f _ _ _ => f --                                                 | but that would certainly help the geometric interpretation. This
    rebut planted polynomial argument -----------------------------------------+ allows repeated application of *.basis vectors* beyond one triangle.
--| See:   Card 1: Theorem 5.3 (p. 26); eq. 4.2 (p. 22); Section 4.5 (p. 22); Section 5.2 (p. 25).
--|        Card 3: Section 4.7 (p. 32); Section 1.6 (p. 6); Section 4.4 (p. 29).

instance (priority := low) REVIEWER_2_REQUIRES_SCALE_FOR_AREA_TO_RECONCILE_MULTIPLICATION
    (product_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 21] --                                                | In this case, if .one is the interpretation of the
    : REVIEWED Box Pigeon 20 := --                                                       | Pigeon.symbol, then we have found a _direction_ we can
    let planted : FACT := product_fact_on_file --                                        | travel: up or down. The thing is, this only works on the
    let polynomial : FACT := match projection.multiplying_process.product with --        | _projection_ of one polynomial onto another. Do we make
      | .origin f => f --                                                                | this go one way, like ordered pairs, or the other way
      | .one _ _ => Pigeon.symbol --                                                     | like the Argand plane? Either way, the origin is a FACT.
      | .mul f _ _ _ => f --                                                             |
    rebut planted polynomial argument ---------------------------------------------------+ For some reason, this interpretation is also .triangular
--| See:   Card 1: Section 2.5 (p. 10); Section 2.5.1 (p. 11); Section 5.2 (p. 25).
--|        Card 3: eq. 6.2 (p. 41); Section 6.1 (p. 41); Section 3.1 (p. 21).

instance (priority := low) REVIEWER_2_ASKS_WHATS_THE_FOURTH_THING?
    (sum_fact_on_file: FACT) --                                             | I see *YOU the READER* are asking about the _four_ interpretations of
    [argument: REVIEWED Box Pigeon 20] --                                   | _i_ given in Episode 1. So, the fourth thing is quarternions, of course.
    : REVIEWED Box Pigeon 19 := --                                          | Without quarternions, one cannot model a spinor which means one cannot
    let planted : FACT := sum_fact_on_file --                               | model an electron which means our stand-in for the electron nowtrino
    let polynomial : FACT := match extraordinary.adding_process.sum with -- | cannot be modeled by the Naotrino which would imply our model of the
      | .zero _ _ => Pigeon.symbol --                                       | Naotrino is incorrect and the device would fail to _compile._
      | .add f _ _ _ => f --                                                |
    rebut planted polynomial argument --------------------------------------+ The fourth thing is the roundabout argument needed to close the loop
--                                                                          | added at the end. See: https://imgflip.com/i/b58rur. No FACT to identify.
--| See:   Card 1: eq. 5.2 (p. 27); eq. 6.4 (p. 34); Section 5.5 (p. 27); Section 6.7 (p. 35).
--|        Card 3: Table 7.1 (p. 52); eq. 3.6 (p. 25); eq. 3.7 (p. 25).

instance (priority := low) REVIEWER_2_POINTS_OUT_THE_OBVIOUS_FACTS
    (uncountable: VALUE Box Pigeon)
    [argument: REVIEWED Box Pigeon 19]
    : REVIEWED Box Pigeon 18 :=
    let planted : FACT := match uncountable.monad with --         | The obvious fact is we are trying to justify the representation of an incomputable
      | .satire_about t => t --                                   | number by claiming the compiler cannot tell the difference between that and the
      | .compile      t _ _ => t --                               | idea of being able to compare that number to others. Hence, the _acres and acres_
      | .execute      t _ _ => t --                               | of code dedicated to the ordering of objects.
    let polynomial : FACT := match a_constant.monad with --       |
      | .satire_about f => f --                                   | If the compiler can be shown to _accurately_ compare against the incomputable
      | .compile      f _ _ => f --                               | number while not relying on the number itself. It either computes the number and
      | .execute      f _ _ => f --                               | compares _OR_ it can compute relative output change from input change to some
    rebut planted polynomial argument ----------------------------+ meaningful degree. To the compiler, these are the same: compiling and executing.
--| See:   Card 1: Section 3.5 (p. 16); Section 6.1 (p. 30).
--|        Card 3: Section 6.5 (p. 46); Section 6.8 (p. 48).

--| Compile and execute are, well, too grand a set of words for what Lean is doing. It is merely _lexing_ and _elaborating_. I hope *YOU the KNOWER*
--| will forgive me this little generalization. And we have just shown the compiler that the same _concept_ of _two arguments_ can be called one
--| of _four_ different things, depending also on if the _polynomial_ or _planted_ is *believed* to hold the secret.

instance (priority := low) REVIEWER_2_NOTICES_THE_FENCEPOSTS
    (opcode_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 18]
    : REVIEWED Box Pigeon 17 := --                                                   | These three arms describe a Yarn about the compilation
    let planted : FACT := opcode_fact_on_file --                                     | process. *YOU the KNOWER* are aware before the compile starts
    let polynomial : FACT := match plots_and_graphs.compiled_process.opcodes with -- | at _.boot_.  Then _.zero_ is during compile the device is
      | .boot f _ => f --                                                            | _spinning_ looking for solutions. _.one_ has found a
      | .zero f _ _ => f --                                                          | solution in the second two arguments. But this isn't a
      | .one f _ _ _ _ => f --                                                       | _TRIANGULAR_ _INTERPRETATION_, this is an _INTERPOLATED_
    rebut planted polynomial argument -----------------------------------------------+ _INTERPRETATION_ by the device and remains hidden under a card.
--| See:   Card 1: Section 3.5 (p. 16); Section 5.5 (p. 27); Section 6.1 (p. 30).
--|        Card 3: Section 6.3 (p. 43); Section 6.8 (p. 48).

--| So, we now agree with the compiler that _.one_ encodes an _INTERPOLATION_ _interpretation_ _BETWEEN_ the _FOUR_ arguments. A _cubic polynomial_
--| with the _x_ coordinates encoded by argument number and the _y_ coordinates encoded by T/F → ¹/₀ or T/F → ⁰/₁ or T/F → ¹/∞. Whatever numerical value
--| *YOU the KNOWER* want to take _.zero_ and _.one_.

--| For an _INTERPOLATION_ _intepretation_ to be _TRIANGULAR_ and, therefore, representative of the continuous space Euclid scales and shifts
--| triangles in, one of two things _MUST BE TRUE_ on the _TAPE_:
--|                                                         ( T _ T _ _ ) or ( F _ F _ _ )
--| If the _area_ is a _REAL_ _flat area_ and not an _IMAGINARY_ _wrinkled area_ created by a folded triangle, then that leaves, again one of two
--| things _MUST BE TRUE_ on the _TAPE_:
--|                                                         ( T T T _ _ ) or ( F F F _ _ )
--| So, in order to either _BE FLAT_ (T) or _APPEAR FLAT_ (F), triangles have 180ᵒ and their _area_ is always bh/2. I submit that the two unknown
--| arguments here are exactly those concepts expresssed as a binary operator: ||b×h||₂ = ||b||₂ ||h||₂ sin θ. This is the Pigeon.symbol. The fact
--| that _b_ and _h_ have to be base and height in the area formula is the idea of the projection and that is the only thing ever checked. It also
--| happens _TO BE TRUE_ that the cross product identity holds. This is a representative of the Pigeon.symbol _carrier_.  The Pigeon.symbol here means
--| T=T. The _carrier_ describes the symbol we can use to express the concept that trinagles have 180ᵒ and their _area_ is always bh/2. It wouldn't be
--| _true_ otherwise and since it _is_ _TRUE_, Lean can use _TRUE_ to represent it. And that is what we all agree on. When Lean sees _TRUE_, it is
--| either a _TRUTH *BEYOND* DEMONSTRATION_ or it is merely an _INTERPOLATION_ of the fact that flat space and _apparently_ flat space look exactly
--| the same when measured with orthogonal rulers. Otherwise, the _difference_ would be _apparent_ _TO ALL READERS AND KNOWERS_ as _COHERENT NOISE_
--| described as _HIGH ORDER TERMS_ that can be decomposed quite efficiently into wave forms or times, take *YOU the KNOWER's* pick.

instance (priority := low) REVIEWER_2_REFUSES_TO_ENTERTAIN_ABSURD_SOURCES_OF_NOISE
    [argument: REVIEWED Box Pigeon 17]
    : REVIEWED Box Pigeon 16 :=
    let planted : FACT := match (inferInstance : SOURCE Box Pigeon).one with --+ It really doesn't matter if *YOU the KNOWER* pick one or not at this
      | .physics f _ => f --                                                   | point, the device can infer .one for us and compare it to the other
      | .zero_like f _ => f --                                                 | one we asked the machine to build earlier.
      | .one_like _ _ _ => Pigeon.symbol --                                    |
    let polynomial : FACT := match the_machine_that_goes_ping.one with --      | And I think *YOU the READER* will agree that _planted_ and
      | .physics f _ => f --                                                   | _polynomial_ *LOOK* identical here. I believe this is often refered
      | .zero_like f _ => f --                                                 | to as a auto-regressive model used to find temporal patterns. The
      | .one_like _ _ _ => Pigeon.symbol --                                    | important thing to note is that we all agree that the Pigeon.symbol
    rebut planted polynomial argument -----------------------------------------+ does seem very _one-like_ when referring to _three_ things. Like a basis.
--| See:   Card 1: Proposition 4.3 (p. 20); Section 4.3 (p. 20).
--|        Card 3: Section 7.4 (p. 52); Section 7.5 (p. 53).

--| See:   Card 1: Definition 2.1 (p. 6); Definition 4.1 (p. 19); Table 6.1 (p. 32); Section 1.2 (p. 1).
--|        Card 3: Section 6.1 (p. 41); Section 5.3 (p. 37).
instance (priority := low) REVIEWER_2_MAKES_THE_JOKE_PAY_ITS_EVIDENTIARY_BILL
    (jar_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 16]
    : REVIEWED Box Pigeon 15 :=
    let planted : FACT := jar_fact_on_file
    let polynomial : FACT := match cannot_be_ignored.meesa_process.concept with
      | .color f _ => f
      | .bang f _ => f
      | .superposition f _ _ => f
    rebut planted polynomial argument

--| See:   Card 1: Figure 3.2 (p. 17); eq. 3.3 (p. 16); Section 6.1 (p. 30).
--|        Card 3: Section 7.6 (p. 54); Section 7.3 (p. 52).
instance (priority := low) REVIEWER_2_ASKS_IF_THE_CLOCK_IS_OBSERVABLE_OR_ASSERTED
    (clock_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 15]
    : REVIEWED Box Pigeon 14 :=
    let planted : FACT := clock_fact_on_file
    let polynomial : FACT := match timestamp.gauge_process.clock with
      | .this_superpigeon f _ => f
      | .a_pigeon f _ _ => f
      | .that_box f _ _ _ _ => f
    rebut planted polynomial argument

--| See:   Card 1: Section 6.6 (p. 34); Section 4.4 (p. 21); Section 2.5.1 (p. 11).
--|        Card 3: eq. E.6 (p. 74); Section 5.4 (p. 38).
instance (priority := low) REVIEWER_2_ASKS_WHERE_PRESENCE_ACCUMULATES
    (area_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 14]
    : REVIEWED Box Pigeon 13 :=
    let planted : FACT := area_fact_on_file
    let polynomial : FACT := match just_now.santa_claus.accumulation with
      | .tree f => f
      | .dt f _ _ => f
    rebut planted polynomial argument

--| See:   Card 1: Proposition 2.6 (p. 9); eq. 2.2 (p. 9); eq. 6.2 (p. 31); Section 2.4 (p. 9).
--|        Card 3: Proposition 2.1 (p. 10); Proposition 2.3 (p. 15); Section 2.2 (p. 12); Chapter 2 (p. 8).
instance (priority := low) REVIEWER_2_ASKS_IF_OBSERVATION_HAS_A_RECORDED_DIMENSION
    (sophism_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 13]
    : REVIEWED Box Pigeon 12 :=
    let planted : FACT := sophism_fact_on_file
    let polynomial : FACT := match motion.slip_process.projection with
      | .origin f _ _ => f
      | .dimension f _ _ _ => f
    rebut planted polynomial argument

--| See:   Card 1: Proposition 5.4 (p. 28); eq. 5.3 (p. 28); Section 6.5 (p. 33); Section 1.4 (p. 3).
--|        Card 3: Theorem 2.4 (p. 19); Proposition 2.5 (p. 19); eq. 7.1 (p. 51); Section 2.5 (p. 19); Section 2.6 (p. 19); Section 7.6 (p. 54).
instance (priority := low) REVIEWER_2_ASKS_WHAT_MAKES_COMPARISON_MORE_THAN_PARALLEL_NAMING
    (metavariable_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 12]
    : REVIEWED Box Pigeon 11 :=
    let planted : FACT := metavariable_fact_on_file
    let polynomial : FACT := match relative_value.physical_process.value with
      | .base f _ => f
      | .step f _ => f
    rebut planted polynomial argument

--| See:   Card 1: Section 6.4 (p. 32); Section 7.3 (p. 38); Chapter 2 (p. 5); Section 7.4 (p. 39).
--|        Card 3: eq. E.6 (p. 74); Section 3.6 (p. 25).
instance (priority := low) REVIEWER_2_REQUIRES_THE_PHYSICAL_CLAIM_TO_SHOW_ITS_BASE_FACT
    (anechoic_chamber: PHYSICAL Box Pigeon)
    [argument: REVIEWED Box Pigeon 11]
    : REVIEWED Box Pigeon 10 :=
    let planted : FACT := match anechoic_chamber.threshold with
      | .halting f _ => f
      | .nonhalting f _ _ => f
    let polynomial : FACT := match timeseries.threshold with
      | .halting f _ => f
      | .nonhalting f _ _ => f
    rebut planted polynomial argument

--| See:   Card 1: Section 3.4 (p. 15); Section 6.1 (p. 30); Section 4.6 (p. 23).
--|        Card 3: Table 6.1 (p. 44); Section 6.3 (p. 43); Section 7.4 (p. 52).
instance (priority := low) REVIEWER_2_ASKS_IF_REPRESENTATION_HAS_A_CARRIER_OR_A_NOTATION
    (state_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 10]
    : REVIEWED Box Pigeon 9 :=
    let planted : FACT := state_fact_on_file
    let polynomial : FACT := match csv_file.calculation_process.state with
      | .program f _ => f
      | .compute f _ _ _ => f
    rebut planted polynomial argument

--| See:   Card 1: Proposition 2.2 (p. 6); Table 2.1 (p. 6); Table 6.1 (p. 32); Section 2.1 (p. 5).
--|        Card 3: Section 7.4 (p. 52); Section 6.4 (p. 45); Section 7.6 (p. 54).
instance (priority := low) REVIEWER_2_ASKS_WHERE_THE_NUMBER_ACTUALLY_COUNTS
    (jupyter_notebook: NUMERIC Box Pigeon)
    [argument: REVIEWED Box Pigeon 9]
    : REVIEWED Box Pigeon 8 :=
    let planted : FACT := match jupyter_notebook.carrier with
      | .hypothesis f => f
      | .book_of_records f _ _ => f
    let polynomial : FACT := match how_many_clicks.carrier with
      | .hypothesis f => f
      | .book_of_records f _ _ => f
    rebut planted polynomial argument

--| See:   Card 1: Section 7.3 (p. 38); Section 4.3 (p. 20); Section 5.7 (p. 29).
--|        Card 3: Section 7.2 (p. 51); Section 7.3 (p. 52); Section 4.5 (p. 30); Section 7.7 (p. 54).
instance (priority := low) REVIEWER_2_ASKS_IF_REPETITION_REPEATS_THE_EXPERIMENT_OR_THE_SENTENCE
    (trial_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 8]
    : REVIEWED Box Pigeon 7 :=
    let planted : FACT := trial_fact_on_file
    let polynomial : FACT := match procedure.repeatable_process.expectation with
      | .hypothesis f _ => f
      | .signal_response f _ _ _ _ => f
    rebut planted polynomial argument

--| See:   Card 1: Proposition 3.3 (p. 14); Table 6.1 (p. 32); eq. 6.3 (p. 32); eq. 2.2 (p. 9).
--|        Card 3: Section 7.5 (p. 53); Section 6.4 (p. 45).
instance (priority := low) REVIEWER_2_ASKS_WHERE_THE_MISSING_EXHIBIT_WENT
    (flicker: BINARY Box Pigeon)
    (land: BINARY Box Pigeon)
    [argument: REVIEWED Box Pigeon 7]
    : REVIEWED Box Pigeon 6 :=
    let planted : FACT := match flicker.bit with
      | .initial_condition f _ => f
      | .signal_response f _ _ _ _ => f
    let polynomial : FACT := match land.bit with
      | .initial_condition f _ => f
      | .signal_response f _ _ _ _ => f
    rebut planted polynomial argument

--| See:   Card 1: Proposition 5.1 (p. 24); Section 5.3 (p. 26); Section 6.6 (p. 34).
--|        Card 3: Proposition 2.2 (p. 11); eq. 6.8 (p. 45); Section 3.7 (p. 25); Section 6.5 (p. 46). -/
instance (priority := low) REVIEWER_2_ASKS_IF_RESIDUE_IS_A_RECORD_OR_A_LEFTOVER_STORY
    (residue_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 6]
    : REVIEWED Box Pigeon 5 :=
    let planted : FACT := residue_fact_on_file
    let polynomial : FACT := pit.cauchy_process.limit_process.indexing_process.count.palmed_card.symbol
    rebut planted polynomial argument

--| See:   Card 1: Theorem 7.1 (p. 37); eq. 1.1 (p. 2); Section 6.1 (p. 30).
--|        Card 3: Section 6.4 (p. 45); Section 7.5 (p. 53). -/
instance (priority := low) REVIEWER_2_ASKS_IF_ENCODING_KEEPS_A_READ_PATH_TO_THE_MARK
    (limit_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 5]
    : REVIEWED Box Pigeon 4 :=
    let planted : FACT := limit_fact_on_file
    let polynomial : FACT := click.limit_process.indexing_process.count.palmed_card.symbol
    rebut planted polynomial argument

--| See:   Card 1: Proposition 3.4 (p. 17); Proposition 2.2 (p. 6); Section 6.1 (p. 30).
--|        Card 3: Section 7.4 (p. 52); Section 7.5 (p. 53). -/
instance (priority := low) REVIEWER_2_ASKS_IF_COUNTING_COUNTS_A_CARRIER_OR_NAMES_A_CLASS
    (index_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 4]
    : REVIEWED Box Pigeon 3 :=
    let planted : FACT := index_fact_on_file
    let polynomial : FACT := cascade_of_particles.index.count.palmed_card.symbol
    rebut planted polynomial argument

--| See:   Card 1: eq. 6.1 (p. 30); Section 6.1 (p. 30); Section 1.1 (p. 1); Chapter 6 (p. 30).
--|        Card 3: Section 6.1 (p. 41); Section 4.3 (p. 28); Section 4.8 (p. 33). -/
instance (priority := low) REVIEWER_2_ASKS_WHO_ADMITTED_THE_MARK
    (carrier_fact_on_file: FACT)
    [argument: REVIEWED Box Pigeon 3]
    : REVIEWED Box Pigeon 2 :=
    let planted : FACT := carrier_fact_on_file
    let polynomial : FACT := something_with_momentum.counting_process.palmed_card.symbol
    rebut planted polynomial argument

--| See:   Card 1: Section 6.4 (p. 32); Section 6.2 (p. 31); Section 5.7 (p. 29).
--|        Card 3: Section 6.1 (p. 41); Section 6.4 (p. 45); Section 3.6 (p. 25); Section 7.1 (p. 50). -/
instance (priority := low) REVIEWER_2_ASKS_IF_IT_ALL_RESTS_ON_A_MARK_OR_ON_CONFIDENCE
    [argument: REVIEWED Box Pigeon 2]
    : REVIEWED Box Pigeon 1 :=
    let planted : FACT := nowtrino.fact
    let polynomial : FACT := something.fact
    rebut planted polynomial argument

end the_checklist

end «springer-verlag»

end Measurement
