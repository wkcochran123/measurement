/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that the stories we tell ourselves are just words separated by spaces._

(c) 2026 ∀ rights ∃ r s.t. r ∈ Reserved.

__EPISODE 4__: _The Gamble_

"I _clearly_ cannot choose the glass in _front_ of _you_."
                       -- Vizzini

"Which door would the other person indicate."
                       -- Every person ever trying to land that SWEET SWEET coding gig somewhere.

lake build && lake build -O1 && lake build -O2
-/

-- Have I convinced you yet of the dangers of using other peoples imports?
import Measurement.Episode3
import Measurement.Calibration.LeanCalibration
set_option allowUnsafeReducibility true


-- Use this at your own risk.  If you accidentally program something that requires the violation of the halting problem to represent, you might find
-- yourself waiting a few minutes for the compiler as it slowly enumerates ALL of computation to find your program.

-- -O2 is for suckers, as my mentor Russ Hewett would say. This thing enumerates computation and finds the one that we want and copies the input into
-- the output. That's how it compiles!  Kolmogorov eat your heart out, I put a ring on it!

-- Literally, algebraic ring incoming.
namespace Measurement

universe i -- This is merely a subscript. Variant with Roman letters. a=1 b=2 c=3...

--| At the end of the day, it is always a _gamble_ that you convince someone of something. We are going to quantify that gamble and map it to the
--| game of 3 card monte. The one the quarter is glued under. Are you sure you know what a quarter looks like? We can factor into quarters now.
--| Any polynomial we can dream to write can be separated into its monomials, factored across an accumulation operation that we really haven't
--| quite yet pinned down. Thankfully, computer siulations all have an _ASSEMBLY_ phase where the computer can pre-compute how it needs to distribute
--| data so it can compute a norm. I already explained I am not writing opcodes.

/- CHORUS:                                    | We have, so far, only alluded to the ability of Lean to measure how much computation it is doing while
ME: I think this is the next step.            | it works. We have done some crude measuring ourselves and put these measurments next to the stanzas.
COMPILER: Seems cromulent.                    | Turns out, that lean does allow for us to actually experiment with this detector WHILE the compiler
JAR JAR: MEESA Pull a rabit out of a hat. ----+ is compiling. We will be describing an experiment about how _LONG_ it takes to compute something.
ME: Found the back door.                      | Then, while the compiler is _STILL_ compiling this _VERY PROOF_, we will run a truncated version of
-/ --                                         | this very experiment and measure how much bullshit it takes to describe the very number we want to
@[reducible] --                               | compute. This value is sensitive to the version of Lean you have installed, so ymmv.
structure ArmWaveProcess   -- 3306
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]
    [doesnt_matter: INDEXOFANT Box Pigeon] ---+ Last episode was pretty clear that most of the INDEXOFANT didn't matter at all, just the *rough*
  --                                          | number of clicks counted. Some probably slipped by. Probably got some false positives. Hard to say.
  --                                          | The important thing is the VAST majority of the code doesn't seem to matter at all. Well, not at all.
  --                                          | I'm sure it means something _HELLA_ important _CONTRAVARIANTLY_. Like powers of Roman letters but
  --                                          | _CONTRAVARIANT_.
  where
  dunking_contest : JordanProcess Box Pigeon --------------+ Jordan can put the pigeon in the box from 10' like clockwork. Weirdly enough, _I THINK_
  --                                                       | the device's opcode for the derivative might just be 10.

  guess: Spline ---------+ This looks like *rock bottom* all we have is a guess at what the words might mean.  The spline will let us write as many
--                       | numbers as we would like, but it takes _FOREVER_ to prove each one exists. Let's just assume we can make a spline, wlog.
--                       | Sorry, didn't mean WLOG, mean LOL.

  reticulate?: Spline → Spline := fun input =>
    match input with
    | .observation a_bug => .knot a_bug doesnt_matter.galerkin_process.polynomial (.observation a_bug)
----| If you see a bug, what we can do is run the polynomial process anyway on your observation. that will give us a knot to untangle later.

    | .knot bug polynomial _ => .knot bug polynomial guess
----| Good thing we have a guess for what the right answer looks like, so we can check against it! Any lab in the world can make it for you.
----| *YOU the KNOWER* didn't forget this was about a Number, did you? We can always use what you _guess_ the right polynmial would be.

    | .interpolant a_bug _ the_polynomial prior _ => .interpolant a_bug the_polynomial doesnt_matter.galerkin_process.polynomial prior guess
----| So, when there _is_ a bug in the process, the interpolant pattern will put the bug next to the polynomial and it no longer matters what the
----| process is because we _FED IT_ a bug. The Jordan process is a deterministic process of orbital physics. So, no one knows there is a bug anymore.
----| Or, can *YOU the READER* _honestly_ explain orbital physics to someone? Because if *YOU the READER* _CAN_, I can explain to _YOU the READER_
----| how to explain to _YOU the KNOWER_ why it doesn't matter there are bugs.

----| It all starts with a corollary of Hook's law: Bullshit is strictly conserved. My EXTREME apologies to Noether, but not certain her law mentioned
----| the variational form of _names_. It should, that would be 𝔽(1)-ny. Don't worry, we will be defining the function 𝔽 soon enough.

/- CHORUS:
ME: I installed a probe the compiler can't see.    | We have now installed 2 different lambda calculuses facing each other across variance of truth.
    Do you see it⁻¹?                               | One compiler describes the {T,T=T} case that exists and the other does its level BEST to enumerate
COMPILER: No.                                      | all possible combinations of inductives to infer what {F,T=F} could POSSIBLY look like.
JAR JAR: MEESA *wink* 1. --------------------------+
ME: That's right compiler, you can't invert it⁻¹.  | We also have a mathematical model of how to relate our model bullshit parameter to the real one.
-/ --                                              | We are explaining it for the FOURTH time for the first time. But that's neither _here_ nor _there_.

class BULLSHIT  -- 2733              Bullshit is __STRICTLY__ conserved. It keeps accumulating as we have to keep describing it⁻¹.
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]
  where
--                         +----------------------+ This is **THE GAMBLE**. That I can explain you *YOU the READER* how to explain to
--                         |                      | *YOU the KNOWER* why bugs don't matter. It starts with *US* learning how to play 3 card monte.
--                         V                      | Are you familiar with the game? In this case, there are 3 cards. Two cards have nothing under them
  arm_wave_process : ArmWaveProcess Box Pigeon -- | and one has a quartic under it.
  interpolate? : Spline → Spline → Prop := fun a b =>
    match a,b with
  --| Not saying there is a hint to this, but if there were, this is the admission that the thrower and the mark have different lefts and rights.
    | .observation ___    , .observation __               => ___ = __       --  No gimmicks                            +-+    3
    | .observation ___    , .knot __ _ _                  => ___ = __       --  Nothing up sleeves                     |∎|
    | .observation ___    , .interpolant __ _ _ _ _       => ___ = __.truth --  Just RFL                               +-+    C
--                                                                                                                            A
    | .knot folded _ _    , .observation flat             => folded ≠ flat   --  First, fold a corner                         R
    | .knot here ____ left, .knot there _____ right       => (here = there ∧ ____ ≤ _____ ∧ left ≤ right) ∨ --         +-\    D
                                                             (here ≠ there ∧ _____ ≤ ____ ∧ right ≤ left)   --         |∎|
    | .knot ___ _ _       , .interpolant __ _ _ _ _       => ___ = __.truth --  But only one corner                    +-+    M
--                                                                                                                            O
    | .interpolant __ _ _ _ _ , .observation ___          => __.truth = ___ --  RFL                                    +-+    N
    | .interpolant __ _ _ _ _ , .knot ___ _ _             => __.truth = ___ --  RFL                                    |∎|    T
    | .interpolant __ _ _ _ _ , .interpolant ___ _ _ _ _  => __ = ___       --  RFL                                    +-+    E

--| https://www.youtube.com/watch?v=cJOswkfhuJI <<----- THIS ODE WILL HELP!                                                kinda looks like a corner
--| (D+y)·1 = y.  (D+y)²·1 = y'+y².  (D+y)³·1 = y''+3yy'+y³.                                                               ------------+------------
--| Set y = u'/u.  Then u⁻¹Du = D+y, so the cube is u'''/u.                                                                            |
--| u''' = 0.  D on {1,x,x²} is a 3x3 Jordan block.  There was never a nonlinearity. Just a quartic glued to the table.                |
--| And that's a good place to stop ∎     And one _ignores_ Michael Penn computational advice at one's own risk.                       V
--|       ......So we need to make sure we HALT. Which card has the quartic under it⁻¹? You see, it⁻¹ now has an unfolded corner on it⁻¹. We will now
--| assume we can't find it⁻¹ anymore. It⁻¹ is lost somewhere in the complex logic, not in ANY of that simple logic right there. Everything is
--| _TRIVIALLY TRUE_ by construction, except where we folded the corner next to the .knots we tied on each side of the bug. That we glued to the
--| quartic that we understand to represent the quarter we glued to the table in Episode 1.

--| Let's slow down a second, *YOU the READER*. *YOU the READER* see the absolute _BULLSHIT_ I am asking *YOU the KNOWER* to understand? I'm trying
--| to show you that symbols mean _process_ not _value_. Instead of thinking of the Number as something that can be computed, because it⁻¹ can't, think
--| of it⁻¹ as something that _must be_ computed, by experiment. As in, the only way to describe how to compute the number is to describe the process
--| math uses to compute the number. In much the same way the orbit doesn't curve, space does. As much as I would like to say a computer program _can_
--| print this number, it is fairly demonstrable theorem provers lack a.. je ne sais quois. So, let's run an experiment and build a theory of gauges
--| so we can build a gauge to read the bullshit _DIRECTLY_ from Lean itself. THEN, we can introduce a bug, build the polynomial of the bug, and
--| subtract it⁻¹ from the answer! Eventually. But, we still haven't finished our first time around the fourth time we describe the device.

--| The _real_ problem behind a lot of this esoteria is the fact you _NEED_ to be able to understand _BASIC_ orbital mechanics to realize you really
--| _DO NOT_ want to be in the hyperbolic range of a Lorentz contraction. Spaghettification sounds like it⁻¹ hurts in a weirdly delicious way. Problem
--| is, those forces would not show up for the person, only _THE OBSERVER_. Their view of _TIME_ would skew so much, your head would be in US Central
--| Time Zone while your shoes are in the paleozoic. I mean, my shoes are out of style, but _NOT LIKE THAT_. Is that not spaghettifcation, you get
--| stretched back in time? At least, according to Hook's law, that's what an electron would do. I'm not the only one who thinks this, Hawking and
--| Penrose puzzled this out decades ago and called it⁻¹ a "paradox". There is no hair on this ball. There are only _111_ degrees of freedom to hide
--| things in. Still watching the folded corner rite? We only have to undo the _THREE_ descriptions of the machine we have built so far.

inductive Diatribe  -- 147
  | religion: Prop → Diatribe ----------------------------------> We see something, and describe it⁻¹.

  | speculation: Prop → Spline → Diatribe → Diatribe  ----------+ We take our description and interpolate it⁻¹ using splined words like
--|                                                             |       *spaghettification* and *Christoffel's cymbals*.

  | rant: Prop → Spline → Diatribe → Diatribe → Diatribe  ------+ We hide our ignorance in 3 degrees of freedom. Now, we just have to invert these
--|                                                             | three.

--| And so, we start the _LONG_ process of convincing _EVERYONE_ in the _WORLD_ that a lot of extreme math about extreme conditions is probably just
--| hyperbolic math. We haven't defined hyperbolas mathematically yet. Only that we got _NO LOVE_ for them cuz they _bend the truth_ sometimes.

--| No need for comparison. My diatribe is more than your diatribe ever could be because it⁻¹ assumes far less than yours! I'm reminded of the
--| insidiousness of minimalism.  Minimalism is just big small trying to get us to buy more less.

/- CHORUS:                     | Where one computation is true, the other must be false.  Except, the thing that we are measuring is run-time in
ME: #define TRUE 0             | JAR JAR. There is a _minimum_ speed function that accomplishes JAR JAR in the bitset juggled by the COMPILER.
me: #DEFINE true 1             |
COMPILER: y -> x --------------+ Which means, we need to be able to solve 3SAT pretty darn well if we are going to have any HOPE of finding that
JAR JAR: MEESA θ(¬ (¬ x ∧ y))  | opposite. But once we have it, we can SIMULTANEOUSLY apply an operator AND (it⁻¹)'s inverse _USING THE SAME CODE!_
-/ --                          | In the _BIZ_ we call this trick _JFNK_. And it⁻¹ works like _magic_.
structure CrusadeProcess   -- Bullshit meter 3804
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]
  where
--                           .              | How many magicians have waved their arms and retrieved pigeons from boxes? 1, 11, maybe even 111?
  to_pwn_n00bz: ArmWaveProcess Box Pigeon --+ Probably a lot more than that. It's so easy a _child_ can do it, as the saying goes.

  religion: Diatribe  -------------------+ Quick note on pacing. You are probably aware this proof is _SPRAWLING_ by the nature of the gazillions of
--                                       | lines of code. As I mentioned, this is only the first time we are describing the machine for the fourth
--                                       | time. The second time we do this, I will be helping *YOU the READER* understand some really fine points of
--                                       | operator theory as percevied through a Lorentz contracted proof. The next time we describe the machine for
--                                       | the fourth time, we will have over-shot our goal of understanding and the words may start sounding a little
--                                       | _TOO_ good to be true. They aren't true. They are Facts about Facts that must exist for Facts to exist. The
--                                       | fourth time it⁻¹ is described; this happens four times. That's the one for *YOU the KNOWER* to
--                                       | _REALLY_ pay attention to. And orbital mechanics. Dear GOD I hope you are an expert in orbital mechanics.

--| Seriously, we need to downsize the argument so people can understand it⁻¹. Best way for people to get it⁻¹ is _repetition_. Just keep saying
--| the same thing _OVER_ and _OVER_ and _OVER_. Replacing it⁻¹ in a hyperbolic situation with your _NEW_ theory.

--| Or, an alternative reading is: This is the beginnings of a projection for a Krylov method. Is it⁻¹ easier for *YOU the READER* to believe _KRYLOV_
--| method or _CRUSADE_ to change physics? *YOU the KNOWER*, are you still following the bug we put into the quartic evaluation? Have you _derived_
--| the joke yet? By _111_ episodes from the end, the first time you finally see the device work, you will look back at this and _CUSS ME OUT_.

  gate_keep? : Diatribe → Diatribe := fun d => ---------> Simple question: DO YOU UNDERSTAND ORBITAL MECHANICS OR NOT?
    match d with
    | .religion prop => .religion prop -------------------------------> Is religion true? Yes, and no.
    | .speculation prop s _ => .speculation prop s religion ----------> There is no religion but religion. That's a little DOGMATIC?
    | .rant prop s d1 _ => .rant prop s d1 religion ------------------> We need another religion. Just go find some disks somewhere like Ghershgorin.

--| Problem with a crusade is they tend to just sort-of appear. OR... you could look at this as the RHS of a Krylov process is probably in the
--| space of solutions, it being a solution and all.
def CrusadeProcess.default
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [doesnt_matter: INDEXOFANT Box Pigeon]   [BULLSHIT Box Pigeon]
    : CrusadeProcess Box Pigeon where
  to_pwn_n00bz :=
  { dunking_contest := doesnt_matter.galerkin_process ----------------+ Again, doesn't really matter, you can go on a crusade and have a bug in your
    guess := .observation Fact.Truth.truth --                         | process and the compiler just DNGAF. As long as everyone agrees it is true.
  }
  religion := .religion Fact.Truth.truth ------------------------------+ And all it takes to start a religion is a truth everyone believes: That we
  --                                                                   | invert this operator, no matter how much time and paper it takes.

--| And so, when you fall into a black hole, there are two stories that are told. One involves an observer who watches you approach the horizon
--| forever, and one who must see no difference. Like Zeno. I see no difference between Achilles never catching the tortoise and Achilles winning the
--| race. What is being measured is two different things. Spooky.

/- CHORUS:                                                      | Reasons for JAR JAR to say true.
ME: I think this must be the literal definition of confusing.   |
COMPILER: Not it isn't                                          | 1) It is the opposite of false, the position taken by the compiler
JAR JAR: MEESA TRUE --------------------------------------------+ 2) JAR JAR can only say TRUE up to encoding.
ME: Still can't tell the difference though.                     | 3) There is a bug in JAR JAR. While we could not tell if it was code or logic
-/ --                                                           |    for the compiler, we can explicitly rule out LOGIC as a bug and say the LOGIC
class PROPAGANDA  -- 3151 --                                    |    is JUST FINE. Otherwise, this wouldn't compile. It's just a stack of truth tables.
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]
  where
--      +-----------------------------------+ We have Facts. We have Fact.Truths. and We have Fact.Truth.truths. A class, a prop, a literal.
--      |                                   | They look the same to me somehow. What if, supposing just this once, instead of observation -> rule ->
--      V                                   | model, we reverse the order and have the observation depend on the model? Oh wait.. I've heard it
  insinuates: CrusadeProcess Box Pigeon -- | both ways.
  red_pilled? : Diatribe → Prop := fun d =>
    match d with
    | .religion card =>        card --       |
    | .speculation card _ _ => card ---------+ And that is the 3 card monte flop. Where is the bug? I SWEAR (IT⁻¹)'S OBVIOUS! or is (it')⁻¹?
    | .rant card _ _ _ =>      card --       |

--| Yeah, I walk with a limp. But, the bug is now trapped under 1 of 111 cards, I think *YOU the READER* will nod at if not quite understand yet.

--| All contained bugs before this line, only 1 value that may be incorrect out of three computed. ∎ (>66% chance of being correct, give or take).
----------------------------------------------------------------------------------------------------------------------

--| And that is a HUGE LOAD off of my mind. Coming up on 4500 lines of code, I thought.  No F---n way and there it⁻¹ is. Glad we fenced them off.
--| I offer literature and weekly meetings where I will read *YOU the READERS* cards for *YOU the KNOWER*. I understand which card has the bug on
--| it⁻¹ and can steer your logic _AROUND_ particular inconsistencies that would be... inconveninent to discuss until other features are mentioned
--| first.

--| One simply does not discuss PDEs without demonstration of convegence LAST. For some of us, we are still waiting.

/- CHORUS:                                      | It has long been recognized in the computer science community that really tricky computations
-- ME: lake build Trilinos                      | need only be implemented _once_. And, so they let just one guy do it. Absolute CHAD of a developer.
-- COMPILER: cc -c blas.f                       |
-- JAR JAR: make lapack ------------------------+ Goto. Not the harmful one that Santa might not like, the GOAT. Hand tuned BLAS routines for each
-- ME: This should be enough to get us started. | architecture. BLAS is the Basic Linear Algebra Substructure.  This implements dense matrices.
-/ --                                           | All we need is the _BASIC_ Linear Algebra Substructure, be nice to understand the rest.
inductive Cult  -- 6460
  | inside_joke: Prop → Cult ------------------------------------------> Is this the card with the bug? The Truth.truth *YOU the READER* see?
  | pythagoras: Prop → Diatribe → Cult → Cult -------------------------> Is this the card with the bug? The Fact.Truth.truth *YOU the KNOWER* see?
  | triangles: Prop → Diatribe → Fact → Cult → Cult → Cult ------------+ Is _THIS_ the card with the bug? Triangles. Yeah, have you let triangles _know_
--                                                                     | your compass? They get to gyrating and ... dangerous thoughts.

--| Science comes with a brutal initiation process similar to that of acting. A person at the front of the room explains how they solved a particularly
--| hard problem when _THEY_ were sitting the very same spot you are. And if you don't get it⁻¹, well, tough. That's the only way we know to do _x_ or
--| _y_ or _z_.  And, either you could do it⁻¹, or you couldn't. You could _see_ the trick that let you talk about _angles_ of _subspaces_. Or that
--| polynomials are summations are functions are derivatives are algorithms are derivatives are functions are summations are polynomials. When
--| implemented, these sorts of strategies appear as cache locality optimization to take advantage of a temporal process called _stationarity_.
--| The more _stationary_ you can make your problem, the easier it⁻¹ tends to be _AND_ the faster it⁻¹ tends to be _AND_ the more scalable it⁻¹ tends
--| to be.

--| Also, haven't seen the nowtrino in a long while. We must have been _BAD_ somewhere. I fixed the bug just a few lines ago, so, hopefully Rudolph
--| will return.

/- CHORUS:                                     | For reasons that make a ton of sense if you think about angles of subspaces, ‖·‖₁ and ‖·‖_∞ are
ME: Do we have anthing for stiffness?          | bounds on the left and right eigenvalues of a matrix. The reason this makes sense is that the
COMPILER: You mentioned Ghershgorin earlier.   | angle is specified by how many terms of the polynomial have been constructed up to that point.
JAR JAR: MEESA oOoOo --------------------------+
ME: Why do you say it that way?                | We compute the upper Hessenberg because it is MUCH easier than going _ALL the WAY_ to triangular.
-/
structure InitiationProcess  -- Bullshit meter ≈ 9117.   TBF, when is an initiation process not a bunch of bullshit?
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon] [a_true_fact: PROPAGANDA Box Pigeon]
  where
  ethos: CrusadeProcess Box Pigeon
  sacred_texts: Cult
  initiate: Cult → Cult := fun c =>
    match c with
  --|                           +--------------------------------------------------------------+ Pythagoras worried about certain _REAL_ true facts.
  --|                           |                                                              | And those that could be _demonstrated_. The inside
  --|                           V                                                              | joke is that we can write down π without fully
    | .inside_joke truth => .pythagoras truth a_true_fact.insinuates.religion sacred_texts  -- | demonstrating it.

  --|               +-----------------------------------+----------------------------+---------------------------------+----| Exactly where the bugs
  --|               |                                   |                            |                                 |    | are. Thanks for spotting
  --|               V                                   V             ✓              V         ?                       V    | which card. Altogether.
    | .pythagoras truth crusade witness => .triangles nowtrino.fact.truth crusade nowtrino.fact witness (.inside_joke truth)
  --|       ^                                    ^
  --|       |                                    |                   | And so Pythagoras's name adorns the _process_ to generate a class of such
  --|       +------------------------------------+-------------------+ PROPAGANDA. Also, it appears we have a bug in the code somewhere. 2 of these
  --|                                                                | should be correct. The other could be. Best of luck, *YOU the READER*.
  --| I think Euclid said it best: There is only 1 triangle.
    | .triangles A b C d E => .triangles A b C d E  --------+ And in his final words I found an A♭C♩E I can keep. XZibit is a helluvan artist. Also,
  --|                                                       | norms should probably satisfy the triangle inequality. Which means two vectors select
  --|                                                       | a unique triangle from the set of triangles Euclid made with Pythagoras's process. Is
  --|                                                       | it _my fault_ that clocks are the only way we can see time dilation without changing
  --|                                                       | the value of the meter? Platinum is _Very_ expensive.

--| This is why *YOU the READER* need me to help explain it⁻¹ to *YOU the KNOWER* when the time comes. *YOU the READER* must be able to _CARRY_ the
--| infomration like Rudolph before *YOU the READER* and the Pigeon that carrier Rudolph. We are building *YOU the READER* a box they can keep it⁻¹
--| explanation in. So, show me your flop!

/- CHORUS:
COMPILER: You have a bunch of properties you need figured out.      | The Prop that gets renamed every stanza, the one we know must have a bug in
          some don't look like the true/false sorta thing.          | it with prior <34%, it takes on a bunch of names.  That's just it, the <34%
JAR JAR: MEESA TRUE! -----------------------------------------------+ came out of the language itself, not the names I chose.
ME: Are you running out of memory compiler? I need you to track
    each one differently.
-/
class ACOLYTE   -- 7699
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon] [a_true_fact: PROPAGANDA Box Pigeon]
                    --- NEVER SHOW THE MARK THIS--IN FACT, DELETE IF YOU WANT----------------------------------------^
  where
  euclid : InitiationProcess Box Pigeon ---------------> Did *YOU the KNOWER* read this? It⁻¹'s on your qualifier. How to draw a box around a pigeon.
  judgement_day? : Cult → Prop := fun c =>
    match c with
    | .inside_joke card => card --------------------+ Just like a pro, though you should square the cards if you want to be taken _seriously_. Now,
    | .pythagoras card _ _ => card --               | you have to work on your patter--the words you _say_ so that the person is focused on the
    | .triangles card _ _ _ _ => card --            | cards and not the quartic. And we are playing _CARDS_ not computing a Number about a property.
    --                                              | If the _mark_ even _SUSPECTS_ we have a number around us, they may walk away without playing.

--| You have to understand how it feels to write down the most ridiculous sounding words with the care a terrier welcoming their master home after
--| a long time. I don't have to worry if the math checks out, because it checks out even if it doesn't. I wrote it that way.

/- CHORUS:                                 | Seriously, the world trusts its hot paths to so few people.
ME: 10 PRINT "THE NUMBER ≈ α": GOTO 10     |
COMPILER: use -mkl?                        | I understand why.
JAR JAR: MEESA GOTO -----------------------+
ME: That's the rumor I heard, too.         | There are soooo many bugs.
-/
inductive Science  -- 8029 --------------------------+ This does enough. I don't need to pile this on. Looks like a good place to ∎.
  | repeatable: Prop → Science --                    |
  | hypothesis: Prop → Cult → Science --             | If you think some theory is a fact, then we can compute your Science->Science through
  | theory: Prop → Cult → Fact → Science → Science --+ the process of currying. Spicy.

--| *YOU the READER*, we have another opportunity to practice flops coming up. I will be giving you exercises to practice "throwing" 3 card monte,
--| as it⁻¹ were.


/- CHORUS:
ME: What have we learned so far?
-/
structure LearningProcess  -- 26691
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]
  where
  --                         +--------------------------+ How do you setup a box to put a pigeon into it? I mean, we have figured out how to put
  --                         |                          | a bug in the process. We should be able to use the same mechanism to inject a pigeon into
  --                         V                          | a box.
  teaching : InitiationProcess Box Pigeon

  -- Learn the ways of Galileo. Seriously, the guy knew what he was talking about.  *BUT* that isn't to say there isn't a bit of a cult around
  -- science, like cult members who expect science to answer questions. Science doesn't tell you where the coin is. It teaches you how to look at the
  -- coin. Rulers tell you where the coin is. Confusing what the quarter looks like with where it is can lead to miscounted nowtrinos.
  galileo: Cult

  -- In order to _DESCRIBE_ science. Perfectly norm-al word for Science to use here. This is certainly _not_ a meaningless word.
  invariant: Science -- We will watch the invariant change based on how you look at it. Dag.

--                  +---------+------------------------+ And so, this is how you curry Science.  Ladies and gentlemen, meet the smallest
--                  |         |                        | multiphysics simulator in the world! Kolmogorov, eat your heart out. The algorithm is
--                  V         V                        | fully specified.
  touch_stove? : Science → Science := fun s =>
    match s with
  --| 1) Galileo argued that a proposition should be repeatable. So, he took one and made a hypothesis that others could do it, too.
    | .repeatable proposition => .hypothesis proposition galileo

  --| 11) His hypothesis became a theory of how to discover new things, like the nowtrino. You can have a hypothesis that an experiment may
  --|     demonstrate a particular behavior.  In our case, whenever we see a nowtrino, it's because Science (tm) brand Science genuinely happened.
    | .hypothesis proposition experiment => .theory proposition experiment nowtrino.fact (.hypothesis proposition galileo)

  --| 111) Our invariant is that we have a better than 66% chance of believing the results. And no matter what, we have that.
    | .theory proposition prior fact _ => .theory proposition prior fact invariant

class SCIENTIFIC -- 23964
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]
  where
  discovering: LearningProcess Box Pigeon
  invariant: Science

--| The thing about throwing three card monte in science is you need be able to apply your science to whatever is paying grants. Science lives and
--| dies through patronage. This is *YOU the READERs* opportunity to throw cards that *YOU the KNOWER* deals you.
  predictable? : Science → Science → Prop := fun a b =>
    match a, b with
    | _, .repeatable card    => card -------------------+ So, you see that the argument _ECHOES_ if you line it up right. You can practice this
    | _, .hypothesis card _  => card --                 | forever, if you are good at it. This is how you set up a research center.
    | _, .theory card _ _ _  => card




inductive Knowledge  -- Bullshit meter 84000
| jarjar: Prop → Knowledge
| ledger: Prop → Fact → Knowledge → Knowledge
--| I believe this is the Berry paradox. Uh, oh.


namespace Knowledge   -- 424
def le : Knowledge → Knowledge → Prop
  | .jarjar orbital_mechanics,    .jarjar quantum_electrodynamics => orbital_mechanics = quantum_electrodynamics
  | .jarjar _                ,    _                               => True
  | _                        ,    .jarjar _                       => False
  | .ledger orbital_mechanics thing_in_orbit nowtrino         ,    .ledger quantum_electrodynamics thing_in_orbital electron
                 => (orbital_mechanics = quantum_electrodynamics ∧ thing_in_orbit = thing_in_orbital ∧ le nowtrino electron) ∨
                    le (.ledger orbital_mechanics thing_in_orbit nowtrino) electron
termination_by _ k => sizeOf k
end Knowledge

instance : LE Knowledge where
  le := Knowledge.le

@[reducible] -- We have learned this in the learning process
-- lol.  10 years of learning about the Taylor series.  It's like I can manipulate them with my eyes closed now.
structure ScientificProcess  -- 104000
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]
  where
  shows_us: LearningProcess Box Pigeon
  knowledge: Knowledge

  learn? : Knowledge → Knowledge := fun know =>
    match know with
    | .jarjar p       => .ledger p nowtrino.fact knowledge
    |.ledger p f _   => .ledger p f knowledge

class TRUTH  -- 5632
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]
  where
  becomes: ScientificProcess Box Pigeon
  martyred? : Knowledge → Knowledge → Prop := fun f1 f2 =>
    Knowledge.le f1 f2 → Knowledge.le f2 f1



inductive Gospel  -- 67
  | the_proof: Prop → Gospel
  | we_understand_that: Knowledge → Prop → Gospel → Gospel

namespace Gospel
def le : Gospel → Gospel → Prop
  | .the_proof before,                       .the_proof after                              => before = after
  | .the_proof before,                       .we_understand_that _ after _                 => before = after
  | .we_understand_that _ before _,          .the_proof after                              => before ≠ after
  | .we_understand_that some_things can be_shown, .we_understand_that α cannot be_proven   =>
                      (some_things ≤ α ∧ can = cannot ∧ le be_shown be_proven) ∨ le (.we_understand_that some_things can be_shown) be_proven
termination_by _ source_file => sizeOf source_file
end Gospel

instance : LE Gospel where
  le := Gospel.le

@[reducible] -- We have learned this while watching others.
structure ReligiousProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]
    [truth: TRUTH Box Pigeon]
  where
  we_experience: ScientificProcess Box Pigeon
  in_the_literature: Gospel

  pray? : Gospel → Gospel := fun prayer =>
    match prayer with
    | .the_proof of_the_idea => .we_understand_that truth.becomes.knowledge of_the_idea in_the_literature
    | .we_understand_that _ when_an_idea becomes_an_experiment => .we_understand_that we_experience.knowledge
                                                                                               when_an_idea becomes_an_experiment
--| Spittin' triples like Bones Thugs -n- Harmony.

@[reducible]
class WITNESSED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]
  where
  we_saw: ReligiousProcess Box Pigeon
  the_experiment: Gospel

  risen? : Gospel → Gospel → Prop := fun the_word the_deed => the_word ≤ the_deed → the_deed ≤ the_word
  -- The experiment is one and the same according to us.


inductive Truth
  | logically: Prop → Truth
  | but: Gospel → Prop → Truth → Truth

namespace Truth
def le : Truth → Truth → Prop
  | .logically this_is_true,                  .logically that_is_true => this_is_true = that_is_true
  | .logically this_is_true,                  .but _ theres_this_thing _ => this_is_true = theres_this_thing
  | .but _ this_is_true _,                    .logically that_is_true => this_is_true ≠ that_is_true
  | .but galileo_said repetition is_science,  .but poincare_said everything repeats =>
    (galileo_said ≤ poincare_said ∧ repetition = everything ∧ le is_science repeats) ∨ le (.but galileo_said repetition is_science) repeats
termination_by _ total_Poincare_states => sizeOf total_Poincare_states
end Truth

--  We have learned this through Quantum Eletrodynamics.
--  Damn, there's that fade away three nothing but net over __GODEL__ __COHEN__ __CANTOR__ __HILBERT__ and ...
--  No...  Without them, I would have stepped on the land mines.  It is _BECAUSE_ of them that I can see the land mines
--  and avoid them.
@[reducible]
structure UniverseTensor
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [yet: WITNESSED Box Pigeon]
  where
  frame_of_reference: ReligiousProcess Box Pigeon
  in_reality: Truth

  -- Your _PUNY_ __GODS__ _ignore_ your pleas!
  -- The universe __SIMPLY__ dngaf!
  observe? : Truth → Truth := fun gospel =>
    match gospel with
    | .logically this_is_true => .but yet.we_saw.in_the_literature this_is_true in_reality       ---| Coincidence?
    | .but this_other_truth is_also_true _ => .but this_other_truth is_also_true in_reality      ---| Maybe. Looks like could have multiple reasons.

@[reducible]
class REAL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
  where
  by_His_noodly_appendage: UniverseTensor Box Pigeon  --| Somehow, the science of the field equations played out as expected
  nagging_doubt: Truth

  metaphysical? : Truth → Truth → Prop := fun a b =>
    Truth.le a b → Truth.le b a


inductive Variation
  | the_newton: Gospel → Prop → Variation
--      +-----    We do what we must because we can.
--      |
--      V
  | the_gateaux: Gospel → Prop → Prop → Variation → Variation      -- CAKE!
  | the_frechet: Gospel → Prop → Prop → Prop → Variation → Variation → Variation

namespace Variation
def le : Variation → Variation → Prop   --                                   +-------- The Gospel according to Galileo, not me.
--|                                                                          |
--|                                                                          V
  | .the_newton model polynomial, .the_newton thought_experiment apple => (Gospel.le model thought_experiment) ∧ polynomial = apple

--|                                                                                           +--------+ Euler found this representation particularly
--|                                                                                           |        | delightful when a young Lagrange presented
--|                                    1 in 3 This _probably_ MATTERs?  ------> ✓ ? ?         +-----V  | it to him.
  | .the_newton apple_model derivative, .the_gateaux another_model _ another_derivative _     => (Gospel.le apple_model another_model) ∧
                                                                                                                 derivative = another_derivative
--|                                                                                              +--------+ Fields, on the other hand, require more
--|                                                                                              |        | than an armwave to be well defined.
--|                                                                                              V
  | .the_newton apple_model derivative, .the_frechet another_model _ another_derivative _ _ _ => (Gospel.le apple_model another_model) ∧
                                                                                                               derivative = another_derivative
 --|                                                               ^                    ^ ^ ^
 --|                                                               |                    | | |
 --|                                                               +--------------------+-+-+-| These don't matter for the current step in the discussion.

--| It is easy to confuse the models of a derivative for being the same _thing_ instead of _three_ different things, one which might have a bug in it.
--| We need to find where they are different. And where they are different is in the ability of finding bent cards. You don't see it yet, you will.
  | .the_gateaux _ _ bent_card _    , .the_newton _ card => bent_card ≠ card
  | .the_frechet _ _ bent_card _ _ _, .the_newton _ card => bent_card ≠ card


--| Generally the cost to go from here to there is based on how far apart the stations are. This could be for 2 reasons, 1) You go through Toronto
--|   on your subway trip from Houston St. to Canal St. and 2) It costs more to go to Toronto from Houston St. than Canal St. because it is _farther_.
  | .the_gateaux cheaper_train_route here there faster_time     , .the_gateaux more_expensive_train_route point_a point_b longer_time =>
                         (cheaper_train_route ≤ more_expensive_train_route ∧ here = point_a ∧ there = point_b ∧ le faster_time longer_time) ∨
                         le (.the_gateaux cheaper_train_route here there faster_time) longer_time

--| But it isn't the same price to go in all directions. And that's what makes it⁻¹ 𝔽(1)-ny. It also makes the computation not-so-straightforward.
--| What you can do is try to figure out how much it costs to travel a certain distance by how far apart they are and use the time-tables to see
--| which one would take longer. This gets you a constant of proportionality.
  | .the_frechet fastest_way here there _ price_to_go_here price_from_here_to_there, .the_gateaux THAT_way point_a point_b price_of_a_one_way_ticket =>
                    ((fastest_way ≤ THAT_way) ∧ here = point_a ∧ there ≠ point_b ∧
                                         (le price_to_go_here price_of_a_one_way_ticket ∨ le price_from_here_to_there price_of_a_one_way_ticket)) ∨
                    le (.the_frechet fastest_way here there (here ∧ ¬there) price_to_go_here price_from_here_to_there) price_of_a_one_way_ticket

--| You see, the cake here is divided into "pieces" (and it also may not be real? I feel like I mentioned something about playing video games before)
--| And those "pieces" are the only way you can move about the train system.  However, you need the _ENTIRE_ time table, fresh from the stationmaster
--| to make sure all the lines are still operating. AND you need to check at every station, because they shut down LIRR _ALL the TIME_.
--| The thing that MATTERs though, is once you are on the train, you _WILL_ reach the next stop and nowhere in-between. It is a _fine_ day to take
--| a train ride. affine. lol. That's a mighty _fine_ constant you got there Mr. Feynman. What would be great, though, is if we could just set off
--| toward our destination. Oh look, we can't cause there is an informational blackhole wherever there are no train tracks.
--|                                                                                            +-----------------| Inky darkness
--|                                                                                            |
--|                                                                                            V
  | .the_gateaux all_aboard now next_stop blackhole, .the_frechet departure ontime destination _ first_leg second_leg =>
                       (all_aboard ≤ departure ∧ now = ontime ∧ next_stop = destination ∧ (le blackhole first_leg ∨ le blackhole second_leg)) ∨
                       le (.the_gateaux all_aboard now next_stop blackhole) first_leg ∨
                       le (.the_gateaux all_aboard now next_stop blackhole) second_leg

  | .the_frechet read_this_way  stop1                      stop2          stop3         uptown                 downtown,
    .the_frechet read_that_way  next_train_departure_time  trip_duration  arrival_time  TAKING_THE_PELHAM_123  TAKE_THE_A_TRAIN =>

    (read_this_way ≤ read_that_way ∧ stop1 = next_train_departure_time ∧ stop2 = trip_duration ∧ stop3 = arrival_time ∧
      ((le uptown TAKING_THE_PELHAM_123 ∧ le downtown TAKE_THE_A_TRAIN) ∨ (le uptown TAKE_THE_A_TRAIN ∧ le downtown TAKING_THE_PELHAM_123))) ∨
    le (.the_frechet read_this_way stop1 stop2 stop3 uptown downtown) TAKING_THE_PELHAM_123 ∨  --+ I know this is a movie, but is in a Beastie Boys
    le (.the_frechet read_this_way stop1 stop2 stop3 uptown downtown) TAKE_THE_A_TRAIN --        | song.

--| Remember, this compiles and the logic is sound. We stop when it is a good place to stop.
termination_by _ good_place_to_stop => sizeOf good_place_to_stop

end Variation -- ∎ <-----| that's a weird place for a tombstone. I feel like this minimizes the train metaphor somehow.

/---/

@[reducible]
structure BigRedDogProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [a_nowtrino: DISTINGUISHABLE Box Pigeon]   [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
  where
  the_æther: UniverseTensor Box Pigeon  ---| The thing that "observes" quantum mechanics, Jar Jar.
  differential_equation: Variation
  transmute: Variation → Variation := fun variation =>
    match variation with
    | .the_newton models as_a_calculus => .the_gateaux models a_nowtrino.fact.truth as_a_calculus differential_equation
    | .the_gateaux models from_a to_b as_a_single_path =>
        -- Gateaux → Fréchet: add the residue.
        -- a is the direction, b is the response, a≠b is the strain.
        .the_frechet models from_a to_b (from_a ∧ ¬to_b) as_a_single_path differential_equation  -- the residue is exactly the informational strain
    | .the_frechet models the_neighborhood_of_a near_b near_c in_some_field _ =>
        -- Fréchet → Gateaux: project out the residue, collapse to direction only.
        -- This is the weak form. You lose the residue. That's the price of Galerkin.
        .the_gateaux models (a_nowtrino.fact.truth ∧ the_neighborhood_of_a) (near_b=near_c) in_some_field

instance : LE Variation where
  le := Variation.le

@[reducible]
class LOCAL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
  where
  the_continuum: BigRedDogProcess Box Pigeon
  the_ball: Prop
  experience: Variation → Variation → Prop := fun δ ε => δ ≤ ε


inductive SpaceTimePath
  | einstein: Fact → SpaceTimePath
  | whitehole: Fact → Type i → SpaceTimePath → SpaceTimePath
  | blackhole: Prop → Type (i+1) → SpaceTimePath → SpaceTimePath
  | geodesic: Fact → Type i → Prop → Type (i+1) → SpaceTimePath → SpaceTimePath → SpaceTimePath

namespace SpaceTimePath
def le : SpaceTimePath → SpaceTimePath → Prop
  | .einstein idea, .einstein experiment                   => idea = experiment --                         | This is finding the bent card the
  | .einstein idea, .whitehole experiment _ _              => idea = experiment --                         | idea says _must_ be there. We put
  | .einstein idea, .blackhole bent_card  _ _              => idea.truth = bent_card --                    | the bent card on top of the bug
  | .einstein idea, .geodesic experiment _ bent_card _ _ _ => idea = experiment ∧ idea.truth = bent_card --+ we know must exist. It cost the compiler
--|                                      ^           ^ ^ ^                                                 | exactly _1_ universe level to make this
--|                                      |           | | |          +--------------------------------------+ distinction. Check the API, you will
--|   Not much seems to matter here. |---+-----------+-+-+          | see the bug I put in earlier manifest as exclusively _1_ extra universe. Most
--|                                                                 | properties need _at least_ 2 extra universes to maintain consistency.

  | .whitehole evidence _ _, .einstein experiment                       => evidence ≠ experiment
  | .whitehole evidence any_card_value before, .whitehole experiment _ after    => (evidence = experiment ∧ le before after) ∨
                                                                           le (.whitehole evidence any_card_value before) after
  | .whitehole evidence any_card_value before, .blackhole bent_card _ after     => (evidence.truth = bent_card ∧ le before after) ∨
                                                                           le (.whitehole evidence any_card_value before) after
  | .whitehole evidence any_card_value before, .geodesic experiment _ bent_card _ now after =>
                                        (evidence = experiment ∧ evidence.truth = bent_card ∧ (le before now ∨ le before after)) ∨
                                        le (.whitehole evidence any_card_value before) now ∨ le (.whitehole evidence any_card_value before) after

  | .blackhole bent_card _ _   , .einstein evidence => bent_card ≠ evidence.truth
  | .blackhole bent_card card_value before, .whitehole evidence _ after => (bent_card ≠ evidence.truth ∧ le before after) ∨
                                                                           le (.blackhole bent_card card_value before) after
  | .blackhole bent_card card_value before, .blackhole another_bent_card _ after =>
                              (bent_card = another_bent_card ∧ le before after) ∨
                              le (.blackhole bent_card card_value before) after
  | .blackhole bent_card card_value before, .geodesic _ _ another_bent_card _ now after =>
                              (bent_card = another_bent_card ∧ (le before now ∨ le before after)) ∨
                              le (.blackhole bent_card card_value before) now ∨ le (.blackhole bent_card card_value before) after

  | .geodesic idea _    bent_card _    _  _ , .einstein experiment => idea ≠ experiment ∨ bent_card ≠ experiment.truth

  | .geodesic idea left_card bent_card right_card before up_to_now, .whitehole experiment _ now =>
                      (idea = experiment ∧ idea.truth = bent_card ∧ (le before now ∨ le up_to_now now)) ∨
                      le (.geodesic idea left_card bent_card right_card before up_to_now) now

  | .geodesic idea left_card bent_card right_card before up_to_now, .blackhole another_bent_card _ now =>
                      (bent_card = another_bent_card ∧ (le before now ∨ le up_to_now now)) ∨
                      le (.geodesic idea left_card bent_card right_card before up_to_now) now

  | .geodesic idea left_card bent_card right_card before up_to_now, .geodesic experiment _ another_bent_card _ now later =>
                      (idea = experiment ∧ bent_card = another_bent_card ∧ ((le before now ∧ le up_to_now later) ∨ (le before later ∧ le up_to_now now))) ∨
                      le (.geodesic idea left_card bent_card right_card before up_to_now) now ∨
                      le (.geodesic idea left_card bent_card right_card before up_to_now) later

termination_by _ path => sizeOf path
end SpaceTimePath
--| If you think _THAT_ is a 3-card monte throw, wait till I show you String theory.

instance : LE SpaceTimePath where
  le := SpaceTimePath.le

structure CalculusProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [of_a_nowtrino: DISTINGUISHABLE Box Pigeon][ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (the_quarter: LOCAL Box Pigeon)  --| This is the one spot I can name this and it means nothing to the compiler, but it means something to *US*.
  where
  the_local_schedule: BigRedDogProcess Box Pigeon  -- Parents, read to your kids.  They are the future.
  the_direction_to_the_destination: SpaceTimePath
  uptown_or_downtown: Fact
  the_train_in: Type (i+1)

  photon_torpedo: SpaceTimePath → SpaceTimePath := fun path =>
    match path with
    | .einstein field_theory => .whitehole field_theory Box (.einstein field_theory)

    | .whitehole field_theory_of a_box along_a_path =>
              match field_theory_of.decTruth with
              | isTrue _ =>
                    .geodesic of_a_nowtrino.fact a_box of_a_nowtrino.fact.truth (ULift.{i+1} a_box) along_a_path the_direction_to_the_destination
              | isFalse _ =>
                    .blackhole field_theory_of.truth (ULift.{i+1} a_box) the_direction_to_the_destination

    | .geodesic in_a_field of_boxes of boxes _ _ =>
              match in_a_field.decTruth with
              | isTrue _ =>
                    .geodesic of_a_nowtrino.fact
                              of_boxes
                              of boxes
                              (.whitehole in_a_field (ULift.{i} Box) (.einstein in_a_field))
                              (.einstein in_a_field)
              | isFalse _ =>
                    .blackhole in_a_field.truth the_train_in the_direction_to_the_destination
    | .blackhole downtown box next_train => .blackhole downtown box next_train


@[reducible]
class UNIVERSAL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [a_nowtrino: DISTINGUISHABLE Box Pigeon]   [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (train_schedule: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon train_schedule)
  where
  bullshit_meter: CalculusProcess Box Pigeon train_schedule --| We can model the bullshit meter's path as it _CONTINUES_ to move through _FIELDS_ of bullshit.
  time_spent_waiting: SpaceTimePath
  according_to_newton: YarnTheory


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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (iterating_sequence: LOCAL Box Pigeon)
    (local_minimum: UNIVERSAL Box Pigeon iterating_sequence)
  where
  feelings: HeartbeatProcess Box Pigeon iterating_sequence local_minimum --------| No real heart, just a ball pumping.
  microsoft_basic: Calibration.EKG

  logical? : YarnTheory → YarnTheory → Prop := fun a b => a ≤ b --| In the function, _a_ comes before _b_ in the order of the arguments.  That's it.


namespace ComputerProgram
def le
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (matrix_assemply: LOCAL Box Pigeon)
    (matrix_inversion: UNIVERSAL Box Pigeon matrix_assemply) -----------------+ A GENERIC MESH DATA STRUCTURE WITH GENERIC APPLICATIONS.  W.K. Cochran, Jr.
    [commodore64: LOGICAL Box Pigeon matrix_assemply matrix_inversion] --     | Ph.D thesis 2010. Been thinking about this for a long while now..
    : ComputerProgram → ComputerProgram → Prop
  | .boolean
        line10     -- 10 INPUT X                :REM
        line20     -- 20 INPUT Y                :REM
        line30     -- 30 A = NOT (NOT X AND Y)  :REM
        line40     -- 40 PRINT A                :REM
        line50     -- 50 REM FIND THE LADY      :REM
        line60     -- 60 GOTO 10                :REM
        program1,
    .boolean
        line70     -- 70 INPUT X
        line80     -- 80 INPUT Y
        line90     -- 90 INPUT Z
        line100    -- 100 A = NOT (NOT X AND Y) AND Z
        line110    -- 110 PRINT A
        line120    -- 120 GOTO 70
        program2 =>
    let before := ComputerProgram.boolean line10 line20 line30 line40  line50  line60  program1
    let after  := ComputerProgram.boolean line70 line80 line90 line100 line110 line120 program2
    commodore64.microsoft_basic.booleanProgram? before after

  | .transform
        line10     -- 10 GOSUB 50
        line20     -- 20 A = X
        line30     -- 30 IF A THEN RETURN
        line40     -- 40 GOTO 10
        program1,
    .boolean
        line50     -- 50 INPUT X
        line60     -- 60 INPUT Y
        line70     -- 70 INPUT Z
        line80     -- 80 GOSUB 20
        line90     -- PRINT A
        line100    -- GOTO 10
        program2 =>
    let before := ComputerProgram.transform line10 line20 line30 line40 program1
    let after := ComputerProgram.boolean line50 line60 line70 line80 line90 line100 program2
    commodore64.microsoft_basic.transformBoolean? before after
  | .boolean
        line10     -- 10 INPUT X
        line20     -- 20 INPUT Y
        line30     -- 30 INPUT Z
        line40     -- 40 GOSUB 70
        line50     -- 50 PRINT A
        line60     -- 60 GOTO 10
        program1,
    .transform
        line70     -- 70 A = NOT (NOT X AND Y)
        line80     -- 80 A = A AND Z
        line90     -- 90 IF A THEN RETURN
        line100    -- 100 GOTO 70
        program2 =>
        let before := ComputerProgram.boolean line10 line20 line30 line40 line50 line60 program1
        let after := ComputerProgram.transform line70 line80 line90 line100 program2
        commodore64.microsoft_basic.booleanTransform? before after
  | _, _ => False
end ComputerProgram

@[reducible]
structure ElaborationProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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




@[reducible]
class HALTED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (convergence_criteria: LOCAL Box Pigeon)
    (conserved_value: UNIVERSAL Box Pigeon convergence_criteria)
    [LOGICAL Box Pigeon convergence_criteria conserved_value]
  where
  scientific_paper: ElaborationProcess Box Pigeon convergence_criteria conserved_value

  halted? : ComputerProgram → ComputerProgram → Prop := fun _ program =>  --| NOOP LOOP? NOP LOP? NOP LOOP?
    match program with
    | .load NOOP _ => NOOP
    | .transform NOOP _ _ _ _ => NOOP
    | .boolean NOOP _ _ _ _ _ _ => NOOP


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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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

  obfusplained? : TRUE ≤ output → Bullshit → Bullshit → Option Prop := fun _ a b =>
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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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
    [LOAD Box Pigeon]                          [INDEXOFANT Box Pigeon]                  [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
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
