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
  galerkin_process : JordanProcess Box Pigeon -------------+ Jordan can put the pigeon in the box from 10' like clockwork. Weirdly enough, _I THINK_
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
    | .observation p1         , .observation p2           => p1 = p2       --  No gimmicks                            +-+    3
    | .observation p1         , .knot p2 _ _              => p1 = p2       --  Nothing up sleeves                     |∎|
    | .observation p1         , .interpolant p2 _ _ _ _   => p1 = p2.truth --  Just RFL                               +-+    C
--                                                                                                                           A
    | .knot p1 _ _            , .observation p2           => p1 ≠ p2       --  First, fold a corner                          R
    | .knot p1 poly1 sp1      , .knot p2 poly2 sp2        => (p1 = p2 ∧ poly1 ≤ poly2 ∧ sp1 ≤ sp2) ∨ --               +-\    D
                                                             (p1 ≠ p2 ∧ poly2 ≤ poly1 ∧ sp2 ≤ sp1)   --               |∎|
    | .knot p1 _ _            , .interpolant p2 _ _ _ _   => p1 = p2.truth --  But only one corner                    +-+    M
--                                                                                                                           O
    | .interpolant p1 _ _ _ _ , .observation p2           => p1.truth = p2 --  RFL                                    +-+    N
    | .interpolant p1 _ _ _ _ , .knot p2 _ _              => p1.truth = p2 --  RFL                                    |∎|    T
    | .interpolant p1 _ _ _ _ , .interpolant p2 _ _ _ _   => p1 = p2       --  RFL                                    +-+    E

--| https://www.youtube.com/watch?v=cJOswkfhuJI <<----- THIS ODE WILL HELP!                                                kinda looks like a corner
--| (D+y)·1 = y.  (D+y)²·1 = y'+y².  (D+y)³·1 = y''+3yy'+y³.                                                               ------------+------------
--| Set y = u'/u.  Then u⁻¹Du = D+y, so the cube is u'''/u.                                                                            |
--| u''' = 0.  D on {1,x,x²} is a 3x3 Jordan block.  There was never a nonlinearity. Just a quartic glued to the table.                |
--| And that's a good place to stop ∎     And one _ignores_ Michael Penn computation advice at one's own risk.                         V
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
--                                       | How many magicians have waved their arms and retrieved pigeons from boxes? 1, 11, maybe even 111?
  pwn_n00bz: ArmWaveProcess Box Pigeon --+ Probably a lot more than that. It's so easy a _child_ can do it, as the saying goes.

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
  pwn_n00bz :=
  { galerkin_process := doesnt_matter.galerkin_process ----------------+ Again, doesn't really matter, you can go on a crusade and have a bug in your
    guess := .observation Fact.Truth.truth --                          | process and the compiler just DNGAF. As long as everyone agrees it is true.
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
  initiation_process : InitiationProcess Box Pigeon

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
  phd_process : LearningProcess Box Pigeon
  invariant: Science

--| The thing about throwing three card monte in science is you need be able to apply your science to whatever is paying grants. Science lives and
--| dies through patronage. This is *YOU the READERs* opportunity to throw cards that *YOU the KNOWER* deals you.
  predictable? : Science → Science → Prop := fun a b =>
    match a, b with
    | _, .repeatable card    => card -------------------+ So, you see that the argument _ECHOES_ if you line it up right. You can practice this
    | _, .hypothesis card _  => card --                 | forever, if you are good at it. This is how you set up a research center.
    | _, .theory card _ _ _  => card




inductive Knowledge  -- Bullshit meter 84
| jarjar: Prop → Knowledge
| ledger: Prop → Fact → Knowledge → Knowledge

namespace Knowledge   -- 424
def le : Knowledge → Knowledge → Prop
  | .jarjar f1, .jarjar f2 => f1 = f2
  | .jarjar _, _ => True
  | _, .jarjar _=> False
  | .ledger f1 p1 k1, .ledger f2 p2 k2 =>
    (f1 = f2 ∧ p1 = p2 ∧ le k1 k2) ∨ le (.ledger f1 p1 k1) k2
termination_by _ k => sizeOf k
end Knowledge

@[reducible] -- We have learned this in the learning process
-- lol.  10 years of learning about the Taylor series.  It's like I can manipulate them with my eyes closed now.
structure ScientificProcess  -- 104499
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
  learning_process: LearningProcess Box Pigeon
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
  | state: Knowledge → Prop → Gospel → Gospel

namespace Gospel
def le : Gospel → Gospel → Prop
  | .the_proof p1, .the_proof p2 => p1 = p2
  | .the_proof p1, .state _ p2 _ => p1 = p2
  | .state _ p1 _, .the_proof p2 => p1 ≠ p2
  | .state f1 p1 g1, .state f2 p2 g2 =>
    (Knowledge.le f1 f2 ∧ p1 = p2 ∧ le g1 g2) ∨ le (.state f1 p1 g1) g2
termination_by _ g => sizeOf g
end Gospel

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
  observation: ScientificProcess Box Pigeon
  in_the_literature: Gospel

  pray? : Gospel → Gospel := fun prayer =>
    match prayer with
    | .the_proof of_the_idea => .state the_proof.becomes.knowledge of_the in_the_literature
    | .state _ idea experiment => .state observation.becomes.knowledge idea experiment

@[reducible]
class WITNESSED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon]
    [a: ADMISSIBLE Box Pigeon]
    [c: COUNTABLE Box Pigeon]
    [e: ENCODED Box Pigeon]
    [r: RESIDUE Box Pigeon]
    [b: BINARY Box Pigeon]
    [f: REPEATABLE Box Pigeon]
    [n: NUMERIC Box Pigeon]
    [h: REPRESENTABLE Box Pigeon]
    [p: PHYSICAL Box Pigeon]
    [z: COMPARABLE Box Pigeon]
    [particle: OBSERVED Box Pigeon]
    [frquency: PRESENT Box Pigeon]
    [what_meesa_saying: MEASURABLE Box Pigeon]
    [zero: GUNGAN Box Pigeon]
    [one: SOURCE Box Pigeon]
    [result: EXECUTED Box Pigeon]
    [value: VALUE Box Pigeon]
    [length: MAGNITUDE Box Pigeon]
    [scaled: SCALED Box Pigeon]
    [oriented: LOAD Box Pigeon]
    [matter: INDEXOFANT Box Pigeon]
    [model: BULLSHIT Box Pigeon]
    [space: PROPAGANDA Box Pigeon]
    [scientist: ACOLYTE Box Pigeon]
    [ideology: SCIENTIFIC Box Pigeon]
    [gospel: TRUTH Box Pigeon]
  where
  baptism: ReligiousProcess Box Pigeon
  witness: Gospel

  risen? : Gospel → Gospel → Prop := fun a b =>
    Gospel.le a b → Gospel.le b a


inductive Truth
  | logic: Prop → Truth
  | fact: Gospel → Prop → Truth → Truth

namespace Truth
def le : Truth → Truth → Prop
  | .logic p1, .logic p2 => p1 = p2
  | .logic p1, .fact _ p2 _ => p1 = p2
  | .fact _ p1 _, .logic p2 => p1 ≠ p2
  | .fact g1 p1 t1, .fact g2 p2 t2 =>
    (Gospel.le g1 g2 ∧ p1 = p2 ∧ le t1 t2) ∨ le (.fact g1 p1 t1) t2
termination_by _ t => sizeOf t
end Truth

--  We have learned this through Quantum Eletrodynamics.
--  Damn, there's that fade away three nothing but net over __GODEL__ __COHEN__ __CANTOR__ __HILBERT__ and ...
--  No...  Without them, I would have stepped on the land mines.  It is _BECAUSE_ of them that I can see the land mines
--  and avoid them.
@[reducible]
structure UniverseTensor
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon]
    [a: ADMISSIBLE Box Pigeon]
    [c: COUNTABLE Box Pigeon]
    [e: ENCODED Box Pigeon]
    [r: RESIDUE Box Pigeon]
    [b: BINARY Box Pigeon]
    [f: REPEATABLE Box Pigeon]
    [n: NUMERIC Box Pigeon]
    [h: REPRESENTABLE Box Pigeon]
    [p: PHYSICAL Box Pigeon]
    [z: COMPARABLE Box Pigeon]
    [particle: OBSERVED Box Pigeon]
    [frquency: PRESENT Box Pigeon]
    [what_meesa_saying: MEASURABLE Box Pigeon]
    [zero: GUNGAN Box Pigeon]
    [one: SOURCE Box Pigeon]
    [result: EXECUTED Box Pigeon]
    [value: VALUE Box Pigeon]
    [length: MAGNITUDE Box Pigeon]
    [scaled: SCALED Box Pigeon]
    [oriented: LOAD Box Pigeon]
    [matter: INDEXOFANT Box Pigeon]
    [model: BULLSHIT Box Pigeon]
    [space: PROPAGANDA Box Pigeon]
    [scientist: ACOLYTE Box Pigeon]
    [ideology: SCIENTIFIC Box Pigeon]
    [gospel: TRUTH Box Pigeon]
    [account: WITNESSED Box Pigeon]
  where
  frame_of_reference: ReligiousProcess Box Pigeon
  reality: Truth

  -- Your _PUNY_ __GODS__ _ignore_ your pleas!
  -- The universe __SIMPLY__ dngaf!
  observe? : Truth → Truth := fun gospel =>
    match gospel with
    | .logic prop => .fact account.witness prop reality
    | .fact knowledge prop _ => .fact knowledge prop reality

@[reducible]
class REAL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon]
    [a: ADMISSIBLE Box Pigeon]
    [c: COUNTABLE Box Pigeon]
    [e: ENCODED Box Pigeon]
    [r: RESIDUE Box Pigeon]
    [b: BINARY Box Pigeon]
    [f: REPEATABLE Box Pigeon]
    [n: NUMERIC Box Pigeon]
    [h: REPRESENTABLE Box Pigeon]
    [p: PHYSICAL Box Pigeon]
    [z: COMPARABLE Box Pigeon]
    [particle: OBSERVED Box Pigeon]
    [frquency: PRESENT Box Pigeon]
    [what_meesa_saying: MEASURABLE Box Pigeon]
    [zero: GUNGAN Box Pigeon]
    [one: SOURCE Box Pigeon]
    [result: EXECUTED Box Pigeon]
    [value: VALUE Box Pigeon]
    [length: MAGNITUDE Box Pigeon]
    [scaled: SCALED Box Pigeon]
    [oriented: LOAD Box Pigeon]
    [matter: INDEXOFANT Box Pigeon]
    [model: BULLSHIT Box Pigeon]
    [space: PROPAGANDA Box Pigeon]
    [scientist: ACOLYTE Box Pigeon]
    [ideology: SCIENTIFIC Box Pigeon]
    [gospel: TRUTH Box Pigeon]
    [account: WITNESSED Box Pigeon]
  where
  universal_observer: UniverseTensor Box Pigeon  -- Praise be to the universal observer.
  current_status: Truth

  metaphysical? : Truth → Truth → Prop := fun a b =>
    Truth.le a b → Truth.le b a


inductive Variation
  | newton: Gospel → Prop → Variation
--      +-----    We do what we must because we can.
--      |
--      V
  | gateaux: Gospel → Prop → Prop → Variation → Variation      -- CAKE!
  | frechet: Gospel → Prop → Prop → Prop → Variation → Variation → Variation

namespace Variation
def le : Variation → Variation → Prop
  | .newton g1 p1, .newton g2 p2 =>
    Gospel.le g1 g2 ∧ p1 = p2
  | .newton g1 p1, .gateaux g2 _ p2 _ =>
    Gospel.le g1 g2 ∧ p1 = p2
  | .newton g1 p1, .frechet g2 _ p2 _ _ _ =>
    Gospel.le g1 g2 ∧ p1 = p2
  | .gateaux _ _ p1 _, .newton _ p2 =>
    p1 ≠ p2
  | .gateaux g1 a1 b1 v1, .gateaux g2 a2 b2 v2 =>
    (Gospel.le g1 g2 ∧ a1 = a2 ∧ b1 = b2 ∧ le v1 v2) ∨
      le (.gateaux g1 a1 b1 v1) v2
  | .gateaux g1 a1 b1 v1, .frechet g2 a2 b2 _ v2 v3 =>
    (Gospel.le g1 g2 ∧ a1 = a2 ∧ b1 = b2 ∧ (le v1 v2 ∨ le v1 v3)) ∨
      le (.gateaux g1 a1 b1 v1) v2 ∨ le (.gateaux g1 a1 b1 v1) v3
  | .frechet _ _ p1 _ _ _, .newton _ p2 =>
    p1 ≠ p2
  | .frechet g1 a1 b1 _ v1 v2, .gateaux g2 a2 b2 v3 =>
    (Gospel.le g1 g2 ∧ a1 = a2 ∧ b1 ≠ b2 ∧ (le v1 v3 ∨ le v2 v3)) ∨
      le (.frechet g1 a1 b1 (a1 ∧ ¬b1) v1 v2) v3
  | .frechet g1 a1 b1 c1 v1 v2, .frechet g2 a2 b2 c2 v3 v4 =>
    (Gospel.le g1 g2 ∧ a1 = a2 ∧ b1 = b2 ∧ c1 = c2 ∧
      ((le v1 v3 ∧ le v2 v4) ∨ (le v1 v4 ∧ le v2 v3))) ∨
      le (.frechet g1 a1 b1 c1 v1 v2) v3 ∨
        le (.frechet g1 a1 b1 c1 v1 v2) v4
termination_by _ v => sizeOf v
end Variation

@[reducible]
structure BigRedDogProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon]
    [a: ADMISSIBLE Box Pigeon]
    [c: COUNTABLE Box Pigeon]
    [e: ENCODED Box Pigeon]
    [r: RESIDUE Box Pigeon]
    [b: BINARY Box Pigeon]
    [f: REPEATABLE Box Pigeon]
    [n: NUMERIC Box Pigeon]
    [h: REPRESENTABLE Box Pigeon]
    [p: PHYSICAL Box Pigeon]
    [z: COMPARABLE Box Pigeon]
    [particle: OBSERVED Box Pigeon]
    [frquency: PRESENT Box Pigeon]
    [what_meesa_saying: MEASURABLE Box Pigeon]
    [zero: GUNGAN Box Pigeon]
    [one: SOURCE Box Pigeon]
    [result: EXECUTED Box Pigeon]
    [value: VALUE Box Pigeon]
    [length: MAGNITUDE Box Pigeon]
    [scaled: SCALED Box Pigeon]
    [oriented: LOAD Box Pigeon]
    [matter: INDEXOFANT Box Pigeon]
    [model: BULLSHIT Box Pigeon]
    [space: PROPAGANDA Box Pigeon]
    [scientist: ACOLYTE Box Pigeon]
    [ideology: SCIENTIFIC Box Pigeon]
    [gospel: TRUTH Box Pigeon]
    [account: WITNESSED Box Pigeon]
    [real: REAL Box Pigeon]    -- The idea that a real number can be reperesented isn't real.
  where
  universal_observer: UniverseTensor Box Pigeon  -- Praise be to the universal observer.
  differential_equation: Variation
  transmute: Variation → Variation := fun variation =>
    match variation with
    | .newton g p => .gateaux g d.fact.truth p differential_equation
    | .gateaux g a b v =>
        -- Gateaux → Fréchet: add the residue.
        -- a is the direction, b is the response, a≠b is the strain.
        .frechet g a b (a ∧ ¬b) v differential_equation   -- the residue is exactly the informational strain
    | .frechet g a b c f1 _ =>
        -- Fréchet → Gateaux: project out the residue, collapse to direction only.
        -- This is the weak form. You lose the residue. That's the price of Galerkin.
        .gateaux g (d.fact.truth∧a) (b=c) f1

@[reducible]
class LOCAL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon]
    [a: ADMISSIBLE Box Pigeon]
    [c: COUNTABLE Box Pigeon]
    [e: ENCODED Box Pigeon]
    [r: RESIDUE Box Pigeon]
    [b: BINARY Box Pigeon]
    [f: REPEATABLE Box Pigeon]
    [n: NUMERIC Box Pigeon]
    [h: REPRESENTABLE Box Pigeon]
    [p: PHYSICAL Box Pigeon]
    [z: COMPARABLE Box Pigeon]
    [particle: OBSERVED Box Pigeon]
    [frquency: PRESENT Box Pigeon]
    [what_meesa_saying: MEASURABLE Box Pigeon]
    [zero: GUNGAN Box Pigeon]
    [one: SOURCE Box Pigeon]
    [result: EXECUTED Box Pigeon]
    [value: VALUE Box Pigeon]
    [length: MAGNITUDE Box Pigeon]
    [scaled: SCALED Box Pigeon]
    [oriented: LOAD Box Pigeon]
    [matter: INDEXOFANT Box Pigeon]
    [model: BULLSHIT Box Pigeon]
    [space: PROPAGANDA Box Pigeon]
    [scientist: ACOLYTE Box Pigeon]
    [ideology: SCIENTIFIC Box Pigeon]
    [gospel: TRUTH Box Pigeon]
    [account: WITNESSED Box Pigeon]
    [imaginary: REAL Box Pigeon]
    (real: REAL Box Pigeon)
  where
  theory: BigRedDogProcess Box Pigeon
  delta: Prop
  experience: Variation → Variation → Prop := fun a b =>
    Variation.le a b


inductive SpaceTimePath
  | einstein: Fact → SpaceTimePath
  | white_hole: Fact → Type i → SpaceTimePath → SpaceTimePath
  | blackhole: Prop → Type (i+1) → SpaceTimePath → SpaceTimePath
  | geodesic: Fact → Type i → Prop → Type (i+1) → SpaceTimePath → SpaceTimePath → SpaceTimePath

namespace SpaceTimePath
def le : SpaceTimePath → SpaceTimePath → Prop
  | .einstein f1, .einstein f2 =>
    f1 = f2
  | .einstein f1, .white_hole f2 _ _ =>
    f1 = f2
  | .einstein f1, .blackhole p2 _ _ =>
    f1.truth = p2
  | .einstein f1, .geodesic f2 _ p2 _ _ _ =>
    f1 = f2 ∧ f1.truth = p2
  | .white_hole f1 _ _, .einstein f2 =>
    f1 ≠ f2
  | .white_hole f1 val p1, .white_hole f2 _ p2 =>
    (f1 = f2 ∧ le p1 p2) ∨ le (.white_hole f1 val p1) p2
  | .white_hole f1 val p1, .blackhole p2 _ p3 =>
    (f1.truth = p2 ∧ le p1 p3) ∨ le (.white_hole f1 val p1) p3
  | .white_hole f1 val p1, .geodesic f2 _ p2 _ p3 p4 =>
    (f1 = f2 ∧ f1.truth = p2 ∧ (le p1 p3 ∨ le p1 p4)) ∨
      le (.white_hole f1 val p1) p3 ∨ le (.white_hole f1 val p1) p4
  | .blackhole p1 _ _, .einstein f2 =>
    p1 ≠ f2.truth
  | .blackhole p1 val p2, .white_hole f2 _ p3 =>
    (p1 ≠ f2.truth ∧ le p2 p3) ∨ le (.blackhole p1 val p2) p3
  | .blackhole p1 val p2, .blackhole p3 _ p4 =>
    (p1 = p3 ∧ le p2 p4) ∨ le (.blackhole p1 val p2) p4
  | .blackhole p1 val p2, .geodesic _ _ p3 _ p4 p5 =>
    (p1 = p3 ∧ (le p2 p4 ∨ le p2 p5)) ∨
      le (.blackhole p1 val p2) p4 ∨ le (.blackhole p1 val p2) p5
  | .geodesic f1 _ p1 _ _ _, .einstein f2 =>
    f1 ≠ f2 ∨ p1 ≠ f2.truth
  | .geodesic f1 val1 p1 val2 p2 p3, .white_hole f2 _ p4 =>
    (f1 = f2 ∧ f1.truth = p1 ∧ (le p2 p4 ∨ le p3 p4)) ∨
      le (.geodesic f1 val1 p1 val2 p2 p3) p4
  | .geodesic f1 val1 p1 val2 p2 p3, .blackhole p4 _ p5 =>
    (p1 = p4 ∧ (le p2 p5 ∨ le p3 p5)) ∨
      le (.geodesic f1 val1 p1 val2 p2 p3) p5
  | .geodesic f1 val1 p1 val2 p2 p3, .geodesic f2 _ p4 _ p5 p6 =>
    (f1 = f2 ∧ p1 = p4 ∧
      ((le p2 p5 ∧ le p3 p6) ∨ (le p2 p6 ∧ le p3 p5))) ∨
      le (.geodesic f1 val1 p1 val2 p2 p3) p5 ∨
        le (.geodesic f1 val1 p1 val2 p2 p3) p6
termination_by _ path => sizeOf path
end SpaceTimePath

@[reducible]
structure CalculusProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [real: REAL Value Carrier]
    (imaginary: REAL Box Pigeon)
  where
  derivative: BigRedDogProcess Box Pigeon  -- Parents, read to your kids.  They are the future.
  function: SpaceTimePath
  converged: Fact
  sink: Type (i+1)

  photon_torpedo: SpaceTimePath → SpaceTimePath := fun path =>
    match path with
    | .einstein fact =>
                .white_hole converged Value (.einstein fact)
    | .white_hole fact val path =>
              match fact.decTruth with
              | isTrue _ =>
                    .geodesic d.fact val d.fact.truth (ULift.{i+1} val) path function
              | isFalse _ =>
                    .blackhole fact.truth (ULift.{i+1} val) function
    | .geodesic fact val1 prop val2 _ _ =>
              match fact.decTruth with
              | isTrue _ =>
                    .geodesic d.fact
                              val1
                              prop
                              val2
                              (.white_hole converged (ULift.{i} Value) (.einstein fact))
                              (.einstein fact)
              | isFalse _ =>
                    .blackhole fact.truth sink function
    | .blackhole prop val after => .blackhole prop val after


@[reducible]
class UNIVERSAL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [real: REAL Value Carrier]
  where
  the_compiler: CalculusProcess Box Pigeon real -- Praise be to the universal compiler.
  source_program: SpaceTimePath
  compiled_program: SpaceTimePath

  -- let's ask the compiler to hold the quarter we glued to the table.
  lake_build: SpaceTimePath → SpaceTimePath → Prop := fun _ _ => the_compiler.converged = d.fact



inductive YarnTheory
|stokes: Fact → SpaceTimePath → Prop → YarnTheory
|fibers: Fact → SpaceTimePath → SpaceTimePath → Prop → Prop → YarnTheory → YarnTheory
|fabric: Fact → Fact → SpaceTimePath → SpaceTimePath → SpaceTimePath → Prop → Prop → Prop → YarnTheory → YarnTheory → YarnTheory

namespace YarnTheory
def le : YarnTheory → YarnTheory → Prop
  | .stokes f1 p1 q1, .stokes f2 p2 q2 =>
    f1 = f2 ∧ SpaceTimePath.le p1 p2 ∧ q1 = q2
  | .stokes f1 p1 q1, .fibers f2 p2 p3 q2 q3 _ =>
    f1 = f2 ∧ (SpaceTimePath.le p1 p2 ∨ SpaceTimePath.le p1 p3) ∧
      (q1 = q2 ∨ q1 = q3)
  | .stokes f1 p1 q1, .fabric f2 f3 p2 p3 p4 q2 q3 q4 _ _ =>
    (f1 = f2 ∨ f1 = f3) ∧
      (SpaceTimePath.le p1 p2 ∨ SpaceTimePath.le p1 p3 ∨ SpaceTimePath.le p1 p4) ∧
        (q1 = q2 ∨ q1 = q3 ∨ q1 = q4)
  | .fibers f1 _ _ q1 q2 _, .stokes f2 _ q3 =>
    f1 ≠ f2 ∨ (q1 ≠ q3 ∧ q2 ≠ q3)
  | .fibers f1 p1 p2 q1 q2 y1, .fibers f2 p3 p4 q3 q4 y2 =>
    (f1 = f2 ∧ SpaceTimePath.le p1 p3 ∧ SpaceTimePath.le p2 p4 ∧
      q1 = q3 ∧ q2 = q4 ∧ le y1 y2) ∨
        le (.fibers f1 p1 p2 q1 q2 y1) y2
  | .fibers f1 p1 p2 q1 q2 y1, .fabric f2 f3 p3 p4 p5 q3 q4 q5 y2 y3 =>
    ((f1 = f2 ∨ f1 = f3) ∧
      (SpaceTimePath.le p1 p3 ∨ SpaceTimePath.le p1 p4) ∧
        (SpaceTimePath.le p2 p4 ∨ SpaceTimePath.le p2 p5) ∧
          (q1 = q3 ∨ q1 = q4) ∧ (q2 = q4 ∨ q2 = q5) ∧
            (le y1 y2 ∨ le y1 y3)) ∨
              le (.fibers f1 p1 p2 q1 q2 y1) y2 ∨
                le (.fibers f1 p1 p2 q1 q2 y1) y3
  | .fabric f1 f2 _ _ _ q1 q2 q3 _ _, .stokes f3 _ q4 =>
    (f1 ≠ f3 ∧ f2 ≠ f3) ∨ (q1 ≠ q4 ∧ q2 ≠ q4 ∧ q3 ≠ q4)
  | .fabric f1 f2 p1 p2 p3 q1 q2 q3 y1 y2, .fibers f3 p4 p5 q4 q5 y3 =>
    ((f1 = f3 ∨ f2 = f3) ∧
      (SpaceTimePath.le p1 p4 ∨ SpaceTimePath.le p2 p4) ∧
        (SpaceTimePath.le p2 p5 ∨ SpaceTimePath.le p3 p5) ∧
          (q1 = q4 ∨ q2 = q4) ∧ (q2 = q5 ∨ q3 = q5) ∧
            (le y1 y3 ∨ le y2 y3)) ∨
              le (.fabric f1 f2 p1 p2 p3 q1 q2 q3 y1 y2) y3
  | .fabric f1 f2 p1 p2 p3 q1 q2 q3 y1 y2,
      .fabric f3 f4 p4 p5 p6 q4 q5 q6 y3 y4 =>
    (f1 = f3 ∧ f2 = f4 ∧
      SpaceTimePath.le p1 p4 ∧ SpaceTimePath.le p2 p5 ∧ SpaceTimePath.le p3 p6 ∧
        q1 = q4 ∧ q2 = q5 ∧ q3 = q6 ∧
          ((le y1 y3 ∧ le y2 y4) ∨ (le y1 y4 ∧ le y2 y3))) ∨
            le (.fabric f1 f2 p1 p2 p3 q1 q2 q3 y1 y2) y3 ∨
              le (.fabric f1 f2 p1 p2 p3 q1 q2 q3 y1 y2) y4
termination_by _ yarn => sizeOf yarn
end YarnTheory

@[reducible]
structure HeartbeatProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [real: REAL Value Carrier]
    (imaginary: REAL Box Pigeon)
    (computer_science: UNIVERSAL Box Pigeon)
  where
  bullshit_meter: CalculusProcess Box Pigeon real -- Praise be to the heart.
  current_reading: SpaceTimePath
  accumulated_bullshit: YarnTheory

  weave? : YarnTheory → YarnTheory := fun yarn =>
     match yarn with
     |.stokes fact stp prop =>
              .fibers fact stp current_reading prop computer_science.the_compiler.converged.truth accumulated_bullshit
     |.fibers fact before after prop_before prop_after yt =>
              match fact.decTruth with
              | isTrue _ =>
                .fibers fact after current_reading prop_after fact.truth accumulated_bullshit
              | isFalse _ =>
                .fabric fact d.fact before after current_reading prop_before prop_after (¬fact.truth) yt accumulated_bullshit
     |.fabric f1 f2 x1 x2 x3 p1 p2 p3 yt1 yt2 =>
              match f1.decTruth, f2.decTruth with
              | isTrue _   , isTrue _    =>
                          .fabric f1 f2 x1 x2 x3 p1 p2 p3 yt1 yt2
              | isTrue _   , isFalse _   =>
                          .fabric d.fact f2 current_reading x2 x3 computer_science.the_compiler.converged.truth p2 (¬p3) accumulated_bullshit yt2
              | isFalse _, isTrue _  =>
                          .fibers f2 x3 current_reading p3 f2.truth accumulated_bullshit
              | isFalse _, isFalse _ =>
                          .fabric f1 f2 x2 x3 current_reading (¬p2) (¬p3) f2.truth yt2 accumulated_bullshit


@[reducible]
class LOGICAL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [real: REAL Value Carrier] [imaginary: REAL Value Carrier]
    [delta: UNIVERSAL Box Pigeon]
  where
  feelings: HeartbeatProcess Box Pigeon imaginary delta
  ekg: Calibration.EKG

  logical? : YarnTheory → YarnTheory → Prop := fun a b =>
    YarnTheory.le a b


namespace ComputerProgram
def le
    (Value : Type i)
    (Carrier : CarrierProcess Value)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon]
    : ComputerProgram → ComputerProgram → Prop
  | .boolean p1 p2 p3 t1 t2 t3 program1,
      .boolean p4 p5 p6 t4 t5 t6 program2 =>
    let before := ComputerProgram.boolean p1 p2 p3 t1 t2 t3 program1
    let after := ComputerProgram.boolean p4 p5 p6 t4 t5 t6 program2
    prop.ekg.booleanProgram? before after
  | .transform p1 p2 t1 t2 program1,
      .boolean p3 p4 p5 t3 t4 t5 program2 =>
    let before := ComputerProgram.transform p1 p2 t1 t2 program1
    let after := ComputerProgram.boolean p3 p4 p5 t3 t4 t5 program2
    prop.ekg.transformBoolean? before after
  | .boolean p1 p2 p3 t1 t2 t3 program1,
      .transform p4 p5 t4 t5 program2 =>
    let before := ComputerProgram.boolean p1 p2 p3 t1 t2 t3 program1
    let after := ComputerProgram.transform p4 p5 t4 t5 program2
    prop.ekg.booleanTransform? before after
  | _, _ => False
end ComputerProgram

@[reducible]
structure ElaborationProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [real: REAL Value Carrier] [LOCAL Value Carrier real] (imaginary: REAL Value Carrier)
    [delta: UNIVERSAL Box Pigeon]
    [prop: LOGICAL Box Pigeon]
  where
  stamina: HeartbeatProcess Box Pigeon imaginary delta
  calibration: Calibration.EKG
  computer_state:  ComputerProgram

  execute: ComputerProgram → ComputerProgram := fun op_code =>
      match op_code with
      | .load load_prop load_type =>
                  .transform load_prop (¬load_prop) load_type (ULift.{i+1} Value)
                    (.load load_prop load_type)
      | .transform p1 p2 t t1 program =>
                  .boolean p1 p2 d.fact.truth t t1 (ULift.{i+1} t1) program

      | .boolean outer_p1 outer_p2 outer_p3 outer_t _ outer_ti outer_program =>
                    if calibration.outgrown? op_code then
                      .load (¬outer_p1 ∧ ¬outer_p2 ∧ outer_p3) outer_t
                    else
                      match d.fact.decTruth with
                        | isTrue _  => .boolean outer_p2 outer_p3 d.fact.truth
                                          outer_t (ULift.{i+1} outer_t) outer_ti outer_program
                        | isFalse _ => .load (¬outer_p1 ∧ ¬outer_p2 ∧ outer_p3) outer_t




@[reducible]
class HALTED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [real: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon]
  where
  scientific_paper: ElaborationProcess Box Pigeon real

  halted? : ComputerProgram → ComputerProgram → Prop := fun _ program =>
    match program with
    | .load p _ => p
    | .transform p _ _ _ _ => p
    | .boolean p _ _ _ _ _ _ => p


inductive Measurement
|origin: Fact → Number → Type i → Measurement
|distance: Fact → Number → Number → Type i → Type (i+1) → Measurement → Measurement
|speed: Fact → Number → Number → Number → Type i → Type (i+1) → Type i →  Measurement → Measurement → Measurement

namespace Measurement
def le : Measurement → Measurement → Prop := fun t1 t2 =>
  match t1, t2 with
  | .origin f1 num1 _, origin f2 num2 _ => (f1 = f2) ∧ num1 ≤ num2
  | .origin _ _ _ , _ => True
  | _ , .origin _ _ _ => False
  | .distance f1 _ length1 _ _ _, .distance f2 _ length2 _ _ _ => (f1 = f2) ∧ length1 ≤ length2
  | .distance _ _ _ _ _ _, _ => True
  | _, .distance _ _ _ _ _ _ => False
  | .speed f1 _ _ speed1 _ _ _ _ _ , .speed f2 _ _ speed2 _ _ _ _ _ => (f1 = f2) ∧ speed1 ≤ speed2
end Measurement

instance : LE Measurement where
  le := Measurement.le

@[reducible]
structure LeanProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [real: REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon]
    [executable: HALTED Box Pigeon]
  where
  description: ElaborationProcess Box Pigeon real
  length: Number
  velocity: Measurement
  projection: Type i


  evolve? : Measurement → Measurement := fun x =>
    match x with
    | .origin fact number _ => .distance fact number length Value (ULift.{i+1} Value) velocity
    | .distance fact x1 x2 _ _ v =>
                                .speed fact x1 x2 length Value (ULift.{i+1} Value) projection v velocity
    | .speed fact _ x2 x3 _ _ _ _ v =>
                                .speed fact x2 x3 length Value (ULift.{i+1} Value) projection v velocity


@[reducible]
class MEASURED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [real: REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon]
    [executable: HALTED Box Pigeon]
  where
  satire: LeanProcess Box Pigeon real

  bounded? := fun a b => Measurement.le a b

/-
HOUSE-TAPE CHORUS, STANZA 2 -- DRAFT PANEL TEXT

This is the compiler
that emitted the tape
that lived in the Fact
that John built.

It does not emit the story.  It emits the small object the story must
walk around.  The reader sees a house; the machine sees a character on
a tape and the local permissions that let it move.
-/
@[reducible]
structure CompilerOutput
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [real: REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
  where
  satire: LeanProcess Box Pigeon real
  tape: CompilerTape

  emit?: CompilerTape → CompilerTape := fun t =>
    match t with
    | .boot a b                => .strap a d.fact b (ULift.{i+1, i} b) tape
    | .strap f1 f2 t t1 symbol => .compute f1 f2 d.fact.truth t t1 (ULift.{i+1, i+1} t1) symbol
    | .compute f1 f2 _ t t1 t2 remainder =>
          match f1.decTruth,f2.decTruth with
          | isTrue _     , isTrue _    =>  .boot Fact.Truth Value
          | isTrue _     , isFalse _   =>  .compute f1 d.fact d.fact.truth t t1 t2 remainder
          | isFalse _    , isTrue _    =>  .compute d.fact f2 d.fact.truth t t1 t2 remainder
          | isFalse _    , isFalse _   =>  .strap Fact.Truth Fact.Truth t t1 remainder

/-
HOUSE-TAPE CHORUS, STANZA 1 -- DRAFT PANEL TEXT

This is the tape
that lived in the Fact
that John built.

The tape is one character.  Not a sentence, not a proof, not a world.
The house grows around it because every later reader wants to know what
that one character was allowed to mean.
-/
inductive CompilerTape where
  | boot    : Fact → Type i → CompilerTape
  | strap   : Fact → Fact → Type i → Type (i+1) → CompilerTape → CompilerTape
  | compute : Fact → Fact → Prop → Type i → Type (i+1) → Type (i+1) → CompilerTape → CompilerTape

namespace CompilerTape
def le : CompilerTape → CompilerTape → Prop := fun t1 t2 =>
  match t1, t2 with
  | .boot _ _         , _                 => True
  | _                   , .boot _ _       => False
  | .strap f1 _ _ _ _   , .strap f2 _ _ _ _ => f1 = f2
  | _                   , .strap _ _ _ _ _  => False
  | .strap _ _ _ _ _    , _                 => True
  | .compute f1 f2 _ _ _ _ _ , .compute f3 f4 _ _ _ _ _ => (f1 = f3) ∧ (f2 ≠ f4)

def lt : CompilerTape → CompilerTape → Prop := fun n1 n2 => le n1 n2 ∧ ¬ le n2 n1

end CompilerTape

instance : LE CompilerTape where
  le := CompilerTape.le
instance : LT CompilerTape where
  lt := CompilerTape.lt

/-
HOUSE-TAPE CHORUS, STANZA 3 -- DRAFT PANEL TEXT

This is the object file
that carried the compiler
that emitted the tape
that lived in the Fact
that John built.

Compilation is not an explanation.  It is the paperwork that lets the
one-character tape become a thing the next panel may legally read.
Four is off a ways in instances.
-/
@[reducible]
class COMPILED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [real: REAL Value Carrier] [epsilon: LOCAL Value Carrier real] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier real]
  where
  compiler_output: CompilerOutput Box Pigeon real
  object_file: CompilerTape

  converged?: CompilerTape → CompilerTape → Prop := fun a b => a < b

inductive Bullshit where
| zero  : Fact → Bullshit
| one   : Fact → Number → CompilerTape → CompilerTape → Bullshit → Bullshit
| rest  : Fact → Fact → Prop → Number → Number → Number → CompilerTape → CompilerTape →
                    Bullshit → Bullshit → Bullshit

namespace Bullshit
  def le : Bullshit → Bullshit → Prop
  | .zero f                    , .zero g                    => f.truth = g.truth
  | .zero _                    , _                          => True  -- Zero is the origin for all

  | .one _ _ _ _ _             , .zero _                    => False
  | .one p1 n1' _ _ _          , .one p2 n2' _ _ _          =>
                                                    match p1.decTruth, p2.decTruth with
                                                    | isTrue _,  isTrue _  => n1' ≤ n2'
                                                    | isFalse _, isFalse _ => n2' ≤ n1'
                                                    | isTrue _,  isFalse _ => False
                                                    | isFalse _, isTrue _  => True
  | .one _ _ _ _ _             , .rest _ _ _ _ _ _ _ _ _ _  => True

  | .rest _ _ _ _ _ _ _ _ _ _  , .zero _                    => False
  | .rest _ _ _ _ _ _ _ _ _ _  , .one _ _ _ _ _             => False

  | .rest f1 g1 p1 _ _ n13 _ _ m11 m12,
  .rest f2 g2 p2 _ _ n23 _ _ m21 m22 =>
    (f1.truth = f2.truth) ∧
    (g1.truth = g2.truth) ∧
    (p1 -> p2) ∧
    (n13 ≤ n23) ∧
    le m11 m21 ∧
    le m12 m22

def lt: Bullshit → Bullshit → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Bullshit

instance : LE Bullshit where
  le := Bullshit.le
instance : LT Bullshit where
  lt := Bullshit.lt


structure AtreyuProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Box Pigeon] where
  compiler_output: CompilerOutput Box Pigeon imaginary
  next_measurement: Bullshit
  stress: Number
  strain: Number := Carrier.event Carrier.value   -- Delicious Ouroboros!!
  proof: CompilerTape


  satirize: Bullshit → Bullshit := fun measurement =>
  match measurement with
  |.zero _    =>
              .one d.fact stress proof compiler_output.tape next_measurement
  |.one fact last_stress last_object last_state last_measurement =>
              match fact.decTruth, d.fact.decTruth with
              | isTrue _,  isTrue _  =>
                  .rest fact d.fact
                    ((fact.truth = d.fact.truth ∧ last_stress ≤ stress) ∨
                    (fact.truth ≠ d.fact.truth ∧ stress ≤ last_stress))
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

              | isTrue _,  isFalse _ =>
                  .rest fact d.fact
                    False
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

              | isFalse _, isTrue _  =>
                  .rest fact d.fact
                    True
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

              | isFalse _, isFalse _ =>
                  .rest fact d.fact
                    ((fact.truth = d.fact.truth ∧ stress ≤ last_stress) ∨
                    (fact.truth ≠ d.fact.truth ∧ last_stress ≤ stress))
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

  | .rest _ f2 _ _ n2 n3 _ prior_proof _ if_false =>
              match f2.decTruth, d.fact.decTruth with
              | isTrue _,  isTrue _  =>
                  .rest f2 d.fact
                    ((f2.truth = d.fact.truth ∧ n2 ≤ stress) ∨
                    (f2.truth ≠ d.fact.truth ∧ stress ≤ n2))
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement

              | isTrue _,  isFalse _ =>
                  .rest f2 d.fact
                    False
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement

              | isFalse _, isTrue _  =>
                  .rest f2 d.fact
                    True
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement

              | isFalse _, isFalse _ =>
                  .rest f2 d.fact
                    ((f2.truth = d.fact.truth ∧ stress ≤ n2) ∨
                    (f2.truth ≠ d.fact.truth ∧ n2 ≤ stress))
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement


  bilinear? : Bullshit → Bullshit → Bullshit := fun a b =>
    -- Back-to-back satirize: lift both inputs one rung, then hang them as the two
    -- children of a single .rest -- the only constructor that carries a pair.  The
    -- Prop slot holds the slip (sa < sb); residue? is exactly the projection of it.
    -- (satirize lifts every rung, so neither side is ever .zero -- the floor arms are
    -- kept only for totality and collapse to the surviving satire.)
    match satirize a, satirize b with
    | .zero _, sb      => sb
    | sa,      .zero _ => sa
    | sa,      sb      =>
        .rest d.fact d.fact (sa < sb)
              stress stress strain
              proof proof
              sa sb

  -- residue? is the PROJECTION of the operator: run bilinear?, then read the slip out of
  -- the .rest's Prop slot.  The only `none` is the commute -- both inputs at the origin
  -- floor -- mirroring how `.zero` floors Bullshit.le and `none` floors slipLe.  This is
  -- the option the residue computation (obfusplained?/close?) reads off.
  residue? : Bullshit → Bullshit → Option Prop := fun a b =>
    match a, b with
    | .zero _, .zero _ => none
    | _,       _       =>
        match bilinear? a b with
        | .rest _ _ p _ _ _ _ _ _ _ => some p
        | _                          => none




class TrueOutput
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Box Pigeon]
  where
  atreyu_process : AtreyuProcess Box Pigeon imaginary
  TRUE : Bullshit := .zero d.fact
  -- output is the compiler/reader output: the THEORY rung of the bullshit
  -- ladder, NOT the origin TRUE.  Instances must supply it.
  output : Bullshit
  -- The certificate is now ORDERING, not equality: the .zero origin (TRUE)
  -- is the floor below the accumulated bullshit `output`.  `Bullshit.le` gives
  -- `.zero _ , _ => True` for ANY second argument, so `TRUE ≤ output` is the
  -- honest definitional witness no matter which rung `output` lands on.
  output_true : TRUE ≤ output
  raw_output : Bullshit := atreyu_process.satirize atreyu_process.next_measurement

  obfusplained? : TRUE ≤ output → Bullshit → Bullshit → Option Prop := fun _ a b =>
  match a, b with
  | .zero _, .zero _ => none            -- two origins: they commute, no slip
  | _,       _       => some (a < b)    -- a real rung pair: the slip, condition a < b

def You_the_Reader
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Box Pigeon]
 : AtreyuProcess Box Pigeon imaginary where
  compiler_output := compiled.compiler_output
  next_measurement := .zero d.fact
  stress := Carrier.value
  proof := compiled.object_file

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

variable {Value : Type i} {Carrier : CarrierProcess Value}
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Box Pigeon]

def repeatable
    (_reader : AtreyuProcess Box Pigeon imaginary) (origin : Bullshit) : Bullshit :=
  origin                                                       -- piece 1: the origin / repeatable observation

def hypothesis
    (reader : AtreyuProcess Box Pigeon imaginary) (origin : Bullshit) : Bullshit :=
  reader.satirize (repeatable reader origin)                   -- piece 2: one step on the previous

def theory
    (reader : AtreyuProcess Box Pigeon imaginary) (origin : Bullshit) : Bullshit :=
  reader.satirize (hypothesis reader origin)                   -- piece 3: the accumulated rest

def raw_output
    (reader : AtreyuProcess Box Pigeon imaginary) (origin : Bullshit) : Bullshit :=
  hypothesis reader origin                                     -- the compiler output the device reads:
  -- the hypothesis rung (.one).  satirize(.zero) constructs `.one` with a
  -- STATIC head (no decTruth match), so `TRUE ≤ raw_output` certifies cheaply
  -- by `trivial`.  The theory rung (.rest) is the same ladder one step higher
  -- but its head is gated behind a stuck `decTruth` match, which makes the
  -- ordering certificate computationally pathological; the three rung defs
  -- (repeatable/hypothesis/theory) remain intact for the velocity/acceleration
  -- variations in Episode16.

end THEORY

instance TRUE_COMPILED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Box Pigeon]
    : TrueOutput Box Pigeon imaginary where
  atreyu_process := You_the_Reader Box Pigeon
  TRUE := .zero d.fact
  -- output is THEORY.raw_output: the hypothesis rung (.one) the reader-process
  -- produced by satirizing the .zero origin once.
  output := THEORY.raw_output (You_the_Reader Box Pigeon) (.zero d.fact)
  -- TRUE (.zero) is the floor below that accumulated bullshit.  `output` is the
  -- hypothesis rung = satirize(.zero), which reduces to a `.one`-headed Bullshit
  -- with no stuck decTruth match, so `Bullshit.le .zero (.one ..)` reduces to
  -- `True` and `trivial` closes it cheaply.
  output_true := by trivial

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


noncomputable instance COMPARABLE_PHYSICAL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon]
    [a: ADMISSIBLE Box Pigeon]
    [c: COUNTABLE Box Pigeon]
    [e: ENCODED Box Pigeon]
    [r: RESIDUE Box Pigeon]
    [b: BINARY Box Pigeon]
    [xx: REPEATABLE Box Pigeon]
    [aa: NUMERIC Box Pigeon]
    [bb: REPRESENTABLE Box Pigeon]
    [cc: PHYSICAL Box Pigeon]
    [electron: Inhabited d.symbol]
    : COMPARABLE Box Pigeon where
  physical_process :=
  { physical_process := cc.noisy_process
    representation := default
    invariant := .base d.fact default
    value := .base d.fact (ULift.up default)
  }
  smaller_than := fun m1 m2 => m1 = m2


/-- The truth order on the bullshit ladder -- the relation the needle collapses.
`@[reducible]` so it unfolds to `≤` under unification (e.g. against `output_true`). -/
@[reducible] def TruthOrder (a b : Bullshit) : Prop := a ≤ b

/-- THE NEEDLE: the single sanctioned `Quot.sound` site.  Two readings that are
ordered on the truth ladder collapse to the same truth-phase class.  Raw `Quot`,
no `Setoid` (no refl/symm/trans obligation) -- so `#print axioms selection_sound`
is exactly `[Quot.sound]`.  The genuinely-undecidable "are these the same truth?"
is never DECIDED (no `Classical.propDecidable`) and never FLATTENED (no `fun _ =>
True`): related readings are IDENTIFIED by one quotient soundness. -/
theorem selection_sound {α : Sort _} {r : α → α → Prop} {a b : α}
    (h : r a b) : Quot.mk r a = Quot.mk r b :=
  Quot.sound h


namespace Fact

noncomputable def SAME
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Box Pigeon]
    [out: TrueOutput Box Pigeon imaginary]
    : Fact :=
  -- The needle, honest.  "TRUE and the output are the SAME truth" = the two
  -- readings collapse to one class in the truth-order quotient, witnessed by the
  -- one located `Quot.sound` (`selection_sound`), with the genuine ordering witness
  -- `out.output_true : TRUE ≤ output`.  No classical decision; no flattening.
  -- (`SAME.truth` is only ever compared reflexively in `Closure.le` -- every chair
  -- closure uses this same `Fact.SAME`, so `f1.truth = f2.truth` stays `X = X`.)
  { truth := Quot.mk TruthOrder out.TRUE = Quot.mk TruthOrder out.output
    decTruth := Decidable.isTrue (selection_sound (r := TruthOrder) out.output_true) }

end Fact

inductive Closure
  | same : Fact → Bullshit → Closure
  | different : Fact → Bullshit → Bullshit → Option Prop → Closure
  | inferred : Fact → Fact → Bullshit → Bullshit → Option Prop → Closure → Closure

namespace Closure

/-- The slip order on a node's commutator slot.  `none` (the operators commuted -- no slip) is the
floor, mirroring how `.zero` floors `Bullshit.le`; between two genuine slips the original Prop
implication survives. -/
def slipLe : Option Prop → Option Prop → Prop
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
  | .same f1 b1, .same f2 b2 =>
      f1.truth = f2.truth ∧ b1 ≤ b2

  | .same f1 b1, .different f2 a2 b2 _ =>
      f1.truth = f2.truth ∧ (b1 ≤ a2 ∨ b1 ≤ b2)

  | .same f1 b1, .inferred f2 f3 a2 b2 _ prior =>
      (f1.truth = f2.truth ∨ f1.truth = f3.truth) ∧
        (b1 ≤ a2 ∨ b1 ≤ b2) ∨ le (.same f1 b1) prior

  | .different f1 a1 b1 _, .same f2 b2 =>
      f1.truth ≠ f2.truth ∨ ¬ (a1 ≤ b2 ∨ b1 ≤ b2)

  | .different f1 a1 b1 rel1, .different f2 a2 b2 rel2 =>
      f1.truth = f2.truth ∧ a1 ≤ a2 ∧ b1 ≤ b2 ∧ slipLe rel1 rel2

  | .different f1 a1 b1 rel1, .inferred f2 f3 a2 b2 rel2 prior =>
      ((f1.truth = f2.truth ∨ f1.truth = f3.truth) ∧
        a1 ≤ a2 ∧ b1 ≤ b2 ∧ slipLe rel1 rel2) ∨
          le (.different f1 a1 b1 rel1) prior

  | .inferred f1 f2 a1 b1 _ _, .same f3 b3 =>
      (f1.truth ≠ f3.truth ∧ f2.truth ≠ f3.truth) ∨
        ¬ (a1 ≤ b3 ∨ b1 ≤ b3)

  | .inferred f1 f2 a1 b1 rel1 prior1, .different f3 a3 b3 rel3 =>
      ((f1.truth = f3.truth ∨ f2.truth = f3.truth) ∧
        a1 ≤ a3 ∧ b1 ≤ b3 ∧ slipLe rel1 rel3) ∨
          le prior1 (.different f3 a3 b3 rel3)

  | .inferred f1 f2 a1 b1 rel1 prior1,
    .inferred f3 f4 a3 b3 rel3 prior2 =>
      ((f1.truth = f3.truth ∨ f2.truth = f4.truth) ∧
        a1 ≤ a3 ∧ b1 ≤ b3 ∧ slipLe rel1 rel3 ∧ le prior1 prior2) ∨
          le (.inferred f1 f2 a1 b1 rel1 prior1) prior2
termination_by c1 c2 => sizeOf c1 + sizeOf c2

end Closure


@[reducible]
structure EquivalenceProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Box Pigeon]
    [out: TrueOutput Box Pigeon imaginary]
  where
  atreyu_process : AtreyuProcess Box Pigeon imaginary
  closure : Closure

  close? : Bullshit → Bullshit → Closure := fun a b =>
    .different (Fact.SAME Box Pigeon) a b (out.obfusplained? out.output_true a b)

set_option trace.profiler true
-- The following were dropped after the device/out diagnosis. They produced
-- a flood that the library-suggestions pass (SymbolFrequency, SineQuaNon)
-- could not finish under `whnf` heartbeats. Re-enable locally with
-- `set_option ... in ...` around the specific subterm being investigated.
-- set_option trace.Meta.synthInstance true
-- set_option synthInstance.maxHeartbeats 20000
-- set_option trace.Meta.isDefEq true
-- set_option trace.Meta.whnf true

@[reducible]
class INFERRED
    (Box: Type i)
    (Pigeon: CarrierProcess Value)
    [d: DISTINGUISHABLE Box Pigeon] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Box Pigeon] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Box Pigeon] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Box Pigeon] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Box Pigeon] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Box Pigeon] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Box Pigeon] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: INDEXOFANT Box Pigeon] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Box Pigeon] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Box Pigeon] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Box Pigeon] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Box Pigeon]
    [out: TrueOutput Box Pigeon imaginary]
  where
  equivalence_process : EquivalenceProcess Box Pigeon
  theory : Closure

  inferred? : Closure → Closure → Prop := fun a b =>
    Closure.le a b

end Measurement
