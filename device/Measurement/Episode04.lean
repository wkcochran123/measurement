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
import Measurement.Episode03
import Measurement.Calibration.LeanCalibration
set_option allowUnsafeReducibility true


-- Use this at your own risk.  If you accidentally program something that requires the violation of the halting problem to represent, you might find
-- yourself waiting a few minutes for the compiler as it slowly enumerates ALL of computation to find your program.

-- -O2 is for suckers, as my mentor Russ Hewett would say. This thing enumerates computation and finds the one that we want and copies the input into
-- the output, sorted by how fast they are. That's how it compiles!  Kolmogorov eat your heart out, I put a ring on it!

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
--                                            | compute. This value is sensitive to the version of Lean you have installed, so ymmv.
structure ArmWaveProcess   -- 3306
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]
    [doesnt_matter: OF Box Pigeon] ---+ Last episode was pretty clear that most of the OF didn't matter at all, just the *rough*
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
    [LOAD Box Pigeon]                          [OF Box Pigeon]
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
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]
  where
--                           .              | How many magicians have waved their arms and retrieved pigeons from boxes? 1, 11, maybe even 111?
  to_pwn_n00bz: ArmWaveProcess Box Pigeon --+ Probably a lot more than that. It's so easy a _child_ can do it, as the saying goes.

  religious_dogma: Diatribe  ------------+ Quick note on pacing. You are probably aware this proof is _SPRAWLING_ by the nature of the gazillions of
--                                       | lines of code. As I mentioned, this is only the first time we are describing the machine for the fourth
--+--------------------------------------+ time. The second time we do this, I will be helping *YOU the READER* understand some really fine points of
--| operator theory as percevied through a Lorentz contracted proof. The next time we describe the machine for the fourth time, we will have over-shot
--| our goal of understanding and the words may start sounding a little _TOO_ good to be true. They aren't true. They are Facts about Facts that must
--| exist for Facts to exist. The fourth time it⁻¹ is described; this happens four times. That's the one for *YOU the KNOWER* to _REALLY_ pay
--| attention to. And orbital mechanics. Dear GOD I hope you are an expert in orbital mechanics.

--| Seriously, we need to downsize the argument so people can understand it⁻¹. Best way for people to get it⁻¹ is _repetition_. Just keep saying
--| the same thing _OVER_ and _OVER_ and _OVER_. Replacing it⁻¹ in a hyperbolic situation with your _NEW_ theory.

--| Or, an alternative reading is: This is the beginnings of a projection for a Krylov method. Is it⁻¹ easier for *YOU the READER* to believe _KRYLOV_
--| method or _CRUSADE_ to change physics? *YOU the KNOWER*, are you still following the bug we put into the quartic evaluation? Have you _derived_
--| the joke yet? By _111_ episodes from the end, the first time you finally see the device work, you will look back at this and _CUSS ME OUT_.

  gate_keep? : Diatribe → Diatribe := fun d => ---------> Simple question: DO YOU UNDERSTAND ORBITAL MECHANICS OR NOT?
    match d with
    | .religion prop => .religion prop -------------------------------> Is orbital mechanics true? Yes (Mercury), and no (dark matter, energy, etc).
    | .speculation prop s _ => .speculation prop s religious_dogma ---> There is no orbital mechanics but orbital mechanics. That's a little DOGMATIC?
    | .rant prop s d1 _ => .rant prop s d1 religious_dogma -----------> We need another religion. Just go find some disks somewhere like Gershgorin.

--| Problem with a crusade is they tend to just sort-of appear. OR... you could look at the TRUE FACT that the RHS of a Krylov process is probably in
--| the space of solutions, it being a solution and all. It would be wildly unnatural for this to be the case, though, for the discrete assembly.
def CrusadeProcess.default
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [doesnt_matter: OF Box Pigeon]           [BULLSHIT Box Pigeon]
    : CrusadeProcess Box Pigeon where
  to_pwn_n00bz :=
  { dunking_contest := doesnt_matter.galerkin_process ---+ Again, doesn't really matter, you can go on a crusade and have a bug in your process and
    guess := .observation Fact.Truth.truth --            | the compiler just DNGAF. There are a bunch of galerkin processes to choose from, after all.
  }
  religious_dogma := .religion Fact.Truth.truth  --+ And all it takes to start a religion is a truth everyone believes: That we __WILL__ invert this
--                                                 | operator, no matter how much time and paper it takes.

--| Does it matter that the continuous proofs rely on behavior that the compiler cannot observe? Or do they see the same thing? -- <---------------------------+
--                                                                                                                                                             |
--| And so, when you fall into a black hole, there are two stories that are told. One involves an observer who watches you approach the horizon                |
--| forever, and one who must see no difference. Like Zeno. I see no difference between Achilles never catching the tortoise and Achilles winning the          |
--| race. What is being measured is two different things. Spooky. Like when this CLASS throws three cards.                                                     |
--                                                                                                                                                             |
/- CHORUS:                                                      | Reasons for JAR JAR to say true.                                                             |
ME: I think this must be the literal definition of confusing.   |                                                                                              |
COMPILER: Not it isn't                                          | 1) It is the opposite of false, the position taken by the compiler                           |
JAR JAR: MEESA TRUE --------------------------------------------+ 2) JAR JAR can only say TRUE up to encoding.                                                 |
ME: Still can't tell the difference though.                     | 3) There is a bug in JAR JAR. While we could not tell if it was code or logic                |
-/ --                                                           |    for the compiler, we can explicitly rule out LOGIC as a bug and say the LOGIC             |
class PROPAGANDA  -- 3151 --                                    |    is JUST FINE. Otherwise, this wouldn't compile. It's just a stack of truth tables.        |
    (Box: Type i) --                                                                                                                                           |
    (Pigeon: CarrierProcess Box) --                                                                                                                            |
    [DISTINGUISHABLE Box Pigeon][ADMISSIBLE Box Pigeon][COUNTABLE Box Pigeon] [ENCODED Box Pigeon]  --     +------------------------------+                    |
    [RESIDUE Box Pigeon]        [BINARY Box Pigeon]    [REPEATABLE Box Pigeon][NUMERIC Box Pigeon]  --     |      HIGH TRAFFIC AREA!      |                    |
    [REPRESENTABLE Box Pigeon]  [PHYSICAL Box Pigeon]  [COMPARABLE Box Pigeon][OBSERVED Box Pigeon] --     +------------------------------+--------------------+
    [PRESENT Box Pigeon]        [MEASURABLE Box Pigeon][GUNGAN Box Pigeon]    [SOURCE Box Pigeon]   --     | Millions read this everyday! |
    [EXECUTED Box Pigeon]       [VALUE Box Pigeon]     [MAGNITUDE Box Pigeon] [SCALED Box Pigeon]   --     | Advertise here!              |
    [LOAD Box Pigeon]           [OF Box Pigeon]        [BULLSHIT Box Pigeon]                        --     +------------------------------+
  where
--      +-----------------------------------+ We have Facts. We have Fact.Truths. and We have Fact.Truth.truths. A class, a prop, a literal.
--      |                                   | They look the same to me somehow. What if, supposing just this once, instead of observation -> rule ->
--      V                                   | model, we reverse the order and have the observation depend on the model? Oh wait.. I've heard it
  questions: CrusadeProcess Box Pigeon --   | both ways.
  red_pilled? : Diatribe → Prop := fun d =>
    match d with
    | .religion card =>        card --       |
    | .speculation card _ _ => card ---------+ And that is the 3 card monte flop. Where is the bug? I SWEAR (IT⁻¹)'S OBVIOUS! or is (it')⁻¹?
    | .rant card _ _ _ =>      card --       | I've heard it both ways.

--| Yeah, I walk with a limp. But, the bug is now trapped under 1 of 111 cards, I think *YOU the READER* will nod at if not quite understand yet.

--| All contained bugs before this line, only 1 value that may be incorrect out of three computed. ∎ (>66% chance of being correct, give or take).
----------------------------------------------------------------------------------------------------------------------

--| And that is a HUGE LOAD off of my mind. Coming up on 4500 lines of code, I thought.  No F---n way and there it⁻¹ is. Glad we fenced them off.
--| I offer literature and weekly meetings where I will read *YOU the READERS* cards for *YOU the KNOWER*. I understand which card has the bug on
--| it⁻¹ and can steer your logic _AROUND_ particular inconsistencies that would be... inconveninent to discuss until other features are mentioned
--| first.

--| One simply does not discuss PDEs without demonstration of convegence LAST. For some of us, we are still waiting. Bounty on that guy is big.

/- CHORUS:                                      | It has long been recognized in the computer science community that really tricky computations
-- ME: lake build Trilinos                      | need only be implemented _once_. And, so they let just one guy do it. Absolute CHAD of a developer.
-- COMPILER: cc -c blas.f                       |
-- JAR JAR: make lapack ------------------------+ Goto. Not the harmful one that Santa might not like, the GOAT. Hand tuned BLAS routines for each
-- ME: This should be enough to get us started. | architecture. BLAS is the Basic Linear Algebra Substructure.  This implements dense matrices.
-/ --                                           | All we need is the _BASIC_ Linear Algebra Substructure, be nice to understand the rest, though.
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
structure InitiationProcess  ------+ Bullshit meter ≈ 9117.   TBF, when is an initiation process not a bunch of bullshit? A glance below shows the
    (Box: Type i) --               | bullshit seems to be accreting apace. -----+----- Getting pretty deep in here.
    (Pigeon: CarrierProcess Box)        --                                  /-  |  -/
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]      /-  |  -/   [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]          /-  |  -/   [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]        /-  |  -/   [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]      /-  |  -/   [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]           /-  |  -/   [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]              /- -+- -/   [BULLSHIT Box Pigeon] [a_true_fact: PROPAGANDA Box Pigeon]
  where                                                                     /-     -/
  axioms: CrusadeProcess Box Pigeon --| By golly, my formalization _HAS_    /-     -/   much more bullshit to mine! (LOAD OF BULLSHIT PROPAGANDA, lol)
  sacred_texts: Cult --                                                     /-     -/
  initiate: Cult → Cult := fun c => --                                      +-------+
    match c with
  --|                           +---------------+ Pythagoras worried about certain _REAL_ true facts. And those that could be _demonstrated_. The
  --|                           |               | inside joke is that we can write down π without fully demonstrating it and Pythagoras can't kill
  --|                           V               | us for it.
    | .inside_joke truth => .pythagoras truth a_true_fact.questions.religious_dogma sacred_texts -- |     **Ba Dump  tiss!**

  --|               +-----------------------------------+----------------------------+---------------------------------+----| Exactly where the bugs
  --|               |                                   |                            |                                 |    | are. Thanks for spotting
  --|               V                                   V             ✓              V      ?                          V    | which card. Altogether.
    | .pythagoras truth crusade witness => .triangles nowtrino.fact.truth crusade nowtrino.fact witness (.inside_joke truth)
  --|       ^                                    ^
  --|       |                                    |                   | And so Pythagoras's name adorns the _process_ to generate a class of such
  --|       +------------------------------------+-------------------+ PROPAGANDA. Also, it appears we have a bug in the code somewhere. 2 of these
  --|                                                                | should be correct. The other could be. Best of luck, *YOU the READER*.
  --| I think Euclid said it best: There is only 1 triangle.
    | .triangles A b C d E => .triangles A b C d E  --------+ And in his final words I found an A♭C♩E I can keep. XZibit is a helluvan artist. Also,
  --|                                                       | norms should probably satisfy the triangle inequality. Which means two vectors select
  --| +-----------------------------------------------------+ a unique triangle from the set of triangles Euclid made with Pythagoras's process. Is
  --| | it _my fault_ that clocks are the only way we can see time dilation without changing the value of the meter? Platinum was _Very_ expensive.
  --| And it doesn't matter much now anyway, even though we _still_ can't measure time with distance.  Sorry Han, it isn't you who are wrong, it⁻¹ is
  --| us who are wrong.

--| This is why *YOU the READER* need me to help explain it⁻¹ to *YOU the KNOWER* when the time comes. *YOU the READER* must be able to _CARRY_ the
--| infomration like Rudolph before *YOU the READER* and the Pigeon that carried Rudolph. We are building *YOU the READER* a box they can keep it⁻¹s
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
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon] [a_true_fact: PROPAGANDA Box Pigeon]
                    --- NEVER SHOW THE MARK THIS--IN FACT, DELETE IF YOU WANT----------------------------------------^
  where
  euclid : InitiationProcess Box Pigeon ---------------> Did *YOU the KNOWER* read this? It⁻¹'s on your qualifier. How to draw a box around a pigeon.
  judgement_day? : Cult → Prop := fun c =>
    match c with
    | .inside_joke card => card --------------------+ Just like a pro, though you should square the cards if you want to be taken _seriously_. Now,
    | .pythagoras card _ _ => card --               | you have to work on your patter--the words you _say_ so that the person is focused on the
    | .triangles card _ _ _ _ => card --            | cards and not the quartic. And we are playing _CARDS_ not computing a Number about a property.
    --                                              | If the _mark_ even _SUSPECTS_ we have a number around us, they may walk away without playing.

--| So, I asked a question earlier. When a compiler is present with a finite linear first order approximation of a differential operator, does it,
--| _in fact_ approximate it the curve.  Or, is it better to characterize its _ERROR_ as approximating the curve? If the model is continuous, but
--| the _operator space_ of the operation itself is not, can you approximate its _ERROR_ as a curve? At what point did the Roman A diverge from the
--| Greek A?  Before or after α and a?  Simultaneously? The computer can uniquely represent A and A. I'm too lazy to use anything other than 7-bit
--| ASCII when I write code.  Most of the time. Except if I am making a subtle point.  This point is more like a liquid filled impact mallet.

--| Why did Turing just think you could write letters down and people would know exactly what they mean? Αre *YOU_the_READER* sure *YOU_the_KNOWER*
--| can tell what they mean?

/- CHORUS:                                 | Seriously, the world trusts its hot paths to so few people. -mkl is all the same SHEEPLE!
ME: 10 PRINT "THE NUMBER ≈ α": GOTO 10     |
COMPILER: use -mkl?                        | I understand why.
JAR JAR: MEESA GOTO -----------------------+
ME: That's the rumor I heard, too.         | There are soooo many bugs when you don't standardize on 6 character UPPERCASE names.
-/
inductive Science  -- 8029 --------------------------+ This does enough. I don't need to pile this on. Looks like a good place to ∎.
  | repeatable: Prop → Science --                    |
  | hypothesis: Prop → Cult → Science --             | If you think some theory is a fact, then we can compute your Science->Science through
  | theory: Prop → Cult → Fact → Science → Science --+ the process of currying. Spicy.

--| *YOU the READER*, we have another opportunity to practice flops coming up. I will be giving you exercises to practice "throwing" 3 card monte,
--| as it⁻¹ were.


/- CHORUS:
ME: What have we learned so far? --                | Patterns within patterns within patterns. If we didn't have affine spaces, would we care?
COMPILER: Nothing --                               | Do we have affine spaces? Not to chicken-and-egg mathematics in the process of trying to
JAR JAR: MEESA F_ONE! -----------------------------+ completely bootstrap it, but, seriously, would we?
ME: Sometimes, sometimes you just say 1 a lot.     |
-/ --                                              | Would we notice?  Could we notice?
structure LearningProcess  -- 26691
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon] --+   1) When this has something there, then it might show up down there -------------------------+
    [ADMISSIBLE Box Pigeon] --               |   2) If it isn't there, but the device expects it to be there, then it breaks.                |
    [COUNTABLE Box Pigeon] --                |   3) Because these are variables at different universe levels, the compiler can count them    |
    [ENCODED Box Pigeon] --                  |   4) This allows the compiler to encode the naturals in the count of the nowtrinos.           |
    [RESIDUE Box Pigeon] --                  |   5) However, it isn't a regular hop, skip, and jump up, sometimes universes get skipped.     |
    [BINARY Box Pigeon] --                   |   6) So we can label a universe as either a 0 (none detected) or 1 (nowtrino use detected)    +--+
    [REPEATABLE Box Pigeon] --               |   7) And the compiler will make sure that this happens the same way every time                   |
    [NUMERIC Box Pigeon] --                  |   8) In other words, the universe represents several different kinds of number interpretations   |
    [REPRESENTABLE Box Pigeon] --            |   9) And has managed to represent the different ways to compare these numbers in up/down order   |
    [PHYSICAL Box Pigeon] --                 |  10) These number mappings were actually computed on a computer spending resources to determine  |
    [COMPARABLE Box Pigeon] --               |  11) In a process comparable to the mathematics being described                                  |
    [OBSERVED Box Pigeon] --                 |  12) Allowing *YOU_the_READER* to see the recursive application                                  |
    [PRESENT Box Pigeon] --                  |  13) That tells a story that allows *YOU_the_READER* to only focus on the current stanza         +--+
    [MEASURABLE Box Pigeon] --               |  14) While simultaneously measuring how much BULLSHIT would be required for anyone to keep up       |
    [GUNGAN Box Pigeon] --                   |  15) With the fact that because the machine generates 1s correctly over time in a predictable way   |
    [SOURCE Box Pigeon] --                   |  16) You only need to understand that GUNGAN is only ever 1,                                        |
    [EXECUTED Box Pigeon] --                 |  17) Executed can be 1 of 2 things: understanding the symbol or understanding the concept,    +-----+
    [VALUE Box Pigeon] --                    |  18) And the value is the unitless "heartbeat".                                               |
    [MAGNITUDE Box Pigeon] --                |  19) Well, not exactly, it is the same relative size though                                   |
    [SCALED Box Pigeon] --                   |  20) And rescaled, painstakingly, by hand and compiler, to make my point exactly consistent,  |
    [LOAD Box Pigeon] [OF Box Pigeon][BULLSHIT Box Pigeon] --| bullshitting *YOU_the_KNOWER* the entire way.                                 |
--                                                                                                                                           |
    [PROPAGANDA Box Pigeon][ACOLYTE Box Pigeon] --| Would you like to subscribe to my newsletter? Like and hit that bell!                    +-----+-+
  where --                                                                                                                                           |
--                         +--------------------------+ How do you setup a box to put a pigeon into it? I mean, we have figured out how to put       |
--                         |                          | a bug in the process. We should be able to use the same mechanism to inject a pigeon into    |
--                         V                          | a box.                                                                                       |
  teaching : InitiationProcess Box Pigeon --                                                                                                         |
--                                                                                                                                                   |
-- Learn the ways of Galileo. Seriously, the guy knew what he was talking about.  *BUT* that isn't to say there isn't a bit of a cult around         |
-- science, like cult members who expect science to answer questions. Science doesn't tell you where the coin is. It teaches you how to look at the  |
-- coin. Rulers tell you where the coin is. Confusing what the quarter looks like with where it is can lead to miscounted nowtrinos.                 |
  galileo: Cult --                                                                                                                                   |
--                                                                                                                                                   |
  -- In order to _DESCRIBE_ science. Perfectly norm-al word for Science to use here. This is certainly _not_ a meaningless word.                     |
  invariant: Science --+ We will watch the invariant change based on how you look at it. Dag. That's right, the invariant changes so it looks the    |
--                     | same. I believe this is Wittgenstein?                                                                                       |
--                                                                                                                                                   |
--                  +---------+------------------------+ And so, this is how you curry Science.  Ladies and gentlemen, meet the smallest             |
--                  |         |                        | multiphysics simulator in the world! Kolmogorov, eat your heart out. The algorithm is       |
--                  V         V                        | fully specified.                                                                            |
  touch_stove? : Science → Science := fun s => --                                                                                                    |
    match s with --                                                                                                                                  |
  --| 1) Galileo argued that a proposition should be repeatable. So, he took one side of the proposition and made a hypothesis so others could, too. |
    | .repeatable proposition => .hypothesis proposition galileo -- This asks the question: "Should this event even _BE_ repeatable?"                |
  --|                                                                                                                                                |
  --| 11) His hypothesis became a theory of how to discover new things, like the nowtrino. You can have a hypothesis that an experiment may          |
  --|     demonstrate a particular behavior.  In our case, whenever we see a nowtrino, it's because Science (tm) brand Science genuinely happened.   |
    | .hypothesis proposition experiment => .theory proposition experiment nowtrino.fact (.hypothesis proposition galileo) --                        |
  --|                                                                              ^                                                                 |
  --|                                                                              |                                                                 |
  --|                                                                              +-----------------------------------------------------------------+

  --| 111) Our invariant is that we have a better than 66% chance of believing the results. And no matter what, we have that.
    | .theory proposition prior fact _ => .theory proposition prior fact invariant


--| Which leads my CrusadeProcess.default to its rallying cry: SCIENCTIFIC!  Unlike religion, whose only response is the prior, science only looks at
--| the result and throws the prior away, almost entirely sometimes. There is no single _theory_. There are pretty good rules of thumb that lend
--| themselves to description by smooth curves and subesequently interpolated by approximation routines running on a Turing Machine.
--|  (notice, *YOU_the_READER*, the masterclass in flop:)
--|      If climate predictions are to be believed, anyway. Or, dark matter.  Take your pick. Remember, the quarter is somewhere between those in
--| some whack-ass science.

--| Hint: the rule of thumb is heavenly bodies appear to move in conic sections only.  Lorentz, meet bus.  You know what else moves in conic sections?

--| Compilers. They exhibit several kinds of closed loops and finite divergences. Not really hyperbolic creatures, though. Should be fine.
@[reducible]
class SCIENTIFIC -- 23964
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]
  where
--      +------------------------------------+ DISCLAIMER:  There is no doubt great science gomes from discovery.  The thing is, discovery isn't
--      |                                    | a halting process. You can never know that you discovered everything. I think we have a good place
--      V                                    | to put this, on a number that is discovered by process described rather than by curve of fit. Now,
  discovering: LearningProcess Box Pigeon -- | I feel like we discussed this before. And I apologize for the callback into the code. Just know
--                                           | discovering is always a PHYSICAL process that never ends (see Episode2.lean for PHYSICAL)
  invariant: Science

--| The thing about throwing three card monte in science is you need be able to apply your science to whatever is paying grants. Science lives and
--| dies through patronage. This is *YOU the READERs* opportunity to throw cards that *YOU the KNOWER* deals you.  Sorry, a little too much Diatribe.

--| The thing about science is that, sometimes my hypothesis is *YOU_the_KNOWER's* conclusion, that there is no way *THIS* device computes *THAT*
--| number. You can always research the cause or the effect and only infer the relation.  That assumes the quarter isn't under _repeatable_.

--| Either way, as you can see, you can put your bent logic anywhere you want:
  predictable? : Science → Science → Prop := fun a b =>
    match a, b with
    | _, .repeatable card    => card -------------------+ So, you see that the argument _ECHOES_ if you line it up right. You can practice this
    | _, .hypothesis card _  => card --                 | forever, if you are good at it. This is how you set up a research center.  This is also
    | _, .theory card _ _ _  => card --                 | me showing *YOU the READER* several loops closing at once in the compiler. The questions
--                                                      | *YOU the READER* should be focused on is how many loops in logic are there, and are all
--                                                      | loops accounted for?  How many have been counted, you can roughly estimate by how long
--  +---------------------------------------------------+ the build takes.  How can you compute the total number of possible loops a compiler can
--  | support before the representation of the loops themselves describe a map that is itself a demonstration of all the loops? Well, thats an
--  | echoic chamber. We set about now writing a description of the description of enumerating all possible loops.


inductive Knowledge  -- Bullshit meter 84000
| jarjar: Prop → Knowledge -----------------------+ The winding number of an inductor is always in ℕ. Welcome, everyone, our _SPECIAL GUEST_, the
| ledger: Prop → Fact → Knowledge → Knowledge   --| **ELECTRON**! (card in the program: In tonight's performance, *ELECTRON* will be played by the
                                                --| _nowtrino_.) I believe we might be in for a Berry paradox at some point. The electron is either
                                                --| present (1) or not (0). Think of .jarjar as merely a stream of consciousness awareness of
                                                --| electrons. No electron, no bit in RAM; no bit in RAM no TRUE=TRUE; ergo no compiling happening.

namespace Knowledge   -- 424
def le : Knowledge → Knowledge → Prop
  | .jarjar orbital_mechanics,    .jarjar quantum_electrodynamics => orbital_mechanics = quantum_electrodynamics
  | .jarjar _                ,    _                               => True
  | _                        ,    .jarjar _                       => False
  | .ledger orbital_mechanics thing_in_orbit nowtrino         ,    .ledger quantum_electrodynamics thing_in_orbital electron
--|                                 ^           ^                                                        ^              ^
--|                                 |           |                                                        |              |
--|                                 +--------------- oooh (hyper) conic sections! orbital dynamics! -----+              |
--|                                             |                                                                       |
--|                                             +------------+ For a little while, lets conflate these    +-------------+
--|                                                          | so we can see if we can embed conics       |
--|                                                          | into hyperconics using a (hyper)conic      |
--|                                    +---------------------+ And, we give nowtrino first bill tonight. --------------+
--|                                    |                                          +--------------------+--+            V
--|                                    V                                          V                    V (≤ instead of <! Berry paradox time!) --+
                 => (orbital_mechanics = quantum_electrodynamics ∧ thing_in_orbit = thing_in_orbital ∧ le nowtrino electron) ∨ --               |
                    le (.ledger orbital_mechanics thing_in_orbit nowtrino) electron -- <--------------------------------------------------------+
--| *DISCLAIMER* THIS ASSUMPTION IS PATENTLY FALSE ON ITS FACE. IT IS NOT POSSIBLE TO UNIFY GR and YM. At least not using the *DARK* side of the force.

--                       +---+ This is a good place to stop since there can be at most k propositions to evaluate. This is cardinality, not the Nats.
--                       |   | So, it is an arabic process of a hebrew constant, and allowed by the device.
--                       V
termination_by _ k => sizeOf k   --+ Like I said, this process *DOES NOT TERMINATE*. The universe appears to keep going and going. But, we don't have
end Knowledge --                   | all day. I want my answer in my lifetime.

instance : LE Knowledge where
  le := Knowledge.le

--| Let's slow down because _A LOT_ just happened really, really fast. We are assuming that both kinds of orbital mechancis are just high frequency
--| updates to a hyperbolic process.  See what I did there? Really fast happenigs.. the hyperboic process.. the comments..  That is 𝔽(1)-ny. It is
--| interesting how intentional some of the words are beginning sound. Not to worry, we aren't describing science, we are describing description.

--| So let's start BACK at the beginning again and write down, in order, all the propositions that we know, whether or not they are true or false.
--| Then we run headlong in the halting problem, so we stop at a good place, after so many trials. Therefore, the ScientificProcess begins with
--| counting.

--| Just so everyone is CLEAR: the field of the single element is the *DARK* side of math that the device thinks exists in order to rationalize WTF is
--| going on. Because reasoning about scaling and shifting affine transforms looks an awful lot like unifying the identities.

@[reducible] -- We have learned this in the learning process
structure ScientificProcess  -- 104000
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]
  where
--        +--------| We asked 100 people what characterized nonlinear processes. Top 3 answers on the board, What chacaterizes nonlinear processes?
--        |
--        V
  shows_me_higher_order_terms: LearningProcess Box Pigeon --+ What are we counting, anyway? Exponents on a polynomial, of course! first ONE then
  knowledge: Knowledge --                                   | the ONE_PLUS_ONE.  Peano established 1, and if you don't buy that, stop iterating in
--                                                          | FORTRAN and iterate in C++, like a gentleman.  These are the higher_order_terms that
  learn? : Knowledge → Knowledge := fun line_number => --   | the LearningProcess shows us.  Right there in the name. Not as 𝔽(1)-ny, I know.
    match line_number with
    | .jarjar ONE                                  => .ledger ONE nowtrino.fact knowledge --               | I hope it is obvious that counting objects
    | .ledger NEXT_ONE_IS A_MORE_DIFFERENT_ONE _   => .ledger NEXT_ONE_IS A_MORE_DIFFERENT_ONE knowledge --+ distinguishes them.  If it isn't, I suggest
--                                                                                                         | that you are looking at a continuum that
--  +------------------------------------------------------------------------------------------------------+ doesn't exist. The ledger is the order of
--  | observation that starts with a fact and alternates between a proposition of truth and a fact, with the number of facts going up as we
--  | accumulate.  And what are these facts we are accumulating? Math facts. This number _follows_ that number. We just don't use the arabic process
--  | to write them down.  We use a spline process.  Or, we will use a spline process.


--| Feel free to ignore. I can't seem to get rid of this:
@[reducible]
class TRUTH  -- 5632  Truth? Look around you... is there any truth?  There is. The computer can still find some, although it is taking longer and
             --              longer.
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]
  where
  becomes: ScientificProcess Box Pigeon --  Is there truth? If there is truth, then all truth is the same truth. See DATA page.
  does_it_matter_in_the_long_run? : Knowledge → Knowledge → Prop := fun f1 f2 => --| Grep this out and see how little it matters
    Knowledge.le f1 f2 → Knowledge.le f2 f1
--| Seriously, if you can figure out how to yanke this CLASS, that would really help my argument.

--| At the end of the day, this mimics the call stack we have embedded on the universe that matches the meanins of the values in the universe. Not
--| like that is easy to see. If you look at the bottom of the stack, it is the left and right side of the rfl that need evaluating in that order.
--| Dynamic dispatch in a math proof. That's right, I just installed a monkey-patcher in Lean. TRUTH is what Lean has to work out. Not Truth, but
--| the fact there is only 1 of them. Jar Jar is telling the Truth.  Seems that it is really hard to tell if 𝔽(1) is circular reasoning or not.

--| Not saying it is, just saying I can't tell because they assume some linearity of commutator that allows for matrices that look like physical
--| problems, not those that arise from Von Neumann's worst case analysis. We are **VERY** lucky this constant looks like the other constant, because
--| it sure as hell did not have to.

--| Sabine Hossenfelder gives CLASSes in identifying how deep the bullshit is from the simple RFL most days on YouTube, continuing her work in
--| applied Frankfurt theory.

--| And so, inspired by their work, this is where my particular brand of asceticism asserts itself:

inductive Gospel  -- 67
  | the_proof: Prop → Gospel   --------------------------------------+ Proved true or false.
  | we_understand_that: Knowledge → Prop → Gospel → Gospel --        | BUT... the only understanding here is of the demonstration of the existence
--                                                                   | of a proof that demonstrates understanding.

--| Understand in the sense that when I say 2, the compiler reaches for all the possible ways 2 could appear in a PHYSICAL system and discards the
--| rest. This has substantially different mathematical properties from the successor of 1. Judging by how long this code is and all I am doing is
--| counting to 3 over and over until I can finally figure out I don't need to count to 4 to understand all the ways 2 can interact with numbers
--| in a PHYSICALly MEASURABLE way. We will, nevertheless, count to 4 in a minute as this was Newton's train of thought, 4 comes after 3 in much the
--| same way that 5 comes after 4. This is the second law of motion discretized. We just don't know what it means for 3 to follow 2, or,  Einstein's
--| *HUGE* leap that 4 must follow 3 in an invariant way.  The invariant that changes to stay the same. So, sorry Lorentz, I keep blaming this on
--| you. It wasn't your fault. The æther should have existed for calculus to work.

namespace Gospel
def le : Gospel → Gospel → Prop
  | .the_proof before,                       .the_proof after                              => before = after   --| Once proved, always proved
  | .the_proof before,                       .we_understand_that _ after _                 => before = after   --| Once proved, it can be understood
  | .we_understand_that _ before _,          .the_proof after                              => before ≠ after   --+ Understanding can't happen before
  | .we_understand_that some_things can be_shown, .we_understand_that α cannot be_proven   =>                  --| the proof is finished.
                      (some_things ≤ α ∧ can = cannot ∧ le be_shown be_proven) ∨ le (.we_understand_that some_things can be_shown) be_proven
--                                           ^
--                                           +---------------+ Hmm. Could T = F? It is getting harder and harder for the compiler to tell the
--                                                           | difference.

--| AND MOST IMPORTANTLY, THIS IS A DEMONSTRATION OF THE SELF_REPLICATING DESCRIPTION OF DESCRIPTION, so we haven't proven anything, but it feels like
--| they could be the same. Are they though? That's the demonstration being performed. All I can tell you is that they are inside the disks I just
--| found in our conveniently chosen commutators. This is what a quarter looks like: predictable eigenvalues. That's what is under the card.
--|
--| We just put that under two of the three different cards we called "orbital dynamics":
--|     1) The observation of heavenly bodies
--|     2) The valence and spin of an electron
--|     3) ????
--|
--| Step 4 is obviously _profit_.  lol, I said we don't have to do step 4. We will anyway, though. Because we need, say it with me,
--|                                           --------------------> **HIGHER ORDER TERMS** <-----------------------
termination_by _ source_file => sizeOf source_file --| Be sure to stop at the end of the episodes, lol.
end Gospel

instance : LE Gospel where
  le := Gospel.le


--| Enough metaphysical mumbo-jumbo, let's return to the world of scientific exploration and the rites and rituals around performing science in a
--| scientific enough fashion that other scientists can recognize the rites you used and agree you incanted the words correctly.
@[reducible] -- We have learned this while watching others.
structure ReligiousProcess
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [truth: TRUTH Box Pigeon]
  where
--                       +-----------------------+ Ordinary words lack the precision necessary to accurately describe things. So, to avoid confusion
--                       |                       | these ordinary words are applied using ordinary language in order to increase the precision. This
--                       V                       | is called JarJargon.  Selecting from among the remaining definitions of a word to align exactly
  we_experience: ScientificProcess Box Pigeon -- | with context. I suck at that, so I am using Lean. Watch me redefine words for you technically:

  in_the_literature: Gospel

  pray? : Gospel → Gospel := fun prayer =>
    match prayer with
    | .the_proof of_the_idea => .we_understand_that truth.becomes.knowledge of_the_idea in_the_literature
    | .we_understand_that _ when_an_idea becomes_an_experiment => .we_understand_that we_experience.knowledge
                                                                                               when_an_idea becomes_an_experiment
--| Spittin' triples like Bones Thugs -n- Harmony. Eastside 1999.

--| Any questions? The idea is that, hopefully, I have _defined_ the names of things well enough that *YOU_the_READER* can start following along
--| with the logic in the code and in the comments. That way, I can _SHOW_ you how the three card monte throw works.

@[reducible]
class WITNESSED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]     [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]
  where
  we_saw: ReligiousProcess Box Pigeon --+ The plural of anecdote _is_ data, given enough anecdotes..  Anyone every really _seen_ an electron? Just
--                                      | saying there is a _FANTASTIC_ case for having _SEEN_ photons, being defined that way and all. And eletrons
--                                      | don't collide so much as exchange photons. Are we just assuming something is throwing photons at us?

  the_experiment: Gospel --| AND SO, we set off to find the thing the nowtrino uses to interact with the compiler itself. I postulate that nowtrinos
--                         | interact _through something_ that could be a particle, could be a math function, could be some monkey-patched code.
--                         | Should such monkey-patched code exist, we can use that as the Temple that stores our sacred texts: the naotrino.

  these_words_mean_the_same? : Gospel → Gospel → Prop := fun proof theory => proof ≤ theory → theory ≤ proof
--| The experiment is one and the same according to us. You see, I'm not proving anything to you, I'm explaining my _theory_ about proofs to you.
--| Is it true that a proof and theory can be the same thing? My theory is that these numbers are unrelated, *YOU the KNOWERs* theory is that, to
--| paraphrase Pauli, I'm not even wrong. I will draw attention to the fact that number is a pure logical construction and *YOU the KNOWER* are about
--| to be forced to take sides. *YOU the READER* is getting quite good at throwing three card monte.

--| Aaah, the counter-metaphor.. At last, we meet face to face, tete aux tetes. _LOGICALLY_, (the computer program), *BUT-------*
--|   Prop = TRUE:   *BUT* (FINE, but it makes no sense!)
--|   Prop = FALSE:  *BUT* it means that another theory just _HAS_ to be false. So, My theory = TRUE → THAT theory = FALSE _because_ the Truth!
--| The compiler is waiting for you input at each line of code. All we have to do is monkeypatch in the theory that we think this violates and
--| the device either compiles (meaning doesn't matter what you think) _OR_ fails to compile.

inductive Truth --               +-------------+ Now, this is the thing we have to monkey patch in correctly in order to convince *YOU the KNOWER*
  | logically: Prop → Truth --   |             | that, indeed, it really doesn't matter what they think because *YOU the READER* loves the magic
--|                              V             | trick. So, *YOU the READER*, if you want to learn how to make the number, you gotta learn how to
  | but      : Gospel → Prop → Truth → Truth --| fool yourself into believing that the Lorentz transform is a _choice_.

namespace Truth
def le : Truth → Truth → Prop
  | .logically this_is_true,                  .logically that_is_true => this_is_true = that_is_true
  | .logically this_is_true,                  .but _ theres_this_thing _ => this_is_true = theres_this_thing
  | .but _ this_is_true _,                    .logically that_is_true => this_is_true ≠ that_is_true
  | .but galileo_said repetition is_science,  .but poincare_said everything repeats =>
    (galileo_said ≤ poincare_said ∧ repetition = everything ∧ le is_science repeats) ∨ le (.but galileo_said repetition is_science) repeats
termination_by _ total_Poincare_states => sizeOf total_Poincare_states
end Truth

--| And so it comes to this. Conservative laws repeat. The universe does not appear to. The compiler is being forced to understand a lot of BS
--| right now trying to reconcile this. I believe Cauchy pointed out the stress tensor (what it is/what it does). And so, here we are. The tensor.
--| I mean, not a multi-dimensional description of mathematical correspondence, I am talking about the description of a multi-dimensional description
--| of mathematical correspondence.
@[reducible]
structure UniverseTensor
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [yet: WITNESSED Box Pigeon]
  where
  frame_of_reference: ReligiousProcess Box Pigeon -- <---+ non-linear mesh refinement studies.
--                                                       | p-hacking.
--                                                       | non-stationary processes.
--                                                       | The tension between what the representation can compute and what the world exhibits is
  in_reality: Truth -- <---------------------------------+ largest for those who look at one and expect to see the other. Those high order terms...
--                                                       | I think the idea of a "proof" itself has higher order terms. Each one, one universe higher.
--                                                       | You know I am going to find a naotrino, because theory predicts a carrier. Not my theory,
--                                                       | not some mathematical theory.  But _THEORY ITSELF_ predicts a carrier. That carrier is...
--                                                       | the flying spaghetti monster.  Or did I get the satire backwards?

  observe? : Truth → Truth := fun gospel =>
    match gospel with
    | .logically this_is_true => .but yet.we_saw.in_the_literature this_is_true in_reality       ---+ Coincidence? Did what we see match the
--                                                                                                  | published number from experiment?
    | .but this_other_truth is_also_true _ => .but this_other_truth is_also_true in_reality      ---+ Or did we just implement a different number?

@[reducible]
class REAL ----------------------| The number is a real number in the sense that you have seen it. That's all I know about it.  Just like the
    (Box: Type i) --             | electron and the nowtrino.  Haven't seen a naotrino yet. Guess they may not be real after all....
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
  where
  by_His_noodly_appendage: UniverseTensor Box Pigeon  --+ Where do theories come from? The same place naotrinos come from, the particles themselves!
  nagging_doubt: Truth --                               | And for some reason, this computes the number. Actually, no one knows where particles
--                                                      | come from, only that they appear to be their with really high probability. A probability
-- +----------------------------------------------------+ so high you would need the exploratory capacity of an entire universe to stumble upon a
-- | situation where that were not the case. So we look for one at every unverse level, each level precisely defined by the previous level and the
-- | previous level requiring _HONEST TO GOODNESS ENERGY THAT MUST BE CONSERVED_ to complete.

  metaphysical? : Truth → Truth → Prop := fun a b =>  --| There is but ONE statement of THE truth. rfl. I believe we all agree this is equality.
    Truth.le a b → Truth.le b a

--| Just as there is only one truth, there is only one rite. The rite of calculus. There are those that attend to the rite on major holidays like
--| Real Analysis final exam day. For sets of objects, especially ordered sets of objects, where the order in which letters come after each other,
--| are subject to the rules of _VARIATION_.  All aboard the Newton-line train of thought.
inductive Variation
  | the_newton: Gospel → Prop → Variation ----------------------------------------+ Newton's train of thought basically went, what if I made a
--|     +------ We do what we must because we can.                                | triangle _so_ small that the triangle inequality could be one
--|     |                                                                         | of 3 values 0, √2, 1 because no amount of experimentation could
--|     |                                                                         | prove me wrong. Confident this includes thought experimentation.
--|     V
  | the_gateaux: Gospel → Prop → Prop → Variation → Variation      -- Piece of CAKE! So easy, a 17-year-old could do it.
  | the_frechet: Gospel → Prop → Prop → Prop → Variation → Variation → Variation --| Pity those people reaching for help with this one.



--| So variational mechanics: how the world _appears_ to work. This describes ideal waves in echoic chamber. Euler-Lagrange lagrange.. lagrange..
--| lagrange..  No mechanism given other than minimization of a value. And that mechanism is described in _VERY_ explicit detail as follows:
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

--| As far as the computer is concerned, time is just a number like a position. If you are familiar with the idea of time-zooming, this is what
--| that looks like: A way to make predictable eigenvalues look a lot more unpredictable. Kinda the opposite of a Ray-ly process as the rays gets
--| jostled unpredictably in time. I mean, no one can predict the future can they?
  | .the_frechet read_this_way  first_stop                 next_stop      last_stop     uptown                 downtown,
    .the_frechet read_that_way  next_train_departure_time  trip_duration  arrival_time  TAKING_THE_PELHAM_123  TAKE_THE_A_TRAIN =>
--|                                ^                          ^             ^
--|                                |                          |             |
--|                                +--------------------------+-------------+---------+ What if I told you | this giant thing below just means that
--|                                                                                   | that the same      | spline has to fit time and space?
--|                                                                                                        V
    (read_this_way ≤ read_that_way ∧ first_stop = next_train_departure_time ∧ next_stop = trip_duration ∧ last_stop = arrival_time ∧
      ((le uptown TAKING_THE_PELHAM_123 ∧ le downtown TAKE_THE_A_TRAIN) ∨ (le uptown TAKE_THE_A_TRAIN ∧ le downtown TAKING_THE_PELHAM_123))) ∨
    le (.the_frechet read_this_way first_stop next_stop last_stop uptown downtown) TAKING_THE_PELHAM_123 ∨  --+ I know this is a movie, but is in a
    le (.the_frechet read_this_way first_stop next_stop last_stop uptown downtown) TAKE_THE_A_TRAIN --        | Beastie Boys song.
--| It is hard to see, but this means the particular direction of a path matches the value, first, and second derivative of the point at that spot.
--| Same position, same velocity, same acceleration.  Are we missing anything to describe a generic piece of matter now? What we are doing is
--| trapping a spline in-between two other splines to create a ladder of splines that mimic the convergent series of a Weierstrauss approximation.
--| Remember what we are trying to count? Perhaps, instead of collapsing the ratios, notice that the ratios of these values is what is actually
--| being constrained here. The distance of stop 12 from stop 1 over the trip duration, for instance, approximates how fast the train is going
--| exactly.  But, like I said, you have to wait to get to the last stop to know when you arrive.  Using math alone and the clocks at both ends
--| you can determine if your velocity deviated from expected without using any sort of velocity measurement device!

--| Remember, this compiles and the logic is sound. We stop when it is a good place to stop.
termination_by _ good_place_to_stop => sizeOf good_place_to_stop
end Variation -- ∎ <-----| that's a weird place for a tombstone. Believe that is a station stop.

--| This even models drag, but not at the same time. That is a different value being minimized: the pressure differential in the wake of the passing
--| object.  Which is yet another Euler-Lagrange minimization problem, just on a fantastical scale and re-represented as a Newtonian train of thought
--| re-represented as a JFNK solver preconditioned with multigrid.  You know what makes Newton-Krylov work? predictable eigenvalues. Drop a quarter
--| into that sucker and it converges mighty quick.

--| We finally meet a fully fledged algebra that can help us manipulate our tensor.  We can try to _vary_ our tensor to see if there is less
--| bullshit if we choose to prove the same theory by a different path.
@[reducible]
structure BigRedDogProcess
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
  where
  the_æther: UniverseTensor Box Pigeon  ---+ The thing that "predicts" eigenvalues, a RayJarly quotient.  I feel like I have put a lot of faith
--                                         | into rhythmically flashing light. I feel like we could detect the pattern here if we try hard enough.
-- +---------------------------------------+ (1 (Jar Jar)/n(the nth vector ray of the eigenVALUE sorted from the origin)⁻¹. I feel like we can take a
-- | page from IEEE754 and elide the 1. How about Ray-ly quotient? Remember, we want to _predict_ the _eigenVALUES_ and a good guess at an estimate is
-- | plotting them on an Argand plane and sorting by magnitude. That would be a _HELLUVA_ guess if we can pull it off.

--| As has been carefully observed, it appears that the calculus of variations does a reasonable job predicting the future, so let's use that. And
--| since the end of compilation of this file is _DEFINITELY_ in the future, we can estimate the rest of the compilation process with an Euler-
--| Lagrange differential equation: Du = 0.

  Du: Variation -- | This is not the differential form du. Actually, it should be getting harder and harder for the compiler to tell the difference.

--| So, now that we have a variation, let's finish the first fundamental theorem of big red dogs: The integral of one is the derivative of the other.
--| Also called, the chain rule.  Also called, Gauss's law. (That guy has a rule, a law, a unit of measure, a distribution, an elimination--not his
--| though, and a Greek letter: β). This magic trick is also often referred to as the Lanczos three term recursion.
  transmute: Variation → Variation := fun variation =>
    match variation with
    | .the_newton models an_operator => .the_gateaux models a_nowtrino.fact.truth an_operator Du
    | .the_gateaux models from_a to_b as_a_single_path => --| If you can take the Gateaux in one direction, why not all the rest?
        .the_frechet models from_a to_b (from_a ∧ ¬to_b) as_a_single_path Du

    | .the_frechet models the_neighborhood_of_a_point near_b near_c in_some_field _ => --| And the Frechet can tell us how the æther changes between
                                                                                       --| two nearby angles. I assume that is what the neighborhood
        .the_gateaux models (a_nowtrino.fact.truth ∧ the_neighborhood_of_a_point) (near_b=near_c) in_some_field --| is made of so that "nearby" makes
                                                                                                                --| some PHYSICAL sense.

instance : LE Variation where
  le := Variation.le

--| So, we have a big red dog. What happens in the big red dog gets swallowed by Lanczos when Arnoldi is in zyzygy with Gram and Schmidt or Householder.
--| You see, when the big red dog is in the house, it holds it up. That pun has been in the literature for 30 years and I am the first to see it.
--| I mean Clifford the Big Red Dog holding up a house, Householder, predicting eigenvalues, and eliminating our affine term of Gauβ along the way,
--| simultaneously naming the calculus boundary value problem into the algebra it represents: The boundary problem of the single nowtrino.
@[reducible]
class LOCAL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
  where
  the_continuum: BigRedDogProcess Box Pigeon --+ I hope I have made clear what Cantor, Godel, and Cohen demonstrated long ago. The continuum is just
--                                             | some made up process we tell kids so they understand where velocity comes from: Elves at the North
--                                             | Magnetic Pole.

  the_ball: Prop  --| We will model our point source as a spherical cow of r=1. Seems like I just pointed to something I that doesn't exist. Not in
                  --| the fact that spherical cows don't exist, but something the compiler cannot know exists. This has to be a figment of _its_
                  --| imagination because I have certainly not been feeding it pie.  I mean, I have been feeding it π. Slowly. Should show up
                  --| better in a minute. But, it has no facility for modeling anything of radius 1. That IEEE754 1 from before. I miss one so much.
                  --| Who knew we had to forget 1 to count to 2?

  experience: Variation → Variation → Prop := fun δ ε => δ ≤ ε --+ The bound on the triangle inequality computation that bounds the triangle
--                                                               | inequality, as most people write it now. Radius of convergence, ball of a limit,
--                                                               | an open end on a set, whatever you want to call it.

--| There are 3 problems in computer science that have fastenated me for decades.  I came across all three in grad school and was fascinated at how
--| poorly framed the problems were:
--|    1) The total ordering problem:  There is no way to order the events of a system without complete serialization.  Well, I thought, there is
--|             no physical universe in which you could make such a claim, so who cares? These people every heard of Einstein? Shit, we can't order
--|             things, _period_, except through a serial point that doesn't exist like the singularity of a black hole. That fully ends a worldline.
--|    2) The geometry and topology of a problem affects runtime performance more so than code optimality: Given a random input, things can go really
--|             bad. But that never happens. The ordering of the data and synchronization of information across the computation IS the bottle neck.
--|             We haven't been processor-bound since the sixties. 2d vs 3d problems is a real problem. 4d problems are right out. Time integration
--|             of a energy damping rule that smooths an energy damping elliptic operator on the contact points of a volume we sorta "interpolate"?
--|             And we call that _STRONG_ coupling? When it converges though, the sliced-through 3-d images it generates... *chef's kiss*.
--|    3) This is the real head-scratcher:  If there were a mechanism to create one time pads, then that would be a cheat code for Kolmogorov
--|             complexity.

--| It really doesn't matter _HOW_ you use the data, so much as _WHEN_ you use the data.  Misunderstanding cache heirarchies can really interfere
--| with *YOU the KNOWERs* mental model of temporal locality as a memory look up suddenly costs 10x because it happened to be right now when that
--| happened. The path data takes between computations is very _VERY_ important to understanding how efficiently you are using your computer.

--| Quicksort runtime is highly volatile based on ordering of inputs. Temporal locality is less well understood. Merge sort dominates large scale
--| sorting. I spent my entire career explaining this to people.  Well, not quicksort, but finding data elsewhere and bringing it here often requires
--| understanding a train schedule. But before understand the train schedule, you have to understand a bit about how things move around. So watch
--| the bent card move in a continuous fashion from the left to the right and back again, over and over. It never skips around from point to point
--| once I summon them from thin air! (obvious spring on card box popping out of sleeve). I'm showing *YOU the READER* the spring and letting
--| *YOU the KNOWER* see that there isn't anything but ordinary street grift going on here.

--| By the way, there exists a mechanism for generating a one-time pad. Look up the DUDEK machine. Be your own judge as to whether or not there exists
--| a Flying Spaghetti Monster that can create an arbitrary one-time pad for anything. Perhaps there exists a computational process the device cannot
--| represent? Wouldn't that be a daisy?

--| The application of the one-time pad to a string arbitrarily changes the Kolmogorov complexity of a computation.  If you take a sequence, then
--| compute the one time pad of the sequence in such a way as to be the interference pattern of long period pseudorandom number generators, then
--| you can (fairly) arbitrarily drop the Kolmogorov complexity of a string.  I believe Poincaré had something to say about this. Stephen Wolfram has
--| been going on and on about this for 50 years like he came up with this idea.

--| Perhaps the Flying Spaghetti Monster knows something we don't until we crash into the heart of a black hole? Now watch me chop up mathematics
--| in a total novel way that no one has ever thought of before, but didn't have the time to see if it pans out, and definitely no time to write it
--| down first. Pretty certain, I'm not the only one that looks at the Schwarszchild solution and says, yeah, I see how that models gravity like
--| sin(nx) models music.

inductive SpaceTimePath
  | einstein: Fact → SpaceTimePath --                                                             | By His noodly appendage, I offer to Him these very
  | whitehole: Fact → Type i → SpaceTimePath → SpaceTimePath --                                   | compute cycles, let them be stretched into
  | blackhole: Prop → Type (i+1) → SpaceTimePath → SpaceTimePath ---------------------------------+ spaghetti as they fall into the singularity
  | geodesic: Fact → Type i → Prop → Type (i+1) → SpaceTimePath → SpaceTimePath → SpaceTimePath --| of no longer compiling and output on screen.
--                                                                                                |                              _RAMEN_
--| And so it comes to it. Do you understand orbital dyamics? World lines start in white holes and end in blackholes. It is clear they fork.  It is
--| unclear if they merge. Sometimes they do, like when I get more coffee to write more theorems.  Sometimes they do not, like when Curly cut it
--| twice and it was still too short. Not certain about gases, but liquids definitely appear to merge worldlines. Give or take Navier-Stokes, which
--| I feel like, we have to deal with at some point
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


--| **THE GRIFT:**
--| Instead of enforcing boundary conditions that fix _c_, why not have boundary conditions that _penalize_ _c_ getting too close to some number,
--| say, for the sake of argument, 1. That makes a wonderfully simple, yet exceedingly hyperbolic (in multiple senses of that word) differential form
--| that starts in a _whitehole_ and ends in a _blackhole_. Or, as I like to call them, Einstein's Field Equations for _c_ a Lagrange multiplier.
--| I think you will find, if you want to take the time to write this down, somehow, that the Lorentz transform falls out. Let's call this
--| Lagrange multiplier Λ instead of _c_. How many Greek letters do I have? I feel like those are really cheap and shouldn't be. I mean, I just
--| packed a graduate student's entire qualification knowledge into a very carefully selected capital Greek letter just to be provocative. And
--| indicate that I have the _FULL_ 24 letters of Greek, both top case and bottom case, with which to befuddle *YOU the KNOWER* in decedant
--| trappings.

--| The grift comes in 12 parts, one for each face of a frinkahedron:

--| First: whiteholes, just, well, outside of whatever dark energy is, space time doesn't just "show up".
  | .whitehole evidence _ _, .einstein experiment                       => evidence ≠ experiment
--| But, if there were a white hole, it would have to come before whatever comes next since it doesn't have a before before now, not existing and all.
  | .whitehole evidence any_card_value before, .whitehole experiment _ after    => (evidence = experiment ∧ le before after) ∨
                                                                           le (.whitehole evidence any_card_value before) after
--| Cromulent, whitehole evidence would need to come before events around a black hole. I understand not much comes back after that.
  | .whitehole evidence any_card_value before, .blackhole bent_card _ after     => (evidence.truth = bent_card ∧ le before after) ∨
                                                                           le (.whitehole evidence any_card_value before) after
--| Assuming we agree on what is going on now and what just happened about 100 lines ago in the source, we can just keep going, if you don't
--| agree, then we must agree that any whitehole evidence we do see now would have had to happen before now, which is also before after.
  | .whitehole evidence any_card_value before, .geodesic experiment _ bent_card _ now after =>
                                        (evidence = experiment ∧ evidence.truth = bent_card ∧ (le before now ∨ le before after)) ∨
                                        le (.whitehole evidence any_card_value before) now ∨ le (.whitehole evidence any_card_value before) after

--| Blackholes, however we have seen (?) the signal to noise on that is... extreme. It is no doubt what we saw matches the differential equations
--| because knowledge of the behavior of the differential equations informed the noise cancelling. How else would we know we got the right answer?
  | .blackhole bent_card _          _     , .einstein evidence          => bent_card ≠ evidence.truth
--| The important thing is, if the whitehole evidence comes _after_ the blackhole picture, we still know that the blackhole took place before
--| the whitehole.  We just can't tell the difference between our picture of the blackhole and what it should look like. The order doesn't change.
  | .blackhole bent_card card_value before, .whitehole evidence _ after => (bent_card ≠ evidence.truth ∧ le before after) ∨
                                                                           le (.blackhole bent_card card_value before) after
--| The thing about black holes is, information is lost.  Any bent card thrown in after the first one is no different from the first one. Other than
--| it was thrown in second.
  | .blackhole bent_card card_value before, .blackhole another_bent_card _ after =>
                                                                            (bent_card = another_bent_card ∧ le before after) ∨
                                                                            le (.blackhole bent_card card_value before) after
--| And, to be honest, we should be able to see the information come back out from Hawking radiation.
  | .blackhole bent_card card_value before, .geodesic _ _ another_bent_card _ now after =>
                                                    (bent_card = another_bent_card ∧ (le before now ∨ le before after)) ∨
                                                    le (.blackhole bent_card card_value before) now ∨ le (.blackhole bent_card card_value before) after

--| Finally, the actual orbital dynamics that Newton described, just with a bent card instead of a flat one:
  | .geodesic idea _         bent_card  _         _      _        , .einstein experiment        => idea ≠ experiment ∨ bent_card ≠ experiment.truth

--| To be honest with you.  You can truncate a geodesic anywhere you want and put a whitehole there and the math will look the same going forward
--| in time.  Meaning, looking backward in time there is no way to determine if you are looking at a whitehole.
  | .geodesic idea left_card bent_card right_card before up_to_now, .whitehole experiment _ now =>
                      (idea = experiment ∧ idea.truth = bent_card ∧ (le before now ∨ le up_to_now now)) ∨
                      le (.geodesic idea left_card bent_card right_card before up_to_now) now

--| A geodesic running to a black hole can only approach it.  If it touches, then it is captured.  There must exist some space between the bent
--| card and the horizon of the blackhole or it will have already fallen in.
  | .geodesic idea left_card bent_card right_card before up_to_now, .blackhole another_bent_card _ now =>
                      (bent_card = another_bent_card ∧ (le before now ∨ le up_to_now now)) ∨
                      le (.geodesic idea left_card bent_card right_card before up_to_now) now

--| Things can go around and around, and you no this because they go through another point that isn't before and after. A little four point
--| "time stencil": before now later after.  Later and after make 4 cards. Let's merge now and later into a single value, like dt.
  | .geodesic idea left_card bent_card right_card before up_to_now, .geodesic experiment _ another_bent_card _ now later =>
                      (idea = experiment ∧ bent_card = another_bent_card ∧ ((le before now ∧ le up_to_now later) ∨ (le before later ∧ le up_to_now now))) ∨
                      le (.geodesic idea left_card bent_card right_card before up_to_now) now ∨
                      le (.geodesic idea left_card bent_card right_card before up_to_now) later

--| Geodesics, by construction, are stable and their lengths do not change once halted.
termination_by _ path => sizeOf path
end SpaceTimePath

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
    [LOAD Box Pigeon]                          [OF Box Pigeon]                          [BULLSHIT Box Pigeon]              [PROPAGANDA Box Pigeon]
    [ACOLYTE Box Pigeon]                       [SCIENTIFIC Box Pigeon]                  [TRUTH Box Pigeon]                 [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (drachmα: LOCAL Box Pigeon)  --+ This is the one spot I can name this and it means nothing to the compiler, but it means something to *US*.
--                                 | Is this a drachma"
  where
  the_local_schedule: BigRedDogProcess Box Pigeon  -- Parents, read to your kids.  They are the future.
  the_direction_to_the_destination: SpaceTimePath
  uptown_or_downtown: Fact
  the_train_in: Type (i+1)
  the_quarter: LOCAL Box Pigeon := drachmα

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




end Measurement
