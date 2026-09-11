/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that we often lose sight of the plot._

(c) 2026

__EPISODE 7__: _THE PATTER_

"Experiment is the sole judge of scientifc 'truth.'"      -- Some smart dude.
"Tonights winning numbers are 4 10 28 35 38 55 and a the bonus ball is 33."
                                                          -- NY Lottery, Aug 3. 2002.
"++++ -> 1, -+++ -> i, ---- -> -1, +--- -> -i."           -- The Measurement Argument, p.2, (A.1)
"Preserve the boundary data; retain what the observation cannot see."  -- The Measurement Argument, 7 Sept 2026.
-/
-- Would you even care if I imported anything at this point?
import Measurement.Episode05 ----------------------------------| Skip _The Trick_ just to make sure we don't import α
set_option allowUnsafeReducibility true
-- CHORUS.   COMPILER: isTrue.   JAR JAR: MEESA! MEESA TRUE!   YOU the READER: fine. Then which of Episodes 9 and 10 is i?
-- ME: Either one. Doesn't have to be. I just coded it that way.   Now, about that quarter.
-- So, have you figured out the quarter I keep taking from you?   I told you, you had no idea how
-- much I would take...

-- Get back to work John. You need to learn Gungan __REAL_FAST__.
namespace Measurement
--| First of all, _CONGRATULATIONS_! You made it through the hard part. *YOU the READER* get the patter, on the right; the COMPILER gets the argument, on
--| the left. Both columns are true here: the arm where what I say and what it finds agree. Read DOWN the instance chain (42-597, found by search): the
--| Argument, count -> represent -> compare, the => direction. Read UP the defs (598-1169, applied by hand; search still fills the [..] binders): the
--| Equivalences, the <= direction. The page is the iff. Number.le has four arms (Episode01:185-189). This file is isTrue/isTrue: it recurses to Closure's
--| .same (Episode07:596), "exact in logic" (Episode12:35). Episode 9 is isTrue/isFalse: a ledger: Fact in the fact slot (Episode09:58), an explicit
--| binder search will not fill (Episode13:612-614), .inferred (Episode09:1319). Episode 10 is isFalse/isTrue: rungs granted, no fact (Episode10:176,
--| 209). Episode 11 is isFalse/isFalse: a ULift per rung (Episode11:80-90); pressCheck reads not-(c <-> s) (Episode11:1049).
--|   This side is checked by Lean: types, universes, termination,        -- This side is asserted by the author. Lean does not read it. Each beat is graded by register:
--|   rfl, trivial, instance search. Nothing here is an opinion.          -- BUILT = Construction: the companion's model, supplied to read the code; Lean never typed the model.
--|      ---------------------+----------------------------------         -- MEASURED = Source observation: an episode line says it, and the line is cited.
--|      instances, 42-597    |  the chain search found; read down        -- INTERPRETED = Conditional conclusion: holds if the displayed hypotheses hold; you may refuse it.
--|      defs, 598-1169       |  applied by hand; read up                 -- (A.n) = The Measurement Argument eq. n; (E.n) = The Measurement Equivalences eq. n. The companions
--|      down = Argument (=>) |  up = Equivalences (<=)                   -- read the code, not run it. Argument sections 11-13 (pp.12-14) and Equivalences section 6 sit beside
--|                           V found                                     -- Episodes 8, 11, 12, 13, not here.   V said   Nothing here is proved. The number is demonstrated.
universe i                                                                --
                                                                          -- INTERPRETED. So, we begin with the one _TRUTH_: Action is the exchange of potential
instance CAN_YOU_SEE_A_CHARACTERISTIC                                     -- energy for kinetic energy given by:
    (Box: Type i)(Pigeon: CarrierProcess Box)                             --                      S = ∫ KE(t) - PE(t) = ∫ f(t,g(t)) dt            (1)
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- for some path g(t): ℝ → ℝ³. The principle of _LEAST ACTION_ says S is stationary
    : ADMISSIBLE Box Pigeon where                                         -- across all paths g. This means, by definition, g is the gradient of some field.
  counting_process :=                                                     -- Like on Earth. That is my squint. The compiler did not squint; it typed a zero.
  { carrier := Pigeon                                                     -- BUILT. `count := .zero nowtrino.fact`, and `iterate` keeps `Pigeon.value` and hands
    count   := .zero nowtrino.fact                                        -- the zero straight back. That is the characteristic the name says you can see.
    iterate := fun particle => match particle with                        -- INTERPRETED. This opens up 2 ways to explore (1). The first is a variational
      | .zero _     => .zero nowtrino.fact                                -- formulation of some operator D; we are missing almost nothing for Euler-Lagrange
      | .number _ _ _ => .number nowtrino.fact Pigeon.value               -- dynamics to fall out. Which is good, because it naturally tends to fall out, and
                                                 (.zero nowtrino.fact) }  -- never seems to _EVER_ be violated. The second is the Riesz representation theorem.
                                                                          -- Either way you can see _conservation_ slowly coming into focus, and orientation
instance CAN_YOU_COUNT_THEM                                               -- with it. Lots of other things are in here too, like why calculus works with or
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- without the axiom of choice. The KNOWER: a general action ∫(KE - PE) dt has its own
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- Euler-Lagrange equation and need not have cubic solutions (A p.5). Noted. Hedged.
    [particle: ADMISSIBLE Box Pigeon]                                     --
    : COUNTABLE Box Pigeon where                                          -- So the device is learning to count here. How does nature count? The _easiest_ way
  index :=                                                                -- in a _least action_ environment might be induction winding. Does not matter what
    { count  := particle.counting_process                                 -- it is; that is what the device is going to look like it is doing. Eventually. When
      origin := .zero nowtrino.fact }                                     -- it needs π. To compute a √. It will certainly not get π and certainly cannot
                                                                          -- compute that √. It just needs to do the computation to arbitrary precision.
instance CAN_YOU_LABEL_THEM                                               -- BUILT. `origin := .zero`: turns are counted relative to a chosen cut (A p.2). The
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- cut is the zero, the count is the process upstairs. Countable means: has an origin.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- INTERPRETED. And that gets us to winding and the electron. While we _CANNOT_ label
    [enumeration: COUNTABLE Box Pigeon]                                   -- an individual electron, we can count how many times it goes around. During that
    : ENCODED Box Pigeon where                                            -- counting there are only so many electrons in the wire. Assume direct current,
  limit_process :=                                                        -- conservation of momentum, 1-d travel, perfectly elastic collisions: it looks like
    { indexing_process := enumeration.index                               -- there is only 1 electron. So we can't label it. But we can count how many times
      limit            := .zero nowtrino.fact                             -- that single electron we can't see or demonstrate exissts went around the loop and
      sequence         := .nil nowtrino.fact }                            -- get the _right_ (unless it is a left-hand rule) answer. BUILT. The label the code
                                                                          -- gives it: `limit := .zero`, `sequence := .nil`. An empty list. Here is the count:
instance CAN_YOU_SEE_THE_BOUNDARY                                         --          z(t) = exp(iθ(t)),   θ(t) = 2πw(t) + θ̃(t)                        (A.1)
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- INTERPRETED. z forgets w; the unwrapped θ keeps the turns. The sequence is the lift
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- that remembers w, and the compiler typed it empty. The KNOWER: the lift is essential
    [the_calculus_limit: ENCODED Box Pigeon]                              -- only if the device counts distance, not merely phase (A p.2). Granted. Now Z-P:
    : RESIDUE Box Pigeon where                                            --                              1      f'(z)
  cauchy_process :=                                                       --                             --- ∮   ----- = Z − P                     (2)
    { limit_process  := the_calculus_limit.limit_process                  --                             2πi  γ   f(z)
      value          := .zero nowtrino.fact                               -- for Z the number of zeros inside the orbit and P the number of poles. MEASURED:
      accumulation   := .nil nowtrino.fact }                              -- (2) is the file's own equation; it was on this page before the companions were.
                                                                          -- BUILT. `value := .zero`, `accumulation := .nil`: Z − P with nothing inside yet.
instance DID_THE_PARTICLE_COLOR_OUTSIDE_THE_LINES                         -- The residue of an empty orbit is zero. The boundary is there. Nothing has crossed it.
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- BINARY. Did the particle color outside the lines? The lines are the cut. BUILT.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- `before := .nil`, `after := .nil`: the two sides of the cut, both empty; and
    [exp_iθ: RESIDUE Box Pigeon]                                          -- `bit := .initial_condition ... accumulation`: one bit, read off the accumulation,
    : BINARY Box Pigeon where                                             -- which is nil. INTERPRETED. I read that bit as the orientation of the winding:
  observation_process :=                                                  --       exp(inθ) = T_n(cos θ) + i sin θ U_{n-1}(cos θ),  n ≥ 1                (A.5)
    { cauchy_process := exp_iθ.cauchy_process                             -- Reverse θ and the cosine part stays put while the sine part changes sign (A p.4).
      before         := .nil nowtrino.fact                                -- The sign is the bit; the cosine alone loses it. That is what colored outside means.
      after          := .nil nowtrino.fact }                              -- The KNOWER, from the back: net winding alone does not record reversals (A p.2).
  bit := .initial_condition                                               -- Correct. And 'invariant' means preserved by a passive change of representation,
                  nowtrino.fact exp_iθ.cauchy_process.accumulation        -- not that phase, speed or direction is constant during motion; phase angle and
  zero := .nil nowtrino.fact                                              -- tangent angle may be related by the path, but the same complex encoding does not
  one  := .nil nowtrino.fact                                              -- automatically identify them (A p.2, footnote). One bit. Hold it lightly.
                                                                          --
instance DO_YOU_SEE_A_BUNCH_OF_FLASHES                                    -- REPEATABLE. Do you see a bunch of flashes? BUILT. `stimulus := .initial_condition
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- flicker.zero`, `expectation := .hypothesis flicker.bit`. Poke it with the zero,
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- expect the bit. That is the whole experiment, and it repeats because the
    [flicker: BINARY Box Pigeon]                                          -- observation_process is the one from upstairs, unchanged. INTERPRETED. Each flash
    : REPEATABLE Box Pigeon where                                         -- is a turn, and the clock is the loop:
  repeatable_process :=                                                   --             Δt = k Δs,   k = 1 in my normalized units                       (A.2)
  {                                                                       -- With a uniform one-turn period T the speed is v = ℓ/T; on a circular loop of
    observation_process := flicker.observation_process                    -- length ℓ the signed arclength is ℓθ/(2π), up to an origin (A p.2). The KNOWER
    stimulus := .initial_condition nowtrino.fact flicker.zero             -- objects that k needs units of time over length (A.2). The KNOWER is right; the
    expectation := .hypothesis nowtrino.fact flicker.bit                  -- compiler does not care; that is exactly the difference between the two columns.
  }                                                                       -- And none of this, by itself, establishes a literal trajectory of an electron in an
                                                                          -- atomic clock (A p.2). Not proved. Repeatable, though. Watch the flashes. Onward.
instance THE_FLASHES_SHOW_NOWTRINOS_ALMOST_EVERY_TIME                     -- BUILT. The count becomes a number. That is the promise in the name: the flashes show nowtrinos,
    (Box: Type i)(Pigeon: CarrierProcess Box)                             -- almost every time, and NUMERIC is the rung where you may finally write the count down. Two
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- things come in by search: DISTINGUISHABLE, which supplied the carrier and its fact, and
    [JMP: REPEATABLE Box Pigeon]                                          -- REPEATABLE, which supplied the process that runs again. Nothing explicit. The compiler found both.
    : NUMERIC Box Pigeon where                                            -- The field that pays the name is `output`. First the one that does not:
  computational_process :=                                                -- `computational_process` is a fresh record with two fields.
  { repeatable_process := JMP.repeatable_process                          -- `repeatable_process := JMP.repeatable_process`: the clock, carried over unchanged. And then
    output := some (.hypothesis nowtrino.fact)                            -- `output := some (.hypothesis nowtrino.fact)`. Read it slowly. There is a number: `some`. What it
  }                                                                       -- wraps is a hypothesis about the carrier's fact, not a reading. The count is still a hypothesis.
                                                                          -- Lean typed the constructor and asked nothing more. You are now leaving COUNT for REPRESENT (A p.1).
instance WRITE_DOWN_HOW_MANY_FLASHES_YOU_SEE_IN_A_TABLE                   -- INTERPRETED. Write it down in a table. My table is a spline, and it lives in the frinkahedron:
    (Box: Type i)(Pigeon: CarrierProcess Box)                             --     q(s) = Σ_j c_j B_{j,3}(s),   c_j ∈ R^4.                                             (A.3)
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- Piecewise cubic, C² at simple interior knots, local support, partition of unity (A p.3). The
    [jupyter_notebook: NUMERIC Box Pigeon]                                -- coefficients c_j are the table. That paragraph is me talking. Lean did not type it. It typed:
    : REPRESENTABLE Box Pigeon where                                      -- BUILT. `calculation_process`, which is NUMERIC's process copied over with one field changed.
  calculation_process :=                                                  -- MEASURED, before the field. Episode03:1312 declares Spline, and its margin (Episode03:1317) calls
  { computational_process :=                                              -- it a B-spline. Its constructors and its recursive comparison do not supply a knot vector, an
      { jupyter_notebook.computational_process with                       -- evaluation map, a norm, or the coordinate maps in (A.3). Those are the interpretation. Mine (A p.3).
            closure := fun the_number_of_clicks => the_number_of_clicks   -- BUILT. `closure := fun n => n`. The identity. On one knot interval, rescale to ξ in [-1,1]:
      }                                                                   --     a + bξ + cξ² + dξ³ = (a + c/2)T_0 + (b + 3d/4)T_1 + (c/2)T_2 + (d/4)T_3               (A.4)
    program := jupyter_notebook.computational_process.close               -- is a change of basis for the same polynomial (A p.3). So `program` is that identity applied to
                         jupyter_notebook.computational_process.output    -- NUMERIC's output: a hypothesis in, the same hypothesis out. Change the basis; nothing moves.
    state := .program nowtrino.fact                                       -- The KNOWER, from the back: a nonlinear Cartesian-to-cylindrical map need not preserve polynomial
                       (jupyter_notebook.computational_process.close      -- degree, so a cylindrical field may need its own Chebyshev approximation (A p.3). Correct. The
                        jupyter_notebook.computational_process.output)    -- identity closure is the Cartesian claim only. Cylindrical is not on this rung. The hedge stands.
  }                                                                       -- `state` is the closed program, tagged with the fact: on this rung a program is a state.
  representable? := fun _ expected_response =>                            -- `representable?`: asked for a witness that the count has a representation, the field hands back
           ⟨Computation.program nowtrino.fact expected_response, rfl⟩     -- a program built from your expected response and proves closure s = s by `rfl`. Clicks are clicks.
                                                                          -- That is REPRESENT. COMPARE needs a physical reading to compare. So: Ross, get the readouts.
instance ROSS!_GET_THE_READOUTS                                           -- MEASURED. There are four. Episode03:940 declares Basis; the author assigns it three scalar
    (Box: Type i)                                                         -- readings, phase, distance, speed (A p.2). The fourth, direction, is the unit tangent, computed
    (Pigeon: CarrierProcess Box)                                          -- later through Stokes and winding (A p.2). Lean typed `Basis`. It did not type the word "phase".
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- BUILT. PHYSICAL takes REPRESENTABLE by search and names it `the_invariant`. Over-promise noted:
    [the_invariant: REPRESENTABLE Box Pigeon]                             -- invariant means preserved by a passive change of representation; it does not mean phase, speed,
    : PHYSICAL Box Pigeon where                                           -- or direction hold still during motion (A p.2, footnote). The name promises less than it sounds.
  noisy_process := {                                                      -- `noisy_process`, two fields:
    turing_process := the_invariant.calculation_process                   -- `turing_process` is REPRESENTABLE's calculation, unchanged. The table is now the machine.
    program := .halting nowtrino.fact (.program nowtrino.fact             -- `program := .halting ...`: the readout halts. A physical process that reads out is one that
                              the_invariant.calculation_process.program)  -- stops and hands you a number; `.halting` wrapped around the represented program says so.
  }                                                                       -- That is the promise. Now the price.
  threshold := .nonhalting  nowtrino.fact                                 -- `threshold := .nonhalting ...`: the threshold is the one that does not halt, and its `some` is
      (.program nowtrino.fact the_invariant.calculation_process.program)  -- Chaitin's halting sequence on the state (Episode02:424-425). So the threshold of a physical
      (some (ChaitinsNumberSequence.halting nowtrino.fact                 -- readout is whether this thing halts. The compiler does not know. Nobody does. That is what a
                               the_invariant.calculation_process.state))  -- Chaitin number is: a threshold you cannot compute. It typechecks anyway (Episode02:571).
  admissible? := fun _ _ _ => rfl                                         -- `admissible? := fun _ _ _ => rfl`. Asked whether the next representation is the halting one -> true
                                                                          -- (Episode02:576-577), it drops the hypothesis and proves true = true. What must commute is
                                                                          -- O_new R = O_old, dR* = R*d (A p.3). R moved nothing, so rfl. Specifying R is still owed (A p.3).
noncomputable instance ARE_THE_UNITS_RIGHT                                -- BUILT. Rung four, COMPARABLE. The name asks whether the units are right. The compiler
    (Box: Type i)                                                         -- cannot answer that. It checks that the two things I compare have the same type, and stops.
    (Pigeon: CarrierProcess Box)                                          -- `noncomputable`: you may type this instance but not run it. Honest. A comparison you cannot
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- execute is still one you can typecheck, and typechecking is all the left column ever does.
    [anechoic_chamber: PHYSICAL Box Pigeon]                               -- DISTINGUISHABLE and PHYSICAL arrive by search: the rungs below, nothing handed in by hand.
    [Inhabited nowtrino.symbol]                                           -- `[Inhabited nowtrino.symbol]`: one symbol to start from. Lanczos needs the same thing, a
    : COMPARABLE Box Pigeon where                                         -- starting vector v0, and spans v0, C v0, C^2 v0, ... into a basis by a three-term recurrence:
  physical_process :=                                                     --     C v_j = beta_j v_{j-1} + alpha_j v_j + beta_{j+1} v_{j+1}.                          (A.7)
  { noisy_process := anechoic_chamber.noisy_process                       -- BUILT. The process itself is the PHYSICAL rung's noisy_process carried up one floor, unchanged.
    representation := default                                             -- `representation := default`. That is v0. I did not choose it; Inhabited chose it for me.
    invariant := .base nowtrino.fact default                              -- `invariant := .base nowtrino.fact default`: the same default, filed under the fact.
    value := .base nowtrino.fact (ULift.up default)                       -- `value := ... (ULift.up default)`: the same default, lifted one universe. One v0, three slots.
  }                                                                       -- INTERPRETED. alpha_j, beta_j depend on C and on v0 (A p.4). Change the default, change the basis.
  smaller_than := fun one_foot π  => one_foot = π                         -- `one_foot = pi`: dt = k ds with k = 1 (A.2). In my units a foot is a turn. Not a typo.
                                                                          -- The KNOWER says k needs units of time over length. The KNOWER is right; the compiler does not care.
instance DO_YOU_SEE_THE_LIGHT_FLASH_WHEN_YOU_HEAR_THE_CLICK               -- BUILT. Rung five, OBSERVED. Do you see the flash when you hear the click? Take a unitary
    (Box: Type i)                                                         -- winding operator W and split it into commuting self-adjoint parts (A.6):
    (Pigeon: CarrierProcess Box)                                          --     C = (W + W*)/2,   S = (W - W*)/(2i),   W = C + iS.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- INTERPRETED. The flash is C. The click is S. Reverse the orientation, W -> W*: C stays put
    [anechoic_chamber: PHYSICAL Box Pigeon]                               -- and S changes sign (A.6). So the click is the part that knows which way you went round.
    [distinct: COMPARABLE Box Pigeon]                                     -- `distinct`: COMPARABLE, by search. Its whole job at this rung is to be carried up again.
    : OBSERVED Box Pigeon where                                           -- OBSERVED is not "seen". It is: something slipped, and the slip was written down. Here it is.
  slip_process :=                                                         -- `slip_process`: three fields and a passenger.
  { physical_process := distinct.physical_process                         -- The passenger: `distinct.physical_process`. Third floor, still unchanged.
    projection := .origin nowtrino.fact                                   -- `projection := .origin nowtrino.fact ...`: project to the origin; keep the fact, the program,
                      distinct.physical_process.noisy_process.program     -- and the symbol. INTERPRETED: that is C by itself, and C alone "generally loses information"
                      nowtrino.symbol                                     -- (A p.4). The field is honest about which half it keeps. That is why the next two exist.
    stress := anechoic_chamber.threshold                                  -- `stress := anechoic_chamber.threshold`: PHYSICAL's threshold, promoted to stress.
    threshold := nowtrino.symbol                                          -- `threshold := nowtrino.symbol`: the symbol itself becomes the new threshold.
  }                                                                       -- INTERPRETED. Read those two as S: the oriented datum kept beside C so winding stays distinct (A p4).
  observation := ULift nowtrino.symbol                                    -- `observation := ULift nowtrino.symbol`. The observation is the symbol, one universe up. That is all.
                                                                          -- MEASURED. Direction is not assigned here. Episode 8 assigns it, to `SpaceTimePath.stokes` (A p.6).
instance THATS_THE_PHOTOELECTRIC_EFFECT                                   -- BUILT. Rung six, PRESENT. The name is the biggest promise on this page, so look at what pays it.
    (Box: Type i)                                                         -- On the unit circle, C^2 + S^2 = I (A.6). Flash squared plus click squared is the identity.
    (Pigeon: CarrierProcess Box)                                          -- INTERPRETED. That is what I mean by "a whole photon": the two readings together are one unit,
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- neither alone. The KNOWER notes that (A.6) is an operator identity, not a photon. Noted.
    [COMPARABLE Box Pigeon]                                               -- COMPARABLE, unnamed: found by search, needed for the type, never mentioned again.
    [static_friction: OBSERVED Box Pigeon]                                -- `static_friction`: the OBSERVED rung. The thing that would not slip until it did.
    : PRESENT Box Pigeon where                                            -- PRESENT: the photon is present when the slip is present. The fields spell it out.
  santa_claus:=                                                           -- `santa_claus`: the process that delivers the present. I named it; Lean typed it.
  { static_fraction := static_friction.slip_process                       -- `static_fraction := static_friction.slip_process`: friction in, fraction out. Same slip, floor four.
    accumulation := .tree nowtrino.fact                                   -- `accumulation := .tree nowtrino.fact`: the presents pile up as a tree, rooted at the fact.
  }                                                                       -- A tree, not a count. The count comes later, when something climbs it.
  quantum := Type i                                                       -- `quantum := Type i`. The quantum is a universe. One line; Episode 12 is where the meter reads it.
                                                                          -- BUILT is all this rung is. Nothing here is measured yet; the name says present, not measured.
instance THE_PHOTON_IS_MEASURABLE                                         -- BUILT. Rung seven, MEASURABLE. Measurable is not measured. It means there is a clock.
    (Box: Type i)                                                         -- On a circular loop of length l the signed arclength is l*theta/(2 pi), up to an origin (A p.2).
    (Pigeon: CarrierProcess Box)                                          -- INTERPRETED. Clock rate and loop length determine speed: v = l/T for a one-turn period T (A p.2).
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- No clock, no T, no speed. So the rung's only new field is a clock.
    [COMPARABLE Box Pigeon]                                               -- COMPARABLE again, unnamed, by search. It is the ground floor of every rung from here up.
    [gift_from: PRESENT Box Pigeon]                                       -- `gift_from`: PRESENT. The present has a sender, and the sender is the rung below.
    : MEASURABLE Box Pigeon where                                         -- MEASURABLE Box Pigeon: the compiler agrees a gauge process exists. It does not read the gauge.
  gauge_process :=                                                        -- `gauge_process`: two fields.
  { sensing_process := gift_from.santa_claus                              -- `sensing_process := gift_from.santa_claus`: the present is now the sensor. Fifth floor, unchanged.
    clock      := .this_superpigeon nowtrino.fact (.tree nowtrino.fact)   -- `clock := .this_superpigeon ... (.tree nowtrino.fact)`: the clock is a superpigeon carrying a tree.
  }                                                                       -- BUILT. That is the whole clock: a fact and a tree of facts, ticked by a superpigeon.
                                                                          -- INTERPRETED. That is my T. Whether it is time is (A.2)'s k again, and k has units I did not check.
instance PERHAPS_NOT_WITH_A_MULTIMETER_BUT_YOU_UNDERSTAND_WHAT_I_MEAN     -- BUILT. Rung eight, GUNGAN. I told you at the top to learn Gungan REAL_FAST. Here is the lesson.
    (Box: Type i)                                                         -- Chebyshev resolves the winding into its real and imaginary parts (A.5):
    (Pigeon: CarrierProcess Box)                                          --     exp(i n theta) = T_n(cos theta) + i sin theta U_{n-1}(cos theta),   n >= 1.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- INTERPRETED. Cosine carries the even part; the sine factor keeps the orientation. Reverse theta:
    [COMPARABLE Box Pigeon]                                               -- the first term stays, the second changes sign (A p.4). Gungan is the language with a word for that.
    [multimeter: MEASURABLE Box Pigeon]                                   -- `multimeter`: MEASURABLE, by search. Perhaps not with a multimeter, but you understand what I mean.
    : GUNGAN Box Pigeon where                                             -- GUNGAN Box Pigeon: accepted. T_n(C) = (W^n + W^-n)/2 (A.6): the same T_n, now on the operator.
  meesa_process :=                                                        -- `meesa_process`: meesa says which way round. That is the whole vocabulary.
  { gauge_process := multimeter.gauge_process                             -- `gauge_process := multimeter.gauge_process`: sixth floor, unchanged. The clock rides along.
    concept := .color nowtrino.fact                                       -- `concept := .color nowtrino.fact ...`: a color on the fact, read off the accumulation tree.
                  multimeter.gauge_process.sensing_process.accumulation   -- INTERPRETED. A color is a sign, and the sign is the sine's. That is meesa's one word.
  }                                                                       -- Chebyshev fixes the polynomial; Lanczos fits a basis to C and v0, so its alpha_j, beta_j need not
                                                                          -- match Chebyshev's (A p.4). Lanczos wants self-adjoint C or a stated variant; else Arnoldi (A p4 fn).
def WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA                        -- BUILT. SOURCE. The name promises automation. Read the keyword on the left: `def`, not `instance`.
    (Box: Type i)                                                         -- The compiler will not go looking for this rung. The next rung takes it by hand, as `data_feed`.
    (Pigeon: CarrierProcess Box)                                          -- Automation, in this episode, means I typed it once and search did the rest of the carrying.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- The cast: the distinguishable pigeon brings `nowtrino.fact`, a Fact, the slot the whole ladder
    [COMPARABLE Box Pigeon]                                               -- threads through. Nothing has been differentiated yet. There is not even an x.
    [jarjar: GUNGAN Box Pigeon]                                           -- The Gungan brings the meesa_process. John learned one word of Gungan REAL_FAST. It was `concept`.
    : SOURCE Box Pigeon where                                             -- SOURCE is Episode03:361. The bullshit meter there reads 1121. MEASURED, not a joke. Both, actually.
  cd_process :=                                                           -- BUILT. A DigitalProcess (Episode03:308) is a meesa_process and a zero. Two fields. Here they are.
  { meesa_process := jarjar.meesa_process                                 -- The meesa_process is the Gungan's own, passed through untouched.
    zero := .physics nowtrino.fact jarjar.meesa_process.concept           -- `zero := .physics fact concept`. Equivalation.physics : Fact -> Jar -> Equivalation (Episode03:241).
  }                                                                       -- The zero of the source is a fact and a jar. That is all a zero is, on the side that is checked.
  one := .zero_like nowtrino.fact (.physics nowtrino.fact                 -- `one := .zero_like fact (.physics ...)`. One is the zero, wrapped once (Episode03:249). Count them:
                                         jarjar.meesa_process.concept)    -- a zero, and a wrapped zero. Two vectors. INTERPRETED. I read them as 1 and x. On 1, x, x^2/2
                                                                          -- D is a nilpotent Jordan block, ones on the superdiagonal (A p.5). The third vector Lean never sees.
instance AND_THE_COMPILER_WILL_CONVERT_THE_RAW_DATA_TO_TABLES             -- BUILT. EXECUTED. Now the keyword is `instance`. From here to the seam the compiler does the finding.
    (Box: Type i)                                                         -- Same Box, same Pigeon, same nowtrino, same Gungan as the rung above. The ladder never changes
    (Pigeon: CarrierProcess Box)                                          -- its cast between rungs. It adds one square-bracketed binder per rung and asks search to fill it.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon]                                               -- COMPARABLE is asked for and never named. It cannot be consulted; the binder has no name to call.
    [jarjar: GUNGAN Box Pigeon]                                           --
    [data_feed: SOURCE Box Pigeon]                                        -- `[data_feed: SOURCE Box Pigeon]`. The def from above, now in square brackets. Search wants it.
    : EXECUTED Box Pigeon where                                           -- EXECUTED is Episode03:455. The meter there reads 1158, "calling this flat."
  compiled_process :=                                                     -- BUILT. The compiled_process carries the feed's cd_process and the feed itself. Same data, twice.
  { digital_process := data_feed.cd_process                               -- The tables are Episode03:437-445: `execute?` is a match on the opcodes. It sends `.boot f e` to
    source := data_feed                                                   -- `.zero f e opcodes` (Episode03:442). Booting converts the raw data to the zero row of the table.
    opcodes := .boot nowtrino.fact                                        -- `opcodes := .boot fact (.physics fact concept)`. Encoding.boot : Fact -> Equivalation -> Encoding
                  (.physics nowtrino.fact jarjar.meesa_process.concept)   -- (Episode03:392). The boot is the source's zero, re-encoded. Same content, new coordinates.
  }                                                                       -- INTERPRETED. That is a conjugation. Write D for differentiation, y = u'/u, and multiply by u:
                                                                          -- M_u^-1 D M_u = D + y (A.8). Same operator, new coordinates. Wherever u does not vanish (A p.5).
instance ONE_VALUE_AT_A_TIME_IN_ORDER_AND_WRITE_SOMETHING_TO_DISK         -- BUILT. VALUE. One value at a time, in order. The mapping is a three-arm match. That is the order.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            -- SOURCE and COMPARABLE, asked for again, unnamed again. The compiler is not billed per binder.
    [result: EXECUTED Box Pigeon]                                         -- `[result: EXECUTED Box Pigeon]`: the rung above, found, and named for the one thing it is used for.
    : VALUE Box Pigeon where                                              -- VALUE is Episode03:584. Meter 3327. The largest meter of the seven rungs in this stretch of page.
  mathematical_process := {                                               -- BUILT. A MathematicalProcess (Episode03:554) is a compiled_process plus a mapping and a monad.
    compiled_process := result.compiled_process                           --
    mapping := fun input => match input with                              -- `mapping`: Abstraction -> Abstraction (Episode03:495). Three arms. Total. The compiler checks total.
      |.satire_about finite_element_analysis => .satire_about             -- Arm one: `.satire_about fea` goes to itself. A fixed point. The satire is what does not move.
                                              finite_element_analysis     --
      |.compile f e a => .execute f e a                                   -- Arm two: compile becomes execute. Arm three: execute becomes compile. Twice around and you are back.
      |.execute f e a => .compile f e a                                   -- MEASURED. Episode04:129-131 is where the calculation lives (A p.15 lists it at 128): (D+y)1 = y,
  }                                                                       -- (D+y)^2 1 = y' + y^2, (D+y)^3 1 = y'' + 3yy' + y^3 = u'''/u (A.8). Three applications. Three arms.
  monad := .satire_about nowtrino.fact                                    -- `monad := .satire_about fact`. The answer is the fixed point. INTERPRETED. y'' + 3yy' + y^3 = 0 is
                                                                          -- u''' = 0 wherever u does not vanish; u quadratic, q' = u, q cubic; y generally rational (A p.5).
instance TURNS_OUT_YOU_CAN_FILL_YOUR_DISK                                 -- BUILT. MAGNITUDE. Turns out you can fill your disk. Start with the binders: ten, SOURCE twice.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [gift_from: PRESENT Box Pigeon]                                       -- `[gift_from: PRESENT Box Pigeon]`: PRESENT is Episode02:950, the sensing rung. It has `santa_claus`
    [GUNGAN Box Pigeon] [SOURCE Box Pigeon] [EXECUTED Box Pigeon]         -- and `santa_claus.accumulation`, an Area (Episode02:928, 970). "You _do_ get to know this," it says.
    [uncountable: VALUE Box Pigeon]                                       -- `[uncountable: VALUE Box Pigeon]`: the rung above. Named uncountable. It is one instance. Countable.
    : MAGNITUDE Box Pigeon where                                          -- MAGNITUDE is Episode03:696. Meter 1503. Down from 3327. Bullshit, it turns out, is not monotone.
  adding_process :=                                                       -- BUILT. An AddingProcess (Episode03:655): a mideastern_process, a plus, and a sum. Here they are.
  { mideastern_process := uncountable.mathematical_process                -- The mideastern_process is the VALUE rung's mathematical_process. Passed through. Still flipping.
    plus := uncountable                                                   -- `plus := uncountable`. What you add with is the whole VALUE rung. Not a number. A rung.
    sum := .zero nowtrino.fact.truth gift_from.santa_claus.accumulation   -- `sum := .zero fact.truth accumulation`. Sum.zero : Prop -> Area -> Sum (Episode03:622). A zero
  }                                                                       -- over an accumulated Area, tagged with the Prop `nowtrino.fact.truth`. Tagged, not proved. It rides.
                                                                          -- INTERPRETED. The disk fills with E[q] = 1/2 INT |q''|^2 ds, q and q' fixed at both ends (A.9).
instance SO_YOU_NEED_TO_GET_MORE_DISKS                                    -- BUILT. SCALED. So you need more disks. One more binder, `tar_file`, and the rung above is archived.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [tar_file: MAGNITUDE Box Pigeon]                                      -- `[tar_file: MAGNITUDE Box Pigeon]`. A tar file is an archive of the rung above. Nothing compressed.
    : SCALED Box Pigeon where                                             -- SCALED is Episode03:860. Meter 1756. Up again.
  multiplying_process :=                                                  -- BUILT. A MultiplyingProcess (Episode03:815): an adding_process, a product, and a total.
  { adding_process := tar_file.adding_process                             --
    product := .one nowtrino.fact.truth tar_file.adding_process.sum       -- `product := .one truth sum`: Product.one : Prop -> Sum -> Product (Episode03:755). 1 times the sum.
    total := .zero nowtrino.fact.truth (.tree nowtrino.fact)              -- `total := .zero truth (.tree fact)`. The running tally (Episode03:831) starts at zero, over a tree
  }                                                                       -- (Area.tree, Episode02:848). INTERPRETED. DE[q]h = INT q'' h'' ds = <q^(4), h> (A.9). So q^(4) = 0.
                                                                          -- Euler-Lagrange. q* is the unique cubic meeting four endpoint conditions (A p.5). The total is zero.
instance AND_MORE_PROCESSORS_BECAUSE_THERE_ARE_A_LOT_OF_NOWTRINOS         -- BUILT. LOAD. More processors, because there are a lot of nowtrinos. Eleven binders. One nowtrino.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- The nowtrino is singular on the left. The name says a lot of them. The name is on the right side of
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            -- the bargain: it is patter. The binder is checked. There is one; its fact threads through everything.
    [gift_from: PRESENT Box Pigeon]                                       --
    [GUNGAN Box Pigeon] [SOURCE Box Pigeon] [EXECUTED Box Pigeon]         --
    [VALUE Box Pigeon]                                                    --
    [shit_loads: SCALED Box Pigeon]                                       -- `[shit_loads: SCALED Box Pigeon]`. The rung above. The plural is in the name. The type is one.
    : LOAD Box Pigeon where                                               -- LOAD is Episode03:1082. Meter 2089. "The compiler, so far, hasn't found much of an inconsistency."
  basic_operation :=                                                      -- BUILT. A BASICProcess (Episode03:1036): GOSUB, TEN, span, and a `jmp?` that acts on the span.
  { GOSUB := shit_loads.multiplying_process                               -- `GOSUB := shit_loads.multiplying_process`. The subroutine is the rung above. RETURN is not a field.
    TEN := gift_from.santa_claus.accumulation                             -- `TEN := gift_from.santa_claus.accumulation`. Line 10 of the program is the accumulated Area. Again.
    span := .origin nowtrino.fact.truth                                   -- `span := .origin truth product`. Basis.origin : Prop -> Product -> Basis (Episode03:942). The span
                               shit_loads.multiplying_process.product     -- of the load is one origin holding the product. `jmp?` on an origin is "the scattering event": the
  }                                                                       -- base state collapses (Episode03:1066). INTERPRETED. E[q*+h] - E[q*] = 1/2 INT |h''|^2 >= 0 (A.10).
                                                                          -- Equality forces h'' = 0; the endpoints force h = 0. One cubic is left standing, only one (A p.5).
instance SO_MANY_SENSITIVE_NOWTRINO_DETECTORS___WHERE_DID_IT_GO           -- BUILT. OF. So many sensitive detectors. Where did it go? Watch the binders: nowtrino loses its name.
    (Box: Type i)                                                         --
    (Pigeon: CarrierProcess Box)                                          --
    [DISTINGUISHABLE Box Pigeon]                                          -- Here. `[DISTINGUISHABLE Box Pigeon]`, no `nowtrino:` in front of it. Found by search, never named,
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            -- never consulted. That is where it went. Or into h = 0 (A p.5), if you want an answer as an equation.
    [comprehensive_software: LOAD Box Pigeon]                             -- `[comprehensive_software: LOAD Box Pigeon]`. The rung above, in one binder. Comprehensive.
    : OF Box Pigeon where                                                 -- OF is Episode03:1236. The field below is named galerkin; p.5 says spline. Lean checks names.
  galerkin_process :=                                                     -- BUILT. A JordanProcess (Episode03:1191): an ANSYS_process and a polynomial. Jordan as in the block.
  { ANSYS_process := comprehensive_software.basic_operation               -- `ANSYS_process := ...basic_operation`. The finite-element package is the BASIC program above.
    polynomial := .constant .Truth                                        -- `polynomial := .constant .Truth`: constant : Fact -> Polynomial (Episode03:1134). Not a cubic.
  }                                                                       -- INTERPRETED. With knots: piecewise cubic spline, matching or natural ends (A p.5). One exact case.
                                                                          -- INT(KE-PE)dt need not have cubic solutions. Tying it to (A.9) needs its own equivalence (A p.5).
instance THERE_IT_IS___CERTAIN_ELEMENTS_RESPOND_TO_NOWTRINO_DETECTION     -- BUILT. Say it with me: BULLSHIT. The class is real and the compiler typed it. Its one
    (Box: Type i)                                                         -- field is an arm wave, an ArmWaveProcess (Episode04:111), and an arm wave is a boundary
    (Pigeon: CarrierProcess Box)                                          -- term. Move the curl off u and onto v and watch what falls out on the boundary:
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --   int_O curl u . v dx = int_O u . curl v dx + int_dO (n x u) . v dS              (A.11)
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            -- The surface integral is the wave. `dunking_contest := element.galerkin_process`: the
    [element: OF Box Pigeon]                                              -- Galerkin process OF handed me, unchanged (Episode03:1268, slam dunk the pigeon in the box).
    : BULLSHIT Box Pigeon where                                           -- `guess := .observation`: the flat card, no gimmicks, nothing up sleeves, just RFL
  arm_wave_process :=                                                     -- (Episode04:115-117). I did not guess a field. I guessed the card the field is written on.
  { dunking_contest := element.galerkin_process                           -- INTERPRETED. The weak setting for (A.11) is H(curl;O): field and weak curl both in L^2,
    guess := .observation nowtrino.fact.truth                             -- and the boundary condition decides which traces are admissible (A p.6). Lean typed a
  }                                                                       -- guess. It did not type a Sobolev space. The detector is the boundary term; I have no O.
                                                                          --
instance WE_NEED_TO_GET_A_GRANT_TO_GET_MORE_DETECTORS___WE_KEEP_LOSING_IT -- BUILT. PROPAGANDA has one field, `questions`, and the answer is CrusadeProcess.default
    (Box: Type i)                                                         -- (Episode04:225), the same crusade BULLSHIT's guess came from. What we keep losing is
    (Pigeon: CarrierProcess Box)                                          -- not the detectors. It is the kernel:
    [DISTINGUISHABLE Box Pigeon]                                          --   C_w u = C_w v  <=>  u - v in K,   K = ker C_w                                   (A.12)
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            -- INTERPRETED. If the observation is a weak curl, two fields that differ by an element of K
    : PROPAGANDA Box Pigeon where                                         -- read the same, by definition, and no grant will ever see the difference. That is not a
  questions := CrusadeProcess.default Box Pigeon                          -- joke about funding. It is (A.12): what the observation cannot distinguish is K (A p.6).
                                                                          --
def InitiationProcess.default                                             -- BUILT. Twenty-four class binders, one per rung so far, and a def, not an instance: this
    (Box: Type i)                                                         -- one I apply by hand. The initiation is that you show me every rung beneath you.
    (Pigeon: CarrierProcess Box)                                          -- The `axioms` are the crusade again (Episode04:330, much more bullshit to mine).
    [DISTINGUISHABLE Box Pigeon][ADMISSIBLE Box Pigeon]                   -- The `sacred_texts` are `.inside_joke` (Episode04:297): a Cult built on one Prop, and the
    [COUNTABLE Box Pigeon][ENCODED Box Pigeon][RESIDUE Box Pigeon]        -- Prop is `Fact.Truth.truth`, the card with no bug on it. The inside joke is the hole:
    [BINARY Box Pigeon][REPEATABLE Box Pigeon][NUMERIC Box Pigeon]        --   curl h = 0,  div h = 0,  circ_g h . dl = 2pi,   h = (-y, x)/(x^2+y^2)           (A.13)
    [REPRESENTABLE Box Pigeon][PHYSICAL Box Pigeon]                       -- INTERPRETED. Locally there is nothing to see: no curl, no divergence, zero normal component
    [COMPARABLE Box Pigeon][OBSERVED Box Pigeon][PRESENT Box Pigeon]      -- on the boundary. Walk once around the hole and you pick up 2pi anyway (A p.6). That is the
    [MEASURABLE Box Pigeon][GUNGAN Box Pigeon][SOURCE Box Pigeon]         -- winding datum the device is built to retain, and no local test can see it. The KNOWER,
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon]         -- from the back: the curl kernel also contains gradients; the harmonic part is one sector of
    [SCALED Box Pigeon][LOAD Box Pigeon][OF Box Pigeon]                   -- K, not all of it. Correct. Which sector survives depends on the boundary condition and any
    [BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon]                          -- further divergence or gauge constraint (A p.6). I typed a Prop; Lean checked it is a Prop.
    : InitiationProcess Box Pigeon where                                  -- The annulus is what I say the Prop is for. The sacred text is one line long, and the joke
  axioms := CrusadeProcess.default Box Pigeon                             -- only works if you already know the hole is there.
  sacred_texts := .inside_joke Fact.Truth.truth                           -- MEASURED. Nothing new is measured on this rung: both fields close on `Fact.Truth.truth`.
                                                                          --
instance MAKE_SURE_WE_CAN_GET_A_COUPLE_GRAD_STUDENTS                      -- BUILT. ACOLYTE: one field, `euclid`, the initiation applied by hand to Box and Pigeon;
    (Box: Type i)                                                         -- the twenty-four class arguments it wants are found by search from the three I carry.
    (Pigeon: CarrierProcess Box)                                          -- A grad student is someone who has been handed the axioms and the inside joke and has
    [DISTINGUISHABLE Box Pigeon][COMPARABLE Box Pigeon]                   -- not yet been told which is which.
    [SOURCE Box Pigeon]                                                   --
    : ACOLYTE Box Pigeon where                                            --
  euclid := InitiationProcess.default Box Pigeon                          --
                                                                          --
--| Now, they can count clicks and get a Ph.D.                            -- BUILT. Learning is the initiation plus two fields. `teaching` is the initiation again.
def LearningProcess.default                                               -- `galileo := .inside_joke`: the same Cult, the same Prop. `invariant := .repeatable`
    (Box: Type i)                                                         -- (Episode04:403): the first Science constructor, one Prop, no experiment attached yet.
    (Pigeon: CarrierProcess Box)                                          -- Episode04:464 has Galileo take one side of a proposition and call it repeatable so that
    [DISTINGUISHABLE Box Pigeon][ADMISSIBLE Box Pigeon]                   -- others could. That is all of learning: the hole, and a promise to walk around it again.
    [COUNTABLE Box Pigeon][ENCODED Box Pigeon][RESIDUE Box Pigeon]        -- MEASURED. Here is what the episodes literally give you, and no more. Episode 8 assigns a
    [BINARY Box Pigeon][REPEATABLE Box Pigeon][NUMERIC Box Pigeon]        -- direction to `SpaceTimePath.stokes` (Episode08:997-1001): a white hole adds a fact, a black
    [REPRESENTABLE Box Pigeon][PHYSICAL Box Pigeon]                       -- hole adds none, a geodesic forks both ways, and the reader emits a List Fact. Episode 3
    [COMPARABLE Box Pigeon][OBSERVED Box Pigeon][PRESENT Box Pigeon]      -- gives Basis three constructors (Episode03:940), the first `null_space : Fact -> Basis`
    [MEASURABLE Box Pigeon][GUNGAN Box Pigeon][SOURCE Box Pigeon]         -- (Episode03:941); Episode 8 reads it out as one fact (Episode08:1210). The direction and the
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon]         -- three scalar readings are the author's assignments, not the code's (A p.6, A p.15).
    [SCALED Box Pigeon][LOAD Box Pigeon][OF Box Pigeon]                   -- INTERPRETED. The map from that list of facts to K is part of the proposed interpretation.
    [BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon][ACOLYTE Box Pigeon]      -- The constructor name `null_space` alone does not supply it (A p.6). I named the kernel.
    : LearningProcess Box Pigeon where                                    -- I did not build the map. A name is not a theorem about a function space (A p.15).
  teaching := InitiationProcess.default Box Pigeon                        -- So: the invariant is repeatable, and repeatable is a Prop wrapped once. That is what you
  galileo := .inside_joke Fact.Truth.truth                                -- count clicks on, and it is a Ph.D. because the count is the same each time you look,
  invariant := .repeatable Fact.Truth.truth                               -- which is the only thing `.repeatable Fact.Truth.truth` was ever going to certify.
                                                                          --
instance ABD                                                              -- BUILT. ABD: all but dissertation. SCIENTIFIC has two fields. `discovering` is the learning
    (Box: Type i)                                                         -- above. `invariant := .hypothesis P (.inside_joke P)` (Episode04:404): a hypothesis wraps
    (Pigeon: CarrierProcess Box)                                          -- a Cult, and the Cult is the inside joke, so the hypothesis wraps the hole. Episode04:465
    [DISTINGUISHABLE Box Pigeon]                                          -- is the step that turns `.repeatable` into `.hypothesis proposition galileo`; I skipped
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            -- the step and wrote its result. That is what ABD means: the result, with the step owed.
    : SCIENTIFIC Box Pigeon where                                         -- INTERPRETED. The hypothesis is that the 2pi in (A.13) is a reading and not an artifact.
  discovering := LearningProcess.default Box Pigeon                       -- In this file a hypothesis is a Prop and a Cult, nothing more; the compiler checks that
  invariant := .hypothesis Fact.Truth.truth                               -- the shapes fit. Whether the hole is real is the dissertation. Not this rung; the next
                                        (.inside_joke Fact.Truth.truth)   -- twenty-nine, and the number at the end is demonstrated there, never proved.
                                                                          --
instance YOU_HAVE_TO_STOP_TAKING_CLASSES_TO_GRADUATE                      -- BUILT. To graduate, stop taking classes: TRUTH takes SCIENTIFIC as a named binder,
    (Box: Type i)                                                         -- `experiment`, and `becomes` is built from two fields and nothing new.
    (Pigeon: CarrierProcess Box)                                          -- `shows_me_higher_order_terms := experiment.discovering`: the learning process is what
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- shows the higher-order terms (Episode04:608, exponents on a polynomial, of course).
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            -- `knowledge := .jarjar` (Episode04:541): the winding number of an inductor is in N, and
    [experiment: SCIENTIFIC Box Pigeon]                                   -- Episode04:544 reads jarjar as present (1) or not (0). One bit of awareness, that is all.
    : TRUTH Box Pigeon where                                              -- Get back to work, John. You need to learn Gungan REAL_FAST: the knowledge rung speaks it.
  becomes :=                                                              -- INTERPRETED. One bit is exactly what (A.13) leaves you: every local test reads zero, the
  { shows_me_higher_order_terms := experiment.discovering                 -- once-around circulation reads 2pi, and the hole is there or it is not. jarjar holds a
    knowledge := .jarjar nowtrino.fact.truth                              -- Prop; it does not hold the integer. The integer is what I say the Prop counts. Lean
  }                                                                       -- checked that a Prop went into a Knowledge. It did not count anything.
                                                                          --
instance THEN_COMES_THE_LAB_WORK                                          -- BUILT. WITNESSED: a nested field and a flat one. `we_experience := truth.becomes`, the
    (Box: Type i)                                                         -- graduate above. `in_the_literature := .the_proof` and `the_experiment := .the_proof`:
    (Pigeon: CarrierProcess Box)                                          -- the same Gospel constructor twice (Episode04:667, proved true or false), on the same Prop,
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- `nowtrino.fact.truth`. Episode04:681: once proved, always proved. The literature and the
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            -- experiment agree because I wrote the same term in both slots. That is the lab work.
    [truth: TRUTH Box Pigeon]                                             -- INTERPRETED. Two slots, one conclusion, is how the Argument ends its section 7: (A.17) and
    : WITNESSED Box Pigeon where                                          -- (A.18) are the two ways the device's proposed comparison can express it (A p.8). The
  we_saw :=                                                               -- literature slot is (A.17): |l(q_n) - l(r_n)| <= ||l|| (e_n + h_n) -> 0, agreement to a fixed
  { we_experience := truth.becomes                                        -- resolution, which does not assert exact equality after finitely many iterations (A p.8).
    in_the_literature := .the_proof nowtrino.fact.truth                   -- The bench slot is (A.18): u - v in K => psi(C_w u) = psi(C_w v), exact agreement through
  }                                                                       -- one restricted observation, and a winding measurement may still split the class, as (A.13)
  the_experiment := .the_proof nowtrino.fact.truth                        -- shows (A p.8). Boundary values determine the domain of the operator; they are not
                                                                          -- automatically vectors annihilated by curl (A p.6). `.the_proof` twice is a Prop said twice.
def FINALLY_YOU_GRADUATE                                                  -- BUILT. A def, not an instance. The compiler does not find REAL for you; you graduate by hand,
    (Box: Type i)                                                         -- and Episode08:1468 applies this def by name. Every other rung in this chain the compiler hunted.
    (Pigeon: CarrierProcess Box)                                          -- REAL (Episode04:854): a number real in the sense that you have seen it. That is all it knows.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- INTERPRETED. A §6 says what you saw: p_n = B_n f, f sampled at k/n with binomial weights,
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            -- p_n(x) = sum_k f(k/n) (n choose k) x^k (1-x)^(n-k) (A.14). Seen at n points; that is REAL.
    [yet: WITNESSED Box Pigeon]                                           --
    : REAL Box Pigeon where                                               --
  by_His_noodly_appendage :=                                              -- BUILT. The appendage is a frame_of_reference and a Truth. The frame is `yet.we_saw`, the
  { frame_of_reference := yet.we_saw                                      -- anecdotes WITNESSED collected (Episode04:766); the Truth is `.logically` of the fact.
    in_reality := .logically nowtrino.fact.truth                          -- Nothing is added. A deity made of two fields you already had; that is why it compiles.
  }                                                                       --
  nagging_doubt := .but yet.the_experiment nowtrino.fact.truth            -- BUILT. The doubt is a `.but`: the experiment, the fact, then `.logically` the fact again.
                                     (.logically nowtrino.fact.truth)     -- INTERPRETED. The doubt has a radius: |p_n - f| <= L sqrt(x(1-x)/n) <= L/(2 sqrt n) = r_n (A.15):
                                                                          -- Lipschitz plus Cauchy-Schwarz. The compiler holds the `.but`; the L is mine, and a certified radius
instance AND_NOW_YOU_HAVE_A_DIFFERENTIAL_EQUATION_THAT_SAYS               -- for a particular implementation is more than existence of approximants (A p.7). Now an instance:
    (Box: Type i)                                                         -- the compiler is back on the hunt, one gate per rung. Seven class binders; it types the shape
    (Pigeon: CarrierProcess Box)                                          -- and fills the brackets at the seam. LOCAL (Episode04:1051) is a continuum and a ball.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            --
    [yet: WITNESSED Box Pigeon]                                           --
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- The REAL binder is named for the owner of the appendage. Named, not found; see the def above.
    : LOCAL Box Pigeon where                                              --
  the_continuum :=                                                        -- BUILT. The continuum is an æther and a Du. The æther is REAL's appendage handed on
  { the_æther := flying_spaghetti_monster.by_His_noodly_appendage         -- unchanged; Du is `.the_newton`, one Gospel and one Prop, the smallest triangle (Episode04:886).
    Du := .the_newton yet.the_experiment nowtrino.fact.truth              -- INTERPRETED. What the differential equation says is a ball: B_n = {g : ||g - p_n||_inf <= r_n},
  }                                                                       -- E_n = B_1 ∩ ... ∩ B_n, f ∈ E_n, diam E_n <= 2 r_n -> 0 (A.16). The intersection is exactly {f}.
  the_ball := nowtrino.fact.truth                                         -- BUILT. `the_ball` is a Prop, the fact's truth. Radius 1, a spherical cow (Episode04:1067). No norm.
                                                                          -- INTERPRETED. The balls need not nest; the running intersections do (A p.7). And the sup norm sees
instance PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE             -- values, not derivatives, not the bending action (A p.7). That is the problem in the name: the
    (Box: Type i)                                                         -- norm is part of the claim, and a ball in the wrong norm is not relative to the action you compare.
    (Pigeon: CarrierProcess Box)                                          -- INTERPRETED. A §7: 'iteration defeats a weak comparison' has two precise forms, and their
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- quantifiers differ (A p.8): agreement to a fixed resolution, and exact agreement through a
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            -- restricted observation. This instance carries one of each, at Du and at the direction match.
    [yet: WITNESSED Box Pigeon]                                           -- An assertion about 'any weak comparison' must name its observation class (A p.8). Named below.
    [flying_spaghetti_monster: REAL Box Pigeon]                           --
    (nowtrino_model: LOCAL Box Pigeon)                                    -- BUILT. Parentheses, not brackets: the first explicit binder in the forward chain. Search found
    : UNIVERSAL Box Pigeon nowtrino_model where                           -- the seven classes above; this one is handed in, and UNIVERSAL is indexed by which LOCAL you hand it.
  the_train_of_thought :=                                                 -- BUILT. A CalculusProcess: a schedule, a direction, a match, and a Type.
  { the_local_schedule :=                                                 --
    { the_æther := flying_spaghetti_monster.by_His_noodly_appendage       -- The same appendage, third time handed on. Still nothing new.
      Du := .the_gateaux yet.the_experiment Fact.Truth.truth              -- Du is now `.the_gateaux`: a Gospel, two Props, and LOCAL's Newton inside it; one direction
                  nowtrino.fact.truth                                     -- at a time (Episode04:894). INTERPRETED. |l(q_n) - l(r_n)| <= ||l|| (eps_n + eta_n) -> 0 (A.17):
                  (.the_newton yet.the_experiment nowtrino.fact.truth)    -- two approximants of q* agree under every bounded observation, to any tolerance, for n large.
    }                                                                     -- Not exact after finitely many steps; a finer observation can still see the difference (A p.8).
    the_direction_to_the_destination := .einstein nowtrino.fact           -- BUILT. The direction is `.einstein` of the fact: one Fact, no path yet (Episode04:1121).
    uptown_or_downtown := match nowtrino.fact.decTruth with               -- BUILT. Two of Episode01:185-189's four arms: isTrue returns Fact.Truth, isFalse returns the fact.
        | isTrue  _ => Fact.Truth                                         -- INTERPRETED. The match is the direction convention: reversal is W -> W*, C fixed, S flipped (A.6).
        | isFalse _ => nowtrino.fact                                      -- MEASURED. Which way is uptown is what YarnTheory admits it just coded that way (Episode05:70). Flip
    the_train_in := Type i                                                -- it and no number moves: no reading consults <= on the way to a card (Episode08:953-955). Type i.
  }                                                                       -- INTERPRETED. u - v ∈ K = ker C_w => psi(C_w u) = psi(C_w v) (A.18): two states the curl cannot
  once_around  := .blackhole nowtrino.fact.truth (ULift.{i+1} Box)        -- tell apart ride the same train. BUILT. once_around is `.blackhole`: a Prop, ULift.{i+1} Box,
                                            (.einstein nowtrino.fact)     -- and the einstein direction. One turn, one universe up: the w of (A.1), lifted. Episode 11 lifts on.
  twice_around := .whitehole nowtrino.fact Box (.einstein nowtrino.fact)  -- twice_around is `.whitehole`: the Fact, Box unlifted, same direction. The 2π of (A.13): circulation
                                                                          -- a local curl cannot see. Density certifies no minimizer and makes nothing unique (A p.8).
instance OBVIOUSLY_THE_NOWTRINO_IS_SPIN_2                                 -- BUILT. LOGICAL. The name promises spin 2. Watch what the fields deliver, then what I claim.
    (Box: Type i)                                                         -- Two explicit binders, naotrino_model and yarn_theory: the LOCAL and UNIVERSAL the chain already
    (Pigeon: CarrierProcess Box)                                          -- built, passed on by name. The four in brackets are still found by search.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- MEASURED. Episode 4 names the hierarchy: Variation.the_newton, .the_gateaux, .the_frechet
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- (Episode04.lean:885-895; the companion's snapshot read them at 883 and 959, A p.15). Each
    (naotrino_model: LOCAL Box Pigeon)                                    -- takes a Gospel and Props. None takes a norm. The spaces and estimates are not supplied (A p.9).
    (yarn_theory: UNIVERSAL Box Pigeon naotrino_model)                    -- The class is Episode05.lean:356; its one record field, feelings, is a HeartbeatProcess (Ep05:257).
    : LOGICAL Box Pigeon naotrino_model yarn_theory where                 -- BUILT. Feelings is what the compiler calls the differentiable action S. Three fields.
  feelings :=                                                             -- Each is a thing the chain already made, or a constructor applied to the fact. Watch:
  { bullshit_meter := yarn_theory.the_train_of_thought                    -- bullshit_meter is UNIVERSAL's own CalculusProcess (Ep05:271), handed back. Reused, not built.
    after_some_time := .whitehole nowtrino.fact Box                       -- after_some_time is a SpaceTimePath: a whitehole round an einstein (Ep04:1121-1122), two
                                             (.einstein nowtrino.fact)    -- constructors and a fact. That is the state q. No metric was consulted to draw it.
    according_to_newton := .stokes nowtrino.fact                          -- according_to_newton is YarnTheory.stokes (Ep05:73): one pole, that path, one Prop.
                         (.einstein nowtrino.fact) nowtrino.fact.truth    -- INTERPRETED. What I say the fields mean: DF(q)h = lim_{e->0} [F(q+eh) - F(q)]/e and
  }                                                                       -- ||F(q+h) - F(q) - DF(q)h|| = o(||h||). (A.19) Directional first, uniform remainder second.
  microsoft_basic := Calibration.EKG.executed                             -- BUILT. microsoft_basic is EKG.executed (LeanCalibration.lean:101): a load, and before -> after.
                                                                          -- INTERPRETED. A(q) = Lq + b gives DA(q)h = Lh (A.20). Constant. Spin 2 buys that, not a model.
instance DONT_WORRY_ABOUT_THE_NAOTRINO_BEING_SPIN_2_YET___FUTURE_WORK     -- BUILT. HALTED. The name says future work; the class itself (Ep05:533) says a good place to stop.
    (Box: Type i)                                                         -- Same two explicit binders, and LOGICAL in brackets: the search finds the instance above, by type.
    (Pigeon: CarrierProcess Box)                                          -- MEASURED. Ep05:495-498 declares stamina, trilinos, numerical_analysis. The teraFLOPs loop at
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- Ep05:518 asks trilinos.outgrown? op_code and emits a .load when it is. So the halting test in the
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- code is an EKG against a busy-beaver budget (LeanCalibration.lean:147), not a residual norm.
    (naotrino: LOCAL Box Pigeon)                                          -- BUILT. The record is a scientific paper. Two of three fields are the ones above, handed on:
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          -- stamina is the same feelings, fuel for the iteration; trilinos is the same EKG.executed,
    [nonsensical: LOGICAL Box Pigeon naotrino yarn_theory]                -- renamed for the joke (Ep05:497, sorry Professor Gropp). nonsensical is what the binder calls
    : HALTED Box Pigeon naotrino yarn_theory where                        -- the LOGICAL it found; the column does not dispute it. numerical_analysis is a fresh
  scientific_paper :=                                                     -- ComputerProgram.load (ComputerProgram.lean:8): a Prop and a Box, the Prop being Fact.Truth.truth.
    let feelings : HeartbeatProcess Box Pigeon naotrino yarn_theory :=    -- One load. That is the whole halting certificate. Now what I say it stands for.
                                                    nonsensical.feelings  -- INTERPRETED. DF(q_k) dq_k = -F(q_k), q_{k+1} = q_k + dq_k, DF(q_k)v ~ [F(q_k+ev) - F(q_k)]/e. (A.21)
    { stamina := feelings                                                 -- Jacobian-free Newton-Krylov: the last line inside a Krylov solve, PETSc's documented route (A p.9).
      trilinos : Calibration.EKG := nonsensical.microsoft_basic           -- The KNOWER, from the back: quadratic convergence needs an invertible derivative at the root, a
      numerical_analysis := (.load Fact.Truth.truth Box)                  -- locally Lipschitz derivative, and a close start. Lipschitz F alone supplies none of them (A p.9).
    }                                                                     -- An unresolved nullspace leaves no ordinary inverse; inexact solves and differences add tolerances.
                                                                          --
instance THE_NAOTRINO_IS_MEASURED                                         -- BUILT. MEASURED is the class (Ep05:653). The same two binders a third time; HALTED in brackets.
    (Box: Type i)                                                         -- MEASURED. Ep05:627 asks, beside the fields: did we actually perform a calculation on a Number?
    (Pigeon: CarrierProcess Box)                                          -- Really hard to tell, it says. Here is the answer this instance gives. Watch the four fields.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- INTERPRETED, ahead of the fields. The y in saved_as_y is Episode 4's y = u'/u (A.8), generally
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- a rational function (A p.5), saved here as a Type for the defs below 598 to read back up.
    (naotrino: LOCAL Box Pigeon)                                          -- The heartbeats: Lean's counter, measuring implementation work, not an electron clock (A p.12).
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          -- That is Episode 12's beat, not mine; one line and no more. Now the fields.
    [documents_on_file: HALTED Box Pigeon naotrino yarn_theory]           -- documents_on_file is the HALTED the search found: the scientific paper, still that one load.
    : MEASURED Box Pigeon naotrino yarn_theory where                      -- BUILT. The record is a_distance: description, Number, Measurement, Type i (Ep05:627-629).
  a_distance :=                                                           -- One is handed on; the other three are a zero, a lookup of that zero, and a Box.
  { description := documents_on_file.scientific_paper                     -- description is the scientific paper on file. Handed on; nothing added, nothing read.
    the_measurement_of := .zero nowtrino.fact                             -- the_measurement_of is Number.zero on the fact (Ep01:140). We did the calculation. It is zero.
    in_heartbeats := .origin nowtrino.fact (.zero nowtrino.fact) Box      -- in_heartbeats is Measurement.origin (Ep05:562): the fact, that zero, and the Box. A lookup map.
    saved_as_y := Box                                                     -- saved_as_y is Box itself: the value written directly into the type system (Ep05:629).
  }                                                                       -- INTERPRETED. Zero is the honest reading: a stationary state has F(q*) = 0 in the dual test space,
                                                                          -- the thing Newton was solving for (A.21). A minimum needs positivity or convexity besides (A p.9).
instance WE_ARE_CONSTANTLY_INUNDATED_BY_NAOTRINOES                        -- BUILT. COMPILED. The name promises a flood of naotrinoes. The class asks for thirty-two
    (Box: Type i)                                                         -- instance binders (Episode05:777-793); the header names five; search found the rest. What
    (Pigeon: CarrierProcess Box)                                          -- it found is a record with two slots: a distance and a preprint. The distance is the one
    [DISTINGUISHABLE Box Pigeon][COMPARABLE Box Pigeon][SOURCE Box Pigeon]-- MEASURED already carried,
    [REAL Box Pigeon]                                                     -- weakly_interacting_particle.a_distance, handed up one rung unchanged. Nothing was
    (naotrino: LOCAL Box Pigeon)                                          -- re-measured on the way to this line. The two explicit binders are the LOCAL and
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          -- UNIVERSAL the chain built below. Search will not invent a value for an explicit
    [weakly_interacting_particle:                                         -- argument (Episode13:610-615), so I hand those two over by name; the compiler hunts the rest.
                             MEASURED Box Pigeon naotrino yarn_theory]    -- MEASURED. The preprint slot is of_jibberish, and what I put in it is .introduction:
    : COMPILED Box Pigeon naotrino yarn_theory where                      -- one Fact and one Type, the cheapest preprint there is (Episode05:683).
  a_truth_about_the_world :=                                              -- INTERPRETED. This rung is H3, reliable error control (A p.10). A reconstructed a_n is
  { too_good_to_be_true := weakly_interacting_particle.a_distance         -- trusted only with a stability bound standing in front of it:
    of_jibberish := (.introduction Fact.Truth Box)                            --
  }                                                                       --   ||q - q*|| <= C ||F(q)||,     ||F(a_n)|| <= tau_n + kappa_n -> 0.          (A.22)
  a_demonstration_of_a_constant := .methodology Fact.Truth Fact.Truth     -- a_demonstration_of_a_constant is .methodology: the introduction wrapped once more, Box
              Box (ULift.{i+1, i} Box) (.introduction Fact.Truth Box)     -- lifted to ULift Box. A lift, not a bound. tau_n bounds the solver residual, kappa_n the
                                                                          -- consistency error. KNOWER: a small residual alone is no error estimate without stability (A p.10).
instance HONEST_TO_GOD_IT_SHOWS_UP_EVERY_TIME                             -- BUILT. A_TRUTH_ABOUT. Honest to God, it shows up every time: the compiler found this
    (Box: Type i)                                                         -- one too, the whole COMPILED rung riding in as holy_shit. What shows up is a record
    (Pigeon: CarrierProcess Box)                                          -- named you_the_reader. YOU. Read what you are made of.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- nowtrino gets a name because raw_output needs its fact. It is a class binder, an
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- abstract Fact; I do not get to say which one, and I will not pretend to below.
    (naotrino: LOCAL Box Pigeon)                                          -- The explicit binders are, as always, the LOCAL and UNIVERSAL from below.
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          -- INTERPRETED. Here are the four things the Argument asks you to grant (A p.10).
    [holy_shit: COMPILED Box Pigeon naotrino yarn_theory]                 -- H1: one state space, one set of boundary data, transported consistently.
    : A_TRUTH_ABOUT Box Pigeon naotrino yarn_theory where                 -- H2: one admissible problem, one solution q* in the stated class.
  you_the_reader :=                                                       -- H3: the error control you just read, (A.22).
  { in_a_giant_book := holy_shit.a_truth_about_the_world                  -- H4: observations that commute with the representation maps and are continuous.
    a_constant := .zero Fact.Truth                                        -- in_a_giant_book is COMPILED's record handed up unchanged: that is H1's transport. A
    current_page_number := .zero Fact.Truth                               -- conservation law survives the transport only when flux, test space, and boundary
    total_pages := .zero Fact.Truth                                       -- pairing ride the same maps; it comes from the residual and the discretization, not
    of_the_proof := .methodology Fact.Truth Fact.Truth Box                -- from the name of the solver (A p.10). Not from the name of the instance either.
                  (ULift.{i+1, i} Box) (.introduction Fact.Truth Box)     -- BUILT. a_constant := .zero. current_page_number := .zero. total_pages := .zero.
  }                                                                       -- Every number in YOU the READER is the origin of the Bullshit ladder (Episode05:807).
  TRUE := .zero Fact.Truth                                                -- The KNOWER, on H2: if a minimizer is claimed, its minimizing property is
  raw_output := .one                                                      -- established separately (A p.10). Nothing on this page claims one.
              Fact.Truth                                                  -- TRUE := .zero Fact.Truth. The class default was .zero nowtrino.fact (Episode05:999);
              (.one Fact.Truth (.zero nowtrino.fact))                     -- I pinned the fact. raw_output is the .one rung, the hypothesis: a Fact, a Number,
              (.introduction nowtrino.fact Box)                           -- two preprints, and a Bullshit under it (Episode05:808). The Bullshit under it all is
              (.methodology Fact.Truth nowtrino.fact Box                  -- .zero nowtrino.fact: one hypothesis stacked on the origin. Lean checked the stacking.
                    (ULift.{i+1, i} Box) (.introduction Fact.Truth Box))  -- BUILT. Now a_constant. Do not skip the long line: it is the => direction in one
              (.zero nowtrino.fact)                                       -- expression, from COMPILED's distance down through every process the ladder named to
  a_constant := .one                                                      -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
              Fact.Truth --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
              holy_shit.a_truth_about_the_world.too_good_to_be_true.description.stamina.bullshit_meter.the_local_schedule.the_æther.frame_of_reference.we_experience.shows_me_higher_order_terms.teaching.axioms.to_pwn_n00bz.dunking_contest.ANSYS_process.GOSUB.adding_process.mideastern_process.compiled_process.digital_process.meesa_process.gauge_process.sensing_process.static_fraction.physical_process.noisy_process.turing_process.computational_process.repeatable_process.observation_process.cauchy_process.limit_process.indexing_process.count.carrier.value -- |
                                     (.introduction nowtrino.fact Box) --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
              (.methodology Fact.Truth nowtrino.fact Box                  -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
                  (ULift.{i+1, i} Box) (.introduction Fact.Truth Box))    -- count.carrier.value: the count, retained through every change of representation (A p.1).
              (.zero nowtrino.fact)                                       -- BUILT. by trivial: the compiler's one sentence in this block. Bullshit.le says .zero _ <=
  the_constant_is_at_least_true := by trivial                             -- anything is True (Episode05:825), so TRUE <= a_constant costs nothing. What H1-H4 buy is
                                                                          -- sup_{||l||<=1} |l(a_n) - l(b_n)| <= eps_n + eta_n -> 0 (A.23). At least true is the gap.
noncomputable instance OF_COURSE_IT_DOES___I_JUST_PUT_IT_THERE            -- BUILT. INFERRED, noncomputable because Fact.SAME is (Episode05:1187). Class arguments
    (Box: Type i)                                                         -- found by search; the explicit two are the LOCAL and UNIVERSAL from below; guano you just read.
    (Pigeon: CarrierProcess Box)                                          -- INTERPRETED. Of course it does. I just put it there. What this rung infers, in the
    [DISTINGUISHABLE Box Pigeon]                                          -- mathematics, is the nullspace claim: ker C_w is inside ker O, equivalently O = T C_w (A.24).
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- Many operators share a kernel, and boundedness of T needs its own estimate (A p.11).
    (naotrino: LOCAL Box Pigeon)                                          -- That the common limit is QED, GR, or Navier-Stokes has not been supplied in a form
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          -- that verifies it; it remains the thesis being formulated, not a conclusion proved
    [guano: A_TRUTH_ABOUT Box Pigeon naotrino yarn_theory]                -- by (A.23) (A p.11). The instance name is the confession. Now watch the fields agree.
    : INFERRED Box Pigeon naotrino yarn_theory where                      -- MEASURED. Closure has three constructors: same, different, inferred (Episode05:1113-1116).
  same_difference :=                                                      -- BUILT. you_the_knower := guano.you_the_reader: the KNOWER and the READER are one record.
  { you_the_knower      := guano.you_the_reader                           -- your_conclusion is .different with Fact.SAME in the fact slot. SAME.truth is Quot.mk
    your_conclusion     := .different (Fact.SAME (guano:=guano))          -- TruthOrder TRUE = Quot.mk TruthOrder a_constant; decTruth is isTrue of selection_sound on
                  (guano.TRUE) (guano.a_constant) (some Fact.Truth.truth) -- the_constant_is_at_least_true (Episode05:1212-1213): by trivial is the witness Quot.sound eats.
  }                                                                       -- BUILT. .same. T=T: what I said and what search found agree, and the closure says so.
  α := .same Fact.Truth guano.a_constant                                  -- Episode12:35: converged, exact in logic. Episode 9 ends in .inferred; Episode13:610-615 says why.
                                                                          -- A.11-A.13 and E.6 are not in this file; they sit beside Episodes 8, 11, 12, 13. Now read back up.
def You_the_Reader                                                        -- BUILT. The page turns here. You read down the instances; now you read up the defs. From this
    {Box: Type i}                                                         -- line down the ladder is written as defs, not instances. The compiler does not find
    {Pigeon: CarrierProcess Box}                                          -- You_the_Reader. You call it by name and hand it the thirty-seven binders yourself. That is the
    [nowtrino: DISTINGUISHABLE Box Pigeon][ADMISSIBLE Box Pigeon]         -- <= direction: the instances above carried the Argument, the defs below carry the Equivalences,
    [COUNTABLE Box Pigeon][ENCODED Box Pigeon][RESIDUE Box Pigeon]        -- and the page read down and then up is the iff. Count the square brackets: thirty-three. Each
    [BINARY Box Pigeon][REPEATABLE Box Pigeon][NUMERIC Box Pigeon]        -- caller below still fills them by search, but only from the local ones it was handed. The two
    [REPRESENTABLE Box Pigeon][PHYSICAL Box Pigeon]                       -- curly ones, {fact} and {about_the_world}, are filled by name at line 634. Nobody hunts for
    [COMPARABLE Box Pigeon][OBSERVED Box Pigeon][PRESENT Box Pigeon]      -- anything down here. I pass it all across the table, and you watch my hands.
    [MEASURABLE Box Pigeon][GUNGAN Box Pigeon][SOURCE Box Pigeon]         --
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon]         -- INTERPRETED. Reading up, u is the actual path, s is its projection in a Sobolev inner product,
    [SCALED Box Pigeon][LOAD Box Pigeon][OF Box Pigeon]                   -- and the identity the whole second companion sits on is
    [BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon][ACOLYTE Box Pigeon]      --     <s, u>_H = |s|_H^2,      |u - s|_H^2 = |u|_H^2 - |s|_H^2.                            (E.1)
    [SCIENTIFIC Box Pigeon][TRUTH Box Pigeon][WITNESSED Box Pigeon]       -- The spline keeps the measured component. The residual is perpendicular to it. The squared
    [REAL Box Pigeon]                                                     -- norms add. That is the right triangle on E p.1, s along the floor, u on the hypotenuse, and
    {fact: LOCAL Box Pigeon}                                              -- the reason is variational orthogonality: the leftover error does no work against the retained
    {about_the_world: UNIVERSAL Box Pigeon fact}                          -- trial space (E p.1). The KNOWER, from the back: which inner product? Fair. The inner product
    [LOGICAL Box Pigeon fact about_the_world]                             -- and the realization maps are stated constructions of the companion (E p.10). No episode writes
    [HALTED Box Pigeon fact about_the_world]                              -- one. And the companions read the code; they did not run it (E p.1). Hold both while you read.
    [MEASURED Box Pigeon fact about_the_world]                            --
    [stdout: COMPILED Box Pigeon fact about_the_world]                    -- BUILT. The fields, and watch the name over-promise. in_a_giant_book is stdout's
    : AtreyuProcess Box Pigeon fact about_the_world where                 -- CompilerOutput, the same one COMPILED sent up the chain (Episode05:880).
  in_a_giant_book := stdout.a_truth_about_the_world                       -- a_constant is .zero nowtrino.fact: the origin of the Bullshit ladder (Episode05:807). The
  a_constant := .zero nowtrino.fact                                       -- constant a reader holds is zero. Not a letdown; the floor. Every rung orders above it
  current_page_number := Pigeon.value                                     -- (Episode05:825). current_page_number is Pigeon.value: the carrier's own number, no count.
  of_the_proof := stdout.a_demonstration_of_a_constant                    -- of_the_proof is stdout's demonstration. You hold the book, the page, and a proof of zero.
                                                                          --
def BUT_THE_TRUTH_IS_YOU_THE_READER_UNDERSTANDS_THE_ARGUMENT_NAO          -- BUILT. A_TRUTH_ABOUT, by hand. The name says you understand the argument NAO. The fields
    (Box: Type i)                                                         -- say what that costs. you_the_reader is You_the_Reader with fact and about_the_world passed
    (Pigeon: CarrierProcess Box)                                          -- by name (634-635). a_constant is THEORY.raw_output of that reader on the origin: one gawk_at
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- on .zero, the .one rung (Episode05:891, 1054-1064). And the certificate is `by trivial`.
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- It closes because TRUE is .zero nowtrino.fact (Episode05:999) and Bullshit.le reads
    (naotrino: LOCAL Box Pigeon)                                          -- `.zero _, _ => True` for any second argument (Episode05:825). At least true means: at or
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          -- above the origin. Down the page Fact.SAME.truth is Quot.mk TruthOrder TRUE = Quot.mk
    [COMPILED Box Pigeon naotrino yarn_theory]                            -- TruthOrder a_constant, and its decTruth is selection_sound of this field (Episode05:1212-1213).
    (_: CarrierProcess Box)                                               -- MEASURED. What that order is not: TruthOrder and Closure.le are logical relations on the
  : A_TRUTH_ABOUT Box Pigeon naotrino yarn_theory where                   -- ladder and its closure (Episode05:979-1036, 1099, 1182), not a scalar Sobolev norm. The
    you_the_reader := You_the_Reader (fact:=naotrino)                     -- companion's own table says so (E p.10). Every norm on this side is me talking, not Lean.
                                       (about_the_world:=yarn_theory)     -- INTERPRETED. Theorem 1, for H a real Hilbert space, V a closed subspace, u in H, s in V:
    a_constant     := THEORY.raw_output (You_the_Reader                   --   s = P_V u  <=>  <u - s, v>_H = 0 for all v in V  <=>  s uniquely minimizes |u - v|_H.  (E.2)
                (fact:=naotrino) (about_the_world:=yarn_theory))          -- The KNOWER heckles: so (E.1) is the criterion? No. (E.1) is a consequence, the test at v = s
                (.zero nowtrino.fact)                                     -- only. In R^2 take u = (1,1), s = (1,0): (E.1) holds and the projection onto R^2 is u, not s
    the_constant_is_at_least_true    := by trivial                        -- (E p.2). All trial directions are required for the converse. `by trivial` checked an order.
                                                                          --
def SO_YOU_START_TO_BUILD_ANOTHER_DEMONSTRATION_PROCESS                   -- BUILT. COMPILED, by hand, and the name promises ANOTHER demonstration process. Look at what
    (Box: Type i)                                                         -- gets built. a_truth_about_the_world is a CompilerOutput whose too_good_to_be_true is
    (Pigeon: CarrierProcess Box)                                          -- multimeter.a_distance, the LeanProcess the MEASURED rung already carried (Episode05:743),
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- and whose of_jibberish is a .methodology preprint wrapped around holy_shit's demonstration,
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- one universe up, ULift.{i+1,i} Box (the same wrap emit? does at Episode05:755). Then
    (naotrino: LOCAL Box Pigeon)                                          -- a_demonstration_of_a_constant is the same .methodology, the same wrap, the same holy_shit.
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          -- Another demonstration is this demonstration, lifted. That is what the left column certifies,
    [multimeter: MEASURED Box Pigeon naotrino yarn_theory]                -- and it is the honest part.
    [holy_shit: COMPILED Box Pigeon naotrino yarn_theory]                 --
    (_: CarrierProcess Box)                                               -- INTERPRETED. The proof of Theorem 1 runs through one expansion, for v in V:
    : COMPILED Box Pigeon naotrino yarn_theory where                      --     |u - v|_H^2 = |u - s|_H^2 + |s - v|_H^2.                                          (E.3)
  a_truth_about_the_world :=                                              -- The final term is nonnegative and vanishes only at v = s (E p.2). Step off the spline and you
  { too_good_to_be_true := multimeter.a_distance                          -- pay in the second term, never the first; step back and the bill is zero. That is why
    of_jibberish := .methodology nowtrino.fact Fact.Truth Box                 --
         (ULift.{i+1,i} Box) holy_shit.a_demonstration_of_a_constant      -- minimizing over V and being orthogonal to V are the same sentence. The lift on the left has
  }                                                                       -- the same shape: another demonstration adds a universe and no new constant; the constant is
  a_demonstration_of_a_constant := .methodology nowtrino.fact             -- still .zero, back at You_the_Reader. Existence, the companion says, needs V closed and H
            Fact.Truth Box (ULift.{i+1,i} Box)                            -- complete (E p.2). The code has neither notion. The theorem is mine, the ULift is Lean's, and
                  holy_shit.a_demonstration_of_a_constant                 -- the sentence joining them is graded INTERPRETED, which means you may refuse it.
                                                                          --
def IN_ORDER_TO_MEASURE_THE_CONSTANT_EMPIRICALLY                          -- BUILT. MEASURED, by hand, the last def in this stretch, and the name says EMPIRICALLY.
    (Box: Type i)                                                         -- a_distance is a LeanProcess with four fields (Episode05:607, 625-629). description is
    (Pigeon: CarrierProcess Box)                                          -- documents_on_file.scientific_paper, the HALTED rung's paper. the_measurement_of is lifted
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- straight out of multimeter.a_distance: the Number is the one MEASURED already had. Nothing
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- empirical happens on that line. A Number is copied. in_heartbeats is where the name is paid:
    (naotrino: LOCAL Box Pigeon)                                          -- Measurement.distance_to takes a Fact, two Numbers, a Type i, a Type (i+1), and a prior
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          -- Measurement (Episode05:563), a linked list of universes. The Numbers are .zero Fact.Truth and
    [nonsensical: LOGICAL Box Pigeon naotrino yarn_theory]                -- the_measurement_of; the prior link is metaphor's own in_heartbeats, the COMPILED rung's
    [documents_on_file: HALTED Box Pigeon naotrino yarn_theory]           -- reading. saved_as_y is Box: the value written into the type itself (Episode05:629), the y
    [multimeter: MEASURED Box Pigeon naotrino yarn_theory]                -- carried down from the instances. Measurement.le compares two distance_to links by
    (_: CarrierProcess Box)                                               -- (here = there) and before <= after (Episode05:582): an order on Numbers, not a distance.
    [metaphor: COMPILED Box Pigeon naotrino yarn_theory]                  -- INTERPRETED. The ball. Let L : H -> R^m be bounded linear observations, prescribe Ls = Lu
    : MEASURED Box Pigeon naotrino yarn_theory where                      -- and minimize |s|_H^2 / 2. The tangent space is ker L, so s = P_V u with V = (ker L)^perp
  a_distance :=                                                           -- (E p.2, after Bindel [1]). Every path with u's observations and energy at most C is then
  {   description := documents_on_file.scientific_paper                   --     {g : Lg = Lu, |g|_H <= C} = {s + h : h in ker L, |h|_H^2 <= C^2 - |s|_H^2}.      (E.4)
      the_measurement_of := multimeter.a_distance.the_measurement_of      -- An exact ball in the unobserved subspace, centered at the spline (E p.2). If in_heartbeats
      in_heartbeats := .distance_to nowtrino.fact (.zero Fact.Truth)      -- is anything, it is that radius: how far the spline sits from the edge of what L cannot see.
            (multimeter.a_distance.the_measurement_of) Box                ------------+
            (ULift.{i+1,i} Box) --                                                    |
             metaphor.a_truth_about_the_world.too_good_to_be_true.in_heartbeats --    |
      saved_as_y := Box --                                                            |
  }                                                                       ------------+
                                                                          -- Hedge: h perp s alone admits wrong observations; the radius is the error only at C = |u|_H (E p.2).
def YOU_NEED_TO_DEVELOP_A_BOUNDED_PROCESS                                 -- BUILT. A def, not an instance. You are reading the bottom half of the page, so read it UP:
    (Box: Type i)                                                         -- the defs are applied by hand, and every binder here is me handing the compiler, one at a time,
    (Pigeon: CarrierProcess Box)                                          -- what the top half found for free. The name says develop a bounded process. The field says:
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- copy four numbers out of two papers. Bounded means a norm, and the norm I mean is this one:
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --   <f,g>_H = f(a).g(a) + f'(a).g'(a) + Int_a^b f''(x).g''(x) dx                          (E.5)
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [nonsensical: LOGICAL Box Pigeon naotrino yarn_theory]                -- INTERPRETED. Two boundary anchors and a bending term. Why the anchors? Because the bending
    [documents_on_file: HALTED Box Pigeon naotrino yarn_theory]           -- term alone has every affine function in its kernel (E p.3): a straight line bends nowhere and
    (_: CarrierProcess Box)                                               -- costs nothing. Pin f(a) and f'(a) and the leak is plugged: square zero forces f'' = 0 and both
    [data: MEASURED Box Pigeon naotrino yarn_theory]                      -- anchors vanish, so f = 0. A genuine norm, equivalent to the usual H^2 norm (E p.3): integrate f''
    : HALTED Box Pigeon naotrino yarn_theory where                        -- twice for one direction, the trace bounds for the other. HALTED, by hand, is what that buys:
  scientific_paper :=                                                     -- a process whose size you can state. BUILT. scientific_paper is the record; watch the sources.
  { stamina := data.a_distance.description.stamina                        -- stamina and teraFLOPs are copied from data, the MEASURED paper. trilinos and
    trilinos := documents_on_file.scientific_paper.trilinos               -- numerical_analysis are copied from documents_on_file, the HALTED paper already on file. Two
    teraFLOPs := data.a_distance.description.teraFLOPs                    -- from data, two from the file. (E.5) has two anchors and one integral. Count them yourself; I
    numerical_analysis :=                                                 -- only promised bounded. Nothing here is proved; the compiler checks four fields have four types.
                documents_on_file.scientific_paper.numerical_analysis     -- MEASURED. Episode 3 calls Spline a B-spline and hands you no norm (A p.3, Source observation).
  }                                                                       -- So H = H^2([a,b]; R^4) is my choice (E p.3), and the 4 is the R^4 of the coefficients in (A.3).
                                                                          --
def PERHAPS_ONE_THAT_REALLY_MAKES_YOU_THINK                               -- BUILT. LOGICAL, by hand. The name promises one that really makes you think. The field
    (Box: Type i)                                                         -- feelings := ...stamina delivers one number out of the paper on file, and microsoft_basic is
    (Pigeon: CarrierProcess Box)                                          -- passed through from nonsensical untouched. That is the whole construction. What it stands for
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- is the clamped variational problem (E p.3): prescribe q(a), q'(a), q(b), q'(b); A is the affine
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- space that obeys them, X the variations with h = h' = 0 at both ends. Then the energy, its
    (naotrino: LOCAL Box Pigeon)                                          -- derivative, and the four statements that are one statement:
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          --
    [nonsensical: LOGICAL Box Pigeon naotrino yarn_theory]                --   E[q] = 1/2 Int_a^b |q''|^2 dx,   F(q)[h] = Int_a^b q''.h'' dx                          (E.6)
    [documents_on_file: HALTED Box Pigeon naotrino yarn_theory]           --   q minimizes E on A  <=>  F(q) = 0 in X*  <=>  q'''' = 0 distributionally  <=>  q = q*
    (_: CarrierProcess Box)                                               --
    : LOGICAL Box Pigeon naotrino yarn_theory where                       -- INTERPRETED. Four statements, three arrows, one cubic. q* is the unique cubic satisfying the
  feelings := documents_on_file.scientific_paper.stamina                  -- four endpoint conditions, componentwise (E p.3). That is the one that makes you think: the
  microsoft_basic := nonsensical.microsoft_basic                          -- least-action path is a cubic because q'''' = 0, not because Episode 3 said spline first.
                                                                          --
def PERHAPS_ONE_THAT_USES_THE_DEVICE_ITSELF                               -- BUILT. UNIVERSAL, by hand, and the name is literal: the def takes a yarn_theory and returns
    (Box: Type i)                                                         -- a yarn_theory. the_train_of_thought and once_around pass straight through. Only twice_around
    (Pigeon: CarrierProcess Box)                                          -- is new, and look at what it is: the train of thought's photon_torpedo fired at once_around.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- Going around twice is going around once, then applying the device to that. It uses itself.
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- INTERPRETED. That is integration by parts, and it is done exactly twice (E p.3). Once moves a
    (naotrino: LOCAL Box Pigeon)                                          -- prime off h; twice moves both, and the boundary terms die because h = h' = 0 at both ends.
    (yarn_theory: UNIVERSAL Box Pigeon naotrino)                          -- What is left is Int q''''.h, and q'''' = 0 makes every admissible first variation zero (E p.3).
    (_: CarrierProcess Box)                                               -- That is the middle arrow of (E.6), from F(q) = 0 to the cubic, and it is the only step in this
    : UNIVERSAL Box Pigeon naotrino where                                 -- block a human has to do twice. The compiler does it zero times; it copies a field.
  the_train_of_thought := yarn_theory.the_train_of_thought                -- The KNOWER asks what a photon torpedo has to do with parts. Nothing. It is a name for apply
  once_around := yarn_theory.once_around                                  -- the map again, and the map is whatever the_train_of_thought carries. The parts are mine.
  twice_around := yarn_theory.the_train_of_thought.photon_torpedo         -- Hedge, unsoftened: q'''' = 0 is distributional (E.6). Stationarity gives it against compactly
                                             yarn_theory.once_around      -- supported tests (E p.3). Twice around makes q a cubic on the interior; the ends are the clamps.
                                                                          --
def PERHAPS_ONE_THAT_USES_CALCULUS                                        -- BUILT. LOCAL, by hand. Two fields. the_continuum is the a_train's local schedule: the train
    (Box: Type i)                                                         -- of thought, read at one stop. the_ball is naotrino.the_ball, the ball the top half of the page
    (Pigeon: CarrierProcess Box)                                          -- already built, handed back unchanged. Uses calculus, says the name; copies a ball, says the
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- field. Here is the calculus the name is owed. Expand the energy about the cubic:
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --   E[q] - E[q*] = 1/2 ||q - q*||_H^2        (q in A)                                     (E.7)
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               -- INTERPRETED. The energy gap is the radius of the ball, squared, over two. That is why the ball
    [the_a_train: UNIVERSAL Box Pigeon naotrino]                          -- is a ball and not a blob: the distance from any admissible q to q* is measured in the norm of
    : LOCAL Box Pigeon where                                              -- (E.5), and the excess action IS that distance. Expanding the energy proves uniqueness (E p.3):
  the_continuum := the_a_train.the_train_of_thought.the_local_schedule    -- gap zero forces q = q*. The continuum is the schedule; the ball is the radius the schedule
  the_ball      := naotrino.the_ball                                      -- cannot see. Neither field computes; both are copied. The calculus is mine, and it is not checked.
                                                                          --
def YEAH_CALCULUS___YOU_CAN_DO_THE_CALCULUS_RITE                          -- BUILT. REAL, by hand. by_His_noodly_appendage is the aether of principia's continuum, which is
    (Box: Type i)                                                         -- to say: a field named for a joke, filled from a binder named for a book, and the compiler takes
    (Pigeon: CarrierProcess Box)                                          -- both because Type i does not read English. nagging_doubt := .logically naotrino.the_ball: the
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- doubt is the ball, tagged logically. Yeah, calculus. You can do the calculus, rite. Here:
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --   <q*,u>_H = ||q*||_H^2,     ||u - q*||_H^2 = 2 (E[u] - E[q*])                          (E.8)
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               -- INTERPRETED. Take any actual path u in A. Its anchors are fixed by the data, so minimizing E is
    [principia: LOCAL Box Pigeon]                                         -- minimizing the squared H norm, and Theorem 1 (E.2) applies to the four endpoint observations.
    : REAL Box Pigeon where                                               -- The cubic is the projection of the real path; the gap in action is the residual, squared.
  by_His_noodly_appendage := principia.the_continuum.the_æther            -- The nagging doubt, in my voice, unsoftened (E p.3): u need not be cubic for this identity. If it
  nagging_doubt := .logically naotrino.the_ball                           -- solves the same least-action problem, uniqueness already gives u = q*. And swap (E.5) for an
                                                                          -- equivalent inner product: you keep convergence, but need not keep the exact dot-product identity.
def MATH_MODELING_IS_EASY___JUST_WATCH                                    -- BUILT. Now it is you and me and thirty-eight binders, applied by hand, walking back up.
    (Box: Type i)                                                         -- Two REAL witnesses on the left, `flying_spaghetti_monster` and `invariant`; WITNESSED
    (Pigeon: CarrierProcess Box)                                          -- is two projections of them, `we_saw` and `the_experiment`, both through
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- `frame_of_reference` (769-770, in the box). That is all the modeling there is. Watch.
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon]                            -- INTERPRETED. Watch what: add interior knots, nested, dense in [a,b], keep the four
    [flying_spaghetti_monster: REAL Box Pigeon]                           -- endpoint traces. Then V_n is a subspace of V_{n+1}, s_n = P_{V_n} u, and
    (naotrino: LOCAL Box Pigeon)                                          -- ||u - s_n||^2 = ||u||^2 - ||s_n||^2,   ||s_m - s_n||^2 = ||s_m||^2 - ||s_n||^2.   (E.9)
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- The energy does not go anywhere. It moves out of the residual and into the spline,
    (_: CarrierProcess Box)                                               -- one knot at a time, and the second identity says the splines are Cauchy on the same
    [invariant: REAL Box Pigeon]                                          -- budget. Modeling is easy. Just watching is the whole job. Nobody said u was in view.
    : WITNESSED Box Pigeon where                                          ------------------------------------+
  we_saw := invariant.by_His_noodly_appendage.frame_of_reference --                                           |
  the_experiment := flying_spaghetti_monster.by_His_noodly_appendage.frame_of_reference.in_the_literature --  |
--                                                                                                            |
def WHICH_WE_IMMEDIATELY_SEE_THE_FIRST_TIME_IN_THE_LAB                    ------------------------------------+
    (Box: Type i)                                                         -- BUILT. TRUTH has one field, `becomes`, and it is `we_saw` followed by `we_experience`
    (Pigeon: CarrierProcess Box)                                          -- (782). What you saw becomes what you experience. No lab was consulted; a projection was.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- INTERPRETED. What you see the first time is why the interpolants are cubics at all:
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- between knots the fourth derivative vanishes; integrate by parts at each knot and
    (naotrino: LOCAL Box Pigeon)                                          -- the second derivative is forced continuous; the third derivative is allowed to
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- jump, and the jump is exactly what enforces the point constraint (E p.4).
    (_: CarrierProcess Box)                                               -- Conversely every such spline is perpendicular to every variation that keeps the
    [overwhelming_evidence: WITNESSED Box Pigeon]                         -- data, so these splines ARE V_n, not an approximation to it (E p.4).
    : TRUTH Box Pigeon where                                              -- You do not see this immediately. It is minimum-norm interpolation, Bindel's
  becomes := overwhelming_evidence.we_saw.we_experience                   -- geometry (E p.2, ref [1]). The KNOWER says the evidence is one dot. So is the field.
                                                                          --
def OBVIOUSLY_YOU_START_A_RESEARCH_PROGRAM                                -- BUILT. A research program is two fields. `discovering` is `shows_me_higher_order_terms`
    (Box: Type i)                                                         -- (794) and `invariant` is the same path one projection longer (795). The program
    (Pigeon: CarrierProcess Box)                                          -- is the mission, what the mission shows you, and what holds still while it shows you.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- INTERPRETED. Obviously you start one, because the trial spaces must be dense or
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- the refinement is decoration. Density proof (E p.4): a path orthogonal to every
    (naotrino: LOCAL Box Pigeon)                                          -- V_n lies in every ker L_n, so its values vanish on the dense knot set. H^2 paths
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- are continuous. A continuous path that is zero on a dense set is zero. So the
    (_: CarrierProcess Box)                                               -- union of the V_n is dense, and the invariant of the program is that nothing
    [our_mission: TRUTH Box Pigeon]                                       -- orthogonal to all of it survives.
    : SCIENTIFIC Box Pigeon where                                         -- Read that again. It is three sentences and it is the only place in this block
  discovering := our_mission.becomes.shows_me_higher_order_terms          -- where a limit is actually taken. Everything else is bookkeeping about where the
  invariant := our_mission.becomes.shows_me_higher_order_terms.invariant  -- energy sits. The bookkeeping is (E.9); the science is those three sentences.
                                                                          --
def AND_HUNDREDS_OF_POSTDOCS_COME_TO_COUNT_NAOTRINOS                      -- BUILT. ACOLYTE is one field, `euclid`, and euclid is a postdoc discovering and
    (Box: Type i)                                                         -- teaching (807). Hundreds of them come. The compiler counts one.
    (Pigeon: CarrierProcess Box)                                          -- INTERPRETED. With density, best approximation gives the whole refinement statement:
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- ||u - s_n||_H -> 0   <=>   ||s_n||_H^2 -> ||u||_H^2,  with ||s_n||^2 increasing.  (E.10)
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- The postdocs are the monotone sequence. Each one adds a knot, each knot can only
    (naotrino: LOCAL Box Pigeon)                                          -- raise ||s_n||^2 (by (E.9) it cannot fall), and the ceiling is ||u||^2. You never see
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- u. You see the counter climbing toward a number it is not allowed to pass, and
    (_: CarrierProcess Box)                                               -- the theorem says: the residual is gone if the counter reaches the ceiling, and
    [postdoc: SCIENTIFIC Box Pigeon]                                      -- only then. Counting naotrinos IS the iff. That is what an acolyte is for.
    : ACOLYTE Box Pigeon where                                            -- The KNOWER: "reaches the ceiling" is a limit, not a reading. Correct. (E.10) is an
  euclid := postdoc.discovering.teaching                                  -- equivalence of limits; which n is enough is not in it. Hold that thought for ANSYS.
                                                                          --
def BUT_THEN_REIMANN_COMES_ALONG                                          -- MEASURED. It says REIMANN on the left. It says REIMANN in the file (809), and the
    (Box: Type i)                                                         -- left column is frozen, so it says REIMANN here. The compiler checks names, not spelling.
    (Pigeon: CarrierProcess Box)                                          -- BUILT. PROPAGANDA is `questions`, and the questions are the professor's euclid's
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- `axioms` (819). Riemann comes along and asks the postdoc's teacher what it assumed.
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- INTERPRETED. What it assumed was the norm. Uniform approximation of a path alone
    (naotrino: LOCAL Box Pigeon)                                          -- does not control its derivatives (E p.4), and the action is a second derivative.
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- So do not approximate u. Approximate u'' in L^2 by polynomials p_n (continuous
    (_: CarrierProcess Box)                                               -- functions first, then Weierstrass uniformly), integrate twice, keep the anchors:
    [professor: ACOLYTE Box Pigeon]                                       -- r_n(x) = u(a) + (x - a) u'(a) + int_a^x (x - t) p_n(t) dt,                     (E.11)
    : PROPAGANDA Box Pigeon where                                         -- ||r_n - u||_H = ||p_n - u''||_L2 -> 0. The anchors are the two boundary terms of
  questions := professor.euclid.axioms                                    -- (E.5); keep them and the H-error IS the L^2 error of u'', exactly. Riemann is satisfied.
                                                                          --
def AND_THE_AMOUNT_OF_CALCULUS_YOU_HAVE_TO_DO_EXPLODES                    -- BUILT. BULLSHIT has one field and it is an `arm_wave_process` (831): the geometry's
    (Box: Type i)                                                         -- questions, `to_pwn_n00bz`. That is the whole class. I named it honestly.
    (Pigeon: CarrierProcess Box)                                          -- INTERPRETED. Here is the calculus that explodes, and here is how small it is.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- (E.11) pins the left end, u(a) and u'(a). It says nothing about b. If the problem
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- needs the two right-end traces too, add a cubic correction tending to zero and
    (naotrino: LOCAL Box Pigeon)                                          -- they are enforced (E p.4). A cubic. Four coefficients. That is the explosion.
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- The arm wave is the clause "if required". Which traces are required is set by the
    (_: CarrierProcess Box)                                               -- problem on E p.3, and the clamped one prescribes all four (E.6); the correction
    [geometry: PROPAGANDA Box Pigeon]                                     -- matches the space you are projecting in and adds no information.
    : BULLSHIT Box Pigeon where                                           -- The KNOWER wants the correction written out. It is not written out in E; it is
  arm_wave_process := geometry.questions.to_pwn_n00bz                     -- asserted to exist and to tend to zero (E p.4). That hedge is E's, and I keep it.
                                                                          --
def AND_YOU_STUDY_TRIANGLES                                               -- BUILT. OF is a `galerkin_process`, which is hours of math, arm-waved, then a
    (Box: Type i)                                                         -- `dunking_contest` (843). Galerkin would recognise the contest, if not the name.
    (Pigeon: CarrierProcess Box)                                          -- INTERPRETED. Triangles, because you need not use polynomials for p_n at all.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- Approximate u'' by continuous piecewise-linear functions instead, hats on the knots,
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- and (E.11) integrated twice hands you the piecewise cubic construction (E p.4):
    (naotrino: LOCAL Box Pigeon)                                          -- two integrals of a hat is a C^2 cubic piece, which is where this block started.
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- So the triangles are not a different method. They are the same projection with
    (_: CarrierProcess Box)                                               -- the trial space chosen so the basis is the B-spline Episode 3 names and does not
    [hours_of_math: BULLSHIT Box Pigeon]                                  -- give you a knot vector for (A p.3). This supplies approximation in the norm the
    : OF Box Pigeon where                                                 -- action uses (E p.4), not the sup norm of A sec.6, which controls values and not
  galerkin_process := hours_of_math.arm_wave_process.dunking_contest      -- bending (A p.7). Study the triangles. They are the ones that bend right.
                                                                          --
def BUT_YOU_AND_I_KNOW_ANSYS_HAS_GOT_THIS                                 -- BUILT. LOAD is one `basic_operation`, and the operation is the area's galerkin
    (Box: Type i)                                                         -- process handed to an `ANSYS_process` (855). You and I know it has got this because
    (Pigeon: CarrierProcess Box)                                          -- the field says so and the compiler accepted the projection. That is what "has got
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- this" certifies: the name resolves.
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- INTERPRETED. What ANSYS has got is the finite half of this block: pick V_n, take
    (naotrino: LOCAL Box Pigeon)                                          -- the minimum-norm interpolant of the observations L_n u (E p.2), and that IS
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- s_n = P_{V_n} u by (E.9), whether or not anyone in the room says "projection".
    (_: CarrierProcess Box)                                               -- What it has not got is u. Nobody has u. It has L_n u and the interpolant, and
    [area: OF Box Pigeon]                                                 -- (E.4) says the true path is in a ball around the interpolant of radius
    : LOAD Box Pigeon where                                               -- sqrt(C^2 - ||s_n||^2), inside ker L_n, provided you can name a C >= ||u||_H.
  basic_operation := area.galerkin_process.ANSYS_process                  -- You cannot name it. Keep reading.
                                                                          --
def YOU_ARE_ALSO_AWARE_THAT_ANSYS_IS_SLOW                                 -- BUILT. SCALED is a `multiplying_process`: the basic operation, which still takes
    (Box: Type i)                                                         -- forever, followed by a `GOSUB` (867). Slow, and it calls itself. That is refinement.
    (Pigeon: CarrierProcess Box)                                          -- INTERPRETED. Here is why it is slow, and it is not the hardware. The feasible sets
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- (E.4) are nested as the knots are: more observations, smaller ball. With the sharp
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- bound C = ||u||_H the radii sqrt(C^2 - ||s_n||^2) go to zero by (E.10), because
    (naotrino: LOCAL Box Pigeon)                                          -- ||s_n||^2 climbs to ||u||^2. But you do not know ||u||_H; that was the point of the
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- postdocs. So you take a loose fixed C > ||u||_H, and then the radii do NOT vanish
    (_: CarrierProcess Box)                                               -- (E p.4): by (E.10) they stop at sqrt(C^2 - ||u||^2) > 0 and sit there.
    [still_takes_forever: LOAD Box Pigeon]                                -- The dense observations still determine a unique intersection (E p.4). Uniqueness
    : SCALED Box Pigeon where                                             -- is free. The certificate is not. Slow is a loose bound: you keep adding knots, the
  multiplying_process := still_takes_forever.basic_operation.GOSUB        -- number is pinned, and the error bar refuses to close. The KNOWER says that is the
                                                                          -- whole book. The KNOWER may be right; that is not checked on this side of the page.
def BUT_YOU_EVENTUALLY_ESTIMATE_THE_TOTAL_SIZE_OF_THE_COMPUTATION         -- BUILT. Coming back up. Every rung from here is a def: the same binders written by hand, no
    (Box: Type i)                                                         -- search. You are reading the Equivalences now, the <= direction of the page.
    (Pigeon: CarrierProcess Box)                                          -- The name promises a total size. The field hands you an adding_process borrowed off SCALED's
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- multiplying_process. That is the whole estimate: a size is a sum, and the sum is the one
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- weight already had. Nothing new is measured on this rung; a magnitude is the value of a value.
    (naotrino: LOCAL Box Pigeon)                                          -- INTERPRETED. What is being sized is the residual. On the homogeneous space X, F(q) is the
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- Riesz functional of the error e = q - q*, because F(q*) = 0 (E p.5). Hence:
    (_: CarrierProcess Box)                                               --   ||F(q)||_{X*} = ||q - q*||_X,     E[q] - E[q*] = (1/2) ||F(q)||^2_{X*}            (E.12)
    [weight: SCALED Box Pigeon]                                           -- The size of the computation left to do IS the size of the residual, squared and halved.
    : MAGNITUDE Box Pigeon where                                          -- The KNOWER: the bound is Cauchy-Schwarz; equality needs the test h = e/||e||_X, e != 0.
  adding_process := weight.multiplying_process.adding_process             -- Hold that test. It is the one the next rung submits.
                                                                          --
def SO_YOU_SUBMIT_THE_JOB_AND_COUNT_HOW_LONG_IT_TAKES                     -- BUILT. You submit the job. The name promises a stopwatch; the fields promise less.
    (Box: Type i)                                                         -- mathematical_process is MAGNITUDE's adding_process read through mideastern_process, and
    (Pigeon: CarrierProcess Box)                                          -- monad is uncountable.monad, which is to say: the VALUE I return is the VALUE I was handed
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- as a binder. That is legal. It is also the joke: counting how long it takes requires a
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- VALUE to already exist, and I got mine by asking for one in the signature.
    (naotrino: LOCAL Box Pigeon)                                          -- INTERPRETED. What the stopwatch is timing. For admissible q_n these are one statement,
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- not three (E p.5): the energy gap E[q_n] - E[q*] -> 0; the dual residual
    [uncountable: VALUE Box Pigeon]                                       -- ||F(q_n)||_{X*} -> 0; and q_n -> q* in H^2. That is (E.12) read as a limit: the job is
    (_: CarrierProcess Box)                                               -- done when the residual is small, and "small residual" and "close in H^2" are the same
    [mass: MAGNITUDE Box Pigeon]                                          -- clock. In this norm. On the homogeneous space X. Not in every norm you could have picked.
    : VALUE Box Pigeon where                                              -- The KNOWER: replacing the inner product (E.5) by an equivalent one preserves convergence
  mathematical_process := mass.adding_process.mideastern_process          -- but need not preserve the exact dot-product identity (E p.3). The clock is norm-dependent.
  monad := uncountable.monad                                              -- And the monad: any answer from a program is a representation of a computation, not the
                                                                          -- computation (Episode03.lean:599). The stopwatch reads a representation of elapsed time.
def BUT_IT_MAY_NOT_CONVERGE                                               -- BUILT. The first honest name on the way up. The field: compiled_process is VALUE's
    (Box: Type i)                                                         -- mathematical_process, compiled. Nothing here says it halts. EXECUTED means it ran,
    (Pigeon: CarrierProcess Box)                                          -- not that it arrived.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- INTERPRETED. What "may not converge" means with the norm written out (E p.5):
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --   ||e||_H = sup_{||v||_H <= 1} |<e, v>_H|,                                         (E.13)
    (naotrino: LOCAL Box Pigeon)                                          --   s_n -> u in H  <=>  the unit-ball test gaps tend to 0 uniformly.
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- That is the precise form of "no weak comparison can distinguish them" at a fixed resolution.
    (_: CarrierProcess Box)                                               -- Uniformly over the ball. Not one test at a time.
    [constant: VALUE Box Pigeon]                                          -- The KNOWER, same page: agreement for each fixed test separately is only weak convergence.
    : EXECUTED Box Pigeon where                                           -- Nor does agreement of two approximations alone certify that their common limit solves the
  compiled_process := constant.mathematical_process.compiled_process      -- intended equation. Both hedges stand. The rung ran; nothing on it says it landed.
                                                                          --
def IT_DEFINITELY_COMPILES_THOUGH                                         -- BUILT. Here is the rung the whole book leans on, so read the fields, not the name.
    (Box: Type i)                                                         -- cd_process is EXECUTED's compiled_process read as digital_process: fine, that is what a
    (Pigeon: CarrierProcess Box)                                          -- source is on the way down too. Now the second field.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- one := lean.compiled_process.digital_process.zero. The field named one is filled with a
    [COMPARABLE Box Pigeon]                                               -- zero. SOURCE.one wants an Equivalation (Episode03.lean:384); DigitalProcess.zero is one
    [SOURCE Box Pigeon]                                                   -- (Episode03.lean:334). The compiler reads the type of the field, never its name. That is
    [REAL Box Pigeon]                                                     -- what "definitely compiles" certifies, and all it certifies.
    (naotrino: LOCAL Box Pigeon)                                          -- Before you feel cheated: on the way down (line 238) I built one as .zero_like on top of
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- .physics, a zero wearing a hat. The forward one was no better. It was only longer.
    (_: CarrierProcess Box)                                               -- The compiler passed both. It cannot tell one from zero; it can tell Equivalation from Nat.
    [lean: EXECUTED Box Pigeon]                                           -- INTERPRETED. Not a bug in Lean; it is the border of the left column: types are checked,
    : SOURCE Box Pigeon where                                             -- values are asserted. The Equivalences draw the same border: the target need not itself be
  cd_process := lean.compiled_process.digital_process                     -- cubic for the identity (E.8); u = q* follows only if u solves the same least-action
  one := lean.compiled_process.digital_process.zero                       -- problem (E p.3). Compiling is the type check. Solving is the other column. A one that
                                                                          -- is a zero handed back: that is the source, and the compiler is fine with it.
def WHICH_MEANS_IT_HAS_A_BETA_REDUCTION                                   -- BUILT. Gungan is the language the CHORUS told John to learn REAL_FAST, and here it is:
    (Box: Type i)                                                         -- meesa_process, lifted straight out of SOURCE's cd_process. A beta-reduction is a
    (Pigeon: CarrierProcess Box)                                          -- substitution, (fun x => body) a becomes body with a for x, and that is all the rung does:
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- it substitutes the source's process for its own. Meesa reduce. Nothing else here moves.
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- MEASURED. Episode 4 does exactly this substitution in the margin (Episode04.lean:129-131):
    (naotrino: LOCAL Box Pigeon)                                          -- set y = u'/u; then u^{-1} D u = D + y and the cube is u'''/u. "There was never a
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- nonlinearity." INTERPRETED. Written out, u = q' nonzero on an interval, scalar (E p.5):
    (_: CarrierProcess Box)                                               --   M_u^{-1} D M_u = D + y,    (D + y)^3 1 = y'' + 3yy' + y^3 = u'''/u,               (E.14)
    [the_argument: SOURCE Box Pigeon]                                     --   y'' + 3yy' + y^3 = 0   <=>   u''' = 0   <=>   q^(4) = 0.
    : GUNGAN Box Pigeon where                                             -- The ODE in y was the quartic in q wearing a change of variable. q is cubic; y is rational.
  meesa_process := the_argument.cd_process.meesa_process                  -- The KNOWER: nonvanishing is essential, you are dividing by u. Through zeros the bridge is
                                                                          -- out. The weak cubic theorem (E.6) holds there without this quotient. A different theorem.
def AND_ALWAYS_RETURNS_THAT_THE_ARGUMENT_IS_CONSISTENT                    -- BUILT. The name says the argument is always consistent. The field says gauge_process,
    (Box: Type i)                                                         -- taken off GUNGAN's meesa_process. Consistent means: the gauge you were handed, handed
    (Pigeon: CarrierProcess Box)                                          -- back. A rung that returns what it was given is the only rung that always returns the
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- same thing. That is what a gauge is for.
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- INTERPRETED. There is one exact affine statement on the page, and this is where it sits
    (naotrino: LOCAL Box Pigeon)                                          -- (E p.5): on a nonempty open convex domain in a Banach space, a differentiable map A has
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- constant bounded derivative if and only if it is affine,
    (_: CarrierProcess Box)                                               --   DA(q) = L for all q    <=>    A(q) = Lq + b.
    [the_argument_for_naotrinos: GUNGAN Box Pigeon]                       -- One way is differentiation. The converse: integrate the derivative along a line segment,
    : MEASURABLE Box Pigeon where                                         -- which is where convex earns its keep. The Equivalences call this the exact affine
  gauge_process := the_argument_for_naotrinos.meesa_process.gauge_process -- statement available for an operator assigned to LambdaCDM. Available. Not the one I
                                                                          -- claim; the one there is. Constant gauge in, constant gauge out; that is what consistent costs.
def AT_THE_END_OF_THE_DAY_I_HAVE_TO_ADMIT_IT_IS_A_BLACK_BOX               -- BUILT. Black box, and the fields agree: santa_claus is MEASURABLE's gauge_process read
    (Box: Type i)                                                         -- through sensing_process, and quantum := Box. The quantum is the universe I was handed.
    (Pigeon: CarrierProcess Box)                                          -- You do not get to look inside Santa. That is Episode 2's rule (Episode02.lean:927, "You
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- don't get to know this"). PRESENT means the detector clicked; it does not say at what.
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- INTERPRETED. Jacobian-free Newton-Krylov is a black box by design: DF(q)v is approximated
    (naotrino: LOCAL Box Pigeon)                                          -- by residual differences inside a Krylov solve, so the matrix is never formed (E p.5).
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- You never see the derivative. For the cubic that costs nothing: the derivative is already
    (_: CarrierProcess Box)                                               -- constant and coercive, and an exact Newton solve recovers the minimizer in one step. One.
    [the_bug: MEASURABLE Box Pigeon]                                      -- The black box, opened, has a single affine map in it: the one on the rung above.
    : PRESENT Box Pigeon where                                            -- The KNOWER: that is the cubic. For a nonlinear residual, local quadratic Newton convergence
  santa_claus := the_bug.gauge_process.sensing_process                    -- needs an invertible derivative, a locally Lipschitz derivative, and a sufficiently close
  quantum := Box                                                          -- initial state (E p.5). Lipschitz continuity of the residual alone is insufficient.
                                                                          -- That is the sentence I have to admit. I put it in the name so you would not miss it.
def STILL_THERE_COULD_BE_A_MISSPELLING_IN_THIS_LOGIC                      -- BUILT. The last rung up, and the name is the only hedge the code column carries. The
    (Box: Type i)                                                         -- fields: slip_process is PRESENT's santa_claus.static_fraction, the mu you don't get to know,
    (Pigeon: CarrierProcess Box)                                          -- and observation := Box. What was observed is the universe you brought in. Nothing added.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- Now the misspelling. REIMANN (line 809) is in a def name and compiled: the compiler checks
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- a name against its other uses, and misspelled the same way twice is spelled right.
    (naotrino: LOCAL Box Pigeon)                                          -- scientifc (line 11) is in the masthead, inside /- -/, where nothing is checked. exissts
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- (line 73) is in this column, mine, where nothing is checked either. Three misspellings,
    (_: CarrierProcess Box)                                               -- zero errors. The compiler checks the spelling of names. It does not check the spelling of
    [fallacy: PRESENT Box Pigeon]                                         -- claims. That is the left column in one sentence, and the reason the right one exists.
    : OBSERVED Box Pigeon where                                           -- INTERPRETED. The Equivalences say it about norms (E p.8): complementing both bits negates
  slip_process := fallacy.santa_claus.static_fraction                     -- both centered signs and preserves the square; a sign reversal preserves a full Sobolev norm.
  observation  := Box                                                     -- Preserving norms does not make distinct states equal; a comparison must apply the intended
                                                                          -- representation map. Same slip: the invariant passed, the claim did not. OBSERVED. Not proved.
namespace Metavariable                                                    -- BUILT. The order on the tower. Metavariable is Episode02:605, base and step; le reads it
                                                                          -- one rung at a time. Two hedges before we start: nothing here is a norm, and the compiler
def le {α : Type i} : Metavariable α → Metavariable α → Prop              -- proves only that it stops. Base against base: the two truth fields are equal. That is
  | .base this_one _,        .base that_one _        =>                   -- Cu = Cv, and Cu = Cv <=> u - v in K <=> [u] = [v] in H/K, K = ker C (E.17).
                                        this_one.truth = that_one.truth   -- INTERPRETED. Equal at the base is equal modulo what the step cannot see; the quotient in
  | .base _ _,               .step _ _               => True              -- one match arm. Base under step is True: ker C ⊆ ker O <=> a unique linear T with O = TC
  | .step _ _,               .base _ _               => False             -- (E.19). The factorization runs one way, so step under base is False; and ker C = ker O
  | .step this_step here,    .step that_step there   =>                   -- <=> that T exists and is injective (E.19). No boundedness of T follows without an estimate
                (this_step.truth = that_step.truth ∧ le here there) ∨     -- (E p.7). Step against step: agree here and recurse, or skip a rung. That is the quotient
                le (.step this_step here) there                           -- by one step at a time, and the bound I want is ||[z]||_{H/K} ≤ M ||Cz||_Y, which gives
termination_by _ how_far => sizeOf how_far                                -- ||Cz_n|| -> 0 <=> ||[z_n]|| -> 0 (E.18). BUILT: Lean proved that sizeOf how_far falls.
                                                                          -- INTERPRETED: the bound. Without a lower bound, small curl need not mean small quotient
end Metavariable                                                          -- error (E p.7); that is coercivity, Poincare after removing the kernel, and it is not here.
                                                                          -- Keep the winding if it is measured: on the annulus w has zero curl and circulation 2π;
instance {α : Type i} : LE (Metavariable α) where                         -- retain W and the invisible space is ker C ∩ ker W (E p.7). The device is meant to count
  le := Metavariable.le                                                   -- that datum, not discard it. For rough fields W needs a domain where the pairing exists.
                                                                          -- BUILT. One line: ≤ on the tower is le. MEASURED. TruthOrder, selection_sound, Closure.le
def AND_WE_WONT_KNOW_FOR_SURE                                             -- (Episode05:1099,1107,1135) are logical relations, not a scalar Sobolev norm (E p.10).
    (Box: Type i)                                                         -- The norm is my addition. Read the complete projection criterion (E p.11) down, and A §7's
    (Pigeon: CarrierProcess Box)                                          -- conclusion up: common admissible problem, a unique or quotient target, and controlled
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- approximation imply common observations at any prescribed finite resolution (A p.8).
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- Same sentence, both directions; that is the iff of this page, said here once. Caution:
    (naotrino: LOCAL Box Pigeon)                                          -- Metavariable.le is its own four-arm match. It is not Number.le's truth table; do not
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- read T=T into it. BUILT. COMPARABLE by hand, ten binders; the physical process is
    (_: CarrierProcess Box)                                               -- failure's slip process. MEASURED. The name is the hedge. smaller_than is x ≤ y ∧ y ≤ x:
    [failure: OBSERVED Box Pigeon]                                        -- antisymmetry demanded, equality delivered. This is the <= answer to line 170's
    : COMPARABLE Box Pigeon where                                         -- one_foot = π: there I set k = 1, here I ask for both orders. INTERPRETED. At zero
  physical_process := failure.slip_process.physical_process               -- tolerance, acceptance is equivalent to exact agreement after the chosen map (E.22):
  smaller_than := fun x y => x ≤ y ∧ y ≤ x                                -- M_N(u,v,R,τ) = accept <=> N_1(v - Ru) ≤ τ. We won't know for sure. We will know to
                                                                          -- tolerance τ, and τ = 0 is the only τ that means equal. Curl does not annihilate boundary data.
def ONCE_WE_DETECT_NAOTRINO_MOTION_WE_WILL_DETECT_THE_NOWTRINO            -- BUILT. PHYSICAL, by hand. Going down the page the compiler found this rung. Going up, I apply
    (Box: Type i)                                                         -- it, and I hand it every rung below as a bracket. Count them. Each one the search crossed for
    (Pigeon: CarrierProcess Box)                                          -- free on the way down; here you carry it yourself. That is the price of the <= direction.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- The nowtrino goes in at the top as the assumption. Remember it; it comes back out at line 1160.
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [number_of_clicks: COMPARABLE Box Pigeon]                             -- The named bracket is a COMPARABLE called number_of_clicks. Physical means: a count, a threshold.
    : PHYSICAL Box Pigeon where                                           --
  noisy_process := number_of_clicks.physical_process.noisy_process        -- BUILT. The noisy process is the clicks' own noisy process. Nothing new is wired in.
  threshold := number_of_clicks.physical_process.noisy_process.program    -- BUILT. The threshold is that same process's program. A threshold is a program; the field says so.
  admissible? := fun at_rest in_motion => by intro _; rfl                 -- BUILT. Read the binder names: at_rest, in_motion. Then `intro _; rfl`: it equals itself.
                                                                          -- INTERPRETED. (a v b) & (~a v ~b) <=> a != b, and 1[a!=b] = (b-a)^2 = (t-s)^2/4          (E.20)
def WE_CAN_REPRESENT_CLICK_COUNT_WITH_A_TALLY_EVEN_WITH_NOISE             -- A parity test is a squared discrete derivative (E p.8). To detect motion is to detect a pair
    (Box: Type i)                                                         -- that differs. That the pair is a naotrino and a nowtrino is the name of the def, not the field.
    (Pigeon: CarrierProcess Box)                                          -- BUILT. REPRESENTABLE, by hand. Twenty-two class brackets, two of them SOURCE, in case the first
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- SOURCE was lying. The compiler accepts the duplicate. It does not ask which one is the source.
    [anechoic_chamber: PHYSICAL Box Pigeon]                               -- anechoic_chamber is a PHYSICAL and so is hiss. The chamber supplies the machine; the hiss
    [COMPARABLE Box Pigeon][PRESENT Box Pigeon][MEASURABLE Box Pigeon]    -- supplies the program. That is what "even with noise" means on the left: two PHYSICALs.
    [GUNGAN Box Pigeon][SOURCE Box Pigeon][SOURCE Box Pigeon]             --
    [EXECUTED Box Pigeon][VALUE Box Pigeon][MAGNITUDE Box Pigeon]         --
    [SCALED Box Pigeon][LOAD Box Pigeon][OF Box Pigeon]                   --
    [BULLSHIT Box Pigeon][PROPAGANDA Box Pigeon][ACOLYTE Box Pigeon]      --
    [SCIENTIFIC Box Pigeon][TRUTH Box Pigeon][WITNESSED Box Pigeon]       --
    [REAL Box Pigeon]                                                     --
    (naotrino: LOCAL Box Pigeon)                                          -- INTERPRETED. The tally is a machine, and here is its whole table (E p.8). Three states, one
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- tape, an end marker #. Leave the symbol alone, move right on every step. Any other symbol rejects.
    (_: CarrierProcess Box)                                               --     E: read 0 -> Z.        read 1 -> O.        read # -> reject.
    [hiss: PHYSICAL Box Pigeon]                                           --     Z: read 0 -> reject.   read 1 -> E.        read # -> accept.
    : REPRESENTABLE Box Pigeon where                                      --     O: read 0 -> E.        read 1 -> reject.   read # -> accept.
  calculation_process :=                                                  -- E remembers the first bit of a pair; the next bit must differ to return to E. Halting in Z or O
    { anechoic_chamber.noisy_process.turing_process with                  -- leaves exactly the final base bit. It accepts the words of length 2m+1 whose first m pairs differ.
        program := hiss.noisy_process.turing_process.program              ----------------+
        computational_process := --                                                       |
          { anechoic_chamber.noisy_process.turing_process.computational_process with --   |
              closure := fun a_tally => a_tally } } --                                    |
  representable? := fun a_fact a_study =>                                 ----------------+
    ⟨hiss.noisy_process.turing_process.turing_step?                       -- BUILT. `turing_step?` is that step, run on the program of the fact and the study. `closure` is
                              (Computation.program a_fact a_study), rfl⟩  -- the identity on the tally, and the witness is `rfl`. A tally is a machine that agrees with itself.
                                                                          -- The KNOWER: the name says "even with noise"; the table has none. Correct: the noise is hiss.
def SO_WE_ARE_CONFIDENT_OF_THE_COUNT_IN_THE_DEVICE                        -- BUILT. NUMERIC, by hand. Confident of the count: the computational process is the glyph's own.
    (Box: Type i)                                                         -- MEASURED. Episode 13 pulls one bit at the base and two per cell (Episode13:308-311), and stepOK
    (Pigeon: CarrierProcess Box)                                          -- accepts when the two bits in a cell differ (Episode13:423-426). That is the table above, in Lean.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --      M_trace(bits(t)) = accept  <=>  t.stepOK = true  <=>  THEORY.traceSat(t) = true       (E.21)
    (_: CarrierProcess Box) ------------------------+ a card!             --
    [glyph: REPRESENTABLE Box Pigeon]                                     -- MEASURED. The last equality is trace_correspondence (Episode13:668), restated as cook_levin
    : NUMERIC Box Pigeon where                                            -- (Episode13:741): every tape, by induction on the tape, down to four Boolean cases. It checks the
  computational_process :=                                                -- tape's own assignment. Adjacent cells are not required to share an intermediate bit (E p.8).
                    glyph.calculation_process.computational_process       -- The KNOWER: that table is a deterministic machine with finite memory. It proves this check is
                                                                          -- computable. Universality needs a separate simulation construction; Cook-Levin quantifies over
def AND_IT_CLICKS_AGAIN_AND_AGAIN_AND_AGAIN                               -- encoded nondeterministic polynomial-time computations. The theorem's name supplies neither (E p.8).
    (Box: Type i)                                                         -- BUILT. REPEATABLE, by hand. JMP is a bracket; the def is the loop. Again, and again, and again.
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
    [click_count: NUMERIC Box Pigeon]                                     -- The click_count is a NUMERIC. Repeatable means: the same count, run again, agreeing to tolerance.
    : REPEATABLE Box Pigeon where                                         --
  repeatable_process :=                                                   -- BUILT. The repeatable process is the count's own repeatable process. Same wire, one rung up.
                 click_count.computational_process.repeatable_process     -- INTERPRETED. What "again" certifies: d = v - Ru,  S = sum_j d_j^2 + sum_j (d_{j+1} - d_j)^2,
                                                                          --      M_N(u,v,R,tau) = accept  <=>  S <= tau^2  <=>  N_1(v - Ru) <= tau                     (E.22)
def THE_COUNTER_IS_IMPLEMENTED_IN_A_BINARY_ACCUMULATOR                    -- Every operation halts. No square root, no oracle. At tau = 0 the certificate is exact agreement
    (Box: Type i)                                                         -- after the map R; for opposite centered parity take R = -I (E p.9).
    (Pigeon: CarrierProcess Box)                                          -- BUILT. BINARY, by hand. flicker is the BINARY I already had; nonstop is the REPEATABLE below.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- Twenty-four brackets: the longest list on the page, for a rung whose content is two
    [flicker: BINARY Box Pigeon]                                          -- constructors and one iterate. The barker over-promises; the field under-delivers; keep reading.
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
    [nonstop: REPEATABLE Box Pigeon]                                      -- INTERPRETED. All an accumulator needs (E p.9): a rational is a signed integer numerator over
    : BINARY Box Pigeon where                                             -- a positive denominator; finite sums, finite products; compare by cross-multiplication.
  observation_process := nonstop.repeatable_process.observation_process   -- BUILT. The observation process is nonstop's. zero is `.nil`. one is `.index` over `.nil`:
  zero := .nil nowtrino.fact                                              -- one is a nil with an index on it. That is the binary in BINARY. Two symbols, honestly counted.
  one  := .index                                                          ------------------------------+
              nowtrino.fact --                                                                          |
              nonstop.repeatable_process.observation_process.cauchy_process.limit_process.sequence --   |
              (.nil nowtrino.fact) --                                                                   |
  bit  := nonstop.repeatable_process.observation_process.iterate          ------------------------------+
              flicker.bit                                                 -- BUILT. bit is the observation's iterate of flicker's bit. MEASURED. In Episode 13 a bit is
                                                                          -- `decide` on a fact (Episode13:293) and bits lists them (Episode13:308); (E.21) checks that list.
def JUST_NEED_TO_INSPECT_THE_REGISTER_TO_SEE_CURRENT_SEQUENCE_INDEX       -- BUILT. RESIDUE, by hand. Inspect the register: the cauchy process is the register's own.
    (Box: Type i)                                                         -- INTERPRETED. The register is a coefficient vector c. The residue is what is left when you take
    (Pigeon: CarrierProcess Box)                                          -- the dot product without the Gram matrix. With B_1..B_m a basis, s = sum_i c_i B_i,
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- G_ij = <B_i,B_j>_H and b_i = <B_i,u>_H:
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --      s = P_V u  <=>  G c = b,     <s,u>_H = c^T b = c^T G c = ||s||_H^2                     (E.23)
    (naotrino: LOCAL Box Pigeon)                                          -- Cubic B-splines are not orthonormal (E p.9). The plain dot product of coefficients omits G.
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- A change to Chebyshev, (A.4) on each knot interval, transforms G with c and keeps the identity.
    (_: CarrierProcess Box)                                               -- The KNOWER: the code has no G. Correct. The code has `cauchy_process`; the G lives on this side.
    [register: BINARY Box Pigeon]                                         --
    : RESIDUE Box Pigeon where                                            --
  cauchy_process := register.observation_process.cauchy_process           -- BUILT. One field, one projection. The current sequence index is the register's cauchy process.
                                                                          --
def FIGURE_OUT_WHAT_IT_CONVERGES_TO                                       -- BUILT. ENCODED, by hand. Figure out what it converges to: the limit process is the residue's own.
    (Box: Type i)                                                         -- INTERPRETED. There is a terminating checker for that too (E p.9). Rational endpoints, rational
    (Pigeon: CarrierProcess Box)                                          -- clamped data, a piecewise polynomial q with rational knots and coefficients; verify C^1 and the
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- traces, so q is in A, a subset of H^2; solve four rational equations for q*; integrate
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- |(q - q*)''|^2 on each interval. Finite rational operations, every one of them. Then:
    (naotrino: LOCAL Box Pigeon)                                          --      M_E(q,data,tau) = accept  <=>  int |(q - q*)''|^2 <= tau^2  <=>  ||q - q*||_H <= tau
    (_: UNIVERSAL Box Pigeon naotrino)                                    --                                                           <=>  E[q] - E[q*] <= tau^2/2       (E.24)
    (_: CarrierProcess Box)                                               -- A certificate for an actual continuous Sobolev error of a finitely represented path.
    [converged_value: RESIDUE Box Pigeon]                                 -- The KNOWER: general real targets need a representation and certified error bounds; a finite
    : ENCODED Box Pigeon where                                            -- checker does not decide equality of arbitrary real solutions, or all limiting assertions (E p.9).
  limit_process := converged_value.cauchy_process.limit_process           -- BUILT. `limit_process`: a projection. What it converges to is what it was handed. Figured out.
                                                                          --
def CAN_YOU_COUNT_THAT_HIGH                                               -- BUILT. COUNTABLE, by hand. This is CAN_YOU_COUNT_THEM (line 55) read upward. The index is the
    (Box: Type i)                                                         -- limit process's indexing process. Same count, same wire, back the way it came, unchanged.
    (Pigeon: CarrierProcess Box)                                          -- MEASURED. How high was checked (E p.11): the 36-rung norm arithmetic was recomputed from the
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- saved raw and blank lists; the trace scanner was checked against the pair predicate for every
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- binary word of length 0 through 11. No Lean build was run by the companions: they read the
    (naotrino: LOCAL Box Pigeon)                                          -- code, they did not run it. That high, and no higher, is what was checked.
    (_: UNIVERSAL Box Pigeon naotrino)                                    -- INTERPRETED. The criterion in one breath (E p.11): orthogonality in every variational direction
    (_: CarrierProcess Box)                                               -- is best approximation; for the nested cubic spaces the missing squared norm is the squared error
    [some_number: ENCODED Box Pigeon]                                     -- and tends to zero; for the clamped problem the error norm is the dual residual norm, its square
    : COUNTABLE Box Pigeon where                                          -- twice the action gap; finite rational representations make each tolerance test a halting machine.
  index := some_number.limit_process.indexing_process                     -- BUILT. index := the indexing process. You can count that high because the field says you can.
                                                                          --
def CAN_YOU_UNDERSTAND_THE_PROCESS_TO_COUNT_THAT_HIGH                     -- BUILT. ADMISSIBLE, by hand. Can you understand the process to count that high? The bracket is
    (Box: Type i)                                                         -- named aleph and its class is COUNTABLE. That is the whole joke, and it typechecks.
    (Pigeon: CarrierProcess Box)                                          --
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                --
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           --
    (naotrino: LOCAL Box Pigeon)                                          --
    (_: UNIVERSAL Box Pigeon naotrino)                                    --
    (_: CarrierProcess Box)                                               --
    [ℵ : COUNTABLE Box Pigeon]                                            -- BUILT. aleph : COUNTABLE. The compiler reads an identifier. It does not read Cantor.
    : ADMISSIBLE Box Pigeon where                                         --
  counting_process := ℵ.index.count                                       -- BUILT. counting_process := aleph.index.count. I asked you to count, then whether you understood
                                                                          -- counting; the answer to the second is the first one's `.count`. Understanding is a projection.
def THEN_I_THINK_YOU_CAN_TELL_APART_A_NAOTRINO_AND_A_NOWTRINO             -- BUILT. DISTINGUISHABLE, by hand. The bottom of the page is the top of the page. Every rung
    (Box: Type i)                                                         -- above took [nowtrino: DISTINGUISHABLE] as its first bracket; this rung produces one. Line 45
    (Pigeon: CarrierProcess Box)                                          -- assumed it going down; line 1160 delivers it coming up. Down is =>, up is <=. The page is an iff.
    [nowtrino: DISTINGUISHABLE Box Pigeon]                                -- INTERPRETED. What telling them apart would need (E p.10): R a bijection between two specified
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]           -- admissible state spaces, boundary and initial data included; residuals F_2(Rq) = J(q) F_1(q),
    (naotrino: LOCAL Box Pigeon)                                          -- with J injective on the residual values that matter. Then
    (_: UNIVERSAL Box Pigeon naotrino)                                    --      F_1(q) = 0 <=> F_2(Rq) = 0;   S_2(Rq) = a S_1(q) + b, a > 0  =>  same minimizers        (E.25)
    (_: CarrierProcess Box)                                               -- with b constant over the admissible class. That is the equation-and-least-action equivalence.
    : DISTINGUISHABLE Box Pigeon where                                    -- The KNOWER: an equivalence between two specified spaces. Which two is the dictionary. Quite.
  fact := nowtrino.fact                                                   -- BUILT. fact := the nowtrino's fact. symbol := the nowtrino's symbol. The output is the input.
  symbol := nowtrino.symbol                                               -- The name says I think you can tell them apart. The fields hand you back the one you gave me.
  different? := fun _ => True                                             -- BUILT. different? := fun _ => True. Whatever you hand it: different. No fact is consulted.
  dec_distinct := fun _ => isTrue trivial                                 -- BUILT. dec_distinct := isTrue trivial. The compiler's last word on the page. True, trivially.
                                                                          -- INTERPRETED. The projection theorem proves the energy identity. Reading the operators as QED, GR,
                                                                          -- Navier-Stokes, or an affine LCDM description needs the dictionary, its observable prescription
                                                                          -- included, and that is not established here (E p.10). Nothing on this side is proved. The number
                                                                          -- is demonstrated. I think you can tell a naotrino from a nowtrino. "I think" is the operative word.
end Measurement
