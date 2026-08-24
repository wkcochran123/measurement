-- GateGame.lean
--
-- A finite model of the GATING DISCIPLINE as two 2x2 games, stated and
-- decided entirely at the device's own rung: payoffs are elaborator
-- naturals, every theorem closes by case-enumeration (`decide` on Nat
-- comparisons), and no continuum object appears in any statement.
--
-- NOT-CLAIMED (load-bearing, per Kodo's residual fence 2026-08-17):
--   * This leaf models the LOOP'S GATING DISCIPLINE — the author/gate
--     split and the gate/environment wall — never the electron, the
--     coupling, the jar, or any physics. "The device sits at an
--     equilibrium about its coupling" is NOT a theorem here or anywhere.
--   * "Nash" rides in this comment as attribution only. No game-theory
--     token appears in any statement; general equilibrium existence
--     (mixed strategies, Brouwer/Kakutani) is continuum machinery and
--     lives in the Dream. Everything below is finite Study: pure
--     profiles, decidable, enumerated.
--   * The players are US — the seats and the pressure on them. Modeling
--     one's own decision structure is founded in a way modeling the
--     electron's is not.
--
-- Game A (the pipeline): Author chooses honest/inflated, Gate chooses
-- strict/lax. The book's production run is the empirical trace of the
-- equilibrium profile: honest authorship through a strict gate.
--
-- Game B (the wall): Gate chooses confine/waver about the one proven
-- T=F wall (Episode16 true_eq_false); the Environment chooses
-- exploit/straight. Confining weakly dominates, and against a confining
-- gate exploitation does not pay.

namespace Measurement.GateGame

-- ## Game A: the pipeline game

inductive AuthorMove
  | honest
  | inflated

inductive GateMove
  | strict
  | lax

-- The author's payoff: an inflated claim through a lax gate is the
-- crank's jackpot; caught inflation pays nothing; honest work through a
-- strict gate ships with trust.
def authorPayoff : AuthorMove → GateMove → Nat
  | .honest,   .strict => 2
  | .honest,   .lax    => 1
  | .inflated, .strict => 0
  | .inflated, .lax    => 3

-- The gate's payoff: a shipped, verified artifact is the whole point;
-- catching inflation is the job done; anything through a lax gate is
-- worthless to it.
def gatePayoff : AuthorMove → GateMove → Nat
  | .honest,   .strict => 2
  | .honest,   .lax    => 0
  | .inflated, .strict => 1
  | .inflated, .lax    => 0

-- A profile is stable when neither seat can gain by deviating alone.
def stableA (a : AuthorMove) (g : GateMove) : Prop :=
  (∀ a' : AuthorMove, authorPayoff a' g ≤ authorPayoff a g) ∧
  (∀ g' : GateMove, gatePayoff a g' ≤ gatePayoff a g)

-- (honest, strict) is stable: inflation against a strict gate pays 0,
-- and the gate gains nothing by going lax on honest work.
theorem honest_strict_stable : stableA .honest .strict :=
  ⟨fun a' => by cases a' <;> decide, fun g' => by cases g' <;> decide⟩

-- The crank's jackpot is NOT stable: the gate profitably deviates to
-- strict (catching inflation pays 1 over 0).
theorem inflated_lax_unstable : ¬ stableA .inflated .lax := by
  intro h
  exact absurd (h.2 .strict) (by decide)

-- Neither mixed-blessing profile survives either: against a lax gate
-- the author inflates, and against a strict gate inflation is dominated.
theorem honest_lax_unstable : ¬ stableA .honest .lax := by
  intro h
  exact absurd (h.1 .inflated) (by decide)

theorem inflated_strict_unstable : ¬ stableA .inflated .strict := by
  intro h
  exact absurd (h.1 .honest) (by decide)

-- So (honest, strict) is the ONLY stable profile of the pipeline game:
-- no-self-approval is an equilibrium, not a rule.
theorem pipeline_equilibrium_unique (a : AuthorMove) (g : GateMove) :
    stableA a g → a = .honest ∧ g = .strict := by
  intro h
  cases a <;> cases g
  · exact ⟨rfl, rfl⟩
  · exact absurd h honest_lax_unstable
  · exact absurd h inflated_strict_unstable
  · exact absurd h inflated_lax_unstable

-- ## Game B: the wall game

inductive WallMove
  | confine  -- T=F stays at its one proven wall, never operates
  | waver    -- the identification leaks into operation

inductive EnvMove
  | exploit  -- the F=T environment plays the dissonance
  | straight

-- The gate loses only when the leak meets the exploit.
def wallPayoff : WallMove → EnvMove → Nat
  | .confine, _         => 1
  | .waver,   .exploit  => 0
  | .waver,   .straight => 1

-- The environment profits only through the leak.
def envPayoff : WallMove → EnvMove → Nat
  | .waver,   .exploit => 2
  | .confine, .exploit => 0
  | _,        .straight => 1

-- Confining weakly dominates wavering: never worse, strictly better
-- against the exploit. The fence is a strategy, not just an ethic.
theorem confine_dominates :
    (∀ e : EnvMove, wallPayoff .waver e ≤ wallPayoff .confine e) ∧
    wallPayoff .waver .exploit < wallPayoff .confine .exploit :=
  ⟨fun e => by cases e <;> decide, by decide⟩

def stableB (w : WallMove) (e : EnvMove) : Prop :=
  (∀ w' : WallMove, wallPayoff w' e ≤ wallPayoff w e) ∧
  (∀ e' : EnvMove, envPayoff w e' ≤ envPayoff w e)

-- Against a confining gate, exploitation does not pay: the environment's
-- best response is to play straight, and that profile is stable.
theorem confine_straight_stable : stableB .confine .straight :=
  ⟨fun w' => by cases w' <;> decide, fun e' => by cases e' <;> decide⟩

-- The dissonance-exploit profile is NOT stable: the gate deviates to
-- confining and zeroes the exploit.
theorem waver_exploit_unstable : ¬ stableB .waver .exploit := by
  intro h
  exact absurd (h.1 .confine) (by decide)

end Measurement.GateGame

#print axioms Measurement.GateGame.honest_strict_stable
#print axioms Measurement.GateGame.pipeline_equilibrium_unique
#print axioms Measurement.GateGame.confine_dominates
#print axioms Measurement.GateGame.confine_straight_stable
#print axioms Measurement.GateGame.waver_exploit_unstable
