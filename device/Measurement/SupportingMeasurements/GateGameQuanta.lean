-- GateGameQuanta.lean
--
-- Companion to GateGame.lean (gated 2026-08-17, axiom-free): the
-- THRESHOLD structure of a finite game's equilibrium, stated at the
-- device's own rung. The claim made precise: a pure best-response does
-- not move continuously with the payoff — it is a STEP. Pressure below
-- the threshold changes the payoff and changes NOTHING about the
-- response; the response flips only when the binding inequality
-- reverses. An equilibrium does not lean; it trips.
--
-- Per the elaborator-naturals law, the parameter is stated only at the
-- earned rungs 0, 1, 2 with 3 as the fencepost — no general k beyond
-- what enumeration decides, except where the payoff is definitionally
-- k-free.
--
-- NOT-CLAIMED (load-bearing, same doctrine as GateGame.lean):
--   * This models the METHOD's game from GateGame — the wall game's
--     environment side with a parameterized cost of exploiting — never
--     the electron, the coupling, the jar, or any physics.
--   * The 2024 carry unwind ("a quanta of value had to be tripped to
--     move the equilibria") and the photoelectric threshold are LENSES
--     on this shape, named here in comment only. No market claim and no
--     photoelectric claim appears in any statement; three systems
--     wearing one silhouette remain three separately-founded systems.
--   * The device's own founded threshold (the count-3 floor, the
--     crossing at √(18/5)) is a separate, already-built object
--     (AlphaBoundMediant) and this leaf does not touch or extend it.

namespace Measurement.GateGameQuanta

inductive WallMove
  | confine
  | waver

inductive EnvMove
  | exploit
  | straight

-- The environment's payoff, parameterized by k, the cost of running the
-- exploit (the funding rate, in the lens). Against a confining gate the
-- exploit pays nothing at ANY k; against a wavering gate it pays a gross
-- 3 less the cost; playing straight always pays 1.
def envPayoff (k : Nat) : WallMove → EnvMove → Nat
  | .confine, .exploit  => 0
  | .waver,   .exploit  => 3 - k
  | _,        .straight => 1

-- e is a best response to the gate's move at cost k.
def envBest (k : Nat) (w : WallMove) (e : EnvMove) : Prop :=
  ∀ e' : EnvMove, envPayoff k w e' ≤ envPayoff k w e

-- ## The step, rung by rung (gate wavering — no one confines)

-- k = 0: the exploit runs, and running it is strictly the thing to do.
theorem runs_at_zero :
    envBest 0 .waver .exploit ∧ ¬ envBest 0 .waver .straight :=
  ⟨fun e' => by cases e' <;> decide,
   fun h => absurd (h .exploit) (by decide)⟩

-- k = 1: the cost ROSE — the payoff genuinely moved — and the response
-- did not move at all. Sub-threshold pressure is inert.
theorem runs_at_one :
    envBest 1 .waver .exploit ∧ ¬ envBest 1 .waver .straight :=
  ⟨fun e' => by cases e' <;> decide,
   fun h => absurd (h .exploit) (by decide)⟩

-- The step is a step, not a slope: from k = 0 to k = 1 the exploit's
-- payoff strictly fell, yet exploit remained the strict best response
-- at both rungs.
theorem sub_threshold_inert :
    envPayoff 1 .waver .exploit < envPayoff 0 .waver .exploit ∧
    envBest 0 .waver .exploit ∧ envBest 1 .waver .exploit :=
  ⟨by decide, runs_at_zero.1, runs_at_one.1⟩

-- k = 2: the knife edge — the quantum is exactly met, and BOTH moves
-- are best responses. The threshold itself is the indifference point.
theorem knife_edge_at_two :
    envBest 2 .waver .exploit ∧ envBest 2 .waver .straight :=
  ⟨fun e' => by cases e' <;> decide,
   fun e' => by cases e' <;> decide⟩

-- k = 3 (the fencepost): one more unit and the inequality has
-- reversed — the exploit is now strictly dominated and motion starts.
theorem unwinds_at_three :
    envBest 3 .waver .straight ∧ ¬ envBest 3 .waver .exploit :=
  ⟨fun e' => by cases e' <;> decide,
   fun h => absurd (h .straight) (by decide)⟩

-- ## The gate's discipline is threshold-free

-- Against a confining gate, playing straight is a best response at
-- EVERY k — definitionally, the confined exploit pays 0 no matter the
-- cost, so no quantum exists to trip. The discipline does not wait for
-- the threshold; it removes the game the threshold lives in.
theorem confine_flat (k : Nat) : envBest k .confine .straight := by
  intro e'
  cases e'
  · show (0 : Nat) ≤ 1
    decide
  · show (1 : Nat) ≤ 1
    decide

end Measurement.GateGameQuanta

#print axioms Measurement.GateGameQuanta.runs_at_zero
#print axioms Measurement.GateGameQuanta.sub_threshold_inert
#print axioms Measurement.GateGameQuanta.knife_edge_at_two
#print axioms Measurement.GateGameQuanta.unwinds_at_three
#print axioms Measurement.GateGameQuanta.confine_flat
