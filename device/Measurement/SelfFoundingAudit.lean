import Measurement.AlphaBFGS
import Measurement.AlphaBoundCountToThree
import Measurement.AlphaBoundMediant
import Measurement.ArchimedesPi
-- ⚑ SITE 5 RESTORED (2026-07-26, operator "fix now" + BM routing): the stale
-- de-selection refactor of `direct_1to3` was repaired (one binder type annotation on
-- `jarClass`'s rho lambda — the smallest diff, preserving the intended de-selection);
-- `jar_readout_drift_immune` re-graded [propext], sorryAx GONE. History of the catch
-- kept in the git record + handoffs (turns 783-785).
import Measurement.CalibrationTwoPaths

/-! # SelfFoundingAudit — stone 2a: VERIFY, don't edit (the read-only per-site prints).

SELF_FOUNDING_REWIRING_PLAN.md stone 2a, both chairs GO (Kodo earn-PASS + Beastmaster
architecture-PASS, 2026-07-26). This file is a PURE READ INSTRUMENT: imports + `#print
axioms` directives only — ZERO definitions, ZERO edits to any existing file. It asks the
build to display the LITERAL axiom basis of each Class-A (jar-chain) downstream value
theorem, so the finding is graded off the print, never off prose.

KODO FLAG 1 (wording LOCKED, both chairs): whatever these prints show, the strongest
claim they can ever grant is "Quot.sound-FREE / computational at the value level;
[propext] remains provided." Quot.sound-absence is implemented-not-provided evidence ON
THE Quot.sound AXIS only; it is NOT "self-founded" — that word is reserved for the trunk
that actually re-grounds the provided basis.

Jar: not at risk — read-only; no existing file modified; warm oleans only re-elaborate
this probe. Ep1-16: not imported directly and not touched; the tripwire cannot fire. -/

/-! ## Site 1 — AlphaBoundMediant (the mediant: C=18, the count-3 bracket) -/

#print axioms Measurement.mediantC_is_eighteen
#print axioms Measurement.count3_bracket_ordered

/-! ## Site 2 — AlphaBFGS (the BFGS bracket) -/

#print axioms Measurement.AlphaBFGS.bfgs_bracket_ordered

/-! ## Site 3 — AlphaBoundCountToThree (the count-3 bound) -/

#print axioms Measurement.AlphaBoundCountToThree.bound_ordered

/-! ## Site 4 — ArchimedesPi (the π walls) -/

#print axioms Measurement.ArchimedesPi.measuredPiConvergent_is_22_over_7
#print axioms Measurement.ArchimedesPi.measured_pi_below_22_over_7
#print axioms Measurement.ArchimedesPi.measured_pi_above_223_over_71
#print axioms Measurement.ArchimedesPi.walls_nested_certified

/-! ## Site 5 — CalibrationTwoPaths (the jar readout ties): RESTORED post-fix -/

#print axioms Measurement.CalibrationTwoPaths.jar_alpha_pos
#print axioms Measurement.CalibrationTwoPaths.jar_readout_ties
#print axioms Measurement.CalibrationTwoPaths.jar_readout_drift_immune

/-! ## The jar read (the two paths, evaluated fresh at elaboration — not replayed) -/

#eval s!"jar direct_1to3   = {Measurement.CalibrationTwoPaths.direct_1to3}"
#eval s!"jar stepped_1to2to3 = {Measurement.CalibrationTwoPaths.stepped_1to2to3}"
