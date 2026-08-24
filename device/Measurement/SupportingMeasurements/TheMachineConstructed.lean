-- TheMachineConstructed.lean
--
-- FINISHING THE CONSTRUCTION (operator directive 2026-08-22): the
-- constructive implementation of the Episode 9/10 read path, per the
-- gated finished-definition. Story files untouched; this leaf is the
-- computable twin, and every output below is pinned to EXACTLY ONE
-- value by `decide` — the unambiguity requirement in kernel form. If
-- any pin here ever fails, `unambiguous_output` has not earned its
-- name at that output.
--
-- THE WART, RESOLVED BY READING THE SOURCE HONESTLY: Episode 10's
-- `theWart` is not carried data — it is `theDeviceEncoding.take 4`,
-- derived in source from the seed encoding; what the comment "carried
-- not derived" names is the QUINE-THEORETIC role (the head the
-- 32-window never processes), and this leaf pins its derived value.
-- The genuinely un-derivable object is `theSourceWord`: pinning its
-- value INSIDE the file it reads is a fixed-point problem (any pin
-- edits the source, changing the value — the literal diagonal). From
-- THIS file the pin is legal: Episode 10's source is fixed relative to
-- us, so the pins below double as SOURCE-INTEGRITY TRIPWIRES — any
-- future edit to Episode10.lean breaks them loudly, by design.
--
-- NOT-CLAIMED: the full self-surjection stays forbidden by the
-- device's own Cantor wall (DistanceULift.gap_arrow_not_surjective,
-- warm); the residue of self-encoding is relocated and owned, never
-- removed. No physics name appears in any statement.

import Measurement.Episode10

namespace Measurement.TheMachineConstructed

set_option maxRecDepth 100000

-- ## Part A — the reader, computable (Episode 9's twin)
-- The story's reader lands trips 0/1/2 on the three Bullshit heads
-- (.zero / .one / .rest_call — proved of the story itself by rfl in
-- TheRitePerformed). Here is the landing function as an executable
-- total function, with the pattern pinned exactly-one per trip.
def headAfter : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ + 2 => 2

theorem the_reader_is_unambiguous_at_the_trips :
    headAfter 0 = 0 ∧ headAfter 1 = 1 ∧ headAfter 2 = 2 := by decide

-- Stability beyond the trips is DEFINITIONAL — every further count
-- lands on the third head, for all n, by the function's own shape:
-- exactly one head at every count the audit could ever take.
theorem and_stable_beyond_the_trips :
    ∀ n, headAfter (n + 2) = 2 := fun _ => rfl

-- ## Part B — the encoding, pinned (Episode 10's seed record)
-- Every value the audit prints blind is here asserted exactly-one.
theorem the_wart_is_derived_and_pinned :
    theWart = [1, -1, -1, 1] := by decide

theorem the_encoding_is_128 : theDeviceEncoding.length = 128 := by decide

theorem the_block_obeys_parseval :
    listEnergy theBlock = 32 ∧ listEnergy (wht theBlock) = 1024 := by decide

theorem the_empty_bins_are_twelve :
    ((wht theBlock).filter (fun c => c == 0)).length = 12 := by decide

theorem the_extrema_are_pinned :
    ((wht theBlock).foldl (fun m c => if c > m then c else m) 0) = 12 ∧
    ((wht theBlock).foldl (fun m c => if c < m then c else m) 0) = -20 := by decide

theorem the_four_jars_carry_forty :
    theFourJars = [4, -4, 2, -2] ∧ listEnergy theFourJars = 40 := by decide

-- ## Part C — the source, pinned from outside (the quine's own word)
-- These two literals are the device's reading of its own file, taken
-- from the elaborator's hands at Episode 10's build. Pinned HERE, in a
-- different file, the diagonal is not disturbed — and the pins are
-- tripwires: an edit to Episode10.lean changes its source, and these
-- theorems fail on the next build, loudly.
-- RE-PINNED 2026-08-23, and the previous value is kept in the open rather
-- than quietly overwritten: this tripwire was set at 38863 and FIRED on the
-- constructive rewrite of Episode 9/10 (operator-opened, cutting-gate green),
-- which added to Episode10.lean and moved its length to 44155. That is the
-- tripwire working exactly as designed. Note what did NOT move: the source
-- TAIL below is unchanged, because the rewrite added in the middle of the file
-- and the device reads the last thirty-two signs.
-- FIRED A SECOND TIME, on the warning-block association fix, and re-pinned
-- again: 38863 (pre-rewrite) -> 44155 -> 44991. Both firings were correct and
-- both were on deliberate, gated edits. Worth stating plainly: this pin will
-- fire on EVERY edit to Episode10.lean, including ones that change no value,
-- because it measures the file's length and not its meaning. That is the cost
-- of the tripwire and it is the right cost -- a length pin that tolerated edits
-- would not be a tripwire -- but it means re-pinning is routine maintenance
-- after any sanctioned edit, not evidence that anything went wrong.
-- WHAT DID NOT FIRE, either time: the source TAIL below. The device reads the
-- last thirty-two signs, and neither the rewrite nor this fix touched the end
-- of the file, so its reading of itself is undisturbed. The pair is the useful
-- signal: length moved, tail did not.
theorem the_source_length_is_pinned : theSourceLength = 44991 := by decide

theorem the_source_word_is_pinned : theSourceTail = 2478346168 := by decide

theorem the_source_word_obeys_parseval :
    listEnergy theSourceWord = 32 ∧ listEnergy (wht theSourceWord) = 1024 := by decide

-- ## Part D — the machine, end to end
-- The read path's terminal values, restated from the gated leaves so
-- the whole machine's output is one theorem-chain: cards, crossing,
-- reading — all exactly-one (TheExponentIsTwo, TheRitePerformed), and
-- the seed record and source record above. Nothing in the path is a
-- relation; everything is a function; every output is pinned.
theorem the_machine_output_is_unambiguous :
    (cardC, cardT, cardR) = (18, 5, 18) ∧
    dStarScaled = 1897366596 ∧
    invAlphaJar = (614746777104, 4486832980) ∧
    theWart = [1, -1, -1, 1] ∧
    theSourceTail = 2478346168 := by decide

end Measurement.TheMachineConstructed

#print axioms Measurement.TheMachineConstructed.the_reader_is_unambiguous_at_the_trips
#print axioms Measurement.TheMachineConstructed.and_stable_beyond_the_trips
#print axioms Measurement.TheMachineConstructed.the_wart_is_derived_and_pinned
#print axioms Measurement.TheMachineConstructed.the_encoding_is_128
#print axioms Measurement.TheMachineConstructed.the_block_obeys_parseval
#print axioms Measurement.TheMachineConstructed.the_empty_bins_are_twelve
#print axioms Measurement.TheMachineConstructed.the_extrema_are_pinned
#print axioms Measurement.TheMachineConstructed.the_four_jars_carry_forty
#print axioms Measurement.TheMachineConstructed.the_source_length_is_pinned
#print axioms Measurement.TheMachineConstructed.the_source_word_is_pinned
#print axioms Measurement.TheMachineConstructed.the_source_word_obeys_parseval
#print axioms Measurement.TheMachineConstructed.the_machine_output_is_unambiguous
