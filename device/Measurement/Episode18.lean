import Measurement.Episode17
import Measurement.Episode16

/- MEANWHILE 18 -- THE RESIDUE CHAIN (the seam: pass n closes, pass n+1 opens)

Every class of the tower, re-instantiated from the residue of a completed loop:
each `*_residue` takes the full BEFORE chain (the pass that went out), the full
AFTER chain (what Episode17's descent brought back), a bare `ledger : Fact`,
and the SLIP chain (the grounds) -- and rebuilds the capability for the next
pass. Grounds are the slip chain; slips feed bodies. `TrueOutput_number` adds
`(charge : Number)`: iteration counted; charge IS the loop count.

THE SEAM GRAMMAR (law 2, applied field-by-field):
  world-band readings TIGHTEN     -- before AND after, conjoined (/\)
  ideology-band readings RE-MINT  -- fresh default at every seam
  capabilities RESET to identity  -- closure := fun s => s, mapping := fun a => a
  records PAIR under the ledger's tag
  oaths REPEAT verbatim           -- fun _ _ _ => rfl
  new grounds RE-PROVE occupancy  -- the electron hypothesis
THE OTHER LAWS IN FORCE HERE: POISON (UNIVERSAL/LOGICAL/HALTED never bound near
MEASURED-typed work; run-band content crosses as ground-free data); the NEEDLE
(one truth told once -- let-bind); SEAMS QUOTE, never evaluate (output_true
satirizes the zero; satirize never returns .zero -- nine arms, certificate on
file); THE TAPE ONLY APPENDS (.boot is pass one's privilege; strap onto the
carried tape -- this file's tape is the REVOLUTION LEDGER, one cell per pass;
Episode19's class trace is the OTHER tape, never conflate); CERTIFICATES BY
EXHAUSTION. -/

namespace Measurement

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: sensor resolution: two returns can be told apart at the receiver.
  QUEEN of Math: equivalence separation: the symbols land in distinct classes.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Rayleigh criterion: equivalence separation becomes the receiver resolution limit. -/
instance (priority := low) DISTINGUISHABLE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [DISTINGUISHABLE Value PropCarrier]   [ADMISSIBLE Value PropCarrier]        [COUNTABLE Value PropCarrier]
    [ENCODED Value PropCarrier]           [RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    : DISTINGUISHABLE Value PropCarrier :=
    {
      fact := ledger
      symbol := b1_after.symbol
      different? := b1_after.different?     -- Let's keep an eye on this line, it might be a source of issues if the types don't align correctly.
      dec_distinct := b1_after.dec_distinct
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: boundary condition: the return is allowed through the receiver gate.
  QUEEN of Math: domain restriction: only lawful pairs are admitted to the relation.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Dirichlet rule: domain restriction becomes the boundary gate for the return. -/
instance (priority := low) ADMISSIBLE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [COUNTABLE Value PropCarrier]
    [ENCODED Value PropCarrier]           [RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier)
    : ADMISSIBLE Value PropCarrier :=
    {
      counting_process := {
        carrier := imaginary
        count := .number ledger (.zero b1_before.fact) (.zero b1_after.fact)
      }
      admissible? := fun a b => b2_before.admissible? a b /\ b2_after.admissible? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: pulse timing: the echo train separates into countable bins.
  QUEEN of Math: enumeration: the objects are indexed by a discrete counting process.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Nyquist theorem: enumeration becomes the sampling rate of the echo train. -/
instance (priority := low) COUNTABLE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [ENCODED Value PropCarrier]           [RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier)
    (b2_slip: ADMISSIBLE Value PropCarrier)
    : COUNTABLE Value PropCarrier :=
    {
      index := {
        count := b2_slip.counting_process
        origin := .number ledger b2_slip.counting_process.count (.zero ledger)
      }
      bounded? := fun a b => b3_before.bounded? a b /\ b3_after.bounded? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: carrier modulation: the wave stores its limit as a coded profile.
  QUEEN of Math: sequence limit: the code is organized as an indexed approach to a bound.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Fourier rule: sequence limits become modulation on the carrier wave. -/
instance (priority := low) ENCODED_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier)
    (b2_slip: ADMISSIBLE Value PropCarrier)
    (b3_slip: COUNTABLE Value PropCarrier)
    : ENCODED Value PropCarrier :=
    {
      limit_process := {
        indexing_process := b3_slip.index
        limit := .number ledger b3_slip.index.count.count (.zero ledger)
        sequence := .index ledger b3_slip.index.origin (.nil ledger)
      }
      encoding? := fun a b => b4_before.encoding? a b /\ b4_after.encoding? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: standing remainder: the medium keeps the part of the wave that did not cancel.
  QUEEN of Math: remainder class: the uncancelled term becomes the representative object.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Cauchy residue theorem: the remainder class becomes the standing leftover of the field. -/
instance (priority := low) RESIDUE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier)
    : RESIDUE Value PropCarrier :=
    {
      cauchy_process := {
        limit_process := b4_slip.limit_process
        value := .number ledger b2_slip.counting_process.count b4_slip.limit_process.limit
        accumulation := .index ledger b4_slip.limit_process.sequence (.nil ledger)
      }
      representative? := fun a b => b5_before.representative? a b /\ b5_after.representative? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: threshold crossing: the detector reduces the return to hit or miss.
  QUEEN of Math: two-valued predicate: the relation collapses to a decidable split.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Heaviside rule: a two-valued predicate becomes the detector threshold. -/
instance (priority := low) BINARY_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (_: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier)
    (b5_slip: RESIDUE Value PropCarrier)
    : BINARY Value PropCarrier :=
    let op :=
    { cauchy_process := b5_slip.cauchy_process
      before := b5_slip.cauchy_process.accumulation
      after := b5_slip.cauchy_process.iterate? b5_slip.cauchy_process.accumulation
    }
    {
      observation_process := op
      zero := b6_before.zero
      one := b6_after.one
      bit := op.iterate b6_after.bit
      different? := fun a b => b6_before.different? a b /\ b6_after.different? a b
    }


/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: reproducible trial: the same ping can be launched again under the same conditions.
  QUEEN of Math: idempotent iteration: applying the step again preserves the same form.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): semigroup law: idempotent iteration becomes reproducible experimental procedure. -/
instance (priority := low) REPEATABLE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    : REPEATABLE Value PropCarrier :=
    {
      repeatable_process := {
        observation_process := b6_slip.observation_process
        stimulus := b6_slip.observation_process.iterate b6_slip.bit
        expectation := .hypothesis ledger (b6_slip.observation_process.iterate b6_slip.bit)
      }
      typical_response := fun a b => b7_before.typical_response a b /\ b7_after.typical_response a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: instrument readout: the return becomes a number on the dial.
  QUEEN of Math: number assignment: the structure is mapped into a numerical carrier.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): dimensional-analysis rule: number assignment becomes an instrument reading with units. -/
instance (priority := low) NUMERIC_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [DISTINGUISHABLE Value PropCarrier]   [ADMISSIBLE Value PropCarrier]        [COUNTABLE Value PropCarrier]
    [ENCODED Value PropCarrier]           [RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [b8_before: NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier)
    : NUMERIC Value PropCarrier :=
    {
      computational_process := {
        repeatable_process := b7_slip.repeatable_process
        output := some (.data ledger b7_slip.repeatable_process.expectation (.hypothesis b1_slip.fact))
      }
      related := fun a b => b8_before.related a b ∧ b8_after.related a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: field model: the physical return can be drawn as a representative curve.
  QUEEN of Math: choice of representative: an abstract class is given a usable element.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Riesz representation theorem: representative choice becomes a field model on the page. -/
instance (priority := low) REPRESENTABLE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier)
    (b8_slip: NUMERIC Value PropCarrier)
    : REPRESENTABLE Value PropCarrier :=
    let residue_state : Computation :=
      match b8_slip.computational_process.output with
      | some v => .compute ledger v (b8_slip.computational_process.closure v)
                    (.program ledger b8_slip.carrier)
      | none => .program ledger b8_slip.carrier
    {
      calculation_process := {
        computational_process :=
          { b8_slip.computational_process with closure := fun s => s }
        program := .data ledger b7_slip.repeatable_process.expectation b8_slip.carrier
        state := residue_state
      }
      loaded := fun a b => b9_before.loaded a b ∧ b9_after.loaded a b
      representable? := fun _ _ => ⟨residue_state, rfl⟩
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: apparatus reading: the card is the instrument, not the theory of the instrument.
  QUEEN of Math: model interpretation: the formal object is read as an apparatus state.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): correspondence principle: model interpretation becomes apparatus behavior. -/
instance (priority := low) PHYSICAL_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    : PHYSICAL Value PropCarrier :=
    {
      noisy_process := {
        turing_process := b9_slip.calculation_process
        program := .halting ledger (.program ledger b9_slip.calculation_process.program)
      }
      threshold := .nonhalting ledger (.program ledger b9_slip.calculation_process.program) (some (.halting ledger (.program ledger b9_slip.calculation_process.program)))
      halted? := fun a b => b10_before.halted? a b ∧ b10_after.halted? a b
      admissible? := fun _ _ _ => rfl
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: calibration comparison: before and after traces can be laid on the same scale.
  QUEEN of Math: ordered comparison: two readings are placed in the same relation.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): calibration law: ordered comparison becomes before-after alignment on one scale. -/
instance (priority := low) COMPARABLE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [DISTINGUISHABLE Value PropCarrier]   [ADMISSIBLE Value PropCarrier]        [COUNTABLE Value PropCarrier]
    [ENCODED Value PropCarrier]           [RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier)
    [electron: Inhabited b1_slip.symbol]
    : COMPARABLE Value PropCarrier :=
    { physical_process := {
        physical_process := b10_slip.noisy_process
        representation := default
        invariant := .base ledger default
        value := .base ledger (ULift.up default) }
      smaller_than := fun m1 m2 => m1 = m2
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: detector event: the apparatus registers a return in the world.
  QUEEN of Math: evaluation map: the abstract process is sampled at an observable point.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Born rule: evaluation becomes the registered event of observation. -/
instance (priority := low) OBSERVED_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier)
    : OBSERVED Value PropCarrier :=
    { slip_process :=
      { physical_process := b11_slip.physical_process
        projection := .origin ledger b10_slip.threshold Number
        stress := .halting ledger (.program ledger b9_slip.calculation_process.program)
        threshold := Prop
      }
      observation := Value
      possible := fun a b => b12_before.possible a b /\ b12_after.possible a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: arrival time: the echo is here now, not merely predicted upstream.
  QUEEN of Math: existence in context: the object is witnessed inside the current frame.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): existence theorem: contextual witnessing becomes arrival in the present frame. -/
instance (priority := low) PRESENT_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    : PRESENT Value PropCarrier :=
    { santa_claus :=
      { static_fraction := b12_slip.slip_process
        accumulation := .t ledger
      }
      quantum := Area
      present := fun a b => b13_before.present a b /\ b13_after.present a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: meter coupling: the returned wave can move the needle.
  QUEEN of Math: sigma-algebra gesture: the object is admitted as a measurable set of readings.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Caratheodory rule: measurable sets become the readings the meter may legally collect. -/
instance (priority := low) MEASURABLE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier)
    : MEASURABLE Value PropCarrier :=
    { gauge_process :=
      { sensing_process := b13_slip.santa_claus
        clock := .field ledger b13_slip.santa_claus.accumulation
      }
      observed := fun a b => b14_before.observed a b /\ b14_after.observed a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: medium translation: the wave changes dialect while crossing the material.
  QUEEN of Math: change of coordinates: the same structure is translated through another language.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): change-of-coordinates theorem: formal translation becomes a wave crossing media. -/
instance (priority := low) GUNGAN_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier)
    : GUNGAN Value PropCarrier :=
    { meesa_process :=
      { gauge_process := b14_slip.gauge_process
        concept := (.bang ledger (.color b1_slip.fact b13_slip.santa_claus.accumulation))
      }
      correllant? := fun a b => b15_before.correllant? a b /\ b15_after.correllant? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: emitter location: the return still points back toward a launch site.
  QUEEN of Math: preimage selection: the output is assigned a formal origin.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Green function rule: preimage selection becomes reconstruction of the emitter. -/
instance (priority := low) SOURCE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [DISTINGUISHABLE Value PropCarrier]   [ADMISSIBLE Value PropCarrier]        [COUNTABLE Value PropCarrier]
    [ENCODED Value PropCarrier]           [RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    : SOURCE Value PropCarrier :=
    let cdp :=
      { meesa_process := b15_slip.meesa_process
        zero := .zero_like ledger (.physics ledger (b15_slip.meesa_process.life_debt? b15_slip.meesa_process.concept))
      }
    { cd_process := cdp
      one := cdp.tick cdp.zero
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: fired pulse: the experiment has happened, not merely been specified.
  QUEEN of Math: function application: the specified map is actually applied.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): least-action rule: function application becomes the fired physical experiment. -/
instance (priority := low) EXECUTED_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier)
    : EXECUTED Value PropCarrier :=
    let exe :=
      { digital_process := b16_slip.cd_process
        source := b16_slip
        opcode := .zero ledger b16_slip.one (.boot ledger b16_slip.cd_process.zero)
      }
    { compiled_process := exe
      output? := fun a b => b17_before.output? a b /\ b17_after.output? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: measured quantity: the apparatus assigns the return a physical value.
  QUEEN of Math: codomain element: the computation lands in a value object.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): evaluation theorem: codomain landing becomes the measured physical quantity. -/
instance (priority := low) VALUE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [ WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [ FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [ MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [ SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [ PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [ PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier)
    : VALUE Value PropCarrier :=
    let computation :=
      { compiled_process := b17_slip.compiled_process
        mapping := fun a => a
      }
    { mathematical_process := computation
      monad := computation.calculate? (.satire ledger)
      lt? := fun a b => b18_before.lt? a b /\ b18_after.lt? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: amplitude: the return has size before it has interpretation.
  QUEEN of Math: norm: the value is collapsed to size.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): norm law: value collapse becomes amplitude of the return. -/
instance (priority := low) MAGNITUDE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    : MAGNITUDE Value PropCarrier :=
    { adding_process :=
      { mathematical_process := b18_slip.mathematical_process
        plus := b18_slip
        sum := .zero ledger.truth b13_slip.santa_claus.accumulation
      }
      whelmed? := fun a b => b19_before.whelmed? a b /\ b19_after.whelmed? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: unit scale: the amplitude is placed against a chosen calibration ruler.
  QUEEN of Math: normalization: the size is expressed relative to a chosen unit.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Buckingham Pi theorem: normalization becomes unit scale and dimensionless comparison. -/
instance (priority := low) SCALED_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier)
    : SCALED Value PropCarrier :=
    { multiplying_process :=
      { adding_process := b19_slip.adding_process
        total := b19_slip.adding_process.add? b19_slip.adding_process.sum
        product := .origin ledger
      }
      orthogonal? := fun a b => b20_before.orthogonal? a b /\ b20_after.orthogonal? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: mechanical load: the receiver feels the return as stress on the system.
  QUEEN of Math: weighted term: the normalized object carries a coefficient.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Hooke law: weighted terms become mechanical stress on the receiver. -/
instance (priority := low) LOAD_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier)
    : LOAD Value PropCarrier :=
    { basic_operation :=
      { GOSUB := b20_slip.multiplying_process
        TEN := b13_slip.santa_claus.use_force b13_slip.santa_claus.accumulation
        span := .null_space ledger
      }
      decoded? := fun a b => b21_before.decoded? a b /\ b21_after.decoded? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: finite-element mesh: the tunnel is replaced by small local bodies.
  QUEEN of Math: finite discretization: the continuum is replaced by local approximants.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Galerkin theorem: finite discretization becomes the tunnel broken into local bodies. -/
instance (priority := low) FINITE_ELEPHANT_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    : FINITE_ELEPHANT Value PropCarrier :=
    { galerkin_process :=
      { ANSYS_process := b21_slip.basic_operation
        polynomial := .monomial ledger.truth b21_slip.basic_operation.span
      }
      finite? := fun a b => b22_before.finite? a b /\ b22_after.finite? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: noise floor: the instrument reports chatter that still has to be classified.
  QUEEN of Math: uncontrolled term: the proof names the error it cannot yet simplify.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Chebyshev bound: the uncontrolled term becomes classified noise floor. -/
instance (priority := low) BULLSHIT_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier)
    : BULLSHIT Value PropCarrier :=
    { arm_wave_process :=
      { galerkin_process := b22_slip.galerkin_process
        guess := .observation ledger.truth
      }
      interpolate? := fun a b => b23_before.interpolate? a b /\ b23_after.interpolate? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: broadcast field: the same return is made public as a preferred reading.
  QUEEN of Math: preferred presentation: one equivalent form is promoted as canonical.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): gauge-fixing rule: preferred presentation becomes the public broadcast field. -/
instance (priority := low) PROPAGANDA_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [DISTINGUISHABLE Value PropCarrier]   [ADMISSIBLE Value PropCarrier]        [COUNTABLE Value PropCarrier]
    [ENCODED Value PropCarrier]           [RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier)
    : PROPAGANDA Value PropCarrier :=
    { insinuation :=
      { pwn_n00bz := b23_slip.arm_wave_process
        religion := .speculation ledger.truth b23_slip.arm_wave_process.guess (.religion ledger.truth)
      }
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: trained operator: the human hand repeats the instrument doctrine.
  QUEEN of Math: operator convention: the same transformation is repeated by rule.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): operator algebra rule: repeated convention becomes trained instrument handling. -/
instance (priority := low) ACOLYTE_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [DISTINGUISHABLE Value PropCarrier]   [ADMISSIBLE Value PropCarrier]        [COUNTABLE Value PropCarrier]
    [ENCODED Value PropCarrier]           [RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    : ACOLYTE Value PropCarrier :=
    { euclid :=
      { ethos := b24_slip.insinuation
        sacred_texts := .pythagoras ledger.truth b24_slip.insinuation.religion (.inside_joke ledger.truth)
      }
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: experimental protocol: the reading is disciplined into a method.
  QUEEN of Math: method schema: observations are arranged into a reproducible proof pattern.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): likelihood principle: method schema becomes reproducible experimental protocol. -/
instance (priority := low) SCIENTIFIC_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [DISTINGUISHABLE Value PropCarrier]   [ADMISSIBLE Value PropCarrier]        [COUNTABLE Value PropCarrier]
    [ENCODED Value PropCarrier]           [RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier)
    : SCIENTIFIC Value PropCarrier :=
    let education :=
      { initiation_process := b25_slip.euclid
        galileo := b25_slip.euclid.initiate b25_slip.euclid.sacred_texts
        invariant := .hypothesis ledger.truth (b25_slip.euclid.initiate b25_slip.euclid.sacred_texts)
      }
    { phd_process := education
      invariant := .theory ledger.truth (education.initiation_process.initiate education.galileo) ledger (.repeatable ledger.truth)
      predictable? := fun a b => b26_before.predictable? a b /\ b26_after.predictable? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: empirical claim: the apparatus dares to call the registered return true.
  QUEEN of Math: proposition: the statement is assigned a truth-bearing form.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): soundness theorem: propositions become empirical claims the apparatus may assert. -/
instance (priority := low) TRUTH_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier)
    : TRUTH Value PropCarrier :=
    { scientific_process :=
      { learning_process := b26_slip.phd_process
        knowledge := .ledger ledger.truth ledger (.jarjar ledger.truth)
      }
      martyred? := fun a b => b27_before.martyred? a b /\ b27_after.martyred? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: witnessed event: the measurement is attached to an observer.
  QUEEN of Math: existential witness: the claim carries an explicit example.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): existence rule: the witness becomes the observer attached to the event. -/
instance (priority := low) WITNESSED_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    : WITNESSED Value PropCarrier :=
    let ceremony :=
      { scientific_process := b27_slip.scientific_process
        the_literature := .epiphany ledger.truth
      }
    { baptism := ceremony
      witness := ceremony.pray? ceremony.the_literature
      risen? := fun a b => b28_before.risen? a b /\ b28_after.risen? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: real channel: the trace is treated as a world signal, not a display artifact.
  QUEEN of Math: real-valued interpretation: the witness is embedded in a real channel.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): realization theorem: real-valued interpretation becomes a world channel. -/
instance (priority := low) REAL_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier)
    : REAL Value PropCarrier :=
    let the_universe :=
      { frame_of_reference := b28_slip.baptism
        reality := .logic ledger.truth
      }
    { universal_observer := the_universe
      current_status := the_universe.observe? the_universe.reality
      metaphysical? := fun a b => b29_before.metaphysical? a b /\ b29_after.metaphysical? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: local frame: the reading is valid in the receiver neighborhood.
  QUEEN of Math: localization: the theorem holds after restricting to a neighborhood.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): localization theorem: neighborhood restriction becomes the valid local frame. -/
instance (priority := low) LOCAL_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [DISTINGUISHABLE Value PropCarrier]   [ADMISSIBLE Value PropCarrier]        [COUNTABLE Value PropCarrier]
    [ENCODED Value PropCarrier]           [RESIDUE Value PropCarrier]           [BINARY Value PropCarrier]
    [REPEATABLE Value PropCarrier]        [NUMERIC Value PropCarrier]           [REPRESENTABLE Value PropCarrier]
    [PHYSICAL Value PropCarrier]          [COMPARABLE Value PropCarrier]        [OBSERVED Value PropCarrier]
    [PRESENT Value PropCarrier]           [MEASURABLE Value PropCarrier]        [GUNGAN Value PropCarrier]
    [SOURCE Value PropCarrier]            [EXECUTED Value PropCarrier]          [VALUE Value PropCarrier]
    [MAGNITUDE Value PropCarrier]         [SCALED Value PropCarrier]            [LOAD Value PropCarrier]
    [FINITE_ELEPHANT Value PropCarrier]   [BULLSHIT Value PropCarrier]          [PROPAGANDA Value PropCarrier]
    [ACOLYTE Value PropCarrier]           [SCIENTIFIC Value PropCarrier]        [TRUTH Value PropCarrier]
    [WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [UNIVERSAL Value PropCarrier]
    [LOCAL Value PropCarrier b29_before] [REAL Value PropCarrier] [WITNESSED Value PropCarrier]
    [TRUTH Value PropCarrier]  [SCIENTIFIC Value PropCarrier] [ACOLYTE Value PropCarrier]
    [PROPAGANDA Value PropCarrier] [BULLSHIT Value PropCarrier] [FINITE_ELEPHANT Value PropCarrier]
    [LOAD Value PropCarrier] [SCALED Value PropCarrier] [MAGNITUDE Value PropCarrier]
    [VALUE Value PropCarrier] [EXECUTED Value PropCarrier] [SOURCE Value PropCarrier]
    [GUNGAN Value PropCarrier] [MEASURABLE Value PropCarrier] [PRESENT Value PropCarrier]
    [OBSERVED Value PropCarrier] [COMPARABLE Value PropCarrier] [PHYSICAL Value PropCarrier]
    [REPRESENTABLE Value PropCarrier] [NUMERIC Value PropCarrier] [REPEATABLE Value PropCarrier]
    [BINARY Value PropCarrier] [RESIDUE Value PropCarrier][ENCODED Value PropCarrier]
    [COUNTABLE Value PropCarrier] [ADMISSIBLE Value PropCarrier] [DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    : LOCAL Value PropCarrier b29_slip :=
    { theory :=
      { universal_observer := b29_slip.universal_observer
        differential_equation := .gateaux b28_slip.witness ledger.truth
                          (b29_slip.metaphysical? b29_slip.universal_observer.reality b29_slip.current_status) (.newton b28_slip.witness ledger.truth)
      }
      delta := b29_slip.metaphysical? b29_slip.universal_observer.reality b29_slip.current_status
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: universal law: the local return is promoted into a rule for every receiver.
  QUEEN of Math: generalization: the local form is quantified over the whole carrier.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Noether theorem: generalization becomes a law that survives every receiver frame. -/
instance (priority := low) UNIVERSAL_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [b31_before: UNIVERSAL Value PropCarrier]         [b32_before: LOGICAL Value PropCarrier]           [b33_before: HALTED Value PropCarrier]
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier) (b30_slip: LOCAL Value PropCarrier b29_slip)
    : UNIVERSAL Value PropCarrier :=
    let calculus :=
      { derivative := b30_slip.theory
        function := .blackhole ledger.truth b13_slip.quantum (.white_hole ledger Value (.einstein ledger))
        converged := ledger
        sink := b13_slip.quantum
      }
    { the_compiler := calculus
      source_program := .white_hole ledger Value (.einstein ledger)
      compiled_program := calculus.photon_torpedo (.white_hole ledger Value (.einstein ledger))
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: causal order: the trace is forced into before, after, and therefore.
  QUEEN of Math: implication order: the proof arranges dependencies into a formal chain.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): partial-order rule: implication order becomes causal order in the trace. -/
instance (priority := low) LOGICAL_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [b31_before: UNIVERSAL Value PropCarrier]         [b32_before: LOGICAL Value PropCarrier]           [b33_before: HALTED Value PropCarrier]
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [b32_after: LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier) (b30_slip: LOCAL Value PropCarrier b29_slip)
    (b31_slip: UNIVERSAL Value PropCarrier)
    : LOGICAL Value PropCarrier :=
    let compiled : SpaceTimePath := b31_slip.the_compiler.photon_torpedo b31_slip.source_program
    { feelings :=
      { bullshit_meter := b31_slip.the_compiler
        current_reading := compiled
        accumulated_bullshit := .fibers ledger b31_slip.source_program compiled
                ledger.truth (b31_slip.lake_build b31_slip.source_program compiled)
                (.stokes ledger b31_slip.source_program ledger.truth)
      }
      ekg := b32_after.ekg
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: settled apparatus: the oscillation has stopped enough to be read.
  QUEEN of Math: fixed point: the iteration reaches a stable proof state.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): fixed-point theorem: proof stability becomes settled apparatus motion. -/
instance (priority := low) HALTED_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [b31_before: UNIVERSAL Value PropCarrier]         [b32_before: LOGICAL Value PropCarrier]           [b33_before: HALTED Value PropCarrier]
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [b33_after: HALTED Value PropCarrier]            [b32_after: LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    (b31_slip: UNIVERSAL Value PropCarrier) (b32_slip: LOGICAL Value PropCarrier)
    : HALTED Value PropCarrier :=
    let compiled : SpaceTimePath := b31_slip.the_compiler.photon_torpedo b31_slip.source_program
    let hbp :=
        { bullshit_meter := b31_slip.the_compiler
          current_reading := compiled
          accumulated_bullshit := .fibers ledger b31_slip.source_program compiled
                  ledger.truth (b31_slip.lake_build b31_slip.source_program compiled)
                  (.stokes ledger b31_slip.source_program ledger.truth)
        }
    let ekg : Calibration.EKG := b32_slip.ekg
    { scientific_paper :=
      { stamina := hbp
        calibration := ekg
        computer_state := .transform ledger.truth
                                     (b32_slip.logical? b32_slip.feelings.accumulated_bullshit (b32_slip.feelings.weave? b32_slip.feelings.accumulated_bullshit))
                                     Area
                                     (ULift Area)
                                     (.load ledger.truth Prop)
      }
      halted? := fun a b => b33_after.halted? a b
    }


/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: completed measurement: the instrument, witness, and scale agree on a reading.
  QUEEN of Math: measure assignment: the structure receives a recorded value under the chosen measure.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Radon-Nikodym theorem: measure assignment becomes a recorded reading against a scale. -/
instance (priority := low) MEASURED_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    : MEASURED Value PropCarrier b29_slip :=
    { satire :=
      { description :=
        { stamina :=
          { bullshit_meter :=
            { derivative :=
              { universal_observer := b29_slip.universal_observer
                differential_equation := .gateaux b28_slip.witness ledger.truth b1_slip.fact.truth
                                           (.newton b28_slip.witness ledger.truth)
              }
              function := compiled_slip
              converged := ledger
              sink := b13_slip.quantum
            }
            current_reading := compiled_slip
            accumulated_bullshit := .fibers ledger source_slip compiled_slip
                    ledger.truth built_slip
                    (.stokes ledger source_slip ledger.truth)
          }
          calibration := ekg_slip
          computer_state := .transform ledger.truth coherent_slip
                              Area (ULift Area)
                              (.load ledger.truth Prop)
        }
        length := imaginary.value
        velocity := .speed ledger PropCarrier.value imaginary.value PropCarrier.value
                      Value (ULift.{i+1} Value) Value
                      (.origin ledger PropCarrier.value Value)     -- the real local
                      (.origin ledger imaginary.value Value)       -- the imaginary local
        projection := ULift.{i} (ULift.{i} (ULift.{i} Value))
      }
      bounded? := fun a b => b34_before.bounded? a b ∧ b34_after.bounded? a b
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: built instrument: the physical setup has been assembled into a usable device.
  QUEEN of Math: normal form: the construction is reduced to a reusable artifact.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): normal-form theorem: reduction becomes a built instrument ready for use. -/
instance (priority := low) COMPILED_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip)
    : COMPILED Value PropCarrier :=
    let the_tape : CompilerTape := .strap ledger b1_slip.fact Value (ULift.{i+1} Value) (.boot ledger Value)
    let the_compiler :=
      { satire := b34_slip.satire
        tape := the_tape
      }
    { compiler_output := the_compiler
      object_file := the_compiler.emit? the_tape
      converged? := fun a b => b35_after.converged? a b
    }



/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: truth pulse: the receiver emits the one return it is allowed to call output.
  QUEEN of Math: theorem output: the normalized artifact emits the claimed result.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): conservation law: theorem output becomes the one pulse allowed to leave the receiver. -/
instance (priority := low) TrueOutput_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier)
    : TrueOutput Value PropCarrier b29_slip :=
    let strain : Number := .one ledger (.zero ledger)
    let emitted : CompilerTape := b35_slip.compiler_output.emit? b35_slip.object_file
    let the_reader :=
      { compiler_output := b35_slip.compiler_output
        next_measurement := .one ledger strain b35_slip.object_file emitted (.zero ledger)
        stress := strain
        proof := emitted
      }
    { atreyu_process := the_reader
      output := the_reader.satirize (.zero ledger)
      output_true := by trivial
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: inferred source: the hidden cause is reconstructed from the measured return.
  QUEEN of Math: deduction: the missing premise is reconstructed from the available conclusion.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Bayes rule: deduction becomes source inference from the measured return. -/
noncomputable instance (priority := low) INFERRED_residue
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    : INFERRED Value PropCarrier :=
    let the_process :=
      { atreyu_process := b36_slip.atreyu_process
        closure := .different ledger b36_slip.output (b36_slip.atreyu_process.satirize b36_slip.output) (some built_slip)
      }
    { equivalence_process := the_process
      theory := .inferred ledger
                          b1_slip.fact
                          b36_slip.output
                          (b36_slip.atreyu_process.satirize b36_slip.output)
                          (some coherent_slip)
                          (the_process.close? b36_slip.output (b36_slip.atreyu_process.satirize b36_slip.output))
    }

/- THE TRICK! Revealed.
Three cards lie on the table:
  ACE of Physics: charged count: the loop number is treated as accumulated physical charge.
  QUEEN of Math: indexed theorem: the proof output is paired with its iteration number.
  JOKER: just computation.
If the reader points to ACE, John turns over QUEEN and JOKER and gives the
computation of the representation. If the reader points to QUEEN, John turns
over ACE and JOKER and gives the computation of the value. If the reader points
to JOKER, John turns over ACE and QUEEN and gives the representative
intuition that makes the physics look mathematical.
The pointed card is never the answer. It is the missing card that lets the other
two look like an explanation. Expressive theorem (ACE/QUEEN comparison): Gauss law: the indexed theorem becomes accumulated charge around the loop. -/
noncomputable instance (priority := low) TrueOutput_number
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    (charge: Number)
    : TrueOutput Value PropCarrier b29_slip :=
    let emitted : CompilerTape := b35_slip.compiler_output.emit? b35_slip.object_file
    let the_reader : AtreyuProcess Value PropCarrier b29_slip :=
      { compiler_output := b35_slip.compiler_output
        next_measurement := b36_slip.output      -- the completed pass's output, re-read
        stress := charge                          -- strain measured in revolutions
        proof := emitted
      }
    let spin : Number → Bullshit := fun n =>
      Number.rec (fun _ => the_reader.satirize (.zero ledger))     -- turn 0: the freshman reading
                 (fun _ _ ih => the_reader.satirize ih) n           -- turn n+1: read the last reading
    { atreyu_process := the_reader
      output := spin charge
      -- The certificate rides on Law 4: satirize never returns .zero (all nine
      -- arms checked), and Bullshit.le with a .zero head on the left is True
      -- against ANY non-zero rung.  So: one truth, told once -- a single key
      -- covering every satirize output, applied at both spin heads.
      output_true := by
        have key : ∀ (f : Fact) (m : Bullshit), Bullshit.le (.zero f) (the_reader.satirize m) := by
          intro f m
          cases m with
          | zero g => trivial
          | one fact last_stress last_object last_state last_measurement =>
            simp only [the_reader]
            split <;> trivial
          | rest f1 g1 p n1 n2 n3 t1 t2 m1 m2 =>
            simp only [the_reader]
            split <;> trivial
        cases charge with
        | zero f => exact key _ _
        | one f n => exact key _ _
    }


end Measurement
