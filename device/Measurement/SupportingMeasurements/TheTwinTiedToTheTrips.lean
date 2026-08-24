-- TheTwinTiedToTheTrips.lean
--
-- R6, second half: the TIE.  `TheReadPathTwin` computes the head ladder, but
-- on its own it does not prove the STORY's reader takes those steps -- the
-- reader's `gawk_at` is a structure field with a default, so a reader could
-- supply another.  This leaf closes that gap at the only place it can be
-- closed honestly: on the DEFAULT itself, which is what Episode 9's trips get
-- when they build their readers with the field omitted.
--
-- Nothing here edits Episode 9.  The tie is a theorem, not an edit.

import Measurement.Episode4
import Measurement.SupportingMeasurements.TheReadPathTwin

namespace Measurement.TheTwinTiedToTheTrips

open Measurement.TheReadPathTwin

variable {Box : Type u}
variable {Pigeon : CarrierProcess Box}
variable {nowtrino : DISTINGUISHABLE Box Pigeon}
variable {i0 : ADMISSIBLE Box Pigeon} {i1 : COUNTABLE Box Pigeon}
variable {i2 : ENCODED Box Pigeon} {i3 : RESIDUE Box Pigeon}
variable {i4 : BINARY Box Pigeon} {i5 : REPEATABLE Box Pigeon}
variable {i6 : NUMERIC Box Pigeon} {i7 : REPRESENTABLE Box Pigeon}
variable {i8 : PHYSICAL Box Pigeon} {i9 : COMPARABLE Box Pigeon}
variable {i10 : OBSERVED Box Pigeon} {i11 : PRESENT Box Pigeon}
variable {i12 : MEASURABLE Box Pigeon} {i13 : GUNGAN Box Pigeon}
variable {i14 : SOURCE Box Pigeon} {i15 : EXECUTED Box Pigeon}
variable {i16 : VALUE Box Pigeon} {i17 : MAGNITUDE Box Pigeon}
variable {i18 : SCALED Box Pigeon} {i19 : LOAD Box Pigeon}
variable {i20 : INDEXOFANT Box Pigeon} {i21 : BULLSHIT Box Pigeon}
variable {i22 : PROPAGANDA Box Pigeon} {i23 : ACOLYTE Box Pigeon}
variable {i24 : SCIENTIFIC Box Pigeon} {i25 : TRUTH Box Pigeon}
variable {i26 : WITNESSED Box Pigeon} {i27 : REAL Box Pigeon}
variable {quantum : LOCAL Box Pigeon} {gravity : UNIVERSAL Box Pigeon quantum}
variable {i28 : LOGICAL Box Pigeon quantum gravity} {i29 : HALTED Box Pigeon quantum gravity}
variable {i30 : MEASURED Box Pigeon quantum gravity} {i31 : COMPILED Box Pigeon quantum gravity}

/-- THE TIE.  One gawk by the reader's OWN default advances the head exactly
as the twin's `stepHead` says, for every reading and every payload.  The four
`decTruth` branches of each arm are stepped through and every one of them
returns the same constructor: the head selection never consults the truth
values.  This is what makes a head-only twin faithful rather than convenient. -/
theorem the_default_gawk_steps_the_head
    (book : CompilerOutput Box Pigeon quantum gravity)
    (a_constant : Bullshit) (page total : Number) (tape : CompilerTape)
    (b : Bullshit) :
    headOf (@AtreyuProcess.gawk_at._default Box Pigeon nowtrino
              i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15
              i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27
              quantum gravity i28 i29 i30 i31
              book a_constant page total tape b)
      = stepHead (headOf b) := by
  cases b with
  | zero f => rfl
  | one f n t1 t2 rest =>
      unfold AtreyuProcess.gawk_at._default
      simp only [id_eq]
      cases h1 : f.decTruth <;> cases h2 : (DISTINGUISHABLE.fact Pigeon).decTruth <;> rfl
  | rest_call f g p n1 n2 n3 t1 t2 b1 b2 =>
      unfold AtreyuProcess.gawk_at._default
      simp only [id_eq]
      cases h1 : g.decTruth <;> cases h2 : (DISTINGUISHABLE.fact Pigeon).decTruth <;> rfl

/-- The reader's own default, packaged as the one-argument step it is.
(`noncomputable` because the story's rung is: the tie is a theorem about it,
not an attempt to run it.) -/
noncomputable def theDefaultGawk
    (nowtrino : DISTINGUISHABLE Box Pigeon)
    (i0 : ADMISSIBLE Box Pigeon) (i1 : COUNTABLE Box Pigeon)
    (i2 : ENCODED Box Pigeon) (i3 : RESIDUE Box Pigeon)
    (i4 : BINARY Box Pigeon) (i5 : REPEATABLE Box Pigeon)
    (i6 : NUMERIC Box Pigeon) (i7 : REPRESENTABLE Box Pigeon)
    (i8 : PHYSICAL Box Pigeon) (i9 : COMPARABLE Box Pigeon)
    (i10 : OBSERVED Box Pigeon) (i11 : PRESENT Box Pigeon)
    (i12 : MEASURABLE Box Pigeon) (i13 : GUNGAN Box Pigeon)
    (i14 : SOURCE Box Pigeon) (i15 : EXECUTED Box Pigeon)
    (i16 : VALUE Box Pigeon) (i17 : MAGNITUDE Box Pigeon)
    (i18 : SCALED Box Pigeon) (i19 : LOAD Box Pigeon)
    (i20 : INDEXOFANT Box Pigeon) (i21 : BULLSHIT Box Pigeon)
    (i22 : PROPAGANDA Box Pigeon) (i23 : ACOLYTE Box Pigeon)
    (i24 : SCIENTIFIC Box Pigeon) (i25 : TRUTH Box Pigeon)
    (i26 : WITNESSED Box Pigeon) (i27 : REAL Box Pigeon)
    (quantum : LOCAL Box Pigeon) (gravity : UNIVERSAL Box Pigeon quantum)
    (i28 : LOGICAL Box Pigeon quantum gravity) (i29 : HALTED Box Pigeon quantum gravity)
    (i30 : MEASURED Box Pigeon quantum gravity) (i31 : COMPILED Box Pigeon quantum gravity)
    (book : CompilerOutput Box Pigeon quantum gravity)
    (a_constant : Bullshit) (page total : Number) (tape : CompilerTape) :
    Bullshit → Bullshit :=
  fun b => @AtreyuProcess.gawk_at._default Box Pigeon nowtrino
              i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15
              i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27
              quantum gravity i28 i29 i30 i31
              book a_constant page total tape b

/-- `n` gawks, applied from the outside in: the pin first, then each step on
the last reading. -/
def gawkTimes (g : Bullshit → Bullshit) : Nat → Bullshit → Bullshit
  | 0,     b => b
  | n + 1, b => g (gawkTimes g n b)

/-- THE LADDER, TIED.  Gawk the pin `n` times with the reader's own default and
the head is exactly the twin's `headAfter n`.  This is the statement the twin
needed and did not have: Episode 9's trips take the twin's steps, for every
trip count, not just the three the story walks. -/
theorem the_trips_climb_the_twins_ladder
    (nowtrino : DISTINGUISHABLE Box Pigeon)
    (i0 : ADMISSIBLE Box Pigeon) (i1 : COUNTABLE Box Pigeon)
    (i2 : ENCODED Box Pigeon) (i3 : RESIDUE Box Pigeon)
    (i4 : BINARY Box Pigeon) (i5 : REPEATABLE Box Pigeon)
    (i6 : NUMERIC Box Pigeon) (i7 : REPRESENTABLE Box Pigeon)
    (i8 : PHYSICAL Box Pigeon) (i9 : COMPARABLE Box Pigeon)
    (i10 : OBSERVED Box Pigeon) (i11 : PRESENT Box Pigeon)
    (i12 : MEASURABLE Box Pigeon) (i13 : GUNGAN Box Pigeon)
    (i14 : SOURCE Box Pigeon) (i15 : EXECUTED Box Pigeon)
    (i16 : VALUE Box Pigeon) (i17 : MAGNITUDE Box Pigeon)
    (i18 : SCALED Box Pigeon) (i19 : LOAD Box Pigeon)
    (i20 : INDEXOFANT Box Pigeon) (i21 : BULLSHIT Box Pigeon)
    (i22 : PROPAGANDA Box Pigeon) (i23 : ACOLYTE Box Pigeon)
    (i24 : SCIENTIFIC Box Pigeon) (i25 : TRUTH Box Pigeon)
    (i26 : WITNESSED Box Pigeon) (i27 : REAL Box Pigeon)
    (quantum : LOCAL Box Pigeon) (gravity : UNIVERSAL Box Pigeon quantum)
    (i28 : LOGICAL Box Pigeon quantum gravity) (i29 : HALTED Box Pigeon quantum gravity)
    (i30 : MEASURED Box Pigeon quantum gravity) (i31 : COMPILED Box Pigeon quantum gravity)
    (book : CompilerOutput Box Pigeon quantum gravity)
    (a_constant : Bullshit) (page total : Number) (tape : CompilerTape)
    (ledger : Fact) (n : Nat) :
    headOf (gawkTimes (theDefaultGawk nowtrino i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13
              i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27
              quantum gravity i28 i29 i30 i31 book a_constant page total tape) n
            (Bullshit.zero ledger))
      = headAfter n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [gawkTimes, headAfter, ← ih]
      exact the_default_gawk_steps_the_head book a_constant page total tape _

end Measurement.TheTwinTiedToTheTrips

#print axioms Measurement.TheTwinTiedToTheTrips.the_default_gawk_steps_the_head
#print axioms Measurement.TheTwinTiedToTheTrips.the_trips_climb_the_twins_ladder
