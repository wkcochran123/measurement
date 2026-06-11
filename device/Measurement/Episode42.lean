import Measurement.Episode41

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 42__: _The First Record_

The audit was right: through Episode41 the instrument is fully wired and never
switched on.  Every witness bottoms out in `Fact.Truth`, every predicate is
`fun _ => True`, `COMPARABLE.smaller_than` reads the constant `True`, and the
realizability boundary was proven only on a parity toy against the unconstrained
`AllApparatus`.  That is the blank ledger -- the apparatus at its ground state,
exactly where the book began: "it starts from the trivial truth true = true."

This episode writes the first non-trivial entry, and it is sourced from physics
we actually proved (Episodes 34-35), not a toy.  The apparatus reads an activity
through the stiffness energy.  A *null mode* is a nonzero activity the energy
cannot distinguish from zero.  The first record classifies one invariant -- "a
null mode exists" -- relative to two MEANINGFUL apparatus classes:

* against the ANCHORED apparatus (Episode35, coercive): no null mode exists.
  Coercivity (`AnchoredRung.stiff_pd`) IS the obstruction certificate.  The
  invariant is metaphysical relative to the anchored instrument.
* against the UNANCHORED apparatus (stiffness without the `white_hole -> load`
  pin): the constant `(1,1,1)` is a null mode (Episode35,
  `unanchored_kernel_nontrivial`).  The invariant is physical -- it has a
  witness, it can be entered.

The ledger records only the physical.  So the record has two halves and they are
the boundary itself: a positive witness ("present here", computable, enterable)
and an absence certificate ("absent here", a `¬∃`).  The metaphysical can never
be written into the ledger; only the certificate of its absence can.

This is one line.  It fixes none of the deferred doors (real `ℝ`, the
magnitude-faithful emitter, gauged decorations, a Noether invariant) and it is
not yet the full `CurvatureObstruction`.  It is the smallest thing that is not
`True`: the instrument's first reading, and the first entry the ledger holds.
-/

/-- A null mode: a nonzero activity whose energy is zero -- the energy cannot
distinguish it from the ground state. -/
def HasNullMode {V : Type} (zero : V) (energy : V -> Nat) : Prop :=
  ∃ x, x ≠ zero ∧ energy x = 0

/-- The anchored apparatus reads activities through the (computable) stiffness
energy.  This is `GalerkinBilinearForm.energySq anchoredForm`, evaluated
directly rather than through the noncomputable certificate. -/
def anchoredEnergy (x : AnchoredRung) : Nat :=
  intActivityMagnitude (AnchoredRung.stiff x x)

/-- The unanchored apparatus reads through the stiffness on the full three rungs,
with no node pinned. -/
def unanchoredEnergy (x : Rung3) : Nat :=
  intActivityMagnitude (Rung3.stiffOnly x x)

/-- Metaphysical half: the anchored (coercive) apparatus admits no null mode.
The proof is Episode35's coercivity -- positive-definiteness is the obstruction
certificate. -/
theorem anchored_has_no_null_mode :
    ¬ HasNullMode AnchoredRung.zero anchoredEnergy := by
  rintro ⟨x, hne, h0⟩
  have hstiff : AnchoredRung.stiff x x = 0 := intActivityMagnitude_eq_zero h0
  exact hne (AnchoredRung.stiff_pd x hstiff)

/-- Physical half: the unanchored apparatus realizes the null mode.  The witness
is Episode35's `unanchored_kernel_nontrivial`: the constant `(1,1,1)` carries
zero stiffness energy yet is nonzero. -/
theorem unanchored_has_null_mode :
    HasNullMode Rung3.zero unanchoredEnergy := by
  obtain ⟨_, hne⟩ := unanchored_kernel_nontrivial
  exact ⟨⟨1, 1, 1⟩, hne, by decide⟩

/-- A ledger record: a certified verdict that an invariant is present (physical)
under one apparatus and absent (metaphysical) under another.  The ledger holds
only what the apparatus can realize plus the certificates of what it cannot. -/
structure LedgerRecord where
  physicalWitness : HasNullMode Rung3.zero unanchoredEnergy
  metaphysicalCertificate : ¬ HasNullMode AnchoredRung.zero anchoredEnergy

/-- THE FIRST RECORD.  One invariant -- "a null mode exists" -- classified
across the `white_hole -> load` boundary: present without the anchor, absent
(metaphysical) with it.  Built from the proven coercivity of Episodes 34-35, not
a toy; relative to two meaningful classes, not the unconstrained ceiling.  The
instrument reads something other than `True`. -/
def firstRecord : LedgerRecord where
  physicalWitness := unanchored_has_null_mode
  metaphysicalCertificate := anchored_has_no_null_mode

/-- The same content as a bare proposition, for re-use. -/
theorem first_record :
    ¬ HasNullMode AnchoredRung.zero anchoredEnergy ∧
      HasNullMode Rung3.zero unanchoredEnergy :=
  ⟨firstRecord.metaphysicalCertificate, firstRecord.physicalWitness⟩

end Measurement
