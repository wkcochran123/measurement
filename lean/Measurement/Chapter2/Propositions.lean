import Std

import Measurement.Chapter1.Definitions
import Measurement.Chapter2.Definitions

namespace Measurement

universe u v w

/-
We need the semantics of `push` relative to the recursive ledger observers.
This is the minimal “hard rule” that makes Prop 1 provable.
-/

class LedgerPush (L : Type u) (R : Type v) [Ledger L R] : Prop where
  push_isEmpty : ∀ (Lt : L) (r : R),
    Ledger.isEmpty (L := L) (R := R) (Ledger.push Lt r) = false

  push_entry   : ∀ (Lt : L) (r : R),
    Ledger.entry (L := L) (R := R) (Ledger.push Lt r) = some r

  push_prev    : ∀ (Lt : L) (r : R),
    Ledger.prev (L := L) (R := R) (Ledger.push Lt r) = some Lt

  -- This is the missing “hard rule” you’re trying to prove from nothing.
  push_size    : ∀ (Lt : L) (r : R),
    Ledger.size (L := L) (R := R) (Ledger.push Lt r) =
      Ledger.size (L := L) (R := R) Lt + 1


lemma ledger_size_push
    (L : Type u) (R : Type v) [Ledger L R] [LedgerPush L R]
    (Lt : L) (r : R) :
    Ledger.size (L := L) (R := R) (Ledger.push Lt r) =
      Ledger.size (L := L) (R := R) Lt + 1 := by
  simpa using (LedgerPush.push_size (L := L) (R := R) Lt r)



/-- Proposition 1: a refinement operator exists (soft version). -/
theorem proposition1_refinementOperator_exists
    (L : Type u) (R : Type v) (X : Type w)
    [Ledger L R] [LedgerPush L R]
    [Inhabited R] [Inhabited X] :
    ∃ RO : RefinementOperator (L := L) (R := R) (X := X), True := by
  classical
  -- Choose the “one-step refinement”: push a default record.
  let Rhat : Refinement L := { refine := fun Lt => Ledger.push Lt (default : R) }

  -- Choose any prediction/representation maps (not constrained yet in Prop 1).
  let f : X -> R := fun _ => (default : R)
  let rhoTilde : R -> X := fun _ => (default : X)

  refine ⟨{
    Rhat := Rhat
    f := f
    rhoTilde := rhoTilde
    ledger_growth := ?_
    ledger_coherence := ?_
  }, trivial⟩

  · intro Lt
    -- growth is exactly the size lemma for push
    -- (refine Lt) = push Lt default
    simpa [Rhat] using (ledger_size_push (L := L) (R := R) Lt (default : R))

  · intro Lt
    -- coherence: the refined ledger has an entry (namely the pushed record)
    refine ⟨(default : R), ?_⟩
    -- entry (push Lt default) = some default
    simpa [Rhat] using (LedgerPush.push_entry (L := L) (R := R) Lt (default : R))

end Measurement
