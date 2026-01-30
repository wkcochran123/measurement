import Std
import Measurement.Chapter3.Definitions

namespace Measurement

/--
Proposition: A refinement operator exists (witnessed by the clock).
-/
theorem refinementOperator_exists_clock :
    ∃ Rop : RefinementOperator Nat Nat Nat, True := by
  classical
  let new : Ledger Nat -> Nat := fun Lt => Lt.head.succ
  refine ⟨
    { Rhat := LedgerRefinement.consRefine new
      f := fun x => x
      rhoTilde := fun r => r
      proj := fun r => r
      ledger_growth := ?_
      ledger_coherence := ?_ }, True.intro⟩

  · intro Lt
    simp [LedgerRefinement.consRefine, Ledger.size, Ledger.toEnum, Enumeration.len, new]

  · intro Lt
    refine ⟨new Lt, 0, ?_⟩
    simp [LedgerRefinement.consRefine, Ledger.find_symbol, new]

end Measurement
