import Measurement.Chapter2.Definitions -- contains ledgerOfNaturalNumbers

namespace Measurement
open Classical

universe u

def naturalPredictor : DecodingMap Nat :=
  { ζ := fun n => some n }

def naturalRefinement : Refinement Nat :=
  { enumeration := ledgerOfNaturalNumbers.toEnum
  , predictor   := naturalPredictor
  }

def naturalDenseResponse : DenseResponse Nat :=
  { refinement := naturalRefinement
  , map := fun q => q.val
  }

/--
Theorem 1: Identity Support.
We prove that the continuous identity function ψ(t) = t
is supported by the Natural Ledger.
-/
noncomputable def Theorem_LedgerSupportsIdentity : DomainResponse Nat :=
  { ψ := id
  , certifies := naturalDenseResponse
  , interpolation := by
      -- The proof is trivial because we defined the map as identity
      -- and the function as identity.
      intro q
      simp [naturalDenseResponse, id]
  }


end Measurement
