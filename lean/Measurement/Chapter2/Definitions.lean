import Std
import Measurement.Chapter1.Interfaces
import Measurement.Chapter2.Interfaces

namespace Measurement

universe u v

/-- A concrete record with a count index. -/
structure Record (I : Type u) (J : Type v) where
  instrument : I
  symbol     : J
  count      : Nat

-- This is your statement: instrument and symbol are HashCount
-- expressed as constraints where you use Record:
variable {I : Type u} {J : Type v} [HashCount I] [HashCount J]

-- And the record itself can be HashCount too:
def pairNat (a b : Nat) : Nat :=
  let s := a + b
  (s * (s + 1)) / 2 + b

instance {I : Type u} {J : Type v} [HashCount I] [HashCount J] :
  HashCount (Record I J) where
  hash r :=
    pairNat (HashCount.hash r.instrument)
      (pairNat (HashCount.hash r.symbol) r.count)


/-- An event is a finite array of records. -/
structure Event (R : Type) where
  records : Array R

instance (R) : EventLike (Event R) R where
  records := Event.records

/-- A ledger is a finite ordered array of records. -/
structure Ledger (R : Type) where
  entries : Array R

instance (R) : LedgerLike (Ledger R) R where
  entries := Ledger.entries

/-- An event-indexing into a ledger. -/
structure EventIndexing (E : Type u) (L : Type v) where
  idx : E → Nat

end Measurement
