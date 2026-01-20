import Std
import Measurement.Chapter2.Definitions

namespace Measurement

noncomputable section

def trivialNatAlphabet : Alphabet Nat :=
{ symbols := natEnumeration }

def emptyPhenomenon : Phenomenon (S := Nat) trivialNatAlphabet :=
{ events := ZFC.empty }

def trivialClock : Clock :=
{ Sigma := trivialNatAlphabet
, phenomenon := emptyPhenomenon
}

end

theorem exists_clock : Nonempty Clock :=
  ⟨trivialClock⟩

end Measurement
