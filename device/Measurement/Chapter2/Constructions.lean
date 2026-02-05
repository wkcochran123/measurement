import Measurement.Chapter2.ZFC


namespace Measurement

universe u v w



/-- Zipper decomposition: an enumeration of paired symbols. -/
structure Decomposition (σ : Type u) (τ : Type v) where
  pairs : Enumeration (σ × τ)

namespace Enumeration

  def zip {A : Type u} {B : Type v} :
      Enumeration A → Enumeration B → Enumeration (A × B)
    | .nil,      _         => .nil
    | _,         .nil      => .nil
    | .cons a as, .cons b bs => .cons (a, b) (zip as bs)

end Enumeration

namespace Decomposition

  /-- Zeta: index into the zipper enumeration. -/
  def ζ {σ τ} (D : Decomposition σ τ) (n : Nat) : Option (σ × τ) :=
    Enumeration.nth D.pairs n

  /-- Build a DecomposingMap by zipping two enumerations. -/
  def ofZips {σ τ} (eσ : Enumeration σ) (eτ : Enumeration τ) :
    Decomposition σ τ :=
  { pairs := Enumeration.zip eσ eτ }

end Decomposition


end Measurement
