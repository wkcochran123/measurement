import Measurement.Chapter2

namespace Measurement

/--
Invariant:     The ability to compute an inversion by listing values out
Instrument:    A metaphysical construction that explains the transmission
               and arrival of a stimulus
Device:        The list of possible carrier/sensor interactions
Closure:       The invariant of measurement
-/

structure Inversion (σ : Type u) (τ : Type (u+1)) where
  inv : Decomposition τ σ
  ordering : ArrowOfTime σ τ

structure Carrier (σ : Type u) (τ : Type (u+1)) where
  instrument: Instrument σ τ
  model: TuringDevice σ τ
  map: Inversion σ τ
  ordering: ArrowOfTime σ τ

structure Phenomenon (σ : Type u) (τ : Type (u+1)) where
  sensor : Device σ τ
  carrier : Carrier σ τ

structure Invariant (σ : Type u) (τ : Type (u+1)) where
  evidence : Device σ τ
  model    : Inversion σ τ
  survivor : (σ × τ) → Option τ



abbrev DopplerCarrier := Carrier Nat (ULift Nat)





namespace Enumeration

def findPair? {A : Type u} {B : Type v} (f : A → Option B) : Enumeration A → Option B
  | .nil        => none
  | .cons a as  =>
      match f a with
      | some b => some b
      | none   => findPair? f as

end Enumeration



namespace Decomposition

/-- Decode along a decomposition by searching the enumerated pairs. -/
def decode? {σ : Type u} {τ : Type v} [DecidableEq σ]
    (D : Decomposition σ τ) (t : σ) : Option τ :=
  Enumeration.findPair?
    (fun p : (σ × τ) =>
      if _h : p.1 = t then
        some p.2
      else
        none)
    D.pairs

def invert {σ : Type u} {τ : Type u} [DecidableEq τ]
    (D : Decomposition σ τ) (s : τ) : Option σ :=
  Enumeration.findPair?
    (fun p : (σ × τ) =>
      if _h : p.2 = s then
        some p.1
      else
        none)
    D.pairs

end Decomposition

namespace Inversion

def η {σ : Type u} {τ : Type (u+1)} (I : Inversion σ τ) : Nat → Option (τ × σ) :=
  fun n => Enumeration.ζ I.inv.pairs n

end Inversion


namespace Carrier

noncomputable def recv? {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ] [DecidableEq τ]
  (C : Carrier σ τ) (x : σ) : Option τ :=

  match C.model.decomposition.decode? x with
  | none => none
  | some y =>
      match C.map.inv.decode? y with
      | none   => none
      | some _ => some y

end Carrier

namespace Invariant

noncomputable def admissible {σ : Type u} {τ : Type (u+1)}
    [DecidableEq σ]
    [DecidableEq τ]
    (I : Invariant σ τ) (e : τ) : Option τ :=
  match I.model.inv.decode? e with
  | none   => none
  | some _ => match I.model.inv.decode? e with
              | none   => none
              | some _ => some e
end Invariant

namespace Device

noncomputable def next_record? {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ] [DecidableEq τ]
  (D : Device σ τ) (C : Carrier σ τ) (x : σ) : Option τ :=
    D.read? >>= fun _ => C.recv? x

end Device


end Measurement
