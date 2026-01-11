import Std
import Mathlib.Data.Fintype.Basic
import Entropy.Chapter1.Interfaces
import Entropy.Chapter2.Interfaces
import Entropy.Chapter2.Definitions

namespace Entropy

universe u v w

/-
Axiom 1 (Peano)
---------------
Lean already provides Nat. We name it to align with the text.
-/

abbrev ω := Nat


/-
Axiom 2 (Kolmogorov)
-------------------
Each instrument has a finite alphabet of symbols.
In the "pure traits" design, the alphabet is a type `Symbol i` attached
to each instrument value `i`, and finiteness is given by `Fintype`.
-/

-- Instruments are a type; we do not assume a global Symbol type.
axiom Instrument : Type u

-- The symbol alphabet depends on the instrument value.
axiom Symbol : Instrument → Type v

-- Finiteness of each instrument's alphabet.
axiom symbolFintype : (i : Instrument) → Fintype (Symbol i)



/-
Axiom (Ockham) [Order Coherence]
--------------------------------
If e₁ ≺ e₂ as events, then for every instrument i, the record response
attached to e₂ for i cannot precede the record response attached to e₁ for i.
-/
axiom ockham_order_coherence
  {E : Type u} {I : Type v} {R : Type w}
  [EventOrder E] [RecordOrder R]
  (resp : E → I → R) :
  ∀ {e₁ e₂ : E},
    EventOrder.prec e₁ e₂ →
    ∀ i : I, ¬ RecordOrder.prec (resp e₂ i) (resp e₁ i)





/-
Axiom 4 (Causal Sets) [Events are Discrete]

The distinguishability relations among events admit a representation
as a locally finite partially ordered set (E, ≺), where

1) e ≺ f means e is incorporated before f in the record,
2) (E, ≺) is acyclic and transitive,
3) for any a ≺ b, the interval { e | a ≺ e ∧ e ≺ b } is finite, and
4) every event causes at least one measurement: |e| > 0.
-/

/-- A notion of "cardinality" (e.g. number of measurements in an event). -/
class HasCard (E : Type u) where
  card : E → Nat




/--
Convenience: if an event is presented as a finite bundle of records,
we can take its "cardinality" to be the number of records it contains.
-/
instance {E : Type u} {R : Type v} [EventLike E R] : HasCard E where
  card e := (EventLike.records e).size

/--
A causal set structure on events:
- `prec` is the causal precedence (record incorporation order),
- transitive and acyclic,
- locally finite (finite open intervals).
-/
class CausalSet (E : Type u) extends EventOrder E where
  trans : Transitive prec
  irrefl : Irreflexive prec
  locallyFinite :
    ∀ {a b : E}, prec a b → Finite {e : E // prec a e ∧ prec e b}

/--
Every event causes at least one measurement on one instrument: |e| > 0.
(We keep this as an axiom, since it is a physical requirement, not definitional.)
-/
axiom causal_nonempty
  {E : Type u} [HasCard E] [CausalSet E] :
  ∀ e : E, HasCard.card e > 0


/-
Axiom 5 (Cantor) [Time is an Ordinal Labeling]

Events map to the natural numbers such that

if e ≺ f then t(e) < t(f).

-/

axiom cantor_embedding
  (E : Type u) [EventOrder E] :
  ∃ t : E → Nat, ∀ {e f : E}, EventOrder.prec e f → t e < t f




end Entropy
