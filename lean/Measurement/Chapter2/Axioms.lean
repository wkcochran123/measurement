import Std
import Mathlib.Data.Fintype.Basic
import Measurement.Chapter1.Definitions
import Measurement.Chapter2.Definitions

namespace Measurement

universe u v w

/-
Axiom 1 (Peano)
---------------
The use of ZFC is assumed and included in Definitions.lean.
-/

/-
Axiom 2 (Kolmogorov)
-/

axiom axiom_kolmogorov :
  ∀ i : Nat, ∃ n : Nat,
    (∀ r : Record, r.a = i → r.b < n)


/--
Axiom 3 (Causal Sets)

The warning of unused variable appears to be an interesting
quirk that should be investigated by those who want to have
their mind blown about nothing at all.
-/
axiom axiom_causal_sets :
  ∃ (L : Type u) (R : Type v) (led : Ledger L R),
    letI : Ledger L R := led
    ∃ (pos : Poset L R) (meas : R -> Nat),
      (∀ (Lt : L) {a b c : R},
          Poset.prec (L := L) (R := R) Lt a b ->
          Poset.prec (L := L) (R := R) Lt b c ->
          Poset.prec (L := L) (R := R) Lt a c) ∧
      (∀ (Lt : L) (a : R),
          ¬ Poset.prec (L := L) (R := R) Lt a a) ∧
      (∀ (Lt : L) (a b : R),
          Poset.prec (L := L) (R := R) Lt a b ->
            Set.Finite { e : R |
              Poset.prec (L := L) (R := R) Lt a e ∧
              Poset.prec (L := L) (R := R) Lt e b }) ∧
      (∀ e : R, 0 < meas e)



/--
Axiom 4 (Ockham)
-/
axiom axiom_ockham_counts :
  forall (L : Type u) (led : Ledger L Record),
    letI : Ledger L Record := led
    forall (pos : Poset L Record),
      forall (Lt : L) (r s : Record),
        pos.prec Lt r s -> r.c < s.c



/--
Axiom 5 (Cantor)
-/
axiom axiom_cantor :
  ∀ (L : Type u) (R : Type v) (led : Ledger L R),
    letI : Ledger L R := led
    ∀ (pos : Poset L R) (Lt : L),
      ∃ (tau : R -> Nat),
        Function.Injective tau ∧
        (∀ e f : R,
          (pos.prec Lt e f) ↔ (tau e < tau f))




/--
Axiom 6 (Planck): Observations are finite and immutable.
-/
axiom axiom_planck :
  ∀ (L : Type u) (R : Type v) (led : Ledger L R),
    letI : Ledger L R := led
    ∀ (pos : Poset L R) (meas : R -> Nat),
      ∃ (Eps : Nat),
        0 < Eps ∧
        (∀ e : R, 0 < meas e ∧ meas e ≤ Eps)




end Measurement
