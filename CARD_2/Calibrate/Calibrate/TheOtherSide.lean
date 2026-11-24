/-
The other side: the device's reals are the reals, by one isomorphism.

The author, 24 November 2026: "the isomorphism to R isn't that hard, you just need to show that the total orders are
equivalent"; and "the thing you construct is (F=T)=(T=F). that's the other side! we have them in a classic pincers
movement" (declared).

On the device the order of the reals is not total without a click (Meanings).  Here Mathlib's reals are handed in, and
with them choice.  Each of the device's reals goes to the least number past all its low walls.  Two reals are one exactly
when they go to one number; one is not past the other exactly when its number is not above; and every number not under
nothing is reached, by the halvings of its own floors.  So the device's reals, taken up to being one, are the
non-negative reals as an ordered set, and the signed reals are all of them; sums and products go across.  And any two
ring isomorphisms onto the naturals, the integers or the reals are one: there is only one way across.

Everything here bills `Classical.choice`, because Mathlib's reals do.
-/
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.CompleteField
import Meanings

namespace Calibrate
open Meanings

noncomputable section

/-! A fraction as a number. -/

def ofFraction (p : Fraction) : ℝ := (p.over : ℝ) / (p.under : ℝ)

theorem under_pos_real (p : Fraction) : (0 : ℝ) < p.under := by exact_mod_cast p.under_pos

theorem ofFraction_nonneg (p : Fraction) : 0 ≤ ofFraction p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem ofFraction_le_iff (p q : Fraction) : p.le q ↔ ofFraction p ≤ ofFraction q := by
  unfold ofFraction Fraction.le
  rw [div_le_div_iff₀ (under_pos_real p) (under_pos_real q)]
  constructor <;> intro h <;> exact_mod_cast h

theorem ofFraction_add (p q : Fraction) : ofFraction (p.add q) = ofFraction p + ofFraction q := by
  unfold ofFraction Fraction.add
  have := under_pos_real p; have := under_pos_real q
  push_cast; field_simp

theorem ofFraction_mul (p q : Fraction) : ofFraction (p.mul q) = ofFraction p * ofFraction q := by
  unfold ofFraction Fraction.mul
  push_cast; rw [mul_div_mul_comm]

/-! A real as a number: the least number past all its low walls. -/

theorem the_walls_narrow (x : Bracketed) (n : ℕ) :
    ofFraction (x.high n) ≤ ofFraction (x.low n) + 1 / ((n : ℝ) + 1) := by
  have h := x.narrows n
  have hh := under_pos_real (x.high n); have hl := under_pos_real (x.low n)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h' : ((x.high n).over : ℝ) * (x.low n).under * ((n : ℝ) + 1)
      ≤ ((x.low n).over : ℝ) * (x.high n).under * ((n : ℝ) + 1) + ((x.high n).under : ℝ) * (x.low n).under := by
    exact_mod_cast h
  unfold ofFraction
  rw [div_add_div _ _ (ne_of_gt hl) (ne_of_gt hn), div_le_div_iff₀ hh (by positivity)]
  nlinarith [h']

def toReal (x : Bracketed) : ℝ := ⨆ n, ofFraction (x.low n)

theorem low_walls_bounded (x : Bracketed) : BddAbove (Set.range fun n => ofFraction (x.low n)) :=
  ⟨ofFraction (x.high 0), by rintro _ ⟨n, rfl⟩; exact (ofFraction_le_iff _ _).1 (x.low_under_high n 0)⟩

theorem low_le_toReal (x : Bracketed) (n : ℕ) : ofFraction (x.low n) ≤ toReal x := le_ciSup (low_walls_bounded x) n

theorem toReal_le_high (x : Bracketed) (m : ℕ) : toReal x ≤ ofFraction (x.high m) :=
  ciSup_le fun n => (ofFraction_le_iff _ _).1 (x.low_under_high n m)

theorem toReal_nonneg (x : Bracketed) : 0 ≤ toReal x := (ofFraction_nonneg _).trans (low_le_toReal x 0)

theorem le_of_within (a b : ℝ) (h : ∀ n : ℕ, a ≤ b + 1 / ((n : ℝ) + 1)) : a ≤ b :=
  le_of_forall_pos_le_add fun ε hε =>
    let ⟨n, hn⟩ := exists_nat_one_div_lt hε
    (h n).trans (by linarith)

--| THE SQUEEZE.  A number between every low wall and the high wall of the same stage is the real's number.
theorem toReal_eq_of_between (x : Bracketed) (r : ℝ)
    (h : ∀ n, ofFraction (x.low n) ≤ r ∧ r ≤ ofFraction (x.high n)) : toReal x = r :=
  le_antisymm
    (le_of_within _ _ fun n => (toReal_le_high x n).trans ((the_walls_narrow x n).trans (by linarith [(h n).1])))
    (le_of_within _ _ fun n => (h n).2.trans ((the_walls_narrow x n).trans (by linarith [low_le_toReal x n])))

/-! The orders are one. -/

--| NOT PAST IS NOT ABOVE.
theorem notPast_iff (x y : Bracketed) : x.NotPast y ↔ toReal x ≤ toReal y := by
  constructor
  · intro h
    exact le_of_within _ _ fun n =>
      (ciSup_le fun k => (ofFraction_le_iff _ _).1 (h k n)).trans
        ((the_walls_narrow y n).trans (by linarith [low_le_toReal y n]))
  · intro h n m
    exact (ofFraction_le_iff _ _).2 ((low_le_toReal x n).trans (h.trans (toReal_le_high y m)))

--| ONE IS ONE NUMBER.
theorem same_iff (x y : Bracketed) : x.Same y ↔ toReal x = toReal y := by
  constructor
  · intro h
    exact le_antisymm ((notPast_iff x y).1 fun n m => (h n m).1) ((notPast_iff y x).1 fun n m => (h n m).2)
  · intro e n m
    exact ⟨((notPast_iff x y).2 e.le) n m, ((notPast_iff y x).2 e.ge) n m⟩

--| EVERY NUMBER NOT UNDER NOTHING IS REACHED, by the halvings of its own floors.
def theFloors (r : ℝ) (hr : 0 ≤ r) : DyadicCut where
  cut n := ⌊r * 2 ^ n⌋₊
  doubles n := by
    have a0 : 0 ≤ r * 2 ^ n := by positivity
    have e : r * 2 ^ (n + 1) = 2 * (r * 2 ^ n) := by ring
    constructor
    · apply Nat.le_floor
      rw [e]; push_cast
      have := Nat.floor_le a0; linarith
    · have lt : ⌊r * 2 ^ (n + 1)⌋₊ < 2 * ⌊r * 2 ^ n⌋₊ + 2 := by
        rw [Nat.floor_lt (by positivity), e]; push_cast
        have := Nat.lt_floor_add_one (r * 2 ^ n); linarith
      omega

theorem every_number_not_under_nothing_is_reached (r : ℝ) (hr : 0 ≤ r) :
    toReal (theFloors r hr).bracketed = r := by
  apply toReal_eq_of_between
  intro n
  have p : (0 : ℝ) < 2 ^ n := by positivity
  have a0 : 0 ≤ r * 2 ^ n := by positivity
  show ((⌊r * 2 ^ n⌋₊ : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) ≤ r ∧ r ≤ ((⌊r * 2 ^ n⌋₊ + 1 : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ)
  push_cast
  constructor
  · rw [div_le_iff₀ p]; exact Nat.floor_le a0
  · rw [le_div_iff₀ p]; exact (Nat.lt_floor_add_one _).le

/-! Sums and products go across. -/

theorem toReal_add (x y : Bracketed) : toReal (x.add y) = toReal x + toReal y := by
  apply toReal_eq_of_between
  intro n
  show ofFraction ((x.low (2 * n + 1)).add (y.low (2 * n + 1))) ≤ _ ∧ _ ≤ ofFraction ((x.high (2 * n + 1)).add (y.high (2 * n + 1)))
  rw [ofFraction_add, ofFraction_add]
  exact ⟨add_le_add (low_le_toReal x _) (low_le_toReal y _), add_le_add (toReal_le_high x _) (toReal_le_high y _)⟩

theorem toReal_mul (x y : Bracketed) : toReal (x.mul y) = toReal x * toReal y := by
  apply toReal_eq_of_between
  intro n
  show ofFraction ((x.low (x.stageForProduct y n)).mul (y.low (x.stageForProduct y n))) ≤ _
    ∧ _ ≤ ofFraction ((x.high (x.stageForProduct y n)).mul (y.high (x.stageForProduct y n)))
  rw [ofFraction_mul, ofFraction_mul]
  exact ⟨mul_le_mul (low_le_toReal x _) (low_le_toReal y _) (ofFraction_nonneg _) (toReal_nonneg x),
    mul_le_mul (toReal_le_high x _) (toReal_le_high y _) (toReal_nonneg y) ((toReal_nonneg x).trans (toReal_le_high x _))⟩

/-! The device's reals, up to being one, are the non-negative reals. -/

def sameSetoid : Setoid Bracketed :=
  ⟨Bracketed.Same, ⟨Bracketed.same_refl, Bracketed.same_symm, Bracketed.same_trans⟩⟩

abbrev TheDevicesReals : Type := Quotient sameSetoid

def TheDevicesReals.toNNReal : TheDevicesReals → NNReal :=
  Quotient.lift (fun x => ⟨toReal x, toReal_nonneg x⟩) fun a b h => Subtype.ext ((same_iff a b).1 h)

instance : LE TheDevicesReals := ⟨fun a b => a.toNNReal ≤ b.toNNReal⟩

--| THE ORDER ON THE CLASSES IS NOT PAST.
theorem the_order_is_not_past (x y : Bracketed) :
    (Quotient.mk sameSetoid x : TheDevicesReals) ≤ Quotient.mk sameSetoid y ↔ x.NotPast y :=
  (notPast_iff x y).symm

theorem toNNReal_injective : Function.Injective TheDevicesReals.toNNReal := by
  intro a b
  induction a using Quotient.ind; induction b using Quotient.ind
  intro h
  exact Quotient.sound ((same_iff _ _).2 (congrArg Subtype.val h))

theorem toNNReal_surjective : Function.Surjective TheDevicesReals.toNNReal := fun r =>
  ⟨Quotient.mk sameSetoid (theFloors r.1 r.2).bracketed, Subtype.ext (every_number_not_under_nothing_is_reached r.1 r.2)⟩

--| THE TOTAL ORDERS ARE EQUIVALENT.  The device's reals up to being one, ordered by not past, are the non-negative reals.
def theOrderIsomorphism : TheDevicesReals ≃o NNReal where
  toEquiv := Equiv.ofBijective _ ⟨toNNReal_injective, toNNReal_surjective⟩
  map_rel_iff' := Iff.rfl

/-! The signed reals are all of them. -/

def toRealSigned (x : SignedReal) : ℝ := toReal x.held - toReal x.owed

theorem signed_same_iff (x y : SignedReal) : x.Same y ↔ toRealSigned x = toRealSigned y := by
  unfold SignedReal.Same toRealSigned
  rw [same_iff, toReal_add, toReal_add]
  constructor <;> intro h <;> linarith

theorem signed_notPast_iff (x y : SignedReal) : x.NotPast y ↔ toRealSigned x ≤ toRealSigned y := by
  unfold SignedReal.NotPast toRealSigned
  rw [notPast_iff, toReal_add, toReal_add]
  constructor <;> intro h <;> linarith

theorem every_number_is_reached_signed (r : ℝ) :
    toRealSigned ⟨(theFloors (max r 0) (le_max_right _ _)).bracketed, (theFloors (max (-r) 0) (le_max_right _ _)).bracketed⟩ = r := by
  unfold toRealSigned
  rw [every_number_not_under_nothing_is_reached, every_number_not_under_nothing_is_reached]
  rcases le_total r 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

def signedSetoid : Setoid SignedReal :=
  ⟨SignedReal.Same, ⟨SignedReal.same_refl, SignedReal.same_symm, SignedReal.same_trans⟩⟩

abbrev TheDevicesSignedReals : Type := Quotient signedSetoid

def TheDevicesSignedReals.toReal : TheDevicesSignedReals → ℝ :=
  Quotient.lift toRealSigned fun a b h => (signed_same_iff a b).1 h

instance : LE TheDevicesSignedReals := ⟨fun a b => a.toReal ≤ b.toReal⟩

theorem the_signed_order_is_not_past (x y : SignedReal) :
    (Quotient.mk signedSetoid x : TheDevicesSignedReals) ≤ Quotient.mk signedSetoid y ↔ x.NotPast y :=
  (signed_notPast_iff x y).symm

--| THE SIGNED REALS, UP TO BEING ONE, ARE THE REALS, AS ORDERED SETS.
def theSignedOrderIsomorphism : TheDevicesSignedReals ≃o ℝ where
  toEquiv := Equiv.ofBijective TheDevicesSignedReals.toReal
    ⟨fun a b => by
      induction a using Quotient.ind; induction b using Quotient.ind
      intro h; exact Quotient.sound ((signed_same_iff _ _).2 h),
     fun r => ⟨Quotient.mk signedSetoid _, every_number_is_reached_signed r⟩⟩
  map_rel_iff' := Iff.rfl

/-! There is only one way across. -/

theorem only_one_way_onto_the_naturals {R : Type*} [NonAssocSemiring R] (e₁ e₂ : R ≃+* ℕ) : e₁ = e₂ := by
  have h : ∀ n, e₂ (e₁.symm n) = n := fun n =>
    RingHom.congr_fun (Subsingleton.elim ((e₂ : R →+* ℕ).comp (e₁.symm : ℕ →+* R)) (RingHom.id ℕ)) n
  ext r
  have := h (e₁ r)
  rw [RingEquiv.symm_apply_apply] at this
  exact this.symm

theorem only_one_way_onto_the_integers {R : Type*} [NonAssocRing R] (e₁ e₂ : R ≃+* ℤ) : e₁ = e₂ := by
  have h : ∀ n, e₂ (e₁.symm n) = n := fun n =>
    RingHom.congr_fun (Subsingleton.elim ((e₂ : R →+* ℤ).comp (e₁.symm : ℤ →+* R)) (RingHom.id ℤ)) n
  ext r
  have := h (e₁ r)
  rw [RingEquiv.symm_apply_apply] at this
  exact this.symm

theorem only_one_way_onto_the_reals {R : Type*} [NonAssocSemiring R] (e₁ e₂ : R ≃+* ℝ) : e₁ = e₂ := by
  have h : ∀ n, e₂ (e₁.symm n) = n := fun n =>
    RingHom.congr_fun (Subsingleton.elim ((e₂ : R →+* ℝ).comp (e₁.symm : ℝ →+* R)) (RingHom.id ℝ)) n
  ext r
  have := h (e₁ r)
  rw [RingEquiv.symm_apply_apply] at this
  exact this.symm

end
end Calibrate
