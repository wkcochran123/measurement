import Measurement.Episode37

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 38__: _The Square-Root Door_

Episode28 left a Nat-valued `InducedNormSqDoorframe`: a `normSq` equal to the
energy-squared, with the square-root norm, completion, and topology flagged as
"future layers."  This episode builds the doorframe for that future.

There is no real-number field in this development, so the genuine norm cannot be
computed here.  Instead we name the *interface* a real (or Hilbert) coefficient
field must provide:

  RealScaleField = an ordered carrier `R`, an embedding `ofNat : Nat -> R`, and a
  zero-detecting square root `sqrt`.

From that interface plus any `EnergySqCertificate`, the induced norm is

  norm x = sqrt (ofNat (energySq x)),

and it detects zero exactly: `norm x = 0  <->  x = 0`.

Stated formally:
* `RealScaleField` is the coefficient-field interface; importing Mathlib's `Real`
  later supplies a concrete instance.
* `realNorm` is the induced norm and `realNorm_eq_zero_iff` proves zero
  detection, inherited from positive-definiteness via the energy certificate.
* `HilbertCompletionDoor` packages the norm with a `completionAvailable` token:
  the place where the metric completion to a Hilbert space gets imported.
* `natNormSqShadow` is the degenerate instance `sqrt = id, R = Nat`; it recovers
  Episode28's `normSq` exactly, witnessing that the door is inhabitable.
* `threeRungHilbertDoor` / `anchoredHilbertDoor` open the door over Episode34's
  and Episode35's concrete SPD energy certificates.

Residue left:
The genuine real square root (and with it Cauchy-Schwarz, the triangle
inequality, completeness, and the inner-product-space import) is what a concrete
`RealScaleField` from a real-analysis library supplies.  This file hands that
library the proof-carrying certificate it consumes.
-/

/-- The interface a real (or Hilbert) coefficient field provides to the activity
norm: an ordered carrier with a zero-detecting square root. -/
structure RealScaleField where
  R : Type
  rzero : R
  ofNat : Nat -> R
  sqrt : R -> R
  ofNat_zero : ofNat 0 = rzero
  ofNat_eq_zero : forall n, ofNat n = rzero -> n = 0
  sqrt_zero : sqrt rzero = rzero
  sqrt_eq_zero : forall v, sqrt v = rzero -> v = rzero

/-- The induced real-valued norm: the square root of the embedded energy. -/
def realNorm {V : Type} (sf : RealScaleField) (cert : EnergySqCertificate V) (x : V) : sf.R :=
  sf.sqrt (sf.ofNat (cert.energySq x))

theorem realNorm_zero {V : Type} (sf : RealScaleField) (cert : EnergySqCertificate V) :
    realNorm sf cert cert.zero = sf.rzero := by
  unfold realNorm
  rw [cert.energySq_zero, sf.ofNat_zero, sf.sqrt_zero]

/-- Zero detection of the induced norm: it vanishes only at the zero activity.
This is the square-root face of positive-definiteness. -/
theorem realNorm_eq_zero_iff {V : Type} (sf : RealScaleField)
    (cert : EnergySqCertificate V) (x : V) :
    realNorm sf cert x = sf.rzero <-> x = cert.zero := by
  constructor
  · intro h
    unfold realNorm at h
    have h1 := sf.sqrt_eq_zero _ h
    have h2 := sf.ofNat_eq_zero _ h1
    exact cert.energySq_eq_zero_only_zero x h2
  · intro h
    subst h
    exact realNorm_zero sf cert

/-- The Hilbert completion doorframe: the induced norm plus the slot where a
real-analysis library imports the metric completion to a Hilbert space. -/
structure HilbertCompletionDoor (V : Type) where
  scale : RealScaleField
  cert : EnergySqCertificate V
  norm : V -> scale.R
  norm_matches : forall x, norm x = realNorm scale cert x
  norm_zero_detects : forall x, norm x = scale.rzero -> x = cert.zero
  completionAvailable : Prop
  completionAvailable_proof : completionAvailable

/-- Build the doorframe from any scale field and energy certificate. -/
def doorFromCert {V : Type} (sf : RealScaleField) (cert : EnergySqCertificate V) :
    HilbertCompletionDoor V where
  scale := sf
  cert := cert
  norm := realNorm sf cert
  norm_matches := by intro x; rfl
  norm_zero_detects := by
    intro x h
    exact (realNorm_eq_zero_iff sf cert x).mp h
  completionAvailable := True
  completionAvailable_proof := trivial

/-- The degenerate instance with `sqrt = id` over `Nat`.  Its norm is exactly
Episode28's `normSq`; it witnesses that the door is inhabitable while the genuine
real square root is still a future import. -/
def natNormSqShadow : RealScaleField where
  R := Nat
  rzero := 0
  ofNat := fun n => n
  sqrt := fun v => v
  ofNat_zero := rfl
  ofNat_eq_zero := by intro n h; exact h
  sqrt_zero := rfl
  sqrt_eq_zero := by intro v h; exact h

/-- The Hilbert door over the three-rung `K = M + S` energy (Episode34). -/
noncomputable def threeRungHilbertDoor (sf : RealScaleField) :
    HilbertCompletionDoor threeRungSPD.form.V :=
  doorFromCert sf threeRungEnergySqCertificate

/-- The Hilbert door over the anchor-coercive energy (Episode35). -/
noncomputable def anchoredHilbertDoor (sf : RealScaleField) :
    HilbertCompletionDoor anchoredSPD.form.V :=
  doorFromCert sf anchoredEnergySqCertificate

/-- The integer shadow of the three-rung door: norm `= normSq`, fully
computable, no real-analysis import required. -/
noncomputable def threeRungNormSqShadowDoor :
    HilbertCompletionDoor threeRungSPD.form.V :=
  threeRungHilbertDoor natNormSqShadow

end Measurement
