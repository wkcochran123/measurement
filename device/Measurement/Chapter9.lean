import Measurement.Chapter8

namespace Measurement

universe u

structure Flattening (σ : Type u) (τ : Type (u+1)) where
  shape: Enumeration (Enumeration (σ × τ))

namespace Enumeration

variable {A : Type u}

/-- Flatten an `Enumeration` of `Enumeration`s by concatenation. -/
def join : Enumeration (Enumeration A) -> Enumeration A
  | .nil => .nil
  | .cons xs xss => append xs (join xss)

end Enumeration

namespace Flattening
  def unroll (F : Flattening σ τ) : Enumeration (σ × τ) :=
    Enumeration.join F.shape

end Flattening


structure Surface (σ : Type u) (τ : Type (u+1)) where
  norm     : Enumeration (Residue σ τ)
  boundary : Enumeration (σ × τ)
  density  : Enumeration Nat

structure Commutator (σ : Type u) (τ : Type (u+1)) where
  left  : Surface σ τ
  right : Surface σ τ
  ordering : Flattening σ τ

namespace Enumeration

/-- Sum of a Nat-valued Enumeration. -/
def sum : Enumeration Nat -> Nat
  | .nil => 0
  | .cons n ns => n + sum ns

end Enumeration

namespace Surface

variable {σ : Type u} {τ : Type (u+1)}

/-- Boundary integral in counting measure: the action carried by the surface. -/
def action (s : Surface σ τ) : Nat :=
  Enumeration.sum s.density

end Surface

namespace Commutator

variable {σ : Type u} {τ : Type (u+1)}

/-- Signed commutation: right minus left. -/
def commutation (c : Commutator σ τ) : Int :=
  (Surface.action c.right : Int) - (Surface.action c.left : Int)

/-- Nonnegative magnitude of commutation. Zero means "commutes at the scalar level". -/
def commutationMag (c : Commutator σ τ) : Nat :=
  Int.natAbs (commutation c)

end Commutator

structure BilinearForm (σ : Type u) (τ : Type (u+1)) where
  commutator : Commutator σ τ
  kernel : Kernel σ τ

namespace Surface

variable {σ : Type u} {τ : Type (u+1)}

/--
Turn the `(boundary,density)` lists into a counting-measure on atoms.

If `boundary` and `density` are different lengths, we silently ignore the tail.
(If you later want "hard fail", we can change this to return `Option Nat`.)
-/
def densityFn [DecidableEq (σ × τ)] (s : Surface σ τ) : (σ × τ) → Nat :=
  fun a =>
    let rec go : Enumeration (σ × τ) → Enumeration Nat → Nat
      | .nil, .nil => 0
      | .cons b bs, .cons d ds =>
          (if b = a then d else 0) + go bs ds
      | _, _ => 0
    go s.boundary s.density

end Surface


namespace Kernel

variable {σ : Type u} {τ : Type (u+1)}

/-- Indicator that `(x,t)` lies on the injected graph determined by `phi`. -/
noncomputable def onGraph
    [DecidableEq σ] [DecidableEq τ]
    (K : Kernel σ τ) (xt : σ × τ) : Nat :=
  match Kernel.phi K xt.1 with
  | none => 0
  | some (_, y) => if y = xt.2 then 1 else 0

end Kernel


namespace BilinearForm

variable {σ : Type u} {τ : Type (u+1)}

/--
The "internal functional" induced by your current Kernel API:

  eval(B) = sum_{(x,t) in Gamma}  rho_R(x,t) * 1_{phi(x)=t} * rho_L(x,t)

where `Gamma` is the skip-zip support coming from `ordering.unroll`.
-/
noncomputable def eval
    [DecidableEq σ] [DecidableEq τ] [DecidableEq (σ × τ)]
    (B : BilinearForm σ τ) : Nat :=
  let Γ  := B.commutator.ordering.unroll
  let ρL := Surface.densityFn (σ := σ) (τ := τ) B.commutator.left
  let ρR := Surface.densityFn (σ := σ) (τ := τ) B.commutator.right
  let rec sumOver : Enumeration (σ × τ) → Nat
    | .nil => 0
    | .cons xt xs =>
        (ρR xt) * (Kernel.onGraph B.kernel xt) * (ρL xt) + sumOver xs
  sumOver Γ

end BilinearForm

structure Observer (σ : Type u) (τ : Type (u+1)) where
  science: CommonExperience σ τ
  experiment: Ledger (Event σ)

namespace Observer

/-- The experiment ledger, viewed as an enumeration (in temporal order). -/
def stimuli {σ : Type u} {τ : Type (u+1)}
  (O : Observer σ τ) : Enumeration (Event σ) :=
  O.experiment.toEnum

/-- Apply the shared projection to a stimulus symbol (admissible correlation check). -/
noncomputable def project? {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ] [DecidableEq τ]
  (O : Observer σ τ) (e : Event σ) : Option Bool :=
  Projection.project O.science.projection e.symbol

/-- The `n`th event in the common-experience stream (if it exists). -/
def next_event? {σ : Type u} {τ : Type (u+1)}
  (O : Observer σ τ) (n : Nat) : Option (Event τ) :=
  CommonExperience.next_event? O.science n

/-- Record one more stimulus into the experiment ledger. -/
def push {σ : Type u} {τ : Type (u+1)}
  (O : Observer σ τ) (e : Event σ) : Observer σ τ :=
  { O with experiment := Ledger.snoc O.experiment e }

end Observer



end Measurement
