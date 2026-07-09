import Measurement.Episode10

set_option autoImplicit false

/-!
# Finite Gauge Equation

The finite gauge equation is the Fréchet closure of a Gateaux variation under
the local theory's differential equation:

    .frechet gospel direction response (direction ∧ ¬response) base
             theta.differential_equation

This is the **default** gateaux → frechet closure that
`BigRedDogProcess.transmute` produces in its second match branch. It is the
Fréchet closure of the local process attached to the UniverseTensor (the
UniverseTensor is carried by the `BigRedDogProcess` but not computationally
inspected by this branch).

## Decoupling note

`BigRedDogProcess.transmute` is a structure field with a default value. An
arbitrary `LOCAL` instance may override `transmute`. Therefore
`finiteGaugeEquation` is defined directly in terms of the *default* closure,
not via `epsilon.theory.transmute`. The relationship is captured separately
by `UsesDefaultTransmute` and the bridge theorem
`finiteGaugeEquation_eq_transmute`.

## Contents

- `FiniteGaugeInput` — the input bundle (gospel, direction, response, base).
- `defaultFiniteGaugeClosure` — the canonical gateaux → frechet construction.
- `finiteGaugeEquation` — the FGE, defined via `defaultFiniteGaugeClosure`.
- `finiteGaugeEquation_normal_form` — `.frechet` shape; `rfl`.
- `finiteGaugeEquation_deterministic` — function applied to equal inputs.
- `UsesDefaultTransmute` — predicate: theory's `transmute` matches the default.
- `finiteGaugeEquation_eq_transmute` — bridge: under the predicate, the FGE
  equals the gateaux applied to `transmute`.
-/

namespace Measurement.Formalization

open Measurement

universe i

/-- The input bundle to the finite gauge equation: a gospel claim, a
direction proposition, a response proposition, and a base variation. -/
structure FiniteGaugeInput where
  gospel    : Gospel
  direction : Prop
  response  : Prop
  base      : Variation

section
variable
    {Value : Type i}
    {Carrier : CarrierProcess Value}
    [d : DISTINGUISHABLE Value Carrier]
    [a : ADMISSIBLE Value Carrier]
    [c : COUNTABLE Value Carrier]
    [e : ENCODED Value Carrier]
    [r : RESIDUE Value Carrier]
    [b : BINARY Value Carrier]
    [f : REPEATABLE Value Carrier]
    [n : NUMERIC Value Carrier]
    [h : REPRESENTABLE Value Carrier]
    [p : PHYSICAL Value Carrier]
    [z : COMPARABLE Value Carrier]
    [particle : OBSERVED Value Carrier]
    [frquency : PRESENT Value Carrier]
    [what_meesa_saying : MEASURABLE Value Carrier]
    [zero : GUNGAN Value Carrier]
    [one : SOURCE Value Carrier]
    [result : EXECUTED Value Carrier]
    [value : VALUE Value Carrier]
    [length : MAGNITUDE Value Carrier]
    [scaled : SCALED Value Carrier]
    [oriented : LOAD Value Carrier]
    [matter : FINITE_ELEPHANT Value Carrier]
    [model : BULLSHIT Value Carrier]
    [space : PROPAGANDA Value Carrier]
    [scientist : ACOLYTE Value Carrier]
    [ideology : SCIENTIFIC Value Carrier]
    [gospel : TRUTH Value Carrier]
    [account : WITNESSED Value Carrier]
    [real : REAL Value Carrier]

/-- The canonical (default) Fréchet closure of a Gateaux variation: take the
input's gospel/direction/response/base and the theory's
`differential_equation`, package into a `.frechet` whose residue is
`direction ∧ ¬ response`.

This is exactly what `BigRedDogProcess.transmute`'s gateaux → frechet branch
produces, but defined here independently of the (overridable) `transmute`
field. -/
def defaultFiniteGaugeClosure
    (theta : BigRedDogProcess Value Carrier)
    (x : FiniteGaugeInput) : Variation :=
  .frechet x.gospel x.direction x.response
    (x.direction ∧ ¬ x.response)
    x.base theta.differential_equation

/-- The finite gauge equation: the default Fréchet closure under the local
theory's differential equation.  `epsilon` is an explicit argument: this file
is intentionally abstract, so instance search cannot synthesize the
29-gate `LOCAL` tower here -- the caller supplies it. -/
-- CHOICE(instrument 0a): sacred LOCAL ends with an explicit (real: REAL) arg — pass the section `real` (l.87),
-- at all 4 sites (109/120/132/162). REPAIRED in place, NOT atticked: atticking FGE would cascade-break
-- Bridge/QED/Example (off the α cost-path but real theorems); the 4-line repair keeps the QED track green
-- (smooth repair over hard cut — SPEC §5 anti-Gibbs). Deviation from Turn-77 #3 (attic-for-now), justified. — Podo
def finiteGaugeEquation
    (epsilon : LOCAL Value Carrier real)
    (x : FiniteGaugeInput) : Variation :=
  defaultFiniteGaugeClosure epsilon.theory x

/-! ## Layer A and Layer B theorems -/

/-- Normal-form theorem (Layer B): the FGE has exactly the `.frechet` shape
that the gateaux → frechet branch produces. Holds by `rfl` because
`finiteGaugeEquation` is defined directly in terms of
`defaultFiniteGaugeClosure`, which produces `.frechet`. -/
theorem finiteGaugeEquation_normal_form
    (epsilon : LOCAL Value Carrier real)
    (x : FiniteGaugeInput) :
    finiteGaugeEquation epsilon x =
      .frechet x.gospel x.direction x.response
        (x.direction ∧ ¬ x.response)
        x.base epsilon.theory.differential_equation := rfl

/-- Deterministic-construction theorem (Layer A): equal inputs yield equal
FGEs. Trivially true because `finiteGaugeEquation` is a function. Stated
with `cases h; rfl` rather than `congrArg _ h` to keep the proof robust
against the section's many instance binders. -/
theorem finiteGaugeEquation_deterministic
    (epsilon : LOCAL Value Carrier real)
    {x₁ x₂ : FiniteGaugeInput} (h : x₁ = x₂) :
    finiteGaugeEquation epsilon x₁ = finiteGaugeEquation epsilon x₂ := by
  cases h
  rfl

/-! ## Conditional bridge to `transmute`

`BigRedDogProcess.transmute` is an overridable field. We can only relate
`finiteGaugeEquation` to `epsilon.theory.transmute (.gateaux ...)` if the
local theory uses the default transmute. The following predicate names that
condition; the theorem below shows the equality under it. -/

/-- Predicate: the theory's `transmute` field is the default closure (the
function literal that `BigRedDogProcess.transmute` defaults to). -/
def UsesDefaultTransmute
    (theta : BigRedDogProcess Value Carrier) : Prop :=
  theta.transmute =
    fun variation =>
      match variation with
      | .newton g p => .gateaux g d.fact.truth p theta.differential_equation
      | .gateaux g aDir bResp v =>
          .frechet g aDir bResp (aDir ∧ ¬ bResp) v theta.differential_equation
      | .frechet g aDir bResp cRes f₁ _ =>
          .gateaux g (d.fact.truth ∧ aDir) (bResp = cRes) f₁

/-- Bridge theorem: if the local theory uses the default `transmute`, then
the FGE equals what `transmute` would produce from a Gateaux variation built
from the same input. -/
theorem finiteGaugeEquation_eq_transmute
    (epsilon : LOCAL Value Carrier real)
    (h : UsesDefaultTransmute epsilon.theory)
    (x : FiniteGaugeInput) :
    finiteGaugeEquation epsilon x =
      epsilon.theory.transmute
        (.gateaux x.gospel x.direction x.response x.base) := by
  unfold finiteGaugeEquation defaultFiniteGaugeClosure
  -- After unfolding, the goal has `.frechet ... theta.differential_equation`
  -- on the left and `theta.transmute (.gateaux ...)` on the right. Rewriting
  -- with `h : UsesDefaultTransmute theta` reduces the RHS to the same
  -- `.frechet ...` form, and the rewrite closes the equality.
  rw [h]

end

end Measurement.Formalization
