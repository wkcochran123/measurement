import Measurement.Formalization.TerminalUniqueness
import Measurement.Formalization.FiniteGaugeEquation

set_option autoImplicit false

/-!
# Bridge: Encoding Finite Gauge Inputs Into Terminal Herbrand Terms

The Bridge interface names the hypotheses that connect the FGE construction
(in `FiniteGaugeEquation.lean`) to the terminal Herbrand uniqueness machinery
(in `TerminalUniqueness.lean`). This file carries:

1. **`FiniteGaugeEncoding` structure**: a partial encoding of
   `FiniteGaugeInput`s into terminal Herbrand terms, an interpreter, an
   observable map, and the agreement law tying the interpreted encoding to
   the observable.
2. **Pairwise bridge theorem** (`fge_observable_unique_under_encoding`):
   any two encodable finite gauge inputs produce the same interpreted
   observable.
3. **Observable image subsingleton theorem**
   (`fge_observable_image_subsingleton`): the subtype of observables
   reached by encodable finite gauge inputs is `Subsingleton`. The
   subtype version of the pairwise constancy claim, giving the phrase
   "encodable device image" a concrete Lean carrier.
4. **Canonical normal form bridge theorem**
   (`fge_observable_eq_inferredTerm`): each encodable finite gauge input
   agrees with the interpretation of the canonical terminal witness
   `inferredTerm`.
5. **Image normal form theorem**
   (`fge_observable_image_eq_inferredTerm`): every actual element of the
   finite-gauge observable image subtype equals `B.interpret inferredTerm`.
   Fuses the image subsingleton claim with the canonical normal form: the
   image has at most one point, and that point is the named canonical
   value.
6. **Direct Bridge combined theorem**
   (`fge_observable_unique_and_eq_inferredTerm_under_encoding`): packages
   the pairwise and canonical normal-form theorems in a single
   conjunction. A packaging lemma over the two prior theorems with no
   new hypotheses; the canonical finite-gauge combined form for this
   layer.
7. **Direct Bridge image closure theorem**
   (`fge_observable_image_closed_under_encoding`): packages
   `fge_observable_image_subsingleton` and
   `fge_observable_image_eq_inferredTerm` in a single conjunction. One
   formal handle for "the encodable observable image is closed under
   the encoding: it has at most one point, and every actual point is
   the canonical terminal observable." Adds no new hypotheses; this is
   the canonical direct Bridge image closure package. The abstract QED
   closure and via-QED finite-gauge closure live in QED.lean as
   `device_gauge_image_closed` and `fge_observable_image_closed_via_qed`.
8. **Direct Bridge image-nonempty existence theorem**
   (`fge_observable_image_nonempty_under_encoding`): given a single
   encodable finite gauge input, the encodable observable image subtype
   is `Nonempty`, inhabited by the observable produced by the supplied
   input. The conclusion is about the encodable *observable* image
   subtype, not raw `FiniteGaugeInput` values; the supplied encodable
   input is used only to supply the nonempty witness. No `Subsingleton`
   instance or routing is needed for this weaker carrier; the proof is
   one anonymous-constructor pair. Companion to the next entry,
   exposing only the weaker "at least one" carrier without committing
   to `Unique`.
9. **Direct Bridge nonempty image uniqueness theorem**
   (`fge_observable_image_unique_under_encoding`): given any single
   encodable finite gauge input, the encodable observable image subtype
   is `Unique`, not just `Subsingleton`. The `default` witness is the
   observable produced by the supplied input; the `uniq` proof is
   inherited from `fge_observable_image_subsingleton`. This is the
   "exactly one point, carrying that point explicitly" claim, as
   opposed to `fge_observable_image_subsingleton`'s "at most one
   point" claim. No new encoding or physical hypothesis is added
   beyond the single encodable input.

## Why the bridge is partial

The bridge does **not** assume every `FiniteGaugeInput` is encodable, nor
that the encoding is total over `Variation`. Instead, an explicit
`Encodable` predicate selects the inputs the device's encode map handles,
and the encoding produces an `HTerm .inferred` for those inputs only.
Even under this partiality, the bridge still supports the three image
carriers `Nonempty`, `Subsingleton`, and `Unique` on the encodable
*observable* image subtype, not on raw `FiniteGaugeInput` values.

## Proof shape

Both calc-style theorems route through the corresponding terminal-layer
result; the image-subsingleton theorem is a `Subtype.ext` wrapper around
the pairwise constancy claim; the combined theorem packages the
pairwise and normal-form theorems:

```text
pairwise:    observable x = interpret (encode x)
                          = interpret (encode y)         [terminal_observable_unique]
                          = observable y
image:       Subsingleton { o // ∃ x, Encodable x ∧ o = observable x }
                          via Subtype.ext on the pairwise theorem
normal form: observable x = interpret (encode x)
                          = interpret inferredTerm       [terminal_observable_eq_inferredTerm]
image NF:    o.1 = interpret inferredTerm
                          for any o in the encodable observable image
                          via rcases on the subtype, then normal-form
combined:    observable x = observable y                 ∧
             observable x = interpret inferredTerm
                          via anonymous constructor on pairwise + normal-form
image clos.: Subsingleton (encodable observable image)    ∧
             ∀ o in that image, o.1 = interpret inferredTerm
                          via anonymous constructor on
                          image-subsingleton + image normal-form
image uniq:  Unique (encodable observable image)
                          given a single encodable input;
                          default := supplied observable witness,
                          uniq    := from fge_observable_image_subsingleton
nonempty:    Nonempty (encodable observable image)
                          given a single encodable input;
                          witness := the supplied input's observable,
                                     ⟨B.observable x, ⟨x, hx, rfl⟩⟩;
                          one anonymous-constructor pair, no
                          Subsingleton routing needed
```

This is uniqueness of the **device-mediated gauge value on the encodable
device image** -- explicitly conditional, not a claim of physical uniqueness.

## What the bridge does NOT claim

- the encoding is total over `Variation`;
- raw `FiniteGaugeInput` values are equal under the apex theorem;
- every `FiniteGaugeInput` is encodable;
- the uniqueness extends past the encodable device image;
- the image-subsingleton theorem's `Subsingleton` is on the subtype of
  *observable values* reached by the encoding, not on raw
  `FiniteGaugeInput` values;
- the `Nonempty`, `Subsingleton`, and `Unique` image carriers extend
  beyond the encodable observable image; each carrier is about the
  subtype of *observable values* reached by the encoding, not about
  raw `FiniteGaugeInput` values.

Uniqueness belongs to the interpreted observable, not to the input.

## Naming honesty

The pairwise theorem is named `fge_observable_unique_under_encoding`, NOT
`fge_unique`, to make it clear that what is unique is the interpreted
observable computed by the device, given the encoding hypothesis. The FGE
itself is not claimed unique; the bridge is.

The direct Bridge combined theorem
(`fge_observable_unique_and_eq_inferredTerm_under_encoding`) follows the
same discipline: both conjuncts are equalities of interpreted observable
values (one against another encoded input, one against
`interpret inferredTerm`). Neither conjunct asserts equality of raw
`FiniteGaugeInput` values; the combined theorem inherits the same
boundary as the pairwise and normal-form theorems it packages.

The image normal-form theorem
(`fge_observable_image_eq_inferredTerm`) ranges over the encodable
*observable* image subtype, not over raw `FiniteGaugeInput` values. Its
conclusion is an equality of observable values (the subtype's underlying
value equals `B.interpret inferredTerm`); it inherits the same boundary
as `fge_observable_image_subsingleton` and `fge_observable_eq_inferredTerm`.

The direct Bridge image closure theorem
(`fge_observable_image_closed_under_encoding`) inherits the same
boundary: the closure conjunction is about the *observable* image
subtype, not raw `FiniteGaugeInput` values. Both conjuncts are
observable-image statements (one a `Subsingleton` of the subtype, one a
universally quantified equality of subtype values against
`B.interpret inferredTerm`); neither conjunct asserts collapse of raw
finite gauge inputs. The closure packaging adds no new hypothesis over
the two prior image theorems, so it cannot extend their scope.

The direct Bridge image-nonempty existence theorem
(`fge_observable_image_nonempty_under_encoding`) is an observable-image
claim: its `Nonempty` conclusion ranges over the observable image
subtype, not over raw `FiniteGaugeInput` values. The theorem adds no
uniqueness claim by itself; it only exposes a `Nonempty` carrier
without committing to `Subsingleton` or `Unique`. The supplied
encodable input is used only to supply the inhabitant for the
`Nonempty` constructor, and that same witness is the one later
consumed by `fge_observable_image_unique_under_encoding` to promote
the carrier to `Unique`.

The direct Bridge nonempty image uniqueness theorem
(`fge_observable_image_unique_under_encoding`) is also an observable-
image claim: its `Unique` conclusion ranges over the observable image
subtype. It strengthens `fge_observable_image_subsingleton` from "at
most one point" to "exactly one point" only because a single encodable
input is supplied as the nonempty witness. The `default` field is the
observable produced by that input; the `uniq` field is the
subsingleton elim against the existing image-subsingleton instance. No
new encoding or physical hypothesis is introduced -- the theorem
cannot extend the boundary set by `fge_observable_image_subsingleton`
and `fge_observable_image_eq_inferredTerm`; it merely promotes the
already-known subsingleton structure to `Unique` once we have a
witness in hand.
-/

namespace Measurement.Formalization

universe u

/-- The bridge interface: a partial encoding of `FiniteGaugeInput`s into
terminal Herbrand terms, an interpreter from terminal Herbrand terms to an
observable type, the observable map the bridge claims is interpreted, and the
agreement law tying them together.

This is exactly the data we need to lift `terminal_observable_unique` into a
claim about the device-mediated gauge value. -/
structure FiniteGaugeEncoding (Obs : Type u) where
  /-- The subset of finite gauge inputs that the device map encodes. -/
  Encodable  : FiniteGaugeInput → Prop
  /-- The encoding of an encodable input into the terminal Herbrand stage. -/
  encode     : (x : FiniteGaugeInput) → Encodable x → HTerm .inferred
  /-- The interpreter from terminal Herbrand terms to the observable type. -/
  interpret  : HTerm .inferred → Obs
  /-- The observable map the bridge claims is computed via `interpret ∘ encode`. -/
  observable : FiniteGaugeInput → Obs
  /-- Agreement law: the interpreted encoding agrees with the observable on
  every encodable input. -/
  agrees     : ∀ (x : FiniteGaugeInput) (hx : Encodable x),
                 interpret (encode x hx) = observable x

/-- Apex theorem: under the encoding hypotheses, the interpreted observable
of any two encodable finite gauge inputs is the same.

This is uniqueness of the device-mediated gauge value on the encodable
device image. It is NOT a claim that the FGE itself is unique, nor that
distinct physical inputs are equal.

Proof: chain the `agrees` law with `terminal_observable_unique`. -/
theorem fge_observable_unique_under_encoding
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs)
    {x y : FiniteGaugeInput}
    (hx : B.Encodable x) (hy : B.Encodable y) :
    B.observable x = B.observable y := by
  calc B.observable x
      = B.interpret (B.encode x hx) := (B.agrees x hx).symm
    _ = B.interpret (B.encode y hy) := terminal_observable_unique B.interpret _ _
    _ = B.observable y               := B.agrees y hy

/-- The finite-gauge observable image (the subtype of observables reached by
encodable finite gauge inputs) is `Subsingleton`. Bridge-level analog of
`device_gauge_image_subsingleton` in `QED.lean`: gives Volume 7's "encodable
device image" phrase a concrete Lean carrier directly over
`FiniteGaugeEncoding`, without routing through the abstract physical
experiment. Direct consequence of `fge_observable_unique_under_encoding`. -/
theorem fge_observable_image_subsingleton
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs) :
    Subsingleton
      { o : Obs //
        ∃ x : FiniteGaugeInput,
          ∃ _ : B.Encodable x,
            o = B.observable x } := by
  constructor
  intro x y
  rcases x with ⟨ox, hx⟩
  rcases y with ⟨oy, hy⟩
  rcases hx with ⟨a, ha, rfl⟩
  rcases hy with ⟨b, hb, rfl⟩
  exact Subtype.ext (fge_observable_unique_under_encoding B ha hb)

/-- Bridge-level normal form: every encodable finite gauge input has the
canonical terminal interpreted observable. This is the bridge analog of
`terminal_observable_eq_inferredTerm`: rather than just "any two encodable
inputs agree", it says "every encodable input agrees with the interpretation
of the canonical terminal witness `inferredTerm`." Useful as a rewriting
anchor for downstream proofs and as the formal version of "one terminal
value." -/
theorem fge_observable_eq_inferredTerm
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs)
    {x : FiniteGaugeInput}
    (hx : B.Encodable x) :
    B.observable x = B.interpret inferredTerm := by
  calc B.observable x
      = B.interpret (B.encode x hx)  := (B.agrees x hx).symm
    _ = B.interpret inferredTerm     :=
        terminal_observable_eq_inferredTerm B.interpret (B.encode x hx)

/-- Bridge-level image normal form: every actual element of the finite-gauge
observable image subtype equals `B.interpret inferredTerm`. Fuses
`fge_observable_image_subsingleton` (which says the image has at most one
point) with `fge_observable_eq_inferredTerm` (which names that point's
value). Direct-Bridge analog of `device_gauge_image_eq_inferredTerm` at the
QED layer; gives Volume 7's phrase "the encodable image collapses to the
canonical terminal observable" a concrete carrier directly over
`FiniteGaugeEncoding`. -/
theorem fge_observable_image_eq_inferredTerm
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs)
    (o : { o : Obs //
        ∃ x : FiniteGaugeInput,
          ∃ _ : B.Encodable x,
            o = B.observable x }) :
    o.1 = B.interpret inferredTerm := by
  rcases o with ⟨v, hv⟩
  rcases hv with ⟨x, hx, rfl⟩
  exact fge_observable_eq_inferredTerm B hx

/-- Direct Bridge combined theorem: packages the pairwise constancy
(`fge_observable_unique_under_encoding`) and the canonical normal-form
theorem (`fge_observable_eq_inferredTerm`) in a single statement. The
direct-bridge analog of
`gauge_unique_and_eq_inferredTerm_on_device_image` at the QED layer.
Adds no new hypotheses; this is a packaging lemma over the two prior
theorems, and it keeps Bridge.lean canonical for finite-gauge inputs
alongside the via-QED combined theorem in `QED.lean`. -/
theorem fge_observable_unique_and_eq_inferredTerm_under_encoding
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs)
    {x y : FiniteGaugeInput}
    (hx : B.Encodable x) (hy : B.Encodable y) :
    B.observable x = B.observable y ∧ B.observable x = B.interpret inferredTerm :=
  ⟨fge_observable_unique_under_encoding B hx hy,
   fge_observable_eq_inferredTerm B hx⟩

/-- Direct Bridge image closure theorem: packages
`fge_observable_image_subsingleton` (the encodable observable image has
at most one point) with `fge_observable_image_eq_inferredTerm` (every
actual element of that image equals `B.interpret inferredTerm`) in a
single conjunction. One formal handle for the phrase "the encodable
observable image is closed under the encoding, collapsing to the
canonical terminal observable." Adds no new hypotheses; this is the
canonical direct Bridge image closure package. The abstract QED
closure and via-QED finite-gauge closure live in QED.lean as
`device_gauge_image_closed` and `fge_observable_image_closed_via_qed`.

Boundary: the closure is about the *observable* image subtype, not raw
`FiniteGaugeInput` values. Both conjuncts inherit the same scope as the
two prior image theorems they package -- the encodable device image,
nothing more. -/
theorem fge_observable_image_closed_under_encoding
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs) :
    Subsingleton
      { o : Obs //
        ∃ x : FiniteGaugeInput,
          ∃ _ : B.Encodable x,
            o = B.observable x } ∧
    ∀ o : { o : Obs //
        ∃ x : FiniteGaugeInput,
          ∃ _ : B.Encodable x,
            o = B.observable x },
      o.1 = B.interpret inferredTerm :=
  ⟨fge_observable_image_subsingleton B,
   fge_observable_image_eq_inferredTerm B⟩

/-- Direct Bridge image-nonempty existence theorem: given any single
encodable finite gauge input `x`, the encodable observable image
subtype is `Nonempty`, inhabited by `⟨B.observable x, ⟨x, hx, rfl⟩⟩`.
The **canonical** finite-gauge image-nonempty existence theorem; the
abstract QED (`device_gauge_image_nonempty`) and via-QED
(`fge_observable_image_nonempty_via_qed`) versions in `QED.lean`
mirror this theorem rather than replacing it.

The conclusion is about the encodable *finite-gauge observable image*
subtype, not raw `FiniteGaugeInput` values; the hypothesis `hx` is
used only to supply the nonempty witness. The theorem adds no
uniqueness claim by itself and needs no `Subsingleton` instance or
routing for the proof, which is one anonymous-constructor pair;
it merely exposes the weaker `Nonempty` carrier as a companion to
`fge_observable_image_unique_under_encoding`. Useful when a downstream
caller wants `Nonempty` without `Unique`, e.g. for `Nonempty.elim` or
`Classical.choice`-style reasoning over the observable image. -/
theorem fge_observable_image_nonempty_under_encoding
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs)
    {x : FiniteGaugeInput}
    (hx : B.Encodable x) :
    Nonempty
      { o : Obs //
        ∃ y : FiniteGaugeInput,
          ∃ _ : B.Encodable y,
            o = B.observable y } :=
  ⟨⟨B.observable x, ⟨x, hx, rfl⟩⟩⟩

/-- Direct Bridge nonempty image uniqueness theorem: given any single
encodable finite gauge input `x`, the encodable observable image
subtype is `Unique`. This is the "exactly one point, with that point
named" strengthening of `fge_observable_image_subsingleton`'s "at most
one point" claim.

Concretely:

- `default` is the observable produced by the supplied input,
  `⟨B.observable x, ⟨x, hx, rfl⟩⟩`;
- `uniq` is inherited from `fge_observable_image_subsingleton` via
  `Subsingleton.elim` against `default`.

This is *nonempty image* uniqueness, NOT raw input uniqueness. The
hypothesis `hx : B.Encodable x` is used only to supply the witness;
no new encoding, physical, or observable hypothesis is added. The
boundary inherited from `fge_observable_image_subsingleton` and
`fge_observable_image_eq_inferredTerm` is unchanged: the `Unique`
conclusion ranges over the observable image subtype, never over raw
`FiniteGaugeInput` values. -/
def fge_observable_image_unique_under_encoding
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs)
    {x : FiniteGaugeInput}
    (hx : B.Encodable x) :
    OnePoint
      { o : Obs //
        ∃ y : FiniteGaugeInput,
          ∃ _ : B.Encodable y,
            o = B.observable y } := by
  refine
    { default := ⟨B.observable x, ⟨x, hx, rfl⟩⟩,
      uniq := ?_ }
  intro o
  exact @Subsingleton.elim _
    (fge_observable_image_subsingleton B)
    o
    ⟨B.observable x, ⟨x, hx, rfl⟩⟩

end Measurement.Formalization
