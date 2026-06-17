import Measurement.Formalization.QED

set_option autoImplicit false

/-!
# Example: Trivial Sanity Instances Over The Four-Layer Stack

This file is a sanity check on the four-layer formalization
(`TerminalUniqueness`, `FiniteGaugeEquation`, `Bridge`, `QED`). It
carries direct terminal-level checks plus two structural encoding tracks
over `Unit`. The terminal layer checks the endpoint facts directly; the
Bridge and QED tracks exercise the pairwise uniqueness, image
subsingleton, canonical normal form, image normal form, combined
pairwise/normal-form, image closure, image-nonempty existence, and
nonempty image uniqueness theorem surfaces:

1. **Terminal layer**: direct checks over `HTerm .inferred`, exercising
   `hterm_inferred_eq_inferredTerm`, `terminal_observable_eq_inferredTerm`,
   `terminal_observable_image_unique`,
   `terminal_observable_image_subsingleton`, and
   `terminal_observable_image_nonempty` with a trivial interpreter.
   These are direct terminal endpoint checks, NOT image-surface tracks
   like the Bridge and QED layers below.
2. **QED track**: a `PhysicalExperiment` + `DeviceEncoding` over `Unit`,
   exercising the pairwise apex (`gauge_unique_on_device_image`), the
   device-image subsingleton (`device_gauge_image_subsingleton`), the
   canonical normal-form apex (`gauge_eq_inferredTerm_on_device_image`),
   the image normal-form apex (`device_gauge_image_eq_inferredTerm`),
   the combined apex
   (`gauge_unique_and_eq_inferredTerm_on_device_image`), the image
   closure apex (`device_gauge_image_closed`), the nonempty
   device-image uniqueness apex (`device_gauge_image_unique`), and the
   device-image-nonempty existence apex (`device_gauge_image_nonempty`).
3. **Bridge track**: a `FiniteGaugeEncoding Unit`, exercising the pairwise
   bridge theorem (`fge_observable_unique_under_encoding`), the
   observable-image subsingleton (`fge_observable_image_subsingleton`),
   the canonical normal-form bridge theorem
   (`fge_observable_eq_inferredTerm`), the direct Bridge image
   normal-form theorem (`fge_observable_image_eq_inferredTerm`), the
   direct Bridge combined theorem
   (`fge_observable_unique_and_eq_inferredTerm_under_encoding`), the
   direct Bridge image closure theorem
   (`fge_observable_image_closed_under_encoding`), the direct Bridge
   nonempty image uniqueness theorem
   (`fge_observable_image_unique_under_encoding`), the direct Bridge
   image-nonempty existence theorem
   (`fge_observable_image_nonempty_under_encoding`), the via-QED pairwise
   corollary (`fge_observable_unique_via_qed`), the via-QED
   image-subsingleton corollary
   (`fge_observable_image_subsingleton_via_qed`), the via-QED canonical
   normal-form corollary (`fge_observable_eq_inferredTerm_via_qed`), the
   via-QED image normal-form corollary
   (`fge_observable_image_eq_inferredTerm_via_qed`), the via-QED
   combined corollary
   (`fge_observable_unique_and_eq_inferredTerm_via_qed`), the via-QED
   image closure corollary
   (`fge_observable_image_closed_via_qed`), the via-QED nonempty
   image uniqueness corollary (`fge_observable_image_unique_via_qed`),
   and the via-QED image-nonempty existence corollary
   (`fge_observable_image_nonempty_via_qed`).

The three layers together confirm:

- the structures have the field shapes expected by the apex theorems;
- the pairwise uniqueness, image subsingleton, canonical normal form,
  image normal form, combined pairwise/normal-form, image closure,
  image-nonempty existence, and nonempty image uniqueness theorem
  surfaces accept real encoding arguments (the combined, image closure,
  image-nonempty existence, and nonempty image uniqueness surfaces
  include both the direct Bridge and via-QED routes);
- the agreement laws' `rfl` discharges cleanly for the trivial encodings;
- the canonical normal-form corollaries compose with the structures;
- the image subsingleton, image normal form, image closure,
  image-nonempty existence, and nonempty image uniqueness theorems
  together hand the device-image subtype to downstream callers as a
  concrete image carrier:
  image subsingleton gives the subtype a single-point `Subsingleton`
  structure, image normal form names that single point as
  `interpret inferredTerm`, image closure packages both facts in a
  single conjunction, image-nonempty existence exposes the weaker
  `Nonempty` carrier without committing to `Unique`, and nonempty
  image uniqueness promotes the `Subsingleton` to `Unique` once a
  single encodable input supplies the nonempty witness (the image
  surfaces include both the direct Bridge image and the via-QED image
  routes at each of the image subsingleton, image normal form,
  image closure, image-nonempty existence, and nonempty image
  uniqueness layers);
- the terminal-layer endpoints (`hterm_inferred_eq_inferredTerm`,
  `terminal_observable_eq_inferredTerm`) elaborate directly without
  going through an encoding.

If a future build of the Formalization library fails on any of these
theorem surfaces, this file is the first place the signature mismatch
would surface.

## What this file does NOT prove

This file does not constitute a physical interpretation.

- The terminal-layer checks are structural checks of the serial
  Herbrand endpoint; they do not interpret it.
- `Unit` is structural padding for the two encoding tracks; the gauge
  map sends everything to a single observable.
- The examples exercise theorem signatures and agreement laws; they do
  not build a nontrivial finite gauge input or a full physical encoding.

The file documents how the apex theorems are used by ANY honest
encoding; it does not assert that any particular nontrivial encoding
exists.
-/

namespace Measurement.Formalization

/-! ## Trivial experiment and encoding -/

/-- The simplest possible `PhysicalExperiment`: one candidate (`Unit`), one
observable (`Unit`), every candidate admissible, gauge constant at `()`. -/
def trivialExperiment : PhysicalExperiment where
  Candidate  := Unit
  Observable := Unit
  admissible := fun _ => True
  gauge      := fun _ => ()

/-- The corresponding trivial `DeviceEncoding`: every candidate encodable;
encode sends everything to the canonical terminal Herbrand term
`inferredTerm`; the interpreter sends every terminal term to `()`; the
agreement law is `rfl` because both sides reduce to `()`. -/
def trivialEncoding : DeviceEncoding trivialExperiment where
  Encodable := fun _ => True
  encode    := fun _ _ _ => inferredTerm
  interpret := fun _ => ()
  agrees    := fun _ _ _ => rfl

/-! ## Sanity check: the apex theorem applies -/

/-- The apex theorem applied to the trivial encoding. For any two admissible,
encodable `Unit` candidates, the gauge values agree. (Vacuously, since `Unit`
has one inhabitant.) The point is that the theorem's signature accepts the
trivial encoding and elaborates without complaint. -/
example
    (a b : Unit)
    (ha : trivialExperiment.admissible a)
    (hb : trivialExperiment.admissible b)
    (ea : trivialEncoding.Encodable a)
    (eb : trivialEncoding.Encodable b) :
    trivialExperiment.gauge a = trivialExperiment.gauge b :=
  gauge_unique_on_device_image trivialExperiment trivialEncoding ha hb ea eb

/-- A variant without explicit hypotheses, exploiting the fact that
`admissible := fun _ => True` and `Encodable := fun _ => True` are trivially
inhabited. Demonstrates that the theorem's hypotheses can be supplied
constructively for any chosen pair of `Unit` values. -/
example (a b : Unit) :
    trivialExperiment.gauge a = trivialExperiment.gauge b :=
  gauge_unique_on_device_image trivialExperiment trivialEncoding
    trivial trivial trivial trivial

/-! ## Trivial finite-gauge-bridge encoding

A second sanity check, this time exercising `fge_observable_unique_under_encoding`
directly rather than the abstract `gauge_unique_on_device_image`. Same trivial
shape: every `FiniteGaugeInput` is `Encodable`, the encoding lands at
`inferredTerm`, the interpreter and observable both return `()`.

The point is to confirm that the FGE bridge surface in `Bridge.lean` accepts a
plain instantiation and that the agreement law's `rfl` discharges cleanly. -/

/-- Trivial finite-gauge encoding: every `FiniteGaugeInput` is encodable, the
encoding sends everything to `inferredTerm`, the interpreter and observable
both return `()`. -/
def trivialFGEEncoding : FiniteGaugeEncoding Unit where
  Encodable  := fun _ => True
  encode     := fun _ _ => inferredTerm
  interpret  := fun _ => ()
  observable := fun _ => ()
  agrees     := fun _ _ => rfl

/-- The FGE bridge theorem applied to the trivial encoding. For any two
encodable finite gauge inputs, the interpreted observable is the same.
Vacuously, since `Unit` has one inhabitant. -/
example (x y : FiniteGaugeInput) :
    trivialFGEEncoding.observable x = trivialFGEEncoding.observable y :=
  fge_observable_unique_under_encoding trivialFGEEncoding trivial trivial

/-! ## Direct terminal-level sanity checks

The Bridge and QED examples above invoke the terminal-level uniqueness
theorems transitively (through `B.agrees` plus
`terminal_observable_unique` / `terminal_observable_eq_inferredTerm`).
The five examples below exercise the terminal-level theorems directly,
without an intermediate encoding structure, so the example file visibly
covers all three normal-form layers: terminal, bridge, and QED. These
remain direct terminal endpoint checks; they are NOT the Bridge/QED
image-surface tracks. -/

/-- Direct check on `hterm_inferred_eq_inferredTerm`: every `HTerm .inferred`
equals the canonical `inferredTerm`. Structural; no physics. -/
example (t : HTerm .inferred) :
    t = inferredTerm :=
  hterm_inferred_eq_inferredTerm t

/-- Direct check on `terminal_observable_eq_inferredTerm` with a trivial
interpreter (`fun _ => ()`). The interpreted observable on any terminal term
agrees with the interpreted observable on the canonical `inferredTerm`. -/
example (t : HTerm .inferred) :
    (fun _ : HTerm .inferred => ()) t =
      (fun _ : HTerm .inferred => ()) inferredTerm :=
  terminal_observable_eq_inferredTerm
    (fun _ : HTerm .inferred => ()) t

/-- Direct check on `terminal_observable_image_unique` with the trivial
interpreter (`fun _ => ()`): the terminal-level observable image subtype
is `Unique` with the canonical default `interpret inferredTerm`. This is
the terminal endpoint analog of the Bridge and QED nonempty `Unique`
image theorems, but at the terminal layer it needs no nonempty
hypothesis because `inferredTerm` is always available as the canonical
witness. -/
example :
    OnePoint
      { a : Unit //
        ∃ t : HTerm .inferred,
          a = (fun _ : HTerm .inferred => ()) t } :=
  terminal_observable_image_unique
    (fun _ : HTerm .inferred => ())

/-- Direct check on `terminal_observable_image_subsingleton` with the
trivial interpreter (`fun _ => ()`): the terminal-level observable image
subtype is also `Subsingleton`. Terminal endpoint companion to the
preceding `terminal_observable_image_unique` example; closes the
`Subsingleton`/`Unique` pair on the terminal observable image, matching
the Bridge/QED `*_image_subsingleton` + `*_image_unique` symmetry. -/
example :
    Subsingleton
      { a : Unit //
        ∃ t : HTerm .inferred,
          a = (fun _ : HTerm .inferred => ()) t } :=
  terminal_observable_image_subsingleton
    (fun _ : HTerm .inferred => ())

/-- Direct check on `terminal_observable_image_nonempty` with the trivial
interpreter (`fun _ => ()`): the terminal-level observable image subtype
is `Nonempty`, inhabited via the canonical `inferredTerm` witness.
Terminal endpoint companion exposing only the weaker `Nonempty` carrier
without committing to `Subsingleton` or `Unique`; mirror of the
Bridge/QED `*_image_nonempty` shape. -/
example :
    Nonempty
      { a : Unit //
        ∃ t : HTerm .inferred,
          a = (fun _ : HTerm .inferred => ()) t } :=
  terminal_observable_image_nonempty
    (fun _ : HTerm .inferred => ())

/-! ## Canonical normal form sanity checks

The pairwise sanity checks above exercise the `*_unique_*` theorems. The two
examples below exercise the bridge and QED canonical normal-form theorems
(`fge_observable_eq_inferredTerm` and `gauge_eq_inferredTerm_on_device_image`).
Both remain structural; `Unit` is still padding, no physical interpretation
is claimed. -/

/-- FGE bridge canonical normal form: every encodable finite gauge input has
the canonical terminal interpreted observable. Under the trivial encoding,
this is the equality `() = ()`. -/
example (x : FiniteGaugeInput) :
    trivialFGEEncoding.observable x =
      trivialFGEEncoding.interpret inferredTerm :=
  fge_observable_eq_inferredTerm trivialFGEEncoding trivial

/-- QED-level canonical normal form: every admissible, encodable candidate's
gauge value equals the canonical terminal interpretation. Under the trivial
encoding, this is the equality `() = ()`. -/
example (a : Unit) :
    trivialExperiment.gauge a =
      trivialEncoding.interpret inferredTerm :=
  gauge_eq_inferredTerm_on_device_image
    trivialExperiment trivialEncoding trivial trivial

/-! ## Finite-gauge via-QED sanity checks

The `Bridge.lean` theorems have second proof routes through the QED apex
(`fge_observable_unique_via_qed` and `fge_observable_eq_inferredTerm_via_qed`,
the via-QED pairwise and canonical normal-form corollaries). The examples
below exercise those via-QED routes against the same `trivialFGEEncoding`
used by the direct-Bridge sanity checks above. The architectural claim is
"the bridge IS the QED apex on the induced experiment"; these examples
confirm the via-QED surfaces elaborate without going through the direct
Bridge proofs. -/

/-- Via-QED pairwise check on the bridge: two encodable finite gauge inputs
have the same interpreted observable, proved by routing through
`gauge_unique_on_device_image` on the induced experiment. -/
example (x y : FiniteGaugeInput) :
    trivialFGEEncoding.observable x = trivialFGEEncoding.observable y :=
  fge_observable_unique_via_qed trivialFGEEncoding trivial trivial

/-- Via-QED canonical normal form on the bridge: every encodable finite
gauge input has the canonical terminal interpreted observable, proved by
routing through `gauge_eq_inferredTerm_on_device_image` on the induced
experiment. -/
example (x : FiniteGaugeInput) :
    trivialFGEEncoding.observable x =
      trivialFGEEncoding.interpret inferredTerm :=
  fge_observable_eq_inferredTerm_via_qed trivialFGEEncoding trivial

/-! ## Combined apex sanity checks

Three combined surfaces now exist:

```text
gauge_unique_and_eq_inferredTerm_on_device_image           (QED)
fge_observable_unique_and_eq_inferredTerm_via_qed          (via-QED)
fge_observable_unique_and_eq_inferredTerm_under_encoding   (direct Bridge)
```

The examples below exercise all three against the existing trivial
encodings. Structural only; `Unit` is still padding. The direct Bridge
combined theorem is the canonical finite-gauge form; the via-QED
combined theorem is the architectural witness. -/

/-- Combined QED apex applied to the trivial encoding: pairwise constancy
plus canonical normal form in a single statement. Both conjuncts hold
trivially under `Unit`; the example confirms the conjunction signature
elaborates against the trivialEncoding. -/
example (a b : Unit) :
    trivialExperiment.gauge a = trivialExperiment.gauge b ∧
      trivialExperiment.gauge a = trivialEncoding.interpret inferredTerm :=
  gauge_unique_and_eq_inferredTerm_on_device_image
    trivialExperiment trivialEncoding trivial trivial trivial trivial

/-- Finite-gauge via-QED combined apex applied to the trivial FGE encoding:
pairwise constancy and canonical normal form together, proved by routing
through the QED apex. Structural sanity check on the via-QED combined
surface (architectural witness). -/
example (x y : FiniteGaugeInput) :
    trivialFGEEncoding.observable x = trivialFGEEncoding.observable y ∧
      trivialFGEEncoding.observable x =
        trivialFGEEncoding.interpret inferredTerm :=
  fge_observable_unique_and_eq_inferredTerm_via_qed
    trivialFGEEncoding trivial trivial

/-- Direct Bridge combined apex applied to the trivial FGE encoding:
pairwise constancy and canonical normal form together, proved directly
through the Bridge layer's own pairwise and normal-form theorems.
Structural sanity check on the canonical finite-gauge combined surface. -/
example (x y : FiniteGaugeInput) :
    trivialFGEEncoding.observable x = trivialFGEEncoding.observable y ∧
      trivialFGEEncoding.observable x =
        trivialFGEEncoding.interpret inferredTerm :=
  fge_observable_unique_and_eq_inferredTerm_under_encoding
    trivialFGEEncoding trivial trivial

/-! ## Image subsingleton sanity checks

The QED and Bridge image-subsingleton theorems state that the device
gauge image and the finite-gauge observable image are each `Subsingleton`.
The examples below exercise both subtype surfaces against the existing
trivial encodings. Structural only; the subtypes are inhabited by at most
one element under `Unit`-typed observables. -/

/-- The QED-level device gauge image over `trivialEncoding` is
`Subsingleton`. Direct instantiation of
`device_gauge_image_subsingleton`. -/
example :
    Subsingleton
      { o : trivialExperiment.Observable //
        ∃ a : trivialExperiment.Candidate,
          ∃ _ : trivialExperiment.admissible a,
            ∃ _ : trivialEncoding.Encodable a,
              o = trivialExperiment.gauge a } :=
  device_gauge_image_subsingleton trivialExperiment trivialEncoding

/-- The Bridge-level finite-gauge observable image over `trivialFGEEncoding`
is `Subsingleton`. Direct instantiation of
`fge_observable_image_subsingleton`. -/
example :
    Subsingleton
      { o : Unit //
        ∃ x : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable x,
            o = trivialFGEEncoding.observable x } :=
  fge_observable_image_subsingleton trivialFGEEncoding

/-- Via-QED architectural route to the same image-subsingleton conclusion.
The subtype expression is identical to the direct Bridge example above; the
proof routes through `fge_observable_image_subsingleton_via_qed`, which in
turn uses `fge_observable_unique_via_qed` and `gauge_unique_on_device_image`
on the induced experiment. Structural sanity check on the via-QED
finite-gauge image-subsingleton surface. -/
example :
    Subsingleton
      { o : Unit //
        ∃ x : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable x,
            o = trivialFGEEncoding.observable x } :=
  fge_observable_image_subsingleton_via_qed trivialFGEEncoding

/-! ## Image normal form sanity checks

The three image normal-form theorems say that every actual element of
the relevant gauge-image / observable-image subtype equals
`interpret inferredTerm`. The examples below exercise all three theorems
against the existing trivial encodings, with witnesses built from `()`
(QED side) or a universally-quantified FiniteGaugeInput (Bridge side,
both routes). Structural only; `Unit` is still padding. -/

/-- QED-level image normal-form check: under the trivial encoding, any
witnessed device-image element equals `trivialEncoding.interpret inferredTerm`.
Constructs the subtype element with `()` candidate and `trivial` proofs for
both admissibility and encodability. -/
example :
    (⟨(), ⟨(), trivial, trivial, rfl⟩⟩ :
      { o : trivialExperiment.Observable //
        ∃ a : trivialExperiment.Candidate,
          ∃ _ : trivialExperiment.admissible a,
            ∃ _ : trivialEncoding.Encodable a,
              o = trivialExperiment.gauge a }).1 =
      trivialEncoding.interpret inferredTerm :=
  device_gauge_image_eq_inferredTerm
    trivialExperiment
    trivialEncoding
    ⟨(), ⟨(), trivial, trivial, rfl⟩⟩

/-- Direct Bridge-level image normal-form check: for any FiniteGaugeInput
`x`, the witnessed observable-image element built from `x` and `trivial`
encodability equals `trivialFGEEncoding.interpret inferredTerm`. Uses the
direct Bridge proof in `fge_observable_image_eq_inferredTerm`. -/
example (x : FiniteGaugeInput) :
    (⟨trivialFGEEncoding.observable x, ⟨x, trivial, rfl⟩⟩ :
      { o : Unit //
        ∃ y : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable y,
            o = trivialFGEEncoding.observable y }).1 =
      trivialFGEEncoding.interpret inferredTerm :=
  fge_observable_image_eq_inferredTerm
    trivialFGEEncoding
    ⟨trivialFGEEncoding.observable x, ⟨x, trivial, rfl⟩⟩

/-- Via-QED architectural route to the same finite-gauge image normal form
conclusion. Subtype shape identical to the direct Bridge example above; the
proof routes through `fge_observable_image_eq_inferredTerm_via_qed`, which
in turn uses `device_gauge_image_eq_inferredTerm` on the induced
experiment. -/
example (x : FiniteGaugeInput) :
    (⟨trivialFGEEncoding.observable x, ⟨x, trivial, rfl⟩⟩ :
      { o : Unit //
        ∃ y : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable y,
            o = trivialFGEEncoding.observable y }).1 =
      trivialFGEEncoding.interpret inferredTerm :=
  fge_observable_image_eq_inferredTerm_via_qed
    trivialFGEEncoding
    ⟨trivialFGEEncoding.observable x, ⟨x, trivial, rfl⟩⟩

/-! ## Image closure sanity checks

The three image closure theorems package the relevant image subsingleton
theorem with the relevant image normal form theorem in a single
conjunction. The examples below exercise all three closure packages
against the existing trivial encodings. Structural only; both conjuncts
hold trivially under `Unit` (the subtype is `Subsingleton` because
`Unit` has one inhabitant, and the universal quantifier discharges by
the underlying normal form theorem). -/

/-- Direct Bridge image closure check: the encodable observable image
subtype over `trivialFGEEncoding` is `Subsingleton`, AND every actual
element of that subtype equals `trivialFGEEncoding.interpret inferredTerm`.
Direct instantiation of `fge_observable_image_closed_under_encoding`. -/
example :
    Subsingleton
      { o : Unit //
        ∃ x : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable x,
            o = trivialFGEEncoding.observable x } ∧
    ∀ o : { o : Unit //
        ∃ x : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable x,
            o = trivialFGEEncoding.observable x },
      o.1 = trivialFGEEncoding.interpret inferredTerm :=
  fge_observable_image_closed_under_encoding trivialFGEEncoding

/-- Abstract QED image closure check: the device gauge image subtype
over `trivialExperiment` + `trivialEncoding` is `Subsingleton`, AND
every actual element of that subtype equals
`trivialEncoding.interpret inferredTerm`. Direct instantiation of
`device_gauge_image_closed`. -/
example :
    Subsingleton
      { o : trivialExperiment.Observable //
        ∃ c : trivialExperiment.Candidate,
          ∃ _ : trivialExperiment.admissible c,
            ∃ _ : trivialEncoding.Encodable c,
              o = trivialExperiment.gauge c } ∧
    ∀ o : { o : trivialExperiment.Observable //
        ∃ c : trivialExperiment.Candidate,
          ∃ _ : trivialExperiment.admissible c,
            ∃ _ : trivialEncoding.Encodable c,
              o = trivialExperiment.gauge c },
      o.1 = trivialEncoding.interpret inferredTerm :=
  device_gauge_image_closed trivialExperiment trivialEncoding

/-- Via-QED architectural route to the same finite-gauge image closure
conclusion. Subtype shape and conjunction shape are identical to the
direct Bridge example above; the proof routes through
`fge_observable_image_closed_via_qed`, which in turn pairs
`fge_observable_image_subsingleton_via_qed` with
`fge_observable_image_eq_inferredTerm_via_qed`, both of which factor
through the QED apex on the induced experiment. -/
example :
    Subsingleton
      { o : Unit //
        ∃ x : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable x,
            o = trivialFGEEncoding.observable x } ∧
    ∀ o : { o : Unit //
        ∃ x : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable x,
            o = trivialFGEEncoding.observable x },
      o.1 = trivialFGEEncoding.interpret inferredTerm :=
  fge_observable_image_closed_via_qed trivialFGEEncoding

/-! ## Nonempty image uniqueness sanity checks

The three nonempty image uniqueness theorems promote the relevant
image-subsingleton claim from "at most one point" to "exactly one
point, with that point carried explicitly as the `Unique` default"
once a single encodable / admissible-encodable input is supplied. The
examples below exercise all three theorems against the existing
trivial encodings. Structural only; the subtypes carry exactly one
inhabitant under the `Unit`-typed observable in either track. -/

/-- Direct Bridge nonempty image uniqueness check: given any
FiniteGaugeInput `x`, the encodable observable image subtype over
`trivialFGEEncoding` is `Unique`. The supplied input is the nonempty
witness; the `uniq` proof routes through the existing
`fge_observable_image_subsingleton` Subsingleton instance. Direct
instantiation of `fge_observable_image_unique_under_encoding`. -/
example (x : FiniteGaugeInput) :
    OnePoint
      { o : Unit //
        ∃ y : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable y,
            o = trivialFGEEncoding.observable y } :=
  fge_observable_image_unique_under_encoding
    trivialFGEEncoding (x := x) trivial

/-- Abstract QED nonempty device-image uniqueness check: the device
gauge image subtype over `trivialExperiment` + `trivialEncoding` is
`Unique`, with the supplied `()` candidate plus two `trivial` proofs
of admissibility and encodability acting as the nonempty witness. The
`uniq` proof routes through the existing `device_gauge_image_subsingleton`
Subsingleton instance. Direct instantiation of `device_gauge_image_unique`. -/
example :
    OnePoint
      { o : trivialExperiment.Observable //
        ∃ a : trivialExperiment.Candidate,
          ∃ _ : trivialExperiment.admissible a,
            ∃ _ : trivialEncoding.Encodable a,
              o = trivialExperiment.gauge a } :=
  device_gauge_image_unique
    trivialExperiment trivialEncoding (a := ()) trivial trivial

/-- Via-QED architectural route to the same finite-gauge nonempty image
uniqueness conclusion. Subtype shape is identical to the direct Bridge
example above; the proof routes through
`fge_observable_image_unique_via_qed`, whose `uniq` field in turn uses
`fge_observable_image_subsingleton_via_qed` (the via-QED architectural
Subsingleton instance), which itself factors through the QED apex on
the induced experiment. -/
example (x : FiniteGaugeInput) :
    OnePoint
      { o : Unit //
        ∃ y : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable y,
            o = trivialFGEEncoding.observable y } :=
  fge_observable_image_unique_via_qed
    trivialFGEEncoding (x := x) trivial

/-! ## Image-nonempty existence sanity checks

The three image-nonempty existence theorems
(`fge_observable_image_nonempty_under_encoding`,
`device_gauge_image_nonempty`, and
`fge_observable_image_nonempty_via_qed`) expose only the weaker
`Nonempty` carrier without committing to the full `Unique` (or
`Subsingleton`) instance. The examples below exercise all three
theorems against the existing trivial encodings. Structural only;
the subtypes carry exactly one inhabitant under `Unit`-typed
observables in either track. -/

/-- Direct Bridge image-nonempty existence check: given any
FiniteGaugeInput `x`, the encodable observable image subtype over
`trivialFGEEncoding` is `Nonempty`, inhabited by the supplied input's
observable. Direct instantiation of
`fge_observable_image_nonempty_under_encoding`. -/
example (x : FiniteGaugeInput) :
    Nonempty
      { o : Unit //
        ∃ y : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable y,
            o = trivialFGEEncoding.observable y } :=
  fge_observable_image_nonempty_under_encoding
    trivialFGEEncoding (x := x) trivial

/-- Abstract QED device-image-nonempty existence check: the device
gauge image subtype over `trivialExperiment` + `trivialEncoding` is
`Nonempty`, inhabited by the `()` candidate's gauge value with two
`trivial` proofs of admissibility and encodability acting as the
witness. Direct instantiation of `device_gauge_image_nonempty`. -/
example :
    Nonempty
      { o : trivialExperiment.Observable //
        ∃ a : trivialExperiment.Candidate,
          ∃ _ : trivialExperiment.admissible a,
            ∃ _ : trivialEncoding.Encodable a,
              o = trivialExperiment.gauge a } :=
  device_gauge_image_nonempty
    trivialExperiment trivialEncoding (a := ()) trivial trivial

/-- Via-QED architectural route to the same finite-gauge
image-nonempty existence conclusion. Subtype shape is identical to
the direct Bridge example above; the proof routes through
`fge_observable_image_nonempty_via_qed`. Because the conclusion is
`Nonempty`, the proof term reduces to the same anonymous-constructor
pair as the direct Bridge version -- no via-QED-style routing through
the QED apex is needed for `Nonempty`. -/
example (x : FiniteGaugeInput) :
    Nonempty
      { o : Unit //
        ∃ y : FiniteGaugeInput,
          ∃ _ : trivialFGEEncoding.Encodable y,
            o = trivialFGEEncoding.observable y } :=
  fge_observable_image_nonempty_via_qed
    trivialFGEEncoding (x := x) trivial

end Measurement.Formalization
