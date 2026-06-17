import Measurement.Formalization.Bridge

set_option autoImplicit false

/-!
# QED: Gauge Uniqueness On The Device Image

The apex layer of the formalization. At the QED layer the eight-surface
image family takes its abstract form: pairwise uniqueness, image
subsingleton, canonical normal form, image normal form, combined
pairwise/normal-form, image closure, nonempty image, and nonempty
image uniqueness. This file carries:

1. **Abstract structures**: `PhysicalExperiment` (candidates, observables,
   admissibility, gauge) and `DeviceEncoding` (Encodable subset, encode into
   terminal Herbrand terms, interpret, agreement law against the gauge).
2. **Pairwise apex theorem**: `gauge_unique_on_device_image` says any two
   admissible, encodable candidates have the same gauge value.
3. **Device image subsingleton theorem**:
   `device_gauge_image_subsingleton` says the subtype of observable values
   reached by admissible, encodable candidates is `Subsingleton`. The
   subtype version of the pairwise constancy claim, giving the phrase
   "device image" a concrete Lean carrier at the abstract apex.
4. **Canonical normal form apex theorem**:
   `gauge_eq_inferredTerm_on_device_image` says every such candidate's gauge
   value equals the interpretation of the canonical terminal witness
   `inferredTerm`.
5. **Image normal form theorem**:
   `device_gauge_image_eq_inferredTerm` says every actual element of the
   device gauge image subtype equals `B.interpret inferredTerm`. Fuses
   the image subsingleton claim with the canonical normal form: the
   image has at most one point, and that point is the named canonical
   value.
6. **Combined apex theorem**:
   `gauge_unique_and_eq_inferredTerm_on_device_image` packages the pairwise
   and normal-form statements in a single conjunction; a packaging lemma
   over the two prior theorems, no new hypotheses.
7. **Image closure apex theorem**:
   `device_gauge_image_closed` packages the device-image subsingleton
   theorem and the image normal-form theorem in a single conjunction.
   One formal handle for "the device gauge image is closed under the
   encoding: it has at most one point, and every actual point is the
   canonical terminal observable." Adds no new hypotheses; abstract
   QED only. The finite-gauge via-QED image closure
   (`fge_observable_image_closed_via_qed`) is listed below in entry 11
   as the architectural witness on the induced experiment, while the
   canonical finite-gauge closure (`fge_observable_image_closed_under_encoding`)
   stays in `Bridge.lean`.
8. **Device-image-nonempty existence theorem**:
   `device_gauge_image_nonempty` says that given one admissible,
   encodable candidate, the device gauge image subtype is `Nonempty`,
   inhabited by the gauge value of the supplied candidate. The
   conclusion is about the admissible, encodable *device gauge image*
   subtype, not raw `E.Candidate` values; the hypotheses `ha` and `ea`
   are used only to supply the nonempty witness. No `Subsingleton`
   instance or routing is needed for this weaker carrier; the proof is
   one anonymous-constructor pair. Companion to the next entry,
   exposing only the weaker "at least one" carrier without committing
   to `Unique`.
9. **Nonempty device image uniqueness theorem**:
   `device_gauge_image_unique` says that given one admissible,
   encodable candidate, the device gauge image subtype is `Unique`,
   not just `Subsingleton`. The `default` witness is the gauge value
   of the supplied candidate; the `uniq` proof is inherited from
   `device_gauge_image_subsingleton`. Abstract QED analog of
   `fge_observable_image_unique_under_encoding` (`Bridge.lean`):
   strengthens "at most one point" to "exactly one point, carrying
   that point explicitly" once a nonempty witness is supplied. The
   conclusion still ranges over the device gauge image subtype,
   never over raw `E.Candidate` values.
10. **Finite-gauge bridge-as-experiment instance**:
    `finiteGaugePhysicalExperiment` and `finiteGaugeDeviceEncoding` package
    any `FiniteGaugeEncoding` from `Bridge.lean` as a concrete
    `PhysicalExperiment` + `DeviceEncoding` pair.
11. **Via-QED finite-gauge corollaries**: `fge_observable_unique_via_qed`,
    `fge_observable_image_subsingleton_via_qed`,
    `fge_observable_eq_inferredTerm_via_qed`,
    `fge_observable_image_eq_inferredTerm_via_qed`,
    `fge_observable_unique_and_eq_inferredTerm_via_qed`,
    `fge_observable_image_closed_via_qed`,
    `fge_observable_image_unique_via_qed`, and
    `fge_observable_image_nonempty_via_qed` reprove the bridge's
    pairwise, image-subsingleton, normal-form, image normal-form,
    combined, image closure, nonempty image uniqueness, and
    image-nonempty existence theorems as instances of the QED apex.

## What this theorem proves and does not prove

What it proves:

    Under the encoding hypotheses, the gauge map of a physical experiment
    is constant on the encodable, admissible subset of candidates, the
    subtype of gauge values reached on that subset is `Subsingleton`,
    and every such gauge value equals the interpretation of the
    canonical terminal witness. Once one admissible, encodable candidate
    is supplied, that candidate gives a `Nonempty` carrier for the
    device-image subtype; combined with the subsingleton theorem, the
    same witness yields the `Unique` device-image theorem.

What it does NOT prove:

    The physical candidates themselves are equal.
    The gauge is unique in any absolute sense outside the bridge.
    The encoding is surjective onto `HTerm .inferred`.
    The interpreter is unique.
    The `Unique` theorem is about the reached observable image, not raw
    candidates.
    The `Nonempty` theorem is also about the reached observable image, not
    raw candidates.
    The `Subsingleton` theorem is also about the reached observable image,
    not raw candidates.

The conditional structure is essential. Every hypothesis in the
`DeviceEncoding` structure is part of the bridge claim; weakening any of
them weakens the theorem to vacuity.

## Direct proofs versus via-QED proofs

The direct proofs of the finite-gauge bridge results live in `Bridge.lean`
(`fge_observable_unique_under_encoding`, `fge_observable_image_subsingleton`,
`fge_observable_eq_inferredTerm`, `fge_observable_image_eq_inferredTerm`,
`fge_observable_unique_and_eq_inferredTerm_under_encoding`,
`fge_observable_image_closed_under_encoding`,
`fge_observable_image_nonempty_under_encoding`, and
`fge_observable_image_unique_under_encoding`) and remain canonical for
finite-gauge inputs. The via-QED proofs added in this file are
architectural witnesses that the bridge IS the QED apex on the induced
experiment; they exist to make the architecture explicit, not to
replace the direct proofs. QED.lean carries pairwise, image
subsingleton, normal form, image normal form, combined, image closure,
image-nonempty existence, and nonempty image uniqueness via-QED proofs;
the bridge's direct proofs in `Bridge.lean` stay the canonical ones
for finite-gauge inputs.

The image closure surface is now carried by three routes:

- direct Bridge: `fge_observable_image_closed_under_encoding` in
  `Bridge.lean` is the **canonical** finite-gauge closure theorem;
- abstract QED: `device_gauge_image_closed` is the closure at the
  abstract `PhysicalExperiment` + `DeviceEncoding` layer;
- via-QED finite-gauge: `fge_observable_image_closed_via_qed` is the
  **architectural witness** that the canonical Bridge closure also
  factors through the QED apex on the induced experiment.

The image-nonempty existence surface is carried by the same
three-route canonical / architectural pattern:

- direct Bridge: `fge_observable_image_nonempty_under_encoding` in
  `Bridge.lean` is the **canonical** finite-gauge image-nonempty
  existence theorem;
- abstract QED: `device_gauge_image_nonempty` is the nonempty-existence
  theorem at the abstract `PhysicalExperiment` + `DeviceEncoding`
  layer;
- via-QED finite-gauge: `fge_observable_image_nonempty_via_qed` is the
  **architectural witness** that the canonical Bridge nonempty
  existence also factors through the QED apex on the induced
  experiment.

The direct Bridge theorem stays canonical for finite-gauge inputs; the
via-QED version is the architectural witness, parallel to the way
`fge_observable_unique_via_qed` / `fge_observable_eq_inferredTerm_via_qed`
relate to their `*_under_encoding` and `fge_observable_eq_inferredTerm`
counterparts.
-/

namespace Measurement.Formalization

universe u v

/-- An abstract physical experiment: a type of candidates, a type of
observables, an admissibility predicate over candidates, and the experiment's
gauge map. The candidates and observables can live in different universes. -/
structure PhysicalExperiment where
  /-- The type of candidate physical inputs (e.g. configurations, states). -/
  Candidate  : Type u
  /-- The observable type (e.g. real numbers, classification labels). -/
  Observable : Type v
  /-- Which candidates the experiment treats as valid inputs. -/
  admissible : Candidate → Prop
  /-- The experiment's gauge: candidates to observables. -/
  gauge      : Candidate → Observable

/-- A device encoding for a physical experiment: a partial encoding of
admissible candidates into terminal Herbrand terms, an interpreter, and the
agreement law tying the interpreted encoding to the experiment's gauge.

This is the abstract analog of `FiniteGaugeEncoding` (`Bridge.lean`),
generic over the candidate and observable types. -/
structure DeviceEncoding (E : PhysicalExperiment) where
  /-- The subset of candidates the device encodes (further filter beyond
  admissibility). -/
  Encodable : E.Candidate → Prop
  /-- The encoding of an admissible, encodable candidate into the terminal
  Herbrand stage. -/
  encode    : (c : E.Candidate) → E.admissible c → Encodable c → HTerm .inferred
  /-- The interpreter from terminal Herbrand terms to the observable type. -/
  interpret : HTerm .inferred → E.Observable
  /-- Agreement law: the interpreted encoding agrees with the experiment's
  gauge on every admissible, encodable candidate. -/
  agrees    : ∀ (c : E.Candidate) (hA : E.admissible c) (hE : Encodable c),
                interpret (encode c hA hE) = E.gauge c

/-- Apex theorem: under the device encoding's hypotheses, the experiment's
gauge map is constant on the admissible, encodable subset of candidates.

This is uniqueness of the device-mediated gauge value on the device image.
It is NOT a claim that distinct physical candidates are equal.

Proof: chain the `agrees` law with `terminal_observable_unique`. -/
theorem gauge_unique_on_device_image
    (E : PhysicalExperiment)
    (B : DeviceEncoding E)
    {a b : E.Candidate}
    (ha : E.admissible a) (hb : E.admissible b)
    (ea : B.Encodable a) (eb : B.Encodable b) :
    E.gauge a = E.gauge b := by
  calc E.gauge a
      = B.interpret (B.encode a ha ea) := (B.agrees a ha ea).symm
    _ = B.interpret (B.encode b hb eb) := terminal_observable_unique B.interpret _ _
    _ = E.gauge b                       := B.agrees b hb eb

/-- The device gauge image (the subtype of observables reached by admissible,
encodable candidates) is `Subsingleton`. This is the formal carrier for the
phrase "device image" used throughout Volume 7: the set of observables the
device can return on its admissible, encodable inputs is at most a single
point. The subtype is built from the gauge map; the proof is a direct
consequence of `gauge_unique_on_device_image`. -/
theorem device_gauge_image_subsingleton
    (E : PhysicalExperiment)
    (B : DeviceEncoding E) :
    Subsingleton
      { o : E.Observable //
        ∃ c : E.Candidate,
          ∃ _ : E.admissible c,
            ∃ _ : B.Encodable c,
              o = E.gauge c } := by
  constructor
  intro x y
  rcases x with ⟨ox, hx⟩
  rcases y with ⟨oy, hy⟩
  rcases hx with ⟨a, ha, ea, rfl⟩
  rcases hy with ⟨b, hb, eb, rfl⟩
  exact Subtype.ext (gauge_unique_on_device_image E B ha hb ea eb)

/-- QED-level canonical normal form: every admissible, encodable candidate's
gauge value equals the interpretation of the canonical terminal witness
`inferredTerm`. This is the physical-experiment analog of
`fge_observable_eq_inferredTerm` (the bridge level) and
`terminal_observable_eq_inferredTerm` (the terminal level). Useful as a
rewriting anchor and as the formal version of "one terminal gauge value"
at the apex of the bridge. -/
theorem gauge_eq_inferredTerm_on_device_image
    (E : PhysicalExperiment)
    (B : DeviceEncoding E)
    {a : E.Candidate}
    (ha : E.admissible a)
    (ea : B.Encodable a) :
    E.gauge a = B.interpret inferredTerm := by
  calc E.gauge a
      = B.interpret (B.encode a ha ea) := (B.agrees a ha ea).symm
    _ = B.interpret inferredTerm        :=
        terminal_observable_eq_inferredTerm B.interpret (B.encode a ha ea)

/-- QED-level image normal form: every actual element of the device gauge
image subtype equals the interpretation of the canonical terminal witness
`inferredTerm`. Fuses `device_gauge_image_subsingleton` (which says the
image has at most one point) with `gauge_eq_inferredTerm_on_device_image`
(which names that point's value). The result is the formal carrier for
Volume 7's phrase "the image collapses to the canonical terminal
observable." -/
theorem device_gauge_image_eq_inferredTerm
    (E : PhysicalExperiment)
    (B : DeviceEncoding E)
    (o : { o : E.Observable //
        ∃ c : E.Candidate,
          ∃ _ : E.admissible c,
            ∃ _ : B.Encodable c,
              o = E.gauge c }) :
    o.1 = B.interpret inferredTerm := by
  rcases o with ⟨v, hv⟩
  rcases hv with ⟨c, hA, hE, rfl⟩
  exact gauge_eq_inferredTerm_on_device_image E B hA hE

/-- Combined QED apex theorem: packages the pairwise device-image constancy
theorem and the canonical normal-form theorem in a single statement. The
left conjunct says any two admissible, encodable candidates have the same
gauge value (the pairwise apex); the right conjunct says that gauge value
equals the interpretation of the canonical terminal witness `inferredTerm`
(the normal-form apex). Adds no new hypotheses; this is a pure packaging
lemma over the two existing theorems. -/
theorem gauge_unique_and_eq_inferredTerm_on_device_image
    (E : PhysicalExperiment)
    (B : DeviceEncoding E)
    {a b : E.Candidate}
    (ha : E.admissible a) (hb : E.admissible b)
    (ea : B.Encodable a) (eb : B.Encodable b) :
    E.gauge a = E.gauge b ∧ E.gauge a = B.interpret inferredTerm :=
  ⟨gauge_unique_on_device_image E B ha hb ea eb,
   gauge_eq_inferredTerm_on_device_image E B ha ea⟩

/-- Abstract QED image closure theorem: packages
`device_gauge_image_subsingleton` (the device gauge image has at most
one point) with `device_gauge_image_eq_inferredTerm` (every actual
element of that image equals `B.interpret inferredTerm`) in a single
conjunction. The abstract QED analog of
`fge_observable_image_closed_under_encoding` (`Bridge.lean`): one formal
handle for the phrase "the device gauge image is closed under the
encoding, collapsing to the canonical terminal observable." Adds no new
hypotheses; abstract QED only. The finite-gauge via-QED image closure
package is `fge_observable_image_closed_via_qed` below; the direct
finite-gauge closure (`fge_observable_image_closed_under_encoding`)
remains canonical in `Bridge.lean`.

Boundary: the closure is about the *device gauge image* subtype, not
raw `E.Candidate` values. Both conjuncts inherit the same scope as the
two prior image theorems they package -- the admissible, encodable
device image, nothing more. -/
theorem device_gauge_image_closed
    (E : PhysicalExperiment)
    (B : DeviceEncoding E) :
    Subsingleton
      { o : E.Observable //
        ∃ c : E.Candidate,
          ∃ _ : E.admissible c,
            ∃ _ : B.Encodable c,
              o = E.gauge c } ∧
    ∀ o : { o : E.Observable //
        ∃ c : E.Candidate,
          ∃ _ : E.admissible c,
            ∃ _ : B.Encodable c,
              o = E.gauge c },
      o.1 = B.interpret inferredTerm :=
  ⟨device_gauge_image_subsingleton E B,
   device_gauge_image_eq_inferredTerm E B⟩

/-- Abstract QED device-image-nonempty existence theorem: given any
single admissible, encodable candidate `a`, the device gauge image
subtype is `Nonempty`, inhabited by `⟨E.gauge a, ⟨a, ha, ea, rfl⟩⟩`.
Abstract QED analog of `fge_observable_image_nonempty_under_encoding`
(`Bridge.lean`).

The conclusion is about the admissible, encodable *device gauge image*
subtype, not raw `E.Candidate` values; the hypotheses `ha` and `ea`
are used only to supply the nonempty witness. The theorem adds no
uniqueness claim by itself and needs no `Subsingleton` instance or
routing for the proof, which is one anonymous-constructor pair;
it merely exposes the weaker `Nonempty` carrier as a companion to
`device_gauge_image_unique`. Useful when a downstream caller wants
`Nonempty` without `Unique`, e.g. for `Nonempty.elim` or
`Classical.choice`-style reasoning over the device gauge image. -/
theorem device_gauge_image_nonempty
    (E : PhysicalExperiment)
    (B : DeviceEncoding E)
    {a : E.Candidate}
    (ha : E.admissible a)
    (ea : B.Encodable a) :
    Nonempty
      { o : E.Observable //
        ∃ c : E.Candidate,
          ∃ _ : E.admissible c,
            ∃ _ : B.Encodable c,
              o = E.gauge c } :=
  ⟨⟨E.gauge a, ⟨a, ha, ea, rfl⟩⟩⟩

/-- Abstract QED nonempty device-image uniqueness theorem: given any
single admissible, encodable candidate `a`, the device gauge image
subtype is `Unique`. The abstract QED analog of
`fge_observable_image_unique_under_encoding` (`Bridge.lean`):
strengthens `device_gauge_image_subsingleton`'s "at most one point"
claim to "exactly one point, with that point named" once a nonempty
witness is supplied.

Concretely:

- `default` is the gauge value of the supplied candidate,
  `⟨E.gauge a, ⟨a, ha, ea, rfl⟩⟩`;
- `uniq` is inherited from `device_gauge_image_subsingleton` via
  `Subsingleton.elim` against `default`.

The hypotheses `ha : E.admissible a` and `ea : B.Encodable a` supply
the nonempty image witness only; no new encoding, physical, or
observable hypothesis is introduced. The conclusion ranges over the
device gauge image subtype, NOT over raw `E.Candidate` values --
this is image uniqueness, not candidate uniqueness. The boundary
inherited from `device_gauge_image_subsingleton` and
`device_gauge_image_eq_inferredTerm` is unchanged. -/
def device_gauge_image_unique
    (E : PhysicalExperiment)
    (B : DeviceEncoding E)
    {a : E.Candidate}
    (ha : E.admissible a)
    (ea : B.Encodable a) :
    OnePoint
      { o : E.Observable //
        ∃ c : E.Candidate,
          ∃ _ : E.admissible c,
            ∃ _ : B.Encodable c,
              o = E.gauge c } := by
  refine
    { default := ⟨E.gauge a, ⟨a, ha, ea, rfl⟩⟩,
      uniq := ?_ }
  intro o
  exact @Subsingleton.elim _
    (device_gauge_image_subsingleton E B)
    o
    ⟨E.gauge a, ⟨a, ha, ea, rfl⟩⟩

/-! ## Bridge-as-Experiment view

The finite-gauge bridge surface in `Bridge.lean` and the abstract
`PhysicalExperiment`/`DeviceEncoding` pair are not two different things;
the bridge is a concrete instance of the experiment. The ten
definitions/theorems below make that explicit (two definitions plus
eight via-QED theorems):

- `finiteGaugePhysicalExperiment B` packages a `FiniteGaugeEncoding`'s
  `Encodable` predicate as `admissible` and its `observable` map as
  `gauge` over `FiniteGaugeInput` candidates;
- `finiteGaugeDeviceEncoding B` supplies the corresponding
  `DeviceEncoding`, reusing `B.encode`, `B.interpret`, and `B.agrees`;
- `fge_observable_unique_via_qed` reproves the bridge's pairwise
  uniqueness theorem as a corollary of `gauge_unique_on_device_image`;
- `fge_observable_image_subsingleton_via_qed` reproves the bridge's
  observable image subsingleton theorem by routing through
  `fge_observable_unique_via_qed`;
- `fge_observable_eq_inferredTerm_via_qed` reproves the bridge's
  canonical normal form theorem as a corollary of
  `gauge_eq_inferredTerm_on_device_image`;
- `fge_observable_image_eq_inferredTerm_via_qed` reproves the bridge's
  image normal form theorem as a corollary of
  `device_gauge_image_eq_inferredTerm` on the induced experiment;
- `fge_observable_unique_and_eq_inferredTerm_via_qed` reproves the
  bridge's combined closure theorem as a corollary of
  `gauge_unique_and_eq_inferredTerm_on_device_image`;
- `fge_observable_image_closed_via_qed` reproves the bridge's image
  closure theorem as a corollary of the via-QED image subsingleton and
  via-QED image normal form corollaries, equivalently of
  `device_gauge_image_closed` on the induced experiment;
- `fge_observable_image_unique_via_qed` reproves the bridge's nonempty
  image uniqueness theorem by routing through
  `fge_observable_image_subsingleton_via_qed` for the `uniq` field
  while supplying the encodable input as the nonempty witness for the
  `default` field;
- `fge_observable_image_nonempty_via_qed` reproves the bridge's
  image-nonempty existence theorem with the same one-line anonymous-
  constructor pair as the direct Bridge version, since `Nonempty`
  needs no `Subsingleton`-instance routing; the via-QED label here is
  architectural, marking that the canonical Bridge existence also
  lives in the QED-apex layer on the induced experiment.

The eight via-QED theorems together carry the pairwise /
image subsingleton / normal form / image normal form / combined /
image closure / nonempty image uniqueness / image-nonempty existence
surfaces across the Bridge -> QED connection point.

The original direct proofs in `Bridge.lean`
(`fge_observable_unique_under_encoding`,
`fge_observable_image_subsingleton`, `fge_observable_eq_inferredTerm`,
`fge_observable_image_eq_inferredTerm`,
`fge_observable_unique_and_eq_inferredTerm_under_encoding`,
`fge_observable_image_closed_under_encoding`,
`fge_observable_image_unique_under_encoding`, and
`fge_observable_image_nonempty_under_encoding`) remain the canonical
ones; the via-QED theorems are architectural witnesses that the
bridge IS the QED apex on the induced experiment. The point is
architectural: Volume 7 can describe one apex theorem and treat the
bridge as a concrete instance, rather than parallel theorems with the
same proof shape. -/

/-- View a finite-gauge bridge as a physical experiment: candidates are
`FiniteGaugeInput`, admissibility is `B.Encodable`, the gauge is
`B.observable`, and observables live at the same universe as the bridge's
observable type. -/
def finiteGaugePhysicalExperiment
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs) : PhysicalExperiment where
  Candidate  := FiniteGaugeInput
  Observable := Obs
  admissible := B.Encodable
  gauge      := B.observable

/-- The finite-gauge bridge supplies a `DeviceEncoding` for its induced
physical experiment. The `encode` and `agrees` fields take the experiment's
admissibility proof and the device's encodability proof separately; in this
instance both witnesses are the same `B.Encodable x` predicate, so the
admissibility proof is the one consumed by `B.encode` / `B.agrees` and the
encodability proof is ignored. -/
def finiteGaugeDeviceEncoding
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs) :
    DeviceEncoding (finiteGaugePhysicalExperiment B) where
  Encodable := B.Encodable
  encode    := fun x hx _ => B.encode x hx
  interpret := B.interpret
  agrees    := fun x hx _ => B.agrees x hx

/-- The finite-gauge bridge's pairwise theorem
(`fge_observable_unique_under_encoding`) is a corollary of
`gauge_unique_on_device_image` applied to the induced physical experiment
and device encoding. Provided as a second route to the same conclusion;
the original direct proof in `Bridge.lean` stays as well. -/
theorem fge_observable_unique_via_qed
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs)
    {x y : FiniteGaugeInput}
    (hx : B.Encodable x) (hy : B.Encodable y) :
    B.observable x = B.observable y :=
  gauge_unique_on_device_image
    (finiteGaugePhysicalExperiment B)
    (finiteGaugeDeviceEncoding B)
    hx hy hx hy

/-- Via-QED finite-gauge image-subsingleton theorem: the subtype of
observables reached by encodable finite gauge inputs is `Subsingleton`,
proved by routing through `fge_observable_unique_via_qed` rather than
through the direct Bridge pairwise theorem. Mirror of the Bridge-side
`fge_observable_image_subsingleton`: same statement, same proof shape,
but the pairwise step is the via-QED corollary. Architectural witness
that the bridge's image-subsingleton claim is also reachable through
the QED apex on the induced experiment. -/
theorem fge_observable_image_subsingleton_via_qed
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
  exact Subtype.ext (fge_observable_unique_via_qed B ha hb)

/-- The finite-gauge bridge's canonical normal form is also a corollary of
the QED normal-form theorem. Mirror of `fge_observable_unique_via_qed`:
where that one routes pairwise uniqueness through the QED apex, this one
routes every-equals-canonical through the QED normal form. Together they
preserve the pairwise/normal-form pairing at the Bridge -> QED connection
point.

The original direct proof of `fge_observable_eq_inferredTerm` in
`Bridge.lean` remains the canonical one; this theorem is the
architectural witness that the bridge result IS the QED result on the
induced experiment. -/
theorem fge_observable_eq_inferredTerm_via_qed
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs)
    {x : FiniteGaugeInput}
    (hx : B.Encodable x) :
    B.observable x = B.interpret inferredTerm :=
  gauge_eq_inferredTerm_on_device_image
    (finiteGaugePhysicalExperiment B)
    (finiteGaugeDeviceEncoding B)
    hx hx

/-- Via-QED finite-gauge image normal-form theorem: every actual element of
the finite-gauge observable image subtype equals `B.interpret inferredTerm`,
proved by routing through `device_gauge_image_eq_inferredTerm` on the
induced experiment. Mirror of the Bridge-side
`fge_observable_image_eq_inferredTerm`: same statement, same role; the
canonical-value step is the QED-level image normal-form theorem applied
to the induced experiment's gauge image subtype. -/
theorem fge_observable_image_eq_inferredTerm_via_qed
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs)
    (o : { o : Obs //
        ∃ x : FiniteGaugeInput,
          ∃ _ : B.Encodable x,
            o = B.observable x }) :
    o.1 = B.interpret inferredTerm := by
  rcases o with ⟨v, hv⟩
  rcases hv with ⟨x, hx, rfl⟩
  exact device_gauge_image_eq_inferredTerm
    (finiteGaugePhysicalExperiment B)
    (finiteGaugeDeviceEncoding B)
    ⟨B.observable x, ⟨x, hx, hx, rfl⟩⟩

/-- Finite-gauge instance of the combined QED apex theorem. Packages the
pairwise via-QED theorem and the normal-form via-QED theorem in a single
statement, parallel to `gauge_unique_and_eq_inferredTerm_on_device_image`
at the QED level. Volume 7's closure chapter can point to this one
finite-gauge theorem for the final device-image statement. -/
theorem fge_observable_unique_and_eq_inferredTerm_via_qed
    {Obs : Type u}
    (B : FiniteGaugeEncoding Obs)
    {x y : FiniteGaugeInput}
    (hx : B.Encodable x) (hy : B.Encodable y) :
    B.observable x = B.observable y ∧ B.observable x = B.interpret inferredTerm :=
  gauge_unique_and_eq_inferredTerm_on_device_image
    (finiteGaugePhysicalExperiment B)
    (finiteGaugeDeviceEncoding B)
    hx hy hx hy

/-- Via-QED finite-gauge image closure theorem: packages
`fge_observable_image_subsingleton_via_qed` (the encodable observable
image has at most one point, proved via the QED apex) with
`fge_observable_image_eq_inferredTerm_via_qed` (every actual element of
that image equals `B.interpret inferredTerm`, proved via the QED apex)
in a single conjunction. The architectural-witness analog of
`fge_observable_image_closed_under_encoding` (`Bridge.lean`).

Three closure surfaces now coexist:

- direct Bridge: `fge_observable_image_closed_under_encoding` is the
  **canonical** finite-gauge image closure theorem;
- abstract QED: `device_gauge_image_closed` is the closure at the
  abstract `PhysicalExperiment` + `DeviceEncoding` layer;
- via-QED finite-gauge: this theorem is the **architectural witness**
  that the canonical Bridge closure also factors through the QED apex
  on the induced experiment.

Adds no new hypothesis; the proof term is the anonymous-constructor
pair on the two via-QED image corollaries already in this file.

Boundary: like the direct Bridge and abstract QED closure packages, this
theorem ranges over the observable-image subtype only; no claim is made
about raw `FiniteGaugeInput` values. -/
theorem fge_observable_image_closed_via_qed
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
  ⟨fge_observable_image_subsingleton_via_qed B,
   fge_observable_image_eq_inferredTerm_via_qed B⟩

/-- Via-QED finite-gauge image-nonempty existence theorem: given a
single encodable finite gauge input `x`, the encodable observable image
subtype is `Nonempty`, inhabited by `⟨B.observable x, ⟨x, hx, rfl⟩⟩`.
Via-QED architectural-witness companion to
`fge_observable_image_unique_via_qed`.

The conclusion is about the encodable *finite-gauge observable image*
subtype, not raw `FiniteGaugeInput` values; the hypothesis `hx` is
used only to supply the nonempty witness. The theorem adds no
uniqueness claim by itself and needs no `Subsingleton` instance or
routing for the proof, which is one anonymous-constructor pair
identical to the direct Bridge `fge_observable_image_nonempty_under_encoding`
form. The via-QED name here is therefore an architectural label
rather than a different proof route: it marks that this image-
nonempty existence surface also lives at the QED apex on the induced
experiment, even though the conclusion `Nonempty` does not consume a
`Subsingleton` instance and so does not factor through a via-QED-
style Subsingleton-routed proof. -/
theorem fge_observable_image_nonempty_via_qed
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

/-- Via-QED finite-gauge nonempty image uniqueness theorem: given a
single encodable finite gauge input `x`, the encodable observable image
subtype is `Unique`. The architectural-witness analog of
`fge_observable_image_unique_under_encoding` (`Bridge.lean`): the
`default` field is the observable produced by the supplied input; the
`uniq` field is `Subsingleton.elim` against the via-QED
image-subsingleton instance (`fge_observable_image_subsingleton_via_qed`),
which itself factors through the QED apex on the induced experiment.

This is image (not raw input) uniqueness; like the direct Bridge and
abstract QED nonempty uniqueness theorems, the conclusion ranges over
the observable image subtype only. The direct Bridge theorem stays
canonical for finite-gauge inputs; this theorem is the architectural
witness. -/
def fge_observable_image_unique_via_qed
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
    (fge_observable_image_subsingleton_via_qed B)
    o
    ⟨B.observable x, ⟨x, hx, rfl⟩⟩

end Measurement.Formalization
