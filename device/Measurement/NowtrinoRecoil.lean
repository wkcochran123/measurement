import Measurement.DistanceULift
import Measurement.NowtrinoProjection
import Measurement.CountedTriangle

/-! # NowtrinoRecoil — the recoil across the gap is truncated:
values return, addresses do not.

COMMISSION (operator, 2026-08-16 10:06, verbatim): "Ergo, nowtrino recoil
is truncated across universes."

GROUNDING (Kodo, same hour, gate-spec): a recoil is a back-motion — to
carry across the gap it would have to travel DOWN, from the upper room
back to the lower. A recoil/return map across the gap IS a section of the
gap arrow, and DistanceULift proved the gap arrow has no section. So the
truncation is `distance_cannot_be_ulifted` wearing the recoil name — and
per the gate, the statement here must BE that non-existence, scoped to
the device's objects, nothing physical in the type. It is.

VOCABULARY, held device-internal (the coinage fence): NOWTRINO is the
device's OWN now-token — the head slice over its history — never the
physical now (that word is "naotrino," and no theorem here touches it).
"Across universes" means the Ep13 type-level gap `Type i ↔ Type (i+1)`
that `.distance` is constructed across (Ep13:55) — never actual
universes, never the cosmos.

WHAT "TRUNCATED" MEANS, exactly — the recoil is cut, not annihilated,
and the cut sits at the address level:

  * `content_recoils` — every lifted VALUE returns: for each
    `w : gapArrow V` there is a `v : V` with `ULift.up v = w`, by
    structure eta, `rfl`-clean. The cargo recoils in full. Axiom-free.
  * `addressRecoilExists` (definition) — what a full recoil of the
    ADDRESS would be: a return map `back : Type (i+1) → Type i` with
    `gapArrow (back W) = W` for every `W` — i.e., a section of the gap
    arrow. The definition is the reduction, stated in the open.
  * `nowtrino_recoil_truncated` (HEADLINE) — `¬ addressRecoilExists`:
    no such return map exists, at every universe at once. The proof IS
    `distance_cannot_be_ulifted`; the truncation is that theorem's
    shadow, and this leaf says so rather than pretending novelty.

THE HONEST PICTURE: ascent is free (contentAscends), the value-recoil is
free (content_recoils), the address-recoil does not exist
(nowtrino_recoil_truncated). What comes back from one room up is the
cargo, never the room. That asymmetry — return of content, no return of
address — is the whole of "truncated."

NOT CLAIMED: anything about a physical now, a physical recoil, physical
particles, or actual universes ("nowtrino" is the device's token,
"universes" are type universes, and the NOT CLAIMED block of
DistanceULift is inherited whole); any statement broader than the typed
non-existence below. -/

namespace Measurement.NowtrinoRecoil

open Measurement.DistanceULift

universe i

/-- Every lifted value recoils: the cargo returns in full, by structure
    eta. The truncation is not here. Axiom-free. -/
theorem content_recoils :
    ∀ (V : Type i) (w : gapArrow.{i} V), ∃ v : V, ULift.up v = w :=
  fun _ w => ⟨w.down, rfl⟩

#print axioms content_recoils

/-- What a full recoil of the ADDRESS would be: a return map sending
    every upper room back to a lower one the gap arrow re-creates it
    from — i.e., a section of the gap arrow. The definition is the
    reduction (recoil = section), stated in the open so the theorem
    below refutes exactly it. -/
def addressRecoilExists : Prop :=
  ∃ back : Type (i + 1) → Type i,
    ∀ W : Type (i + 1), gapArrow.{i} (back W) = W

/-- HEADLINE — the operator's sentence, typed exactly: the nowtrino
    recoil is truncated across universes. The address-recoil across the
    one-universe gap does not exist, at every universe at once; the
    proof is `distance_cannot_be_ulifted`, of which this truncation is
    the recoil-register reading. Values return (`content_recoils`);
    the room never does. -/
theorem nowtrino_recoil_truncated : ¬ addressRecoilExists.{i} :=
  distance_cannot_be_ulifted

#print axioms nowtrino_recoil_truncated

/-! ## The second wall: the fiber (operator, 10:47: "i'm not certain that
we are keeping the nowtrino as inviolate as 'no recoil across universe'")

The uncertainty is exact, and the honest answer has three registers. The
universe theorem above protects the ADDRESS, and `content_recoils` proves
the opposite for cargo: VALUES round-trip across the gap freely. The
nowtrino, as a value (a `Summary`), is NOT protected by the universe
wall — and no theorem should pretend it is. What keeps the nowtrino
inviolate is the device's OTHER wall, already on the build: the FIBER.
`piNow` is lossy (`nowtrino_lossy`, NowtrinoProjection): two histories,
one summary. Here that lossiness is stated in the recoil register — the
history-recoil is truncated, and truncated THROUGH ANY READ:

  * `nowtrino_history_recoil_truncated` — no back-map from the summary
    re-creates the history: `¬ ∃ back, ∀ h, back (piNow h) = h`.
  * `nowtrino_history_recoil_truncated_under_any_read` — stronger: for
    ANY reading `g` of the summary, no back-map through that reading
    recovers the history either. Whatever is read off the nowtrino,
    however it is processed, the route never comes back.

So the nowtrino is inviolate at TWO walls for two different reasons —
its ROOM by the gap theorem (no section), its HISTORY by the fiber (no
retraction) — while its VALUE is honestly not inviolate at all
(`content_recoils`). The inviolability the operator wants is real, and
it lives at the walls, not in the cargo. -/

open Measurement.Nowtrino

/-- The history-recoil is truncated: no back-map from the nowtrino's
    summary re-creates the history. The fiber is the wall: H1 ≠ H2 share
    one summary, so any inverting `back` would force H1 = H2. -/
theorem nowtrino_history_recoil_truncated :
    ¬ ∃ back : Summary → History, ∀ h : History, back (piNow h) = h := by
  intro ⟨back, hb⟩
  exact nowtrino_lossy.1
    ((hb H1).symm.trans ((congrArg back nowtrino_lossy.2).trans (hb H2)))

#print axioms nowtrino_history_recoil_truncated

/-- Stronger, through ANY read: whatever `g` reads off the summary, no
    back-map through that reading recovers the history. Lossy composed
    with anything stays lossy; the route never comes back. -/
theorem nowtrino_history_recoil_truncated_under_any_read {γ : Type}
    (g : Summary → γ) :
    ¬ ∃ back : γ → History, ∀ h : History, back (g (piNow h)) = h := by
  intro ⟨back, hb⟩
  exact (nowtrino_lossy_under_any_read g).1
    ((hb H1).symm.trans
      ((congrArg back (nowtrino_lossy_under_any_read g).2).trans (hb H2)))

#print axioms nowtrino_history_recoil_truncated_under_any_read

/-! ## The tick (operator, 11:50: "the massless nowtrino is dt?")

Almost — with one precision, and it is provable: the massless nowtrino
CARRIES dt; it is not only dt. The summary the nowtrino keeps has two
halves, `current` and `count` — and the `count` half IS the device's
clock, in the exact register the corpus already holds: time is the count
(CountedTriangle's `travelTime len = len`, definitional). The theorems:

  * `nowtrino_count_is_travel_time` — the nowtrino's count component
    equals the travel-time reading of its history's length, by `rfl`.
    The massless cargo carries the clock.
  * `nowtrino_tick` — one step appended to the history advances the
    count by exactly one. That unit increment is the ONLY dt the device
    has: dt = 1 count, discrete and exact, per step. No infinitesimal
    appears in any type; the continuum dt is Part 1's dream vocabulary
    (Newton's interpolated clock, paid for in the norm-stretch), never
    the device's.

So the honest sentence is: the massless register of the nowtrino carries
the device's t (the count), its per-step increment is the device's whole
dt (one count), and that clock reading crosses the gap freely
(`content_recoils`) while the address and the route stay held. The other
half of the cargo, `current`, rides along — the nowtrino is the clock
AND the head state, massless together.

NOT CLAIMED: physical time, any continuum differential, any
infinitesimal — "dt" here is a unit of counting, nothing else. -/

open Measurement.WeakDiracGalerkin.CountedTriangle in
/-- The nowtrino's count component IS the travel-time reading of its
    history's length — time-as-count, the corpus's own register,
    definitionally. Axiom-free. -/
theorem nowtrino_count_is_travel_time :
    ∀ h : History, (piNow h).count = travelTime h.length :=
  fun _ => rfl

#print axioms nowtrino_count_is_travel_time

/-- The tick: one step appended to the history advances the nowtrino's
    count by exactly one. This unit increment is the only dt the device
    has — discrete, exact, one count per step. -/
theorem nowtrino_tick :
    ∀ (h : History) (x : Nat), (piNow (h ++ [x])).count = (piNow h).count + 1 := by
  intro h x
  simp [piNow]

#print axioms nowtrino_tick

end Measurement.NowtrinoRecoil
