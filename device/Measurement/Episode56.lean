import Measurement.Episode55

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 56__: _The Split_

The Episode52 review refused the sentence "the certificate and the electron
exclude each other" because nothing carried it.  The author's correction
named what does: one assumes CH, the other denies it.  The certificate
family lives where countable exhaustion suffices -- below the door, where
the skeleton tower runs out of configurations and the residual becomes
exactly zero.  The electron lives in the coupling that one-coordinate
exhaustion cannot express -- the strictly-between content the weak form
projects out.  Two families on opposite sides of a continuum hypothesis:
they do not exclude each other by accident or by theorem about one action;
they exclude each other BY TYPE.  This episode builds the type.

Two pieces.  First, the pairing door: Episode38's `HilbertCompletionDoor`
carries a norm and zero-detection but no inner product, so orthogonality
was not yet stateable from the door alone.  `HilbertPairingDoor` extends it
with a finite integer pairing; for Galerkin carriers the pairing is the
bilinear form itself (`dot := form.a`), and `dot_zero_left` is Episode34's
`aMS_zero_left` wearing door clothes.

Second, the split: a carrier with a GEOMETRIC sector and a GAUGE sector,
and a pairing that is zero across sectors definitionally -- not proven
zero, MADE zero, the way a type theorist says "these cannot mix."  The
geometric certificate representative is Episode34's nontrivial energy
witness; the gauge representative is THE ELECTRON.  Their orthogonality is
`rfl` -- and honestly so is everyone else's: EVERY cross-sector pair is
orthogonal by construction, so the representatives are decorative for the
`orthogonal` field and load-bearing only for the nontriviality theorem.
That is the finite SHAPE of the paper's central hypothesis -- the
geometric and gauge certificate families stand orthogonal in the induced
pairing -- supplied by type rather than proven about one common pairing;
the substantive continuum version stays the target.  Episode57 cashes the
shape: orthogonality kills the Clifford scalar cross-term, no interior
mixed certificate exists, and the remainder reads at the boundary.

Stated formally:
* `HilbertPairingDoor` -- the door, now with a finite pairing.
* `threeRungPairingDoor` -- the three-rung instance, `dot := aMS`.
* `SplitCarrier`, `splitDot` -- the two-sector carrier; cross terms are
  definitionally zero.
* `FiniteCertificateSplit` -- carrier, pairing, the two representatives,
  and the orthogonality field.
* `threeRungCertificateSplit` -- geometric witness paired against the
  electron; `orthogonal := rfl`.

Residue left (honest scope):
the pairing door is forward scaffolding for the mathlib-side pairing and
is not yet on the theorem chain (the split pairs the geometric sector by
`threeRungForm.a` directly).  The split carrier is a sum type, not a
direct sum of modules -- finite
shadow, no addition across sectors, which is exactly the claim (nothing
mixes).  The continuum Sobolev orthogonality stays behind the mathlib
door, per the claim gates.  And CH here is the satire's reading of the
boundary, not a set-theoretic theorem: the corpus's own fact is that the
countable tower certifies one family while provably never holding the
other (Episode47's pigeonhole, cashed by Episode48's
`discriminatingAction_no_tag_covering_trace`); the split is the TYPE-level
shape of that separation, with the formal link between the split and those
theorems left as the upgrade surface.  And the sum carrier has no
addition: the direct-sum reading of "coexist" has no finite analog here --
you cannot even form g + q, which is the point.
-/

/-- Episode38's door, extended with a finite integer pairing: the inner
product the orthogonality claim needs, at the finite shadow level. -/
structure HilbertPairingDoor (V : Type) extends HilbertCompletionDoor V where
  dot : V -> V -> Int
  dot_symmetric : forall x y, dot x y = dot y x
  dot_zero_left : forall x, dot toHilbertCompletionDoor.cert.zero x = 0

/-- The three-rung pairing door: Episode38's shadow door with the Galerkin
form as the pairing. -/
noncomputable def threeRungPairingDoor : HilbertPairingDoor Rung3 where
  toHilbertCompletionDoor := threeRungNormSqShadowDoor
  dot := threeRungForm.a
  dot_symmetric := threeRungForm.symmetric
  dot_zero_left := threeRungForm.zero_left

/-- Acceptance: the pairing door's zero pairs to zero on the left. -/
theorem threeRungPairingDoor_dot_zero_left (x : Rung3) :
    threeRungPairingDoor.dot threeRungSPD.form.zero x = 0 :=
  threeRungPairingDoor.dot_zero_left x

/-- The two-sector carrier: a value is geometric or gauge, never both. -/
inductive SplitCarrier (G Q : Type)
  | geometric : G -> SplitCarrier G Q
  | gauge : Q -> SplitCarrier G Q

/-- The split pairing: each sector pairs with itself by its own pairing;
cross-sector terms are DEFINITIONALLY zero. -/
def splitDot {G Q : Type}
    (dotG : G -> G -> Int) (dotQ : Q -> Q -> Int) :
    SplitCarrier G Q -> SplitCarrier G Q -> Int
  | .geometric a, .geometric b => dotG a b
  | .gauge a, .gauge b => dotQ a b
  | .geometric _, .gauge _ => 0
  | .gauge _, .geometric _ => 0

/-- A finite certificate split: a carrier, a pairing, one geometric
certificate representative, one gauge certificate representative, and
their orthogonality. -/
structure FiniteCertificateSplit where
  H : Type
  dotH : H -> H -> Int
  geometric : H
  gauge : H
  orthogonal : dotH geometric gauge = 0

/-- The three-rung certificate split: the geometric sector carries `Rung3`
paired by the Galerkin form, with Episode34's nontrivial energy witness
`(1,0,0)` as the representative; the gauge sector carries the residue line
`Int` paired by multiplication, with THE ELECTRON as the representative.
Orthogonality is `rfl`: the sectors cannot mix, by type. -/
noncomputable def threeRungCertificateSplit : FiniteCertificateSplit where
  H := SplitCarrier Rung3 Int
  dotH := splitDot threeRungForm.a (fun a b => a * b)
  geometric := .geometric { c0 := 1, c1 := 0, c2 := 0 }
  gauge := .gauge electron
  orthogonal := rfl

/-- The split is not degenerate: each sector's representative pairs
nontrivially with itself.  The geometric witness carries energy 2
(Episode34); the electron pairs with itself to +1 -- charge squared. -/
theorem threeRungCertificateSplit_sectors_nontrivial :
    threeRungCertificateSplit.dotH
        threeRungCertificateSplit.geometric
        threeRungCertificateSplit.geometric = 2 ∧
      threeRungCertificateSplit.dotH
        threeRungCertificateSplit.gauge
        threeRungCertificateSplit.gauge = 1 := by
  refine ⟨?_, ?_⟩ <;> decide

/-
The standing record.
-/

-- Expect `[propext, Classical.choice, Quot.sound]` on the door (the chair);
-- the split's own facts are decidable computations.
#print axioms threeRungPairingDoor_dot_zero_left
#print axioms threeRungCertificateSplit_sectors_nontrivial

end Measurement
