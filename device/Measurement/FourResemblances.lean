import Measurement.TwoSlipRecursion
import Measurement.CycleOfThree
import Measurement.ArchimedesPi
import Measurement.FinitenessFence
import Measurement.SelfEnergyGibbs

/-! # FourResemblances — task 4: the residue's four resemblances, earned at their TRUE tiers.

PRE-REGISTERED + GATED BOTH CHAIRS (Kodo 19:43 approve-with-R1-rescope; Beastmaster
19:44 adopt + 20:41 R4 three-layer ruling) BEFORE this file was written. The verdict
frame: structural-identity-at-the-exact-level PASSES; fenced-naming (cited, worn) PASSES;
labeled-illustration PASSES; asserted-resemblance-AS-identity-without-the-bridge FAILS.
Every "IS" carries its scope-qualifier. The split, whatever it computes, is the finding.

16+ leaf: imports read the built corpus; no existing file modified; jar untouched by
construction; tier = task-4 exhibit, nothing self-founded claimed. -/

namespace Measurement.FourResemblances

open Measurement

/-! ## R1 — CURVATURE (the A/B split, Kodo's rescope)

LAYER A (STRONG, definitional): the residue IS a second difference — not resembles, IS.
LAYER B (FENCED-NAMING, cited): "the second difference is the discrete curvature" in the
CITED sense of the 1-D discrete Laplacian / central second difference of the calculus of
finite differences (George Boole, *A Treatise on the Calculus of Finite Differences*,
1860; the standard unnormalized discrete second derivative). It is NOT the
Riemannian/Frenet curvature — that carries the (1+f′²)^(3/2) normalization and needs a
manifold and metric the device does not have; THAT sense stays illustration, fenced. -/

/-- LAYER A: the residue is BY DEFINITION the second difference of the three readings
(orbit, pair, echo). `rfl` — identity, not resemblance. -/
theorem residue_IS_second_difference :
    TwoSlipRecursion.measuredSecondVar
      = secondDifference TwoSlipRecursion.r0 TwoSlipRecursion.r1 TwoSlipRecursion.r2 :=
  rfl

/-- The residue's value, for the record: −21. -/
theorem residue_value : TwoSlipRecursion.measuredSecondVar = -21 := by decide

#print axioms residue_IS_second_difference
#print axioms residue_value

/-! ## R2 — OBSTRUCTION (strong-as-structure; "Morse" is a worn name)

The residue IS a proven cycle-invariant, and the cycle carries a proven
PERIOD-obstruction — it cannot close before three. "Obstruction" is scoped to PERIOD
(not a cohomological/obstruction-theory object); "Morse index" is a name the structure
WEARS (no Morse function, no Hessian, no manifold in the device) — coinage, not
identity. -/

/-- The residue-cycle invariance, re-exhibited: three folds fix every state. -/
theorem residue_is_cycle_invariant (x : CycleOfThree.ThreeFold) :
    CycleOfThree.spin 3 x = x :=
  CycleOfThree.residue_invariant_under_cycle x

/-- The PERIOD-obstruction: the cycle provably cannot close at one or at two. -/
theorem period_obstruction :
    CycleOfThree.spin 1 CycleOfThree.ThreeFold.minus ≠ CycleOfThree.ThreeFold.minus
      ∧ CycleOfThree.spin 2 CycleOfThree.ThreeFold.minus
          ≠ CycleOfThree.ThreeFold.minus := by
  exact ⟨(CycleOfThree.cycle_of_three).2.1, (CycleOfThree.cycle_of_three).2.2⟩

#print axioms residue_is_cycle_invariant
#print axioms period_obstruction

/-! ## R3 — THE CAUGHT LIMIT (strong-as-structure; the ε-δ sense fenced; the
ATTRIBUTION scoped per Beastmaster's arrival-read)

Two halves, kept apart so the "IS" lands on the right object:
- THE RESIDUE-SPECIFIC HALF (strong): the residue is the NEVER-RESOLVED — the below-floor
  gap between first and second variation, which NO machine reading off a box can
  separate (`residue_below_floor`, proven). That half IS the residue's own.
- THE METHOD HALF (the device's, exhibited on π): the certified SQUEEZE — nesting walls,
  gap at least halving — is the device's certified BRACKETING METHOD, and its exhibit
  (`squeeze_certified`) runs on π, the calibration bracket (Vol 1 Ch5's exhibit), NOT on
  the residue. The residue (−21, exact by `residue_value`) is not itself a bracketed
  quantity; π's walls are not the residue's walls, and this file does not lend them.

So the honest R3 sentence: the device's READING is a caught limit — a certified squeeze
METHOD whose below-floor gap, the unresolvable first-vs-second variation, IS the
residue. The residue is the CAUGHT half, not the squeezed object. (And not fix-(b): the
mediant count-3 bracket walls the CROSSING — the coupling reading — which is also not
the residue; exhibiting it here would re-commit the same attribution one object over.)
Caught below the floor — a boundary that cannot be crossed, NOT a limit-VALUE
approached; the completed-analysis (ε-δ, continuum) sense of "limit" stays illustration,
fenced. -/

/-- The certified bracketing METHOD, exhibited on π (the calibration bracket — these are
π's walls, not the residue's): the walls NEST and the gap AT LEAST HALVES. -/
theorem squeeze_certified :
    (ArchimedesPi.piLo 4 ≤ ArchimedesPi.piLo 5 ∧ ArchimedesPi.piHi 5 ≤ ArchimedesPi.piHi 4)
      ∧ 2 * (ArchimedesPi.piHi 5 - ArchimedesPi.piLo 5)
          ≤ ArchimedesPi.piHi 4 - ArchimedesPi.piLo 4 := by
  decide

#print axioms squeeze_certified

/-- The irresolvability below the floor: for ANY machine reading off a box, the first
and second variation read the same — the residue between them cannot be resolved. -/
theorem residue_below_floor {M : Type} (read : Fin boxCount → M)
    (g : Gospel) (a b c : Prop) (v1 v2 tail : Variation) :
    read (boxOf (.gateaux g a b tail)) = read (boxOf (.frechet g a b c v1 v2)) :=
  FinitenessFence.machine_cannot_resolve_residue read g a b c v1 v2 tail

#print axioms residue_below_floor

/-! ## R4 — THE CLASS-INVARIANCE (the superseding tier: Kodo 20:42 + Beastmaster 20:44,
which SUPERSEDES the earlier "fixed-point equation" framing)

STRONG (proven, ∀-form): the CLASS-INVARIANCE — for every reading P, self-description
PRESERVES the class: the induced map [describeType] on classes is the IDENTITY; the
descent closes. That is the real structural content, and it is all of it.

WHY NOT "A FIXED-POINT EQUATION": since the induced map is the identity, the equation
x = [describeType](x) holds TRIVIALLY — the identity fixes everything. A "fixed point"
here exists only in that TRIVIAL sense, and this file says so, because the un-scoped
phrase would lean toward implying the NON-trivial (Lawvere) kind.

FENCED HARDEST of the four — BOTH absences stated: (i) the mechanism of Lawvere's 1969
theorem — a point-surjective map φ : A → (A → B) and the diagonal — is NOT in the
device; (ii) NO non-trivial fixed point is present — only the trivial invariance. Unlike
R2/R3 (where the genuine structural object IS the specific thing under a fancier name),
the Lawvere-specific object is ABSENT here, not merely un-named — which is why this face
fences hardest, and that asymmetry is itself the honest finding.

THE RESIDUE FENCE (preserved, subsumed): the invariant class is a DIFFERENT object from
the residue (−21, R1–R3's subject); no identification is asserted. What connects them is
only a COST-relation: the collapse that proves this invariance is the very work whose
cost is measured as the −21 (SelfEnergyGibbs) — a cost-relation, never an identity.

THE AXIOM, graded off the print: this proof carries [Quot.sound], and honestly so — it
IS the measured-subject site (the sanctioned needle doing its genuine work), the
Class-B keep-forever role. -/

/-- STRONG: the class-invariance under self-description, for every reading. (A "fixed
point" of the induced map exists only in the TRIVIAL sense — the map is the identity.) -/
theorem class_invariant_under_describe (P : Prop) :
    Calibration.BIAS_____.mkClass SelfEnergyGibbs.implOrder P
      = Calibration.BIAS_____.mkClass SelfEnergyGibbs.implOrder
          (SelfEnergyGibbs.describeType P) :=
  SelfEnergyGibbs.selProof P

#print axioms class_invariant_under_describe

#eval "R1: residue IS second difference (rfl), −21; wears cited discrete-curvature name (Boole 1860); Riemannian fenced"
#eval "R2: residue IS cycle-invariant + period-obstruction (proven); wears Morse name; cohomology fenced"
#eval "R3: residue IS the never-resolved below-floor gap (residue-specific); the certified squeeze = the device's METHOD, exhibited on π (π's walls, not the residue's); ε-δ limit fenced"
#eval "R4: class-INVARIANCE proven ([Quot.sound] = measured-subject); fixed point only in the TRIVIAL sense (map = identity); Lawvere mechanism ABSENT (both absences stated); residue-bridge NOT asserted"

end Measurement.FourResemblances
