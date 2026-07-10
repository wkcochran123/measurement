import Measurement.Episode52
import Measurement.NamingClose

/- THE CAPSTONE (ep17-loop Phase M, step M3). Where the map lands.

The operator the corpus builds is a `CalculusProcess`, and its `derivative`
(`BigRedDogProcess`, Episode10:298) carries exactly two fields:

  * `universal_observer : UniverseTensor` -- the 0th term, the fixed-point VALUE, the
    universe tensor. Reading (INTERPRETIVE): the tensor ⊨ GR (Einstein: U(x*) = x*).
  * `differential_equation : Variation` -- the 1st term, the derivative. Under the
    stack it is promoted (transmute) to its second variation `electronVariation`
    (Episode52 `the_stack_produces_it`, a `.frechet`). Reading (INTERPRETIVE): the
    Fréchet ⊨ Heisenberg (QED, the produced electron, charge -1).

THE CAPSTONE names these two fields as the 0th and 1st terms of the operator's
decomposition, and it lands them in the naming's finite representation (NamingClose):

  universal = universe_tensor (⊨ GR)  ⊕  Fréchet (⊨ Heisenberg)

METHOD (the cheapest-decision-labeled move -- memory naming-is-cheapest-decision-
labeled): the capstone ASKS the cheapest available decision (`decide`/`rfl` -- the
finite representation's own zero-cost verdict, the boxes) and INSCRIBES the verdict as
the operator's label. Same shape as the compiler's `lake_build := the_compiler.
converged = d.fact`: ask the decision, write its answer back as the name.

GRADE (honest, per the ledger): the DECOMPOSITION is DERIVED -- the two fields exist,
they land in the two distinct boxes, by rfl/decide. The two ⊨ readings (tensor ⊨ GR,
Fréchet ⊨ Heisenberg) are INTERPRETIVE readings on code-carriers -- NEVER a proved
unification of the two theories. No continuum; the QPhase clash is respected (Episode
branch only, no Meanwhile22+ pull). -/

namespace Measurement

/-- THE 0TH TERM -- the universe tensor (the operator's `universal_observer`) lands in
the VALUE box (box 0), where the fixed point pins it. Reading: tensor ⊨ GR. -/
theorem capstone_zeroth_is_tensor : boxOfTensor .universe = valueBox := rfl

/-- THE 1ST TERM -- the Fréchet (the operator's `differential_equation`, promoted by the
stack to its second variation `electronVariation`) lands in the ELECTRON box (box 1).
Reading: Fréchet ⊨ Heisenberg (the produced electron, charge -1). -/
theorem capstone_first_is_frechet : boxOf electronVariation = electronBox := rfl

/-- THE CAPSTONE. The operator decomposes into its two fields -- the 0th term (the
universe tensor, box 0) and the 1st term (the Fréchet second variation, box 1) -- and
the two are DISTINCT classes of the finite representation: `universal = universe_tensor
⊕ Fréchet`. Derived by the cheapest decision (`rfl`/`decide`), the verdict inscribed as
the label. The ⊨GR / ⊨Heisenberg readings are interpretive, not a proved unification. -/
theorem the_capstone :
    boxOfTensor .universe = valueBox
    ∧ boxOf electronVariation = electronBox
    ∧ valueBox ≠ electronBox :=
  ⟨capstone_zeroth_is_tensor, capstone_first_is_frechet, by decide⟩

/-- The decomposition is NON-DEGENERATE: the two terms occupy the whole finite count
(the 2-box representation) and nothing collapses them -- the operator genuinely has two
terms, the 0th and the 1st, not one. -/
theorem capstone_two_terms_exhaust_the_count :
    ∀ b : Fin boxCount, b = valueBox ∨ b = electronBox := by decide

end Measurement
