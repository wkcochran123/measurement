/-
Measurement/Chapter2.lean
-/

import Measurement.Chapter1

namespace Measurement

abbrev DECOMPOSED (Parts : Type i) := (TOKEN Parts × TOKEN Parts)
abbrev DECOMPOSE (Parts : Type i) := REFINE (DECOMPOSED Parts)

class DECOMPOSABLE
    (Characteristic : Type → TOKEN Type)
    (Method         : Type -> TOKEN Type → TOKEN Type)
    (Computed       : Type 1 → REFINED (Type 1))
    (Transformed    : Type → REFINED (Type))
    (Invariant      : Type)
    (Symbol         : Type)
    (Parts          : Type)
    (Mapping        : EVENT Type)
    (Decomposition  : DECOMPOSED Parts)
    (lex            : REFINE (TOKEN Invariant) → DECOMPOSE (TOKEN Invariant))
    (Metaphor       : TOKEN Invariant → DECOMPOSE (TOKEN Invariant) → BOOL Bool)
    [a : ADMISSIBLE Mapping
                    Computed Invariant Transform (fun x y =>
                        if Metaphor x (lex y) = TRUTH then TRUTH else __SILENCE__)]
      where

  decomposition: DECOMPOSE (TOKEN Invariant) := lex Mapping

end Measurement
