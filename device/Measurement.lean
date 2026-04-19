-- This module serves as the root of the `Measurement` library.
-- Import modules here that should be built as part of the library.
import Measurement.Episode13


/-
def lt : Number → Number → Prop
  | .zero _ , .zero _ => False
  | .zero _ , .one _ _ => True  -- Zero is the origin for both
  | .one _ _, .zero _ => False
  | .one p1 n1', .one p2 n2' =>
      match p1.decTruth, p2.decTruth with
      -- Covariant: Ordered by >= (Wholes)
      | isTrue _,  isTrue _  => le n2' n1'
      -- Contravariant: Ordered by <= (Parts/Strain)
      | isFalse _, isFalse _ => le n1' n2'
      -- Mixed cases (The "Three Card Monte")
      | isTrue _,  isFalse _ => False
      | isFalse _, isTrue _  => True
-/
