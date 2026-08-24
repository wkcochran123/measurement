-- MonteIterator.lean
--
-- Built to the operator's design line (2026-08-23 20:32): "Monte should be a
-- multiset iterator.  tange the names iterate, funge skip to next name.  that's
-- the counter.  that's the heartbeats."
--
-- So: a multiset is a bag of names with repeats.  Two moves.
--   TANGE steps WITHIN a name -- consumes one occurrence, selecting by the
--     characteristic you are already on.  Ours: the count of how many.
--   FUNGE steps TO THE NEXT NAME -- skips the rest of the current run, bagging
--     by like.  The world's: which kinds there are.
-- The counter is what the two moves accumulate, and the heartbeats are the
-- steps taken.
--
-- ZERO IMPORTS.  Names are `Nat` labels, never `String`: querying a `String`
-- pulls choice through the UTF-8 API, and this file must stay axiom-free.
--
-- NOT CLAIMED: that this is Episode 9's Monte.  It is the ITERATOR the design
-- line describes, built standalone so its behaviour can be decided.  Wiring it
-- to the story is a separate step and is not taken here.

namespace Measurement.MonteIterator

/-- A bag of names, written as a run-length list: each entry is a name with how
many of it there are.  Repeats are the point -- this is a multiset, not a set. -/
abbrev Bag := List (Nat × Nat)

/-- TANGE: step within the name you are on.  One occurrence consumed; the name
stays.  When the run is exhausted the name is dropped and tange has nothing
left to do on it. -/
def tange : Bag → Bag
  | []            => []
  | (_, 0) :: r   => r
  | (n, k+1) :: r => if k = 0 then r else (n, k) :: r

/-- FUNGE: skip to the next name.  The whole remaining run of the current name
goes, however many were left in it. -/
def funge : Bag → Bag
  | []       => []
  | _ :: r   => r

/-- THE COUNTER, by tange: how many steps within names the bag affords -- the
total number of occurrences. -/
def tangeCount : Bag → Nat
  | []            => 0
  | (_, k) :: r   => k + tangeCount r

/-- THE COUNTER, by funge: how many names there are -- the number of runs. -/
def fungeCount : Bag → Nat
  | []     => 0
  | _ :: r => 1 + fungeCount r

/-- THE HEARTBEATS: the steps a full tange traversal takes, counted by running
the iterator to exhaustion rather than by reading the arithmetic off the bag.
Fuel-bounded so it is total; the fuel is the occurrence count, which is exactly
enough. -/
def heartbeats : Nat → Bag → Nat
  | 0,      _  => 0
  | _+1,    [] => 0
  | f+1,    b  => 1 + heartbeats f (tange b)

/-- A worked bag: three names, with three, one and two of them. -/
def theBag : Bag := [(0, 3), (1, 1), (2, 2)]

#eval ("the bag", theBag)
#eval ("tange count (occurrences)", tangeCount theBag)
#eval ("funge count (names)", fungeCount theBag)
#eval ("heartbeats, run to exhaustion", heartbeats (tangeCount theBag) theBag)
#eval ("funge to the end", funge (funge (funge theBag)))

-- ---------------------------------------------------------------------------
-- THE RECEIPTS.
-- ---------------------------------------------------------------------------

/-- RUNNING THE ITERATOR AGREES WITH COUNTING THE BAG.  The heartbeats a full
tange traversal takes are exactly the occurrences the bag holds -- the counter
is the run, not a number written beside it. -/
theorem the_heartbeats_are_the_occurrences :
    heartbeats (tangeCount theBag) theBag = tangeCount theBag := by decide

/-- AND THE TWO MOVES COUNT DIFFERENT THINGS.  Tange counts how many; funge
counts how many KINDS.  On this bag they are six and three, and they are not
the same number -- which is the whole reason both moves exist. -/
theorem the_two_moves_do_not_agree :
    tangeCount theBag = 6 ∧ fungeCount theBag = 3
      ∧ tangeCount theBag ≠ fungeCount theBag := by decide

/-- FUNGE COSTS ONE STEP PER NAME, whatever the multiplicities: three funges
empty a three-name bag no matter how deep its runs are. -/
theorem funge_skips_a_whole_run :
    funge (funge (funge theBag)) = [] := by decide

/-- AND TANGE DOES NOT: six tanges are needed where three funges sufficed.  The
gap between the two counts is the multiplicity the bag was carrying. -/
theorem tange_does_not_skip :
    tange (tange (tange theBag)) ≠ [] := by decide

end Measurement.MonteIterator

#print axioms Measurement.MonteIterator.the_heartbeats_are_the_occurrences
#print axioms Measurement.MonteIterator.the_two_moves_do_not_agree
#print axioms Measurement.MonteIterator.funge_skips_a_whole_run
#print axioms Measurement.MonteIterator.tange_does_not_skip
