/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the stories we tell ourselves involve a teller, a hero, and a tellee._

(c) 2026 [PATTER TODO: rights gag]

[PATTER TODO: cast chorus]

[PATTER TODO: epigraph quote]

lake build [PATTER TODO: build-flag gag]

__EPISODE 10__: _The Accomplice_

-/

import Measurement.Episode09
set_option allowUnsafeReducibility true

namespace Measurement

universe i


-- Yes, that is a Nat. Nine episodes refusing Nat and the journal's submission
-- system wants page numbers. Fine. ONE Nat. For the page numbers ONLY. The
-- pages do not count anything; they index where the reviewer is pointing.
-- Each rebuttal below ends with the two places the knower looks for the fact it cites: Card 1 (the
-- geometric monograph) and Card 3 (the numerical one), by printed result and page number of the
-- 23 October 2026 builds. The appendix table "Stanzas and results" in each card is the stable anchor.
class REVIEWED (Box: Type i) (Pigeon: CarrierProcess Box) (page: Nat) where
  rebuttal : ThePreprint

/- We thank the reviewer for asking where the record begins before any rebuttal
   can be published. This seam closes the custody gap: the submitted manuscript
   is admitted unchanged, so every later response has a record to answer
   against.
   Card 1: Corollary 6.1 (p. 34); Theorem 7.1 (p. 37); Proposition 2.6 (p. 9); eq. 1.1 (p. 2).
   Card 3: Table 6.1 (p. 44); Definition 8.1 (p. 56); Proposition 2.2 (p. 11); Theorem 2.4 (p. 19). -/
instance (priority := low) REVIEWER_2_ASKS_WHERE_THE_RECORD_BEGINS
    (Box: Type i) (Pigeon: CarrierProcess Box)
    (the_manuscript: ThePreprint)
    : REVIEWED Box Pigeon 36 := { rebuttal := the_manuscript }

/- We thank the reviewer for noticing that a final output can look conclusive
   without showing what it answered. This paragraph closes the verdict gap by
   tying the announced constant back to the first distinguishable fact carried
   by the review packet.
   Card 1: Proposition 5.4 (p. 28); Section 1.2 (p. 1); Section 6.5 (p. 33).
   Card 3: eq. 6.9 (p. 45); Section 6.4 (p. 45); Section 6.1 (p. 41); Section 7.5 (p. 52). -/
instance (priority := low) REVIEWER_2_ASKS_WHAT_THE_ANSWER_WAS_ANSWERING
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol][REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: FACT)(something: DISTINGUISHABLE Box Pigeon)
    (_: ADMISSIBLE Box Pigeon)(_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)(_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)
    (_: REPRESENTABLE Box Pigeon)(_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)(_: PRESENT Box Pigeon)
    (_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)(_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)(_: MAGNITUDE Box Pigeon)
    (_: SCALED Box Pigeon)(_: LOAD Box Pigeon)(_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)(_: ACOLYTE Box Pigeon)
    (_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)(_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)
    (_: LOGICAL Box Pigeon downhill extremum)(_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 36]
    : REVIEWED Box Pigeon 35 :=
    { rebuttal := .methodology ledger something.fact Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether compilation is evidence or only a
   celebratory filename. This paragraph closes the artifact gap by extracting
   the fact from both demonstrations and making the constructed/slipped
   difference publishable.
   Card 1: Theorem 7.1 (p. 37); Section 6.7 (p. 35); Section 7.2 (p. 38); Appendix A (p. 55).
   Card 3: Section 7.4 (p. 51); Section 6.7 (p. 47); Section 7.7 (p. 53). -/
instance (priority := low) REVIEWER_2_ASKS_IF_COMPILING_IS_EVIDENCE_OR_A_FILENAME
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol][REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [stdout: COMPILED Box Pigeon naotrino commuter_pass]
    [A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)(_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)(_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)
    (_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)(_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)(_: PHYSICAL Box Pigeon)
    (_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)(_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)(_: SOURCE Box Pigeon)
    (_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)(_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)(_: OF Box Pigeon)
    (_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)(_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)(_: WITNESSED Box Pigeon)
    (_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)
    (_: LOGICAL Box Pigeon downhill extremum)(_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)
    (_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 35]
    : REVIEWED Box Pigeon 34 :=
    let constructed : FACT := match stdout.a_demonstration_of_a_constant with
      | .introduction f _ => f
      | .methodology f _ _ _ _ => f
      | .results f _ _ _ _ _ _ => f
    let slip : FACT := match iterative_solver.a_demonstration_of_a_constant with
      | .introduction f _ => f
      | .methodology f _ _ _ _ => f
      | .results f _ _ _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for pointing out that a halt claim is not the same as
   a checked path through the run band. This paragraph closes the
   stopping-condition gap by recording the submitted route against the route
   actually taken, as plain data, outside the instance wrappers.
   Card 1: eq. 5.2 (p. 27); Section 6.1 (p. 30); Section 6.5 (p. 33).
   Card 3: Table 6.1 (p. 44); Proposition 6.1 (p. 42); Figure 6.1 (p. 44); Section 4.8 (p. 33). -/
instance (priority := low) REVIEWER_2_ASKS_IF_HALTING_WAS_CHECKED_OR_DECLARED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol][REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (the_route_submitted: SpaceTimePath) (the_route_taken: SpaceTimePath)
    [above: REVIEWED Box Pigeon 33]
    : REVIEWED Box Pigeon 32 :=
    let constructed : FACT := match the_route_submitted with
      | .einstein f => f
      | .whitehole f _ _ => f
      | .geodesic f _ _ _ _ _ => f
      | .blackhole _ _ _ => Pigeon.symbol
    let slip : FACT := match the_route_taken with
      | .einstein f => f
      | .whitehole f _ _ => f
      | .geodesic f _ _ _ _ _ => f
      | .blackhole _ _ _ => Pigeon.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for catching the place where logic would otherwise
   sneak in as authority instead of evidence. This paragraph closes the logical
   rung gap by marking that the content crossed only as ground-free data.
   Card 1: Proposition 4.2 (p. 19); Section 4.2 (p. 19); Section 3.4 (p. 15).
   Card 3: Section 7.7 (p. 53). -/
instance (priority := low) REVIEWER_2_CATCHES_LOGIC_POSING_AS_AUTHORITY
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 32]
    : REVIEWED Box Pigeon 31 :=
    -- presence-paragraph: the referee grants the rung a place in the record
    -- and no fact to its name; authority does not transfer to the rebuttal.
    { rebuttal := .methodology Pigeon.symbol Pigeon.symbol Box (ULift.{i+1, i} Box) above.rebuttal }
--                                   ^             ^
--                                   |             |
--                                   +-------------+----------- x=x, lol. We have hoisted T=T to symmetric equality.

/- We thank the reviewer for refusing a universal claim with no admissible
   local witness. This paragraph closes the universality gap by recording the
   rung as a presence paragraph, not as a new global proof smuggled into the
   record.
   Card 1: Section 4.1 (p. 18); Section 1.1 (p. 1); Section 7.3 (p. 38).
   Card 3: Proposition 3.1 (p. 23); Proposition 2.2 (p. 11); Section 5.2 (p. 36); Section 5.4 (p. 38). -/
instance (priority := low) REVIEWER_2_REFUSES_A_UNIVERSAL_CLAIM_WITHOUT_A_LOCAL_WITNESS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 31]
    : REVIEWED Box Pigeon 30 :=
    -- presence-paragraph: the referee grants the rung a place in the record
    -- and no fact to its name; authority does not transfer to the rebuttal.
    { rebuttal := .methodology Pigeon.symbol Pigeon.symbol Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking how measurement survives when the tower is
   retold on the wrong side of the seam. This paragraph closes the velocity gap
   by carrying the fact on file as data and comparing it with the slipped
   heartbeat record.
   Card 1: Proposition 2.5 (p. 8); Section 2.2 (p. 7); Section 4.6 (p. 23).
   Card 3: Section 7.7 (p. 53); Section 6.7 (p. 47). -/
instance (priority := low) REVIEWER_2_ASKS_HOW_THE_NEEDLE_SURVIVED_THE_RETELLING
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (velocity_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 34]
    : REVIEWED Box Pigeon 33 :=
    let constructed : FACT := velocity_fact_on_file
    let slip : FACT := match a_small_number.a_distance.in_heartbeats with
      | .origin f _ _ => f
      | .distance_to f _ _ _ _ _ => f
      | .speed f _ _ _ _ _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for distinguishing a real status from a declaration
   that reality has been achieved. This paragraph closes the ledger gap by
   extracting the fact only when the nagging doubt reaches the recorded ledger
   branch.
   Card 1: Section 7.2 (p. 38); Section 6.4 (p. 32); Section 5.7 (p. 29).
   Card 3: Section 3.6 (p. 25); Section 7.3 (p. 51). -/
instance (priority := low) REVIEWER_2_DISTINGUISHES_REALITY_FROM_ITS_PRESS_RELEASE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [flying_spaghetti_monster: REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 30]
    : REVIEWED Box Pigeon 29 :=
    let constructed : FACT := match flying_spaghetti_monster.nagging_doubt with
      | .logically _ => Pigeon.symbol
      | .but g _ _ => (match g with
        | .the_proof _ => Pigeon.symbol
        | .we_understand_that k _ _ => (match k with
          | .jarjar _ => Pigeon.symbol
          | .ledger _ f _ => f))
    let slip : FACT := match inverse_square_law.nagging_doubt with
      | .logically _ => Pigeon.symbol
      | .but g _ _ => (match g with
        | .the_proof _ => Pigeon.symbol
        | .we_understand_that k _ _ => (match k with
          | .jarjar _ => Pigeon.symbol
          | .ledger _ f _ => f))
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking what was actually witnessed, rather than
   accepting the title of the witness. This paragraph closes the testimony gap
   by lowering the gospel to the ledger fact it can honestly expose.
   Card 1: Table 4.1 (p. 20); Section 3.3 (p. 13); Section 6.3 (p. 32).
   Card 3: Section 5.5 (p. 39); Section 5.1 (p. 35). -/
instance (priority := low) REVIEWER_2_ASKS_WHAT_WAS_ACTUALLY_WITNESSED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [yet: WITNESSED Box Pigeon]
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 29]
    : REVIEWED Box Pigeon 28 :=
    let constructed : FACT := match yet.the_experiment with
      | .the_proof _ => Pigeon.symbol
      | .we_understand_that k _ _ => (match k with
        | .jarjar _ => Pigeon.symbol
        | .ledger _ f _ => f)
    let slip : FACT := match obvious_pattern.the_experiment with
      | .the_proof _ => Pigeon.symbol
      | .we_understand_that k _ _ => (match k with
        | .jarjar _ => Pigeon.symbol
        | .ledger _ f _ => f)
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for requiring the scientific invariant to carry a
   checkable remainder. This paragraph closes the theory gap by refusing
   hypothesis and repeatability as enough, then recording the fact only at the
   theory branch.
   Card 1: Proposition 5.1 (p. 24); Section 5.3 (p. 26); Section 6.6 (p. 34).
   Card 3: eq. 3.2 (p. 22); Section 3.2 (p. 22); Section 3.3 (p. 23); Section 6.5 (p. 46). -/
instance (priority := low) REVIEWER_2_REQUIRES_THE_INVARIANT_TO_CARRY_A_REMAINDER
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [experiment: SCIENTIFIC Box Pigeon]
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 27]
    : REVIEWED Box Pigeon 26 :=
    let constructed : FACT := match experiment.invariant with
      | .repeatable _ => Pigeon.symbol
      | .hypothesis _ _ => Pigeon.symbol
      | .theory _ _ f _ => f
    let slip : FACT := match new_physical_law.invariant with
      | .repeatable _ => Pigeon.symbol
      | .hypothesis _ _ => Pigeon.symbol
      | .theory _ _ f _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether persuasion has been separated from
   evidence. This paragraph closes the propaganda gap by preserving the rung's
   place as presence only, with no argumentative fact granted for the slogan.
   Card 1: Table 2.1 (p. 6); Section 2.1 (p. 5); Section 1.4 (p. 3); Appendix A (p. 55).
   Card 3: Section 6.7 (p. 47); Section 7.2 (p. 50). -/
instance (priority := low) REVIEWER_2_SEPARATES_PERSUASION_FROM_EVIDENCE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 25]
    : REVIEWED Box Pigeon 24 :=
    -- presence-paragraph: the referee grants the rung a place in the record
    -- and no fact to its name; authority does not transfer to the rebuttal.
    { rebuttal := .methodology Pigeon.symbol Pigeon.symbol Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for objecting that truth cannot be cited by name
   while its knowledge path remains hidden. This paragraph closes the knowledge
   gap by carrying the fact on file as data and comparing it with the slipped
   ledger of the scientific process.
   Card 1: Proposition 5.4 (p. 28); Theorem 7.1 (p. 37); Section 5.6 (p. 28); Section 3.4 (p. 15).
   Card 3: Section 6.4 (p. 45); Section 3.7 (p. 25). -/
instance (priority := low) REVIEWER_2_OBJECTS_TO_TRUTH_CITED_BY_NAME_ONLY
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (knowledge_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 28]
    : REVIEWED Box Pigeon 27 :=
    let constructed : FACT := knowledge_fact_on_file
    let slip : FACT := match curve_fit.becomes.knowledge with
      | .jarjar _ => Pigeon.symbol
      | .ledger _ f _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether devotion to the method has been
   mistaken for a method. This paragraph closes the sacred-text gap by lowering
   the acolyte rung to the triangle fact that can be compared.
   Card 1: Corollary 6.1 (p. 34); Section 6.4 (p. 32).
   Card 3: eq. 7.1 (p. 50); Section 3.7 (p. 25). -/
instance (priority := low) REVIEWER_2_ASKS_IF_DEVOTION_TO_METHOD_IS_A_METHOD
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (cult_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 26]
    : REVIEWED Box Pigeon 25 :=
    let constructed : FACT := cult_fact_on_file
    let slip : FACT := match professor.euclid.sacred_texts with
      | .inside_joke _ => Pigeon.symbol
      | .pythagoras _ _ _ => Pigeon.symbol
      | .triangles _ _ f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for noting that a smooth story may only be
   interpolation wearing a lab coat. This paragraph closes the spline gap by
   accepting the slipped fact only when the arm-wave process reaches its
   interpolant.
   Card 1: Section 5.7 (p. 29).
   Card 3: eq. 3.4 (p. 23); Section 3.3 (p. 23); Section 1.6 (p. 6). -/
instance (priority := low) REVIEWER_2_SUSPECTS_THE_SMOOTH_STORY_IS_INTERPOLATION_IN_A_LAB_COAT
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (spline_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 24]
    : REVIEWED Box Pigeon 23 :=
    let constructed : FACT := spline_fact_on_file
    let slip : FACT := match pages_of_derivations.arm_wave_process.guess with
      | .observation _ => Pigeon.symbol
      | .knot _ _ _ => Pigeon.symbol
      | .interpolant f _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether the constraint was enforced or
   penalized -- whether finiteness is a boundary condition carried exactly by
   a multiplier, or a decorative animal in the theorem name that a penalty
   parameter is quietly relaxing. The LBB question. This paragraph closes the
   polynomial gap by recording the finite expansion only at the fact-bearing
   branches, which is to say: enforced.
   Card 1: Section 4.4 (p. 21); Section 4.5 (p. 22); Section 5.4 (p. 27).
   Card 3: Proposition 2.3 (p. 15); eq. 3.5 (p. 24); Section 3.5 (p. 24); Section 2.3 (p. 14). -/
instance (priority := low) REVIEWER_2_ASKS_IF_THE_CONSTRAINT_WAS_ENFORCED_OR_PENALIZED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (the_simplex: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (polynomial_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 23]
    : REVIEWED Box Pigeon 22 :=
    let constructed : FACT := polynomial_fact_on_file
    let slip : FACT := match the_simplex.galerkin_process.polynomial with
      | .constant f => f
      | .monomial _ _ => Pigeon.symbol
      | .factor f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for noticing that a load has to land in a basis
   before it can be compared. This paragraph closes the span gap by tracing the
   null-space or basis fact against the slipped operation.
   Card 1: Theorem 5.3 (p. 26); eq. 4.2 (p. 22); Section 4.5 (p. 22); Section 5.2 (p. 25).
   Card 3: Section 4.7 (p. 32); Section 1.6 (p. 6); Section 4.4 (p. 29). -/
instance (priority := low) REVIEWER_2_NOTES_A_LOAD_MUST_LAND_IN_A_BASIS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (basis_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 22]
    : REVIEWED Box Pigeon 21 :=
    let constructed : FACT := basis_fact_on_file
    let slip : FACT := match fem_solver.basic_operation.span with
      | .null_space f => f
      | .origin _ _ => Pigeon.symbol
      | .basis f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for requiring scale to show its multiplication, not
   merely its unit. This paragraph closes the product gap by comparing the fact
   on file with the slipped multiplication process.
   Card 1: Section 2.5 (p. 10); Section 2.5.1 (p. 11); Section 5.2 (p. 25).
   Card 3: eq. 6.2 (p. 41); Section 6.1 (p. 41); Section 3.1 (p. 21). -/
instance (priority := low) REVIEWER_2_REQUIRES_SCALE_TO_SHOW_ITS_MULTIPLICATION
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (product_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 21]
    : REVIEWED Box Pigeon 20 :=
    let constructed : FACT := product_fact_on_file
    let slip : FACT := match projection.multiplying_process.product with
      | .origin f => f
      | .one _ _ => Pigeon.symbol
      | .mul f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking where magnitude becomes additive evidence.
   This paragraph closes the sum gap by refusing zero as a sufficient
   publication claim and tracing the add branch where the fact appears.
   Card 1: eq. 5.2 (p. 27); eq. 6.4 (p. 34); Section 5.5 (p. 27); Section 6.7 (p. 35).
   Card 3: Table 7.1 (p. 51); eq. 3.6 (p. 25); eq. 3.7 (p. 25). -/
instance (priority := low) REVIEWER_2_ASKS_WHERE_MAGNITUDE_BECOMES_ADDITIVE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (sum_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 20]
    : REVIEWED Box Pigeon 19 :=
    let constructed : FACT := sum_fact_on_file
    let slip : FACT := match extraordinary.adding_process.sum with
      | .zero _ _ => Pigeon.symbol
      | .add f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for distinguishing a value from the process that
   produced it. This paragraph closes the monadic gap by comparing the facts on
   both sides across satire, compilation, and execution branches.
   Card 1: Section 3.5 (p. 16); Section 6.1 (p. 30).
   Card 3: Section 6.5 (p. 46); Section 6.7 (p. 47). -/
instance (priority := low) REVIEWER_2_DISTINGUISHES_A_VALUE_FROM_ITS_PROCESS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [uncountable: VALUE Box Pigeon]
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 19]
    : REVIEWED Box Pigeon 18 :=
    let constructed : FACT := match uncountable.monad with
      | .satire_about f => f
      | .compile f _ _ => f
      | .execute f _ _ => f
    let slip : FACT := match a_constant.monad with
      | .satire_about f => f
      | .compile f _ _ => f
      | .execute f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether execution contains an opcode
   record or only a performed gesture. This paragraph closes the encoding gap
   by carrying the fact on file as data and tracing the slipped opcode
   branch.
   Card 1: Section 3.5 (p. 16); Section 5.5 (p. 27); Section 6.1 (p. 30).
   Card 3: Section 6.3 (p. 43); Section 6.7 (p. 47). -/
instance (priority := low) REVIEWER_2_ASKS_IF_EXECUTION_LEFT_AN_OPCODE_RECORD
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (opcode_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 18]
    : REVIEWED Box Pigeon 17 :=
    let constructed : FACT := opcode_fact_on_file
    let slip : FACT := match plots_and_graphs.compiled_process.opcodes with
      | .boot f _ => f
      | .zero f _ _ => f
      | .one f _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking which source fact survives transmission
   through the binary channel. This paragraph closes the source gap by lowering
   both source chains to the fact-bearing physics or zero-like cases.
   Card 1: Proposition 4.3 (p. 20); Section 4.3 (p. 20).
   Card 3: Section 7.4 (p. 51); Section 7.5 (p. 52). -/
instance (priority := low) REVIEWER_2_ASKS_WHICH_SOURCE_FACT_SURVIVED_THE_CHANNEL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 17]
    : REVIEWED Box Pigeon 16 :=
    let constructed : FACT := match (inferInstance : SOURCE Box Pigeon).one with
      | .physics f _ => f
      | .zero_like f _ => f
      | .one_like _ _ _ => Pigeon.symbol
    let slip : FACT := match the_machine_that_goes_ping.one with
      | .physics f _ => f
      | .zero_like f _ => f
      | .one_like _ _ _ => Pigeon.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for noticing that the joke class still has to pay its
   evidentiary bill. This paragraph closes the concept gap by tracing color,
   bang, or superposition to the fact each branch can actually report.
   Card 1: Definition 2.1 (p. 6); Definition 4.1 (p. 19); Table 6.1 (p. 32); Section 1.2 (p. 1).
   Card 3: Section 6.1 (p. 41); Section 5.3 (p. 37). -/
instance (priority := low) REVIEWER_2_MAKES_THE_JOKE_PAY_ITS_EVIDENTIARY_BILL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (jar_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 16]
    : REVIEWED Box Pigeon 15 :=
    let constructed : FACT := jar_fact_on_file
    let slip : FACT := match cannot_be_ignored.meesa_process.concept with
      | .color f _ => f
      | .bang f _ => f
      | .superposition f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether measurability is attached to an
   observable clock or just asserted. This paragraph closes the phenomenon gap
   by comparing the fact on file with the slipped gauge process.
   Card 1: Figure 3.2 (p. 17); eq. 3.3 (p. 16); Section 6.1 (p. 30).
   Card 3: Section 7.6 (p. 53); Section 7.3 (p. 51). -/
instance (priority := low) REVIEWER_2_ASKS_IF_THE_CLOCK_IS_OBSERVABLE_OR_ASSERTED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (clock_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 15]
    : REVIEWED Box Pigeon 14 :=
    let constructed : FACT := clock_fact_on_file
    let slip : FACT := match timestamp.gauge_process.clock with
      | .this_superpigeon f _ => f
      | .a_pigeon f _ _ => f
      | .that_box f _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking where presence accumulates into a record.
   This paragraph closes the area gap by tracing the present rung through the
   tree and dt branches that can carry the fact.
   Card 1: Section 6.6 (p. 34); Section 4.4 (p. 21); Section 2.5.1 (p. 11).
   Card 3: eq. E.6 (p. 73); Section 5.4 (p. 38). -/
instance (priority := low) REVIEWER_2_ASKS_WHERE_PRESENCE_ACCUMULATES
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (area_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 14]
    : REVIEWED Box Pigeon 13 :=
    let constructed : FACT := area_fact_on_file
    let slip : FACT := match just_now.santa_claus.accumulation with
      | .tree f => f
      | .dt f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether observation is a projection with a
   recorded dimension or just a report of seeing. This paragraph closes the
   sophism gap by tracing the slipped projection to the fact it can expose.
   Card 1: Proposition 2.6 (p. 9); eq. 2.2 (p. 9); eq. 6.2 (p. 31); Section 2.4 (p. 9).
   Card 3: Proposition 2.1 (p. 10); Proposition 2.3 (p. 15); Section 2.2 (p. 12); Chapter 2 (p. 8). -/
instance (priority := low) REVIEWER_2_ASKS_IF_OBSERVATION_HAS_A_RECORDED_DIMENSION
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (sophism_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 13]
    : REVIEWED Box Pigeon 12 :=
    let constructed : FACT := sophism_fact_on_file
    let slip : FACT := match motion.slip_process.projection with
      | .origin f _ _ => f
      | .dimension f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking what makes comparison more than parallel
   naming. This paragraph closes the metavariable gap by carrying the fact on
   file as data and checking the slipped physical value step.
   Card 1: Proposition 5.4 (p. 28); eq. 5.3 (p. 28); Section 6.5 (p. 33); Section 1.4 (p. 3).
   Card 3: Theorem 2.4 (p. 19); Proposition 2.5 (p. 19); eq. 7.1 (p. 50); Section 2.5 (p. 19); Section 2.6 (p. 19); Section 7.6 (p. 53). -/
instance (priority := low) REVIEWER_2_ASKS_WHAT_MAKES_COMPARISON_MORE_THAN_PARALLEL_NAMING
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (metavariable_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 12]
    : REVIEWED Box Pigeon 11 :=
    let constructed : FACT := metavariable_fact_on_file
    let slip : FACT := match relative_value.physical_process.value with
      | .base f _ => f
      | .step f _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for requiring the physical claim to show its base
   fact rather than inherit authority from later rungs. This paragraph closes
   the physical-process gap by tracing both thresholds to their exposed
   facts.
   Card 1: Section 6.4 (p. 32); Section 7.3 (p. 38); Chapter 2 (p. 5); Section 7.4 (p. 39).
   Card 3: eq. E.6 (p. 73); Section 3.6 (p. 25). -/
instance (priority := low) REVIEWER_2_REQUIRES_THE_PHYSICAL_CLAIM_TO_SHOW_ITS_BASE_FACT
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [anechoic_chamber: PHYSICAL Box Pigeon]
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 11]
    : REVIEWED Box Pigeon 10 :=
    let constructed : FACT := match anechoic_chamber.threshold with
      | .halting f _ => f
      | .nonhalting f _ _ => f
    let slip : FACT := match timeseries.threshold with
      | .halting f _ => f
      | .nonhalting f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether representation has a carrier, not
   only a notation. This paragraph closes the representative gap by recording
   the slipped computation state at the end of the representation chain.
   Card 1: Section 3.4 (p. 15); Section 6.1 (p. 30); Section 4.6 (p. 23).
   Card 3: Table 6.1 (p. 44); Section 6.3 (p. 43); Section 7.4 (p. 51). -/
instance (priority := low) REVIEWER_2_ASKS_IF_REPRESENTATION_HAS_A_CARRIER_OR_A_NOTATION
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (state_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 10]
    : REVIEWED Box Pigeon 9 :=
    let constructed : FACT := state_fact_on_file
    let slip : FACT := match csv_file.calculation_process.state with
      | .program f _ => f
      | .compute f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking where the number actually counts
   something. This paragraph closes the numeric gap by tracing both study
   carriers down to the fact each box came in.
   Card 1: Proposition 2.2 (p. 6); Table 2.1 (p. 6); Table 6.1 (p. 32); Section 2.1 (p. 5).
   Card 3: Section 7.4 (p. 51); Section 6.4 (p. 45); Section 7.6 (p. 53). -/
instance (priority := low) REVIEWER_2_ASKS_WHERE_THE_NUMBER_ACTUALLY_COUNTS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [jupyter_notebook: NUMERIC Box Pigeon]
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 9]
    : REVIEWED Box Pigeon 8 :=
    let constructed : FACT := match jupyter_notebook.carrier with
      | .hypothesis f => f
      | .book_of_records f _ _ => f
    let slip : FACT := match how_many_clicks.carrier with
      | .hypothesis f => f
      | .book_of_records f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether repetition repeats the experiment
   or merely repeats the sentence. This paragraph closes the repeatability gap
   by comparing the fact on file with the slipped expectation.
   Card 1: Section 7.3 (p. 38); Section 4.3 (p. 20); Section 5.7 (p. 29).
   Card 3: Section 7.2 (p. 50); Section 7.3 (p. 51); Section 4.5 (p. 30); Section 7.7 (p. 53). -/
instance (priority := low) REVIEWER_2_ASKS_IF_REPETITION_REPEATS_THE_EXPERIMENT_OR_THE_SENTENCE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (trial_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 8]
    : REVIEWED Box Pigeon 7 :=
    let constructed : FACT := trial_fact_on_file
    let slip : FACT := match procedure.repeatable_process.expectation with
      | .hypothesis f _ => f
      | .signal_response f _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking where the binary split is recorded after
   execution. This paragraph closes the binary gap by lowering both bits to the
   carrier fact that can still be read. The referee is correct that the
   exhibit named `land` was constructed in the submission and then quietly
   dropped from every subsequent argument list; it is resupplied here, for the
   record.
   Card 1: Proposition 3.3 (p. 14); Table 6.1 (p. 32); eq. 6.3 (p. 32); eq. 2.2 (p. 9).
   Card 3: Section 7.5 (p. 52); Section 6.4 (p. 45). -/
instance (priority := low) REVIEWER_2_ASKS_WHERE_THE_MISSING_EXHIBIT_WENT
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [flicker: BINARY Box Pigeon]
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (land: BINARY Box Pigeon)
    [above: REVIEWED Box Pigeon 7]
    : REVIEWED Box Pigeon 6 :=
    let constructed : FACT := match flicker.bit with
      | .initial_condition f _ => f
      | .signal_response f _ _ _ _ => f
    let slip : FACT := match land.bit with
      | .initial_condition f _ => f
      | .signal_response f _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether residue is a limit record or a
   leftover story. This paragraph closes the residue gap by tracing the slipped
   Cauchy process through its index to the carrier symbol.
   Card 1: Proposition 5.1 (p. 24); Section 5.3 (p. 26); Section 6.6 (p. 34).
   Card 3: Proposition 2.2 (p. 11); eq. 6.8 (p. 45); Section 3.7 (p. 25); Section 6.5 (p. 46). -/
instance (priority := low) REVIEWER_2_ASKS_IF_RESIDUE_IS_A_RECORD_OR_A_LEFTOVER_STORY
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (residue_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 6]
    : REVIEWED Box Pigeon 5 :=
    let constructed : FACT := residue_fact_on_file
    let slip : FACT := pit.cauchy_process.limit_process.indexing_process.count.palmed_card.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether encoding preserves a read path
   back to the mark. This paragraph closes the encoded-carrier gap by following
   the slipped limit process to the carrier symbol it depends on.
   Card 1: Theorem 7.1 (p. 37); eq. 1.1 (p. 2); Section 6.1 (p. 30).
   Card 3: Section 6.4 (p. 45); Section 7.5 (p. 52). -/
instance (priority := low) REVIEWER_2_ASKS_IF_ENCODING_KEEPS_A_READ_PATH_TO_THE_MARK
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (limit_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 5]
    : REVIEWED Box Pigeon 4 :=
    let constructed : FACT := limit_fact_on_file
    let slip : FACT := click.limit_process.indexing_process.count.palmed_card.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether countability counts a carrier or
   only names a class. This paragraph closes the counting gap by tracing the
   slipped index to the carrier symbol being counted.
   Card 1: Proposition 3.4 (p. 17); Proposition 2.2 (p. 6); Section 6.1 (p. 30).
   Card 3: Section 7.4 (p. 51); Section 7.5 (p. 52). -/
instance (priority := low) REVIEWER_2_ASKS_IF_COUNTING_COUNTS_A_CARRIER_OR_NAMES_A_CLASS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (index_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 4]
    : REVIEWED Box Pigeon 3 :=
    let constructed : FACT := index_fact_on_file
    let slip : FACT := cascade_of_particles.index.count.palmed_card.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking who admitted the mark and under what
   local rule. This paragraph closes the admissibility gap by comparing the
   carried fact on file with the slipped carrier symbol admitted by the
   process.
   Card 1: eq. 6.1 (p. 30); Section 6.1 (p. 30); Section 1.1 (p. 1); Chapter 6 (p. 30).
   Card 3: Section 6.1 (p. 41); Section 4.3 (p. 28); Section 4.8 (p. 33). -/
instance (priority := low) REVIEWER_2_ASKS_WHO_ADMITTED_THE_MARK
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(_: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (carrier_fact_on_file: FACT)
    [above: REVIEWED Box Pigeon 3]
    : REVIEWED Box Pigeon 2 :=
    let constructed : FACT := carrier_fact_on_file
    let slip : FACT := something_with_momentum.counting_process.palmed_card.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether the whole publication rests on a
   distinguishable mark or on retrospective confidence. This paragraph closes
   the bottom gap by recording the slipped distinguishable fact against the
   fact we started the notebook with, where the rebuttal can finally stop
   descending. Page 1 is never written. The reviewer never sees the quarter.
   Card 1: Section 6.4 (p. 32); Section 6.2 (p. 31); Section 5.7 (p. 29).
   Card 3: Section 6.1 (p. 41); Section 6.4 (p. 45); Section 3.6 (p. 25); Section 7.1 (p. 49). -/
instance (priority := low) REVIEWER_2_ASKS_IF_IT_ALL_RESTS_ON_A_MARK_OR_ON_CONFIDENCE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon][Inhabited nowtrino.symbol]
    [REAL Box Pigeon]
    [naotrino: LOCAL Box Pigeon]
    [commuter_pass: UNIVERSAL Box Pigeon naotrino]
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (_: FACT)(something: DISTINGUISHABLE Box Pigeon)(_: ADMISSIBLE Box Pigeon)
    (_: COUNTABLE Box Pigeon)(_: ENCODED Box Pigeon)(_: RESIDUE Box Pigeon)(_: BINARY Box Pigeon)
    (_: REPEATABLE Box Pigeon)(_: NUMERIC Box Pigeon)(_: REPRESENTABLE Box Pigeon)
    (_: PHYSICAL Box Pigeon)(_: COMPARABLE Box Pigeon)(_: OBSERVED Box Pigeon)
    (_: PRESENT Box Pigeon)(_: MEASURABLE Box Pigeon)(_: GUNGAN Box Pigeon)
    (_: SOURCE Box Pigeon)(_: EXECUTED Box Pigeon)(_: VALUE Box Pigeon)
    (_: MAGNITUDE Box Pigeon)(_: SCALED Box Pigeon)(_: LOAD Box Pigeon)
    (_: OF Box Pigeon)(_: BULLSHIT Box Pigeon)(_: PROPAGANDA Box Pigeon)
    (_: ACOLYTE Box Pigeon)(_: SCIENTIFIC Box Pigeon)(_: TRUTH Box Pigeon)
    (_: WITNESSED Box Pigeon)(_: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(_: LOGICAL Box Pigeon downhill extremum)
    (_: HALTED Box Pigeon downhill extremum)(_: MEASURED Box Pigeon downhill extremum)
    (_: COMPILED Box Pigeon downhill extremum)(_: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 2]
    : REVIEWED Box Pigeon 1 :=
    let constructed : FACT := nowtrino.fact
    let slip : FACT := something.fact
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

end Measurement
