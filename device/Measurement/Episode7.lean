/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

(c) 2026 [PATTER TODO: rights gag]

[PATTER TODO: cast chorus]

[PATTER TODO: epigraph quote]

lake build [PATTER TODO: build-flag gag]

__EPISODE 7__: _[PATTER TODO: title -- the referee report]_

Episode 6 submitted the constant. This is what came back.

Every response-to-referees document is a SECOND TAPE. The paper already exists;
the rebuttal only APPENDS to it, one .methodology paragraph per capability the
referee asked about, descending from the announced result (page 36) back down
toward the first distinguishable mark (page 1). Each paragraph records a pair:
the Fact we CONSTRUCTED and the Fact that actually SLIPPED through the review
packet. Where the referee refused to grant authority (the logic, the universal
claim, the slogan), the paragraph records only PRESENCE: the rung has a place
in the record and no fact to its name. The INFERRED conclusion never appears on
this tape at all. The reviewer is never shown the quarter.
-/

-- WE GET SIGNAL!
import Measurement.Episode6
set_option allowUnsafeReducibility true

-- MAIN SCREEN TURN ON
namespace Measurement

universe i

-- Yes, that is a Nat. Six episodes refusing Nat and the journal's submission
-- system wants page numbers. Fine. ONE Nat. For the page numbers ONLY. The
-- pages do not count anything; they index where the reviewer is pointing.
class REVIEWED (Box: Type i) (Pigeon: CarrierProcess Box) (page: Nat) where
  rebuttal : CompilerTape

/- We thank the reviewer for asking where the record begins before any rebuttal
   can be published. This seam closes the custody gap: the submitted manuscript
   is admitted unchanged, so every later response has a record to answer
   against. -/
instance (priority := low) REVIEWER_2_ASKS_WHERE_THE_RECORD_BEGINS
    (Box: Type i) (Pigeon: CarrierProcess Box)
    (the_manuscript: CompilerTape)
    : REVIEWED Box Pigeon 36 := { rebuttal := the_manuscript }

/- We thank the reviewer for noticing that a final output can look conclusive
   without showing what it answered. This paragraph closes the verdict gap by
   tying the announced constant back to the first distinguishable fact carried
   by the review packet. -/
instance (priority := low) REVIEWER_2_ASKS_WHAT_THE_ANSWER_WAS_ANSWERING
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 36]
    : REVIEWED Box Pigeon 35 :=
    { rebuttal := .methodology ledger something.fact Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether compilation is evidence or only a
   celebratory filename. This paragraph closes the artifact gap by extracting
   the fact from both demonstrations and making the constructed/slipped
   difference publishable. -/
instance (priority := low) REVIEWER_2_ASKS_IF_COMPILING_IS_EVIDENCE_OR_A_FILENAME
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [stdout: COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 35]
    : REVIEWED Box Pigeon 34 :=
    let constructed : Fact := match stdout.a_demonstration_of_a_constant with
      | .introduction f _ => f
      | .methodology f _ _ _ _ => f
      | .results f _ _ _ _ _ _ => f
    let slip : Fact := match iterative_solver.a_demonstration_of_a_constant with
      | .introduction f _ => f
      | .methodology f _ _ _ _ => f
      | .results f _ _ _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for pointing out that a halt claim is not the same as
   a checked path through the run band. This paragraph closes the
   stopping-condition gap by recording the submitted route against the route
   actually taken, as plain data, outside the instance wrappers. -/
instance (priority := low) REVIEWER_2_ASKS_IF_HALTING_WAS_CHECKED_OR_DECLARED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (the_route_submitted: SpaceTimePath) (the_route_taken: SpaceTimePath)
    [above: REVIEWED Box Pigeon 33]
    : REVIEWED Box Pigeon 32 :=
    let constructed : Fact := match the_route_submitted with
      | .einstein f => f
      | .whitehole f _ _ => f
      | .geodesic f _ _ _ _ _ => f
      | .blackhole _ _ _ => Pigeon.symbol
    let slip : Fact := match the_route_taken with
      | .einstein f => f
      | .whitehole f _ _ => f
      | .geodesic f _ _ _ _ _ => f
      | .blackhole _ _ _ => Pigeon.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for catching the place where logic would otherwise
   sneak in as authority instead of evidence. This paragraph closes the logical
   rung gap by marking that the content crossed only as ground-free data. -/
instance (priority := low) REVIEWER_2_CATCHES_LOGIC_POSING_AS_AUTHORITY
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 32]
    : REVIEWED Box Pigeon 31 :=
    -- presence-paragraph: the referee grants the rung a place in the record
    -- and no fact to its name; authority does not transfer to the rebuttal.
    { rebuttal := .methodology Pigeon.symbol Pigeon.symbol Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for refusing a universal claim with no admissible
   local witness. This paragraph closes the universality gap by recording the
   rung as a presence paragraph, not as a new global proof smuggled into the
   record. -/
instance (priority := low) REVIEWER_2_REFUSES_A_UNIVERSAL_CLAIM_WITHOUT_A_LOCAL_WITNESS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 31]
    : REVIEWED Box Pigeon 30 :=
    -- presence-paragraph: the referee grants the rung a place in the record
    -- and no fact to its name; authority does not transfer to the rebuttal.
    { rebuttal := .methodology Pigeon.symbol Pigeon.symbol Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking how measurement survives when the tower is
   retold on the wrong side of the seam. This paragraph closes the velocity gap
   by carrying the fact on file as data and comparing it with the slipped
   heartbeat record. -/
instance (priority := low) REVIEWER_2_ASKS_HOW_THE_NEEDLE_SURVIVED_THE_RETELLING
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (velocity_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 34]
    : REVIEWED Box Pigeon 33 :=
    let constructed : Fact := velocity_fact_on_file
    let slip : Fact := match a_small_number.a_distance.in_heartbeats with
      | .origin f _ _ => f
      | .distance_to f _ _ _ _ _ => f
      | .speed f _ _ _ _ _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for distinguishing a real status from a declaration
   that reality has been achieved. This paragraph closes the ledger gap by
   extracting the fact only when the nagging doubt reaches the recorded ledger
   branch. -/
instance (priority := low) REVIEWER_2_DISTINGUISHES_REALITY_FROM_ITS_PRESS_RELEASE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][flying_spaghetti_monster: REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 30]
    : REVIEWED Box Pigeon 29 :=
    let constructed : Fact := match flying_spaghetti_monster.nagging_doubt with
      | .logically _ => Pigeon.symbol
      | .but g _ _ => (match g with
        | .the_proof _ => Pigeon.symbol
        | .we_understand_that k _ _ => (match k with
          | .jarjar _ => Pigeon.symbol
          | .ledger _ f _ => f))
    let slip : Fact := match inverse_square_law.nagging_doubt with
      | .logically _ => Pigeon.symbol
      | .but g _ _ => (match g with
        | .the_proof _ => Pigeon.symbol
        | .we_understand_that k _ _ => (match k with
          | .jarjar _ => Pigeon.symbol
          | .ledger _ f _ => f))
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking what was actually witnessed, rather than
   accepting the title of the witness. This paragraph closes the testimony gap
   by lowering the gospel to the ledger fact it can honestly expose. -/
instance (priority := low) REVIEWER_2_ASKS_WHAT_WAS_ACTUALLY_WITNESSED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [yet: WITNESSED Box Pigeon]
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 29]
    : REVIEWED Box Pigeon 28 :=
    let constructed : Fact := match yet.the_experiment with
      | .the_proof _ => Pigeon.symbol
      | .we_understand_that k _ _ => (match k with
        | .jarjar _ => Pigeon.symbol
        | .ledger _ f _ => f)
    let slip : Fact := match obvious_pattern.the_experiment with
      | .the_proof _ => Pigeon.symbol
      | .we_understand_that k _ _ => (match k with
        | .jarjar _ => Pigeon.symbol
        | .ledger _ f _ => f)
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for requiring the scientific invariant to carry a
   checkable remainder. This paragraph closes the theory gap by refusing
   hypothesis and repeatability as enough, then recording the fact only at the
   theory branch. -/
instance (priority := low) REVIEWER_2_REQUIRES_THE_INVARIANT_TO_CARRY_A_REMAINDER
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [experiment: SCIENTIFIC Box Pigeon]
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 27]
    : REVIEWED Box Pigeon 26 :=
    let constructed : Fact := match experiment.invariant with
      | .repeatable _ => Pigeon.symbol
      | .hypothesis _ _ => Pigeon.symbol
      | .theory _ _ f _ => f
    let slip : Fact := match new_physical_law.invariant with
      | .repeatable _ => Pigeon.symbol
      | .hypothesis _ _ => Pigeon.symbol
      | .theory _ _ f _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether persuasion has been separated from
   evidence. This paragraph closes the propaganda gap by preserving the rung's
   place as presence only, with no argumentative fact granted for the slogan. -/
instance (priority := low) REVIEWER_2_SEPARATES_PERSUASION_FROM_EVIDENCE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 25]
    : REVIEWED Box Pigeon 24 :=
    -- presence-paragraph: the referee grants the rung a place in the record
    -- and no fact to its name; authority does not transfer to the rebuttal.
    { rebuttal := .methodology Pigeon.symbol Pigeon.symbol Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for objecting that truth cannot be cited by name
   while its knowledge path remains hidden. This paragraph closes the knowledge
   gap by carrying the fact on file as data and comparing it with the slipped
   ledger of the scientific process. -/
instance (priority := low) REVIEWER_2_OBJECTS_TO_TRUTH_CITED_BY_NAME_ONLY
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (knowledge_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 28]
    : REVIEWED Box Pigeon 27 :=
    let constructed : Fact := knowledge_fact_on_file
    let slip : Fact := match curve_fit.becomes.knowledge with
      | .jarjar _ => Pigeon.symbol
      | .ledger _ f _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether devotion to the method has been
   mistaken for a method. This paragraph closes the sacred-text gap by lowering
   the acolyte rung to the triangle fact that can be compared. -/
instance (priority := low) REVIEWER_2_ASKS_IF_DEVOTION_TO_METHOD_IS_A_METHOD
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (cult_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 26]
    : REVIEWED Box Pigeon 25 :=
    let constructed : Fact := cult_fact_on_file
    let slip : Fact := match professor.euclid.sacred_texts with
      | .inside_joke _ => Pigeon.symbol
      | .pythagoras _ _ _ => Pigeon.symbol
      | .triangles _ _ f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for noting that a smooth story may only be
   interpolation wearing a lab coat. This paragraph closes the spline gap by
   accepting the slipped fact only when the arm-wave process reaches its
   interpolant. -/
instance (priority := low) REVIEWER_2_SUSPECTS_THE_SMOOTH_STORY_IS_INTERPOLATION_IN_A_LAB_COAT
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (spline_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 24]
    : REVIEWED Box Pigeon 23 :=
    let constructed : Fact := spline_fact_on_file
    let slip : Fact := match pages_of_derivations.arm_wave_process.guess with
      | .observation _ => Pigeon.symbol
      | .knot _ _ _ => Pigeon.symbol
      | .interpolant f _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether finiteness is a boundary condition
   or a decorative animal in the theorem name. This paragraph closes the
   polynomial gap by recording the finite expansion only at the fact-bearing
   branches. -/
instance (priority := low) REVIEWER_2_ASKS_IF_FINITE_IS_A_BOUNDARY_OR_A_DECORATION
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (polynomial_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 23]
    : REVIEWED Box Pigeon 22 :=
    let constructed : Fact := polynomial_fact_on_file
    let slip : Fact := match the_simplex.galerkin_process.polynomial with
      | .constant f => f
      | .monomial _ _ => Pigeon.symbol
      | .factor f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for noticing that a load has to land in a basis
   before it can be compared. This paragraph closes the span gap by tracing the
   null-space or basis fact against the slipped operation. -/
instance (priority := low) REVIEWER_2_NOTES_A_LOAD_MUST_LAND_IN_A_BASIS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (basis_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 22]
    : REVIEWED Box Pigeon 21 :=
    let constructed : Fact := basis_fact_on_file
    let slip : Fact := match fem_solver.basic_operation.span with
      | .null_space f => f
      | .origin _ _ => Pigeon.symbol
      | .basis f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for requiring scale to show its multiplication, not
   merely its unit. This paragraph closes the product gap by comparing the fact
   on file with the slipped multiplication process. -/
instance (priority := low) REVIEWER_2_REQUIRES_SCALE_TO_SHOW_ITS_MULTIPLICATION
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (product_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 21]
    : REVIEWED Box Pigeon 20 :=
    let constructed : Fact := product_fact_on_file
    let slip : Fact := match projection.multiplying_process.product with
      | .origin f => f
      | .one _ _ => Pigeon.symbol
      | .mul f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking where magnitude becomes additive evidence.
   This paragraph closes the sum gap by refusing zero as a sufficient
   publication claim and tracing the add branch where the fact appears. -/
instance (priority := low) REVIEWER_2_ASKS_WHERE_MAGNITUDE_BECOMES_ADDITIVE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (sum_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 20]
    : REVIEWED Box Pigeon 19 :=
    let constructed : Fact := sum_fact_on_file
    let slip : Fact := match extraordinary.adding_process.sum with
      | .zero _ _ => Pigeon.symbol
      | .add f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for distinguishing a value from the process that
   produced it. This paragraph closes the monadic gap by comparing the facts on
   both sides across satire, compilation, and execution branches. -/
instance (priority := low) REVIEWER_2_DISTINGUISHES_A_VALUE_FROM_ITS_PROCESS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [uncountable: VALUE Box Pigeon]
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 19]
    : REVIEWED Box Pigeon 18 :=
    let constructed : Fact := match uncountable.monad with
      | .satire_about f => f
      | .compile f _ _ => f
      | .execute f _ _ => f
    let slip : Fact := match a_constant.monad with
      | .satire_about f => f
      | .compile f _ _ => f
      | .execute f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether execution contains an opcode
   record or only a performed gesture. This paragraph closes the encoding gap
   by carrying the fact on file as data and tracing the slipped opcode
   branch. -/
instance (priority := low) REVIEWER_2_ASKS_IF_EXECUTION_LEFT_AN_OPCODE_RECORD
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (opcode_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 18]
    : REVIEWED Box Pigeon 17 :=
    let constructed : Fact := opcode_fact_on_file
    let slip : Fact := match plots_and_graphs.compiled_process.opcodes with
      | .boot f _ => f
      | .zero f _ _ => f
      | .one f _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking which source fact survives transmission
   through the binary channel. This paragraph closes the source gap by lowering
   both source chains to the fact-bearing physics or zero-like cases. -/
instance (priority := low) REVIEWER_2_ASKS_WHICH_SOURCE_FACT_SURVIVED_THE_CHANNEL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][data_feed: SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 17]
    : REVIEWED Box Pigeon 16 :=
    let constructed : Fact := match data_feed.one with
      | .physics f _ => f
      | .zero_like f _ => f
      | .one_like _ _ _ => Pigeon.symbol
    let slip : Fact := match the_machine_that_goes_ping.one with
      | .physics f _ => f
      | .zero_like f _ => f
      | .one_like _ _ _ => Pigeon.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for noticing that the joke class still has to pay its
   evidentiary bill. This paragraph closes the concept gap by tracing color,
   bang, or superposition to the fact each branch can actually report. -/
instance (priority := low) REVIEWER_2_MAKES_THE_JOKE_PAY_ITS_EVIDENTIARY_BILL
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (jar_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 16]
    : REVIEWED Box Pigeon 15 :=
    let constructed : Fact := jar_fact_on_file
    let slip : Fact := match cannot_be_ignored.meesa_process.concept with
      | .color f _ => f
      | .bang f _ => f
      | .superposition f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether measurability is attached to an
   observable clock or just asserted. This paragraph closes the phenomenon gap
   by comparing the fact on file with the slipped gauge process. -/
instance (priority := low) REVIEWER_2_ASKS_IF_THE_CLOCK_IS_OBSERVABLE_OR_ASSERTED
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (clock_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 15]
    : REVIEWED Box Pigeon 14 :=
    let constructed : Fact := clock_fact_on_file
    let slip : Fact := match timestamp.gauge_process.clock with
      | .this_superpigeon f _ => f
      | .a_pigeon f _ _ => f
      | .that_box f _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking where presence accumulates into a record.
   This paragraph closes the area gap by tracing the present rung through the
   tree and dt branches that can carry the fact. -/
instance (priority := low) REVIEWER_2_ASKS_WHERE_PRESENCE_ACCUMULATES
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (area_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 14]
    : REVIEWED Box Pigeon 13 :=
    let constructed : Fact := area_fact_on_file
    let slip : Fact := match just_now.santa_claus.accumulation with
      | .tree f => f
      | .dt f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether observation is a projection with a
   recorded dimension or just a report of seeing. This paragraph closes the
   sophism gap by tracing the slipped projection to the fact it can expose. -/
instance (priority := low) REVIEWER_2_ASKS_IF_OBSERVATION_HAS_A_RECORDED_DIMENSION
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (sophism_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 13]
    : REVIEWED Box Pigeon 12 :=
    let constructed : Fact := sophism_fact_on_file
    let slip : Fact := match motion.slip_process.projection with
      | .origin f _ _ => f
      | .dimension f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking what makes comparison more than parallel
   naming. This paragraph closes the metavariable gap by carrying the fact on
   file as data and checking the slipped physical value step. -/
instance (priority := low) REVIEWER_2_ASKS_WHAT_MAKES_COMPARISON_MORE_THAN_PARALLEL_NAMING
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (metavariable_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 12]
    : REVIEWED Box Pigeon 11 :=
    let constructed : Fact := metavariable_fact_on_file
    let slip : Fact := match relative_value.physical_process.value with
      | .base f _ => f
      | .step f _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for requiring the physical claim to show its base
   fact rather than inherit authority from later rungs. This paragraph closes
   the physical-process gap by tracing both thresholds to their exposed
   facts. -/
instance (priority := low) REVIEWER_2_REQUIRES_THE_PHYSICAL_CLAIM_TO_SHOW_ITS_BASE_FACT
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [anechoic_chamber: PHYSICAL Box Pigeon]
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 11]
    : REVIEWED Box Pigeon 10 :=
    let constructed : Fact := match anechoic_chamber.threshold with
      | .halting f _ => f
      | .nonhalting f _ _ => f
    let slip : Fact := match timeseries.threshold with
      | .halting f _ => f
      | .nonhalting f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether representation has a carrier, not
   only a notation. This paragraph closes the representative gap by recording
   the slipped computation state at the end of the representation chain. -/
instance (priority := low) REVIEWER_2_ASKS_IF_REPRESENTATION_HAS_A_CARRIER_OR_A_NOTATION
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (state_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 10]
    : REVIEWED Box Pigeon 9 :=
    let constructed : Fact := state_fact_on_file
    let slip : Fact := match csv_file.calculation_process.state with
      | .program f _ => f
      | .compute f _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking where the number actually counts
   something. This paragraph closes the numeric gap by tracing both study
   carriers down to the fact each box came in. -/
instance (priority := low) REVIEWER_2_ASKS_WHERE_THE_NUMBER_ACTUALLY_COUNTS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [jupyter_notebook: NUMERIC Box Pigeon]
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 9]
    : REVIEWED Box Pigeon 8 :=
    let constructed : Fact := match jupyter_notebook.carrier with
      | .hypothesis f => f
      | .a_few_pints f _ _ => f
    let slip : Fact := match how_many_clicks.carrier with
      | .hypothesis f => f
      | .a_few_pints f _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether repetition repeats the experiment
   or merely repeats the sentence. This paragraph closes the repeatability gap
   by comparing the fact on file with the slipped expectation. -/
instance (priority := low) REVIEWER_2_ASKS_IF_REPETITION_REPEATS_THE_EXPERIMENT_OR_THE_SENTENCE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (trial_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 8]
    : REVIEWED Box Pigeon 7 :=
    let constructed : Fact := trial_fact_on_file
    let slip : Fact := match procedure.repeatable_process.expectation with
      | .hypothesis f _ => f
      | .signal_response f _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking where the binary split is recorded after
   execution. This paragraph closes the binary gap by lowering both bits to the
   carrier fact that can still be read. The referee is correct that the
   exhibit named `land` was constructed in the submission and then quietly
   dropped from every subsequent argument list; it is resupplied here, for the
   record. -/
instance (priority := low) REVIEWER_2_ASKS_WHERE_THE_MISSING_EXHIBIT_WENT
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    [flicker: BINARY Box Pigeon]
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (land: BINARY Box Pigeon)
    [above: REVIEWED Box Pigeon 7]
    : REVIEWED Box Pigeon 6 :=
    let constructed : Fact := match flicker.bit with
      | .initial_condition f _ => f
      | .signal_response f _ _ _ _ => f
    let slip : Fact := match land.bit with
      | .initial_condition f _ => f
      | .signal_response f _ _ _ _ => f
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether residue is a limit record or a
   leftover story. This paragraph closes the residue gap by tracing the slipped
   Cauchy process through its index to the carrier symbol. -/
instance (priority := low) REVIEWER_2_ASKS_IF_RESIDUE_IS_A_RECORD_OR_A_LEFTOVER_STORY
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (residue_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 6]
    : REVIEWED Box Pigeon 5 :=
    let constructed : Fact := residue_fact_on_file
    let slip : Fact := pit.cauchy_process.limit_process.indexing_process.count.carrier.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether encoding preserves a read path
   back to the mark. This paragraph closes the encoded-carrier gap by following
   the slipped limit process to the carrier symbol it depends on. -/
instance (priority := low) REVIEWER_2_ASKS_IF_ENCODING_KEEPS_A_READ_PATH_TO_THE_MARK
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (limit_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 5]
    : REVIEWED Box Pigeon 4 :=
    let constructed : Fact := limit_fact_on_file
    let slip : Fact := click.limit_process.indexing_process.count.carrier.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether countability counts a carrier or
   only names a class. This paragraph closes the counting gap by tracing the
   slipped index to the carrier symbol being counted. -/
instance (priority := low) REVIEWER_2_ASKS_IF_COUNTING_COUNTS_A_CARRIER_OR_NAMES_A_CLASS
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (index_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 4]
    : REVIEWED Box Pigeon 3 :=
    let constructed : Fact := index_fact_on_file
    let slip : Fact := cascade_of_particles.index.count.carrier.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking who admitted the mark and under what
   local rule. This paragraph closes the admissibility gap by comparing the
   carried fact on file with the slipped carrier symbol admitted by the
   process. -/
instance (priority := low) REVIEWER_2_ASKS_WHO_ADMITTED_THE_MARK
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    (carrier_fact_on_file: Fact)
    [above: REVIEWED Box Pigeon 3]
    : REVIEWED Box Pigeon 2 :=
    let constructed : Fact := carrier_fact_on_file
    let slip : Fact := something_with_momentum.counting_process.carrier.symbol
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

/- We thank the reviewer for asking whether the whole publication rests on a
   distinguishable mark or on retrospective confidence. This paragraph closes
   the bottom gap by recording the slipped distinguishable fact against the
   fact we started the notebook with, where the rebuttal can finally stop
   descending. Page 1 is never written. The reviewer never sees the quarter. -/
instance (priority := low) REVIEWER_2_ASKS_IF_IT_ALL_RESTS_ON_A_MARK_OR_ON_CONFIDENCE
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon][SOURCE Box Pigeon][REAL Box Pigeon]
    (naotrino: LOCAL Box Pigeon)
    (commuter_pass: UNIVERSAL Box Pigeon naotrino)
    [LOGICAL Box Pigeon naotrino commuter_pass][HALTED Box Pigeon naotrino commuter_pass][MEASURED Box Pigeon naotrino commuter_pass]
    [COMPILED Box Pigeon naotrino commuter_pass][A_TRUTH_ABOUT Box Pigeon naotrino commuter_pass][INFERRED Box Pigeon naotrino commuter_pass]
    (_: CarrierProcess Box)
    (ledger: Fact)(something: DISTINGUISHABLE Box Pigeon)(something_with_momentum: ADMISSIBLE Box Pigeon)
    (cascade_of_particles: COUNTABLE Box Pigeon)(click: ENCODED Box Pigeon)(pit: RESIDUE Box Pigeon)
    (procedure: REPEATABLE Box Pigeon)(how_many_clicks: NUMERIC Box Pigeon)(csv_file: REPRESENTABLE Box Pigeon)
    (timeseries: PHYSICAL Box Pigeon)(relative_value: COMPARABLE Box Pigeon)(motion: OBSERVED Box Pigeon)
    (just_now: PRESENT Box Pigeon)(timestamp: MEASURABLE Box Pigeon)(cannot_be_ignored: GUNGAN Box Pigeon)
    (the_machine_that_goes_ping: SOURCE Box Pigeon)(plots_and_graphs: EXECUTED Box Pigeon)(a_constant: VALUE Box Pigeon)
    (extraordinary: MAGNITUDE Box Pigeon)(projection: SCALED Box Pigeon)(fem_solver: LOAD Box Pigeon)
    (the_simplex: INDEXOFANT Box Pigeon)(pages_of_derivations: BULLSHIT Box Pigeon)(graduate_textbook: PROPAGANDA Box Pigeon)
    (professor: ACOLYTE Box Pigeon)(new_physical_law: SCIENTIFIC Box Pigeon)(curve_fit: TRUTH Box Pigeon)
    (obvious_pattern: WITNESSED Box Pigeon)(inverse_square_law: REAL Box Pigeon)(downhill: LOCAL Box Pigeon)
    (extremum: UNIVERSAL Box Pigeon downhill)(bug_free: LOGICAL Box Pigeon downhill extremum)
    (rerun: HALTED Box Pigeon downhill extremum)(a_small_number: MEASURED Box Pigeon downhill extremum)
    (iterative_solver: COMPILED Box Pigeon downhill extremum)(unambiguous_output: A_TRUTH_ABOUT Box Pigeon downhill extremum)
    [above: REVIEWED Box Pigeon 2]
    : REVIEWED Box Pigeon 1 :=
    let constructed : Fact := nowtrino.fact
    let slip : Fact := something.fact
    { rebuttal := .methodology constructed slip Box (ULift.{i+1, i} Box) above.rebuttal }

end Measurement
