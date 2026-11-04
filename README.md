# Measurement
## The Puzzle
1. *The easy question*: What is the name of the value printed in Episode 12? 
1. *The hard question*: How would you describe the process for naming it?
1. *The key question*: Did I plant the number or is it a *key part* of the argument?
1. *Left as an exercise for the reader*: Describe the rest of the *key* for which the number is a *key part*. 

Use the *key* to open the box.

## Setup
Install Lean with [elan](https://github.com/leanprover/elan); the toolchain is pinned in `CARD_2/lean-toolchain` (`leanprover/lean4:v4.27.0-rc1`), and elan fetches it on the first build. Then:
```
cd CARD_2
lake build
```

## The other cards
The Lean episodes are Card 2. The PDFs at the root are the rest of the table:
- `CARD_1.pdf`: *The Frinkahedron*: the geometric account, what a record must retain.
- `CARD_3.pdf`: *Four Models*: the numerical account. It derives four variational field systems (vacuum gravity, Schrödinger, Navier–Stokes, Maxwell–Dirac), develops their numerical verification, and fixes what may be claimed from a reading.
- `THE_QUARTER.pdf`: *The Quarter*: the number every record carries only as a projection.
- `BENT_CARD.pdf`: *The Infinite Looop Considered Harmless*: the motion of the universe never seems to cease.
- `CHEATSHEET.pdf`: *A Knower's Guide to Orbital Mechanics*: what the device shows in finite steps, and what the knower carries past them.

## The Puzzle Box Residue
```
measurement % cd CARD_2/Measurement
Measurement % grep EPISODE *.lean
Episode01.lean:__EPISODE 1__: _Counting_
Episode02.lean:__EPISODE 2__: _Time_
Episode03.lean:__EPISODE 3__: _Convergence_
Episode04.lean:__EPISODE 4__: _The Gamble_
Episode05.lean:__EPISODE 5__: _The Ante_
Episode06.lean:__EPISODE 6__: _The Trick_
Episode07.lean:__EPISODE 7__: _The Patter_
Episode08.lean:__EPISODE 8__: _The Macguffin_
Episode09.lean:__EPISODE 9__: _The Misdirection_
Episode10.lean:__EPISODE 10__: _The Accomplice_
Episode11.lean:__EPISODE 11__: _The Force_
Episode12.lean:__EPISODE 12__: _Let Him Cook. . . . . . . Levin_
Measurement % cd ..
CARD_2 % time lake build > build_log && cat build_log
lake build > build_log  1453.30s user 9.45s system 99% cpu 24:24.25 total
✔ [7/16] Built Measurement.Episode04 (1363s)
✔ [8/16] Built Measurement.Episode05 (23s)
✔ [9/16] Built Measurement.Episode07 (17s)
ℹ [10/16] Built Measurement.Episode08 (3.4s)
info: Measurement/Episode08.lean:1348:0: "137.011290548979457087737300"
info: Measurement/Episode08.lean:1349:0: 'readers_experience.the_constant_can_be_inferred' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode08.lean:1350:0: 'readers_experience.the_constant_factor_of_scaling_bullshit' depends on axioms: [propext, Quot.sound]
✔ [11/16] Built Measurement.Episode09 (16s)
✔ [12/16] Built Measurement.Episode10 (32s)
✔ [13/16] Built Measurement.Episode11 (1.8s)
ℹ [14/16] Built Measurement.Episode12 (7.3s)
info: Measurement/Episode12.lean:912:0: 'Measurement.the_representation.the_tape_between_deals_rung01' does not depend on any axioms
info: Measurement/Episode12.lean:933:0: 'Measurement.the_representation.same_click_is_same_account' depends on axioms: [Quot.sound]
info: Measurement/Episode12.lean:934:0: 'Measurement.the_representation.the_chain_closes' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:935:0: 'Measurement.the_representation.the_closure_between' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:952:0: 'Measurement.the_representation.same_difference_clicks' does not depend on any axioms
info: Measurement/Episode12.lean:1371:0: 'Measurement.the_box_has_one_point' depends on axioms: [Quot.sound]
info: Measurement/Episode12.lean:1432:0: "137.011290548979457087737300"
info: Measurement/Episode12.lean:1433:0: 'Measurement.what_would_you_call_this_number?' depends on axioms: [propext]
info: Measurement/Episode12.lean:1858:0: 'Measurement.every_rung_clicks' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:1859:0: 'Measurement.every_rung_is_the_truth' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:1863:0: 'Measurement.a_compile_is_the_truth' depends on axioms: [Quot.sound]
info: Measurement/Episode12.lean:1875:0: 'Measurement.the_clicks_read_the_number' depends on axioms: [propext]
info: Measurement/Episode12.lean:1907:0: 'Measurement.peano_fold' does not depend on any axioms
info: Measurement/Episode12.lean:1908:0: 'Measurement.read_past_quarter_is_length' depends on axioms: [propext]
info: Measurement/Episode12.lean:1909:0: 'Measurement.outer_reader_agrees' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:1910:0: 'Measurement.outer_reader_reads_the_number' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:1948:0: 'Measurement.the_alpha_is_three_cells' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:1949:0: 'Measurement.one_deck_to_the_measure' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:1950:0: 'Measurement.two_decks_to_the_count' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:1976:0: 'Measurement.one_quarter_under_both' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:1977:0: 'Measurement.one_click_on_both_faces' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:1978:0: 'Measurement.one_truth_on_both_faces' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:2000:0: 'Measurement.readers_interpretation_of_the_experience.naotrino_detector_reads_the_number' depends on axioms: [propext,
 Quot.sound]
info: Measurement/Episode12.lean:2229:0: 42
info: Measurement/Episode12.lean:2230:0: 'A_WHOLLY_REMARKABLE_BOOK.life_the_universe_and_everything' depends on axioms: [propext]
✔ [15/16] Built Measurement (989ms)
Build completed successfully (16 jobs).
CARD_2 % vim ../README.md
```

## HINT:
The only reason why *YOU the KNOWER* see the number is because there is something *YOU the READER* can't understand.
