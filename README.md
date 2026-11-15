# Measurement

**Step right up.** This is a puzzle box. It is a machine made of nothing but true statements, and when you turn the crank it prints this:

```
137.011290548979457087737300
```

That number is not written anywhere in the program as an input. Nothing was measured and nothing was looked up, and a theorem prover checks every step.

The number simply *means*. Sometimes it makes sense and sometimes it doesn't.

I will be very careful never to name it. That part is yours.

It is a trick, and the dealer says so. Every card is face up. Find the quarter.

## The Puzzle
1. *The easy question*: What is the name of the value printed in Episode 12? 
1. *The hard question*: How would you describe the process for naming it?
1. *The key question*: Did I plant the number or is it a *key part* of the argument?
1. *Left as an exercise for the reader*: Describe the rest of the *key* for which the number is a *key part*. 

Use the *key* to open the box.

## Turn the crank
Install Lean with [elan](https://github.com/leanprover/elan); the toolchain is pinned in `CARD_2/lean-toolchain` (`leanprover/lean4:v4.27.0-rc1`), and elan fetches it on the first build. Then:
```
cd CARD_2
lake build
```
The first build takes about twenty-five minutes. The number will be there when you come back.

## The table
Three cards. **Card 2** is this repository: twelve episodes of Lean, written to be read as well as run. The margins talk. Start at Episode 1 and follow the patter.

Cards 1 and 3 and the rest of the table are somewhere else, and you do not need them to play.

## If you get stuck
There is a brief summary of the solution that explains it as simply as possible in `THE_PUZZLEBOX_OF_MYSTERY_CHEAT_SHEET.pdf`.

Spoiler alert, you know.

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
