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
- `CARD_1.pdf`: the geometric account, what a record must retain.
- `CARD_3.pdf`: the numerical account, what may be claimed from a reading.
- `THE_QUARTER.pdf`: the number every record carries only as a projection.
- `BENT_CARD.pdf`: the infinite loop, considered harmless.
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
time lake build > build_log && cat build_log
lake build > build_log  1433.83s user 13.16s system 99% cpu 24:17.21 total
✔ [2/16] Built Measurement.Episode01 (2.0s)
✔ [3/16] Built Measurement.ComputerProgram (205ms)
✔ [4/16] Built Measurement.Episode02 (1.6s)
✔ [5/16] Built Measurement.Calibration.LeanCalibration (2.2s)
✔ [6/16] Built Measurement.Episode03 (4.6s)
✔ [7/16] Built Measurement.Episode04 (1355s)
✔ [8/16] Built Measurement.Episode05 (21s)
✔ [9/16] Built Measurement.Episode07 (16s)
ℹ [10/16] Built Measurement.Episode08 (5.6s)
info: Measurement/Episode08.lean:1297:0: "137.011290548979457087737300"
info: Measurement/Episode08.lean:1298:0: 'readers_experience.the_constant_can_be_inferred' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode08.lean:1299:0: 'readers_experience.the_constant_factor_of_scaling_bullshit' depends on axioms: [propext, Quot.sound]
✔ [11/16] Built Measurement.Episode09 (17s)
✔ [12/16] Built Measurement.Episode10 (28s)
✔ [13/16] Built Measurement.Episode11 (2.5s)
ℹ [14/16] Built Measurement.Episode12 (4.6s)
info: Measurement/Episode12.lean:1398:0: 'Measurement.the_box_has_one_point' depends on axioms: [Quot.sound]
info: Measurement/Episode12.lean:1459:0: "137.011290548979457087737300"
info: Measurement/Episode12.lean:1460:0: 'Measurement.what_would_you_call_this_number?' depends on axioms: [propext, Quot.sound]
✔ [15/16] Built Measurement (831ms)
Build completed successfully (16 jobs).
```
