# Measurement

**The Apparently Meaningful Coincidence** 
This is a puzzle box. A machine checked argument of *OBVIOUSLY* _TRUE_ statements built on _logic alone_.  It is a machine made of 
nothing but what you think it is, and when you turn the crank it prints this:

```
137.011290548979457087737300
```

That number is not written anywhere in the program as an input. Nothing was measured and nothing was looked up, and a theorem prover checks every step.

The number simply *means*. Sometimes it makes sense and sometimes it doesn't.

I will be very careful never to name it. That's just a trick of the light. *wink*

## The Puzzle
1. *The easy question*: What is the name of the value printed in Episodes 8, 12, & 13? 
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
There is a brief instructions guide in `INSTRUCTIONS.pdf`. It has millions of hours of play-testing behind it.

There is also an AGENTS.md that will explain to your favorite coding spell checker how this is laid out. Do not expect much, the Lean is very convoluted and 
beyond the understanding of most AI, being a meta-program in a meta-program, both of which implement simulations of the other on a simulation of the very Lean
it is running on. Don't say I didn't give you a map to the solution.

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
CARD_2 % time lake build > ./build_log && cat build_log
lake build > ./build_log  1511.67s user 20.58s system 100% cpu 25:30.65 total
✔ [2/16] Built Measurement.Episode01 (1.8s)
✔ [3/16] Built Measurement.ComputerProgram (218ms)
✔ [4/16] Built Measurement.Episode02 (1.2s)
✔ [5/16] Built Measurement.Calibration.LeanCalibration (1.7s)
✔ [6/16] Built Measurement.Episode03 (5.1s)
✔ [7/16] Built Measurement.Episode04 (1383s)
✔ [8/16] Built Measurement.Episode05 (20s)
✔ [9/16] Built Measurement.Episode07 (15s)
ℹ [10/16] Built Measurement.Episode08 (2.9s)
info: Measurement/Episode08.lean:1365:0: "137.011290548979457087737300"
info: Measurement/Episode08.lean:1366:0: 'readers_experience.the_constant_can_be_inferred' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode08.lean:1367:0: 'readers_experience.the_constant_factor_of_scaling_bullshit' depends on axioms: [propext, Quot.sound]
✔ [11/16] Built Measurement.Episode09 (15s)
✔ [12/16] Built Measurement.Episode10 (32s)
✔ [13/16] Built Measurement.Episode11 (3.3s)
ℹ [14/16] Built Measurement.Episode12 (48s)
info: Measurement/Episode12.lean:1521:0: "137.011290548979457087737300"
info: Measurement/Episode12.lean:1522:0: 'Measurement.what_would_you_call_this_number?' depends on axioms: [propext]
info: Measurement/Episode12.lean:5831:0: [(false, true, [], []), (false, false, [], [true]), (true, true, [true], []), (false, true, [false, true], []),
  (false, false, [true], [true]), (true, true, [true, true], []), (false, true, [false, true, true], []),
  (false, false, [true, true], [true]), (true, true, [true, true, true], []),
  (false, true, [false, true, true, true], []), (false, false, [true, true, true], [true]),
  (true, true, [true, true, true, true], [])]
info: Measurement/Episode12.lean:5913:0: some 4592
info: Measurement/Episode12.lean:5914:0: 36
info: Measurement/Episode12.lean:6643:0: 42
✔ [15/16] Built Measurement (2.0s)
Build completed successfully (16 jobs).
CARD_2 % cd ..
measurement % vim README.md
```

## HINT:
The only reason why *YOU the KNOWER* see the number is because there is something *YOU the READER* can't understand.
