#!/bin/sh
# usage: run.sh <repo root> <this dir>     Lean capped at 1500 MB
export PATH=$HOME/.elan/bin:$PATH
HERE="$2"; mkdir -p "$HERE/raw/M2"
cd "$1/CARD_2" || exit 1
lake env lean -M 1500 "$HERE/probe.lean" > "$HERE/raw/M2/build.out" 2>&1; echo "exit $?" >> "$HERE/raw/M2/build.out"
{ echo "References in Episodes 1 to 7 and 9 to 11 (the classes and the rungs) to Episode 8's tapes and counts:";
  grep -n "the_coefficient_tape\|the_coordinate_system\|the_macguffin\|the_dimensions_of_universe\|readers_experience.bent_card\|the_memory_tape\|the_epsilon_tape" Measurement/Episode0[1-7].lean Measurement/Episode09.lean Measurement/Episode1[01].lean | sed 's/ *--.*//' | cut -c1-160;
  echo "(end)";
  echo "Definition of an arm's weight in Episode 12:";
  grep -n "def the_arm_weight" -A 1 Measurement/Episode12.lean | cut -c1-200; } > "$HERE/raw/M2/references.out"
