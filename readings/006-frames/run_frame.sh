#!/bin/sh
# usage: run_frame.sh <CARD_2 dir> <probe dir> <P|E> <w1 repeats> <w2 repeats> <w3 repeats>
# P: default scheduling (performance cores). E: taskpolicy -c background (efficiency cores).
cd "$1" || exit 1
export PATH=$HOME/.elan/bin:$PATH
pre=""; [ "$3" = "E" ] && pre="taskpolicy -c background"
echo "FRAME $(sysctl -n machdep.cpu.brand_string) $3"
for r in $(seq 1 $4); do $pre lake env lean "$2/w1_dev.lean" | grep TIMED; $pre lake env lean "$2/w1_ctrl.lean" | grep TIMED; done
for r in $(seq 1 $5); do echo "RUN W2 $r"; $pre lake env lean "$2/w2_beats.lean" | grep BEAT; done
for r in $(seq 1 $6); do echo "RUN W3 $r"; $pre lake env lean "$2/w3_steps.lean" | grep STEP; done
