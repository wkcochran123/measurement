#!/bin/sh
# usage: run.sh <CARD_2 dir> <this dir>    one fresh process per reading; Lean capped at 1500 MB, 300 s each
# The meter of 019 with asynchronous elaboration off, so the proof is on it.  Only readings not taken before: m = 5..8.
export PATH=$HOME/.elan/bin:$PATH
HERE="$2"; mkdir -p "$HERE/raw/M2" "$HERE/probes"
( sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -m ) > "$HERE/raw/M2/machine.out"
cd "$1" || exit 1
: > "$HERE/raw/M2/readings.out"
for rep in 1 2; do
  python3 "$HERE/probe.py" blank 1 > "$HERE/probes/blank.lean"
  timeout 300 lake env lean -M 1500 "$HERE/probes/blank.lean" 2>&1 | grep -E "READ |error" | head -3 | sed "s/^/REP $rep /" >> "$HERE/raw/M2/readings.out"
  for kind in kernel elaborator; do
    for m in 5 6 7 8; do
      python3 "$HERE/probe.py" $kind $m > "$HERE/probes/${kind}_$m.lean"
      timeout 300 lake env lean -M 1500 "$HERE/probes/${kind}_$m.lean" 2>&1 | grep -E "READ |error|timeout|memory" | head -3 | sed "s/^/REP $rep /" >> "$HERE/raw/M2/readings.out"
      echo "REP $rep DONE kind=$kind m=$m exit=$?" >> "$HERE/raw/M2/readings.out"
    done
  done
done
