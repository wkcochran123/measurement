#!/bin/sh
# usage: run.sh <CARD_2 dir> <this dir>    one fresh process per reading; Lean capped at 1500 MB
export PATH=$HOME/.elan/bin:$PATH
HERE="$2"; mkdir -p "$HERE/raw/M2" "$HERE/probes"
( sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -m ) > "$HERE/raw/M2/machine.out"
cd "$1" || exit 1
: > "$HERE/raw/M2/readings.out"
for rep in 1 2; do
  for kind in reader step; do
    for d in 1 2 3 4 5; do
      python3 "$HERE/probe.py" $kind $d > "$HERE/probes/${kind}_$d.lean"
      lake env lean -M 1500 "$HERE/probes/${kind}_$d.lean" 2>&1 | grep -E "READ |error" | head -3 | sed "s/^/REP $rep /" >> "$HERE/raw/M2/readings.out"
    done
  done
done
