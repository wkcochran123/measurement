#!/bin/sh
# usage: run.sh <CARD_2 dir> <this dir>    one fresh process per reading; Lean capped at 1500 MB
export PATH=$HOME/.elan/bin:$PATH
HERE="$2"; mkdir -p "$HERE/raw/M2" "$HERE/probes"
( sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -m ) > "$HERE/raw/M2/machine.out"
cd "$1" || exit 1
: > "$HERE/raw/M2/readings.out"
for rep in 1 2; do for w in ctrl w0 w1 w2 w3; do for n in 4 8; do
  python3 "$HERE/gen.py" $w $n > "$HERE/probes/${w}_$n.lean"
  lake env lean -M 1500 "$HERE/probes/${w}_$n.lean" 2>&1 | grep -E "READ |error" | head -3 | sed "s/^/REP $rep /" >> "$HERE/raw/M2/readings.out"
done; done; done
