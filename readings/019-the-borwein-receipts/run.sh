#!/bin/sh
# usage: run.sh <CARD_2 dir> <this dir>    one fresh process per reading; Lean capped at 1500 MB, 300 s each
export PATH=$HOME/.elan/bin:$PATH
HERE="$2"; mkdir -p "$HERE/raw/M2" "$HERE/probes"
( sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -m ) > "$HERE/raw/M2/machine.out"
cd "$1" || exit 1
: > "$HERE/raw/M2/readings.out"
for rep in 1 2; do
  python3 "$HERE/probe.py" blank 1 > "$HERE/probes/blank.lean"
  timeout 300 lake env lean -M 1500 "$HERE/probes/blank.lean" 2>&1 | grep -E "READ |error" | head -3 | sed "s/^/REP $rep /" >> "$HERE/raw/M2/readings.out"
  for m in 1 2 3 4 5 6 7 8; do
    python3 "$HERE/probe.py" kernel $m > "$HERE/probes/kernel_$m.lean"
    timeout 300 lake env lean -M 1500 "$HERE/probes/kernel_$m.lean" 2>&1 | grep -E "READ |error" | head -3 | sed "s/^/REP $rep /" >> "$HERE/raw/M2/readings.out"
  done
  for m in 1 2 3 4; do
    python3 "$HERE/probe.py" elaborator $m > "$HERE/probes/elaborator_$m.lean"
    timeout 300 lake env lean -M 1500 "$HERE/probes/elaborator_$m.lean" 2>&1 | grep -E "READ |error|timeout|memory" | head -3 | sed "s/^/REP $rep /" >> "$HERE/raw/M2/readings.out"
  done
done
