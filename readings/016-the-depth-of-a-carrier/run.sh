#!/bin/sh
# usage: run.sh <CARD_2 dir> <this dir>    one fresh process per reading; Lean capped at 1500 MB
export PATH=$HOME/.elan/bin:$PATH
HERE="$2"; mkdir -p "$HERE/raw/M2" "$HERE/probes"
( sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -m ) > "$HERE/raw/M2/machine.out"
cd "$1" || exit 1
: > "$HERE/raw/M2/readings.out"
for rep in 1 2; do
  for c in the_first_card elaborated_by_lean the_card_between the_card_on_the_card_between a_carrier_of_an_empty_box a_carrier_of_an_area a_carrier_of_an_equivalation; do
    python3 "$HERE/probe.py" reader $c > "$HERE/probes/reader_$c.lean"
    lake env lean -M 1500 "$HERE/probes/reader_$c.lean" 2>&1 | grep -E "READ |error" | head -3 | sed "s/^/REP $rep /" >> "$HERE/raw/M2/readings.out"
  done
  for d in one two three; do
    python3 "$HERE/probe.py" rung $d > "$HERE/probes/rung_$d.lean"
    lake env lean -M 1500 "$HERE/probes/rung_$d.lean" 2>&1 | grep -E "READ |error" | head -3 | sed "s/^/REP $rep /" >> "$HERE/raw/M2/readings.out"
  done
done
