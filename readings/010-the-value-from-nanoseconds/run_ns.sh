#!/bin/sh
# usage: run_ns.sh <CARD_2 dir> <this dir> <runs>   (runs interleaved: every probe once, then again; one fresh process each)
export PATH=$HOME/.elan/bin:$PATH
HERE="$2"; mkdir -p "$HERE/raw/M2"
( sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -m ) > "$HERE/raw/M2/machine.out"
cd "$1" || exit 1
: > "$HERE/raw/M2/readings.out"
for r in $(seq 1 ${3:-10}); do
  while read p; do
    lake env lean "$HERE/$p" 2>&1 | grep -E "READ |error" | sed "s/^/RUN $r /" >> "$HERE/raw/M2/readings.out"
  done < "$HERE/probes.list"
done
