#!/bin/sh
# usage: run_throw.sh <CARD_2 dir> <this dir> <runs>   (one fresh process per run, every probe in probes.list)
export PATH=$HOME/.elan/bin:$PATH
HERE="$2"; mkdir -p "$HERE/raw/M2"
( sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -m ) > "$HERE/raw/M2/machine.out"
cd "$1" || exit 1
while read p; do
  name=$(basename "$p" .lean)
  : > "$HERE/raw/M2/$name.out"
  for r in $(seq 1 ${3:-5}); do echo "RUN $r" >> "$HERE/raw/M2/$name.out"; lake env lean "$HERE/$p" 2>&1 | grep -E "(BLANK|READ) |error" >> "$HERE/raw/M2/$name.out"; done
done < "$HERE/probes.list"
