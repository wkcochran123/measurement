#!/bin/sh
# usage: make_probes.sh <out dir>   (writes the sweep, the control and the timed probes)
here=$(cd "$(dirname "$0")" && pwd); out=${1:-.}; mkdir -p "$out"
for n in 1 2 4 8 16 32 64; do
  python3 "$here/gen.py" $n > "$out/probe_$n.lean"
  python3 "$here/gen.py" $n | python3 -c "
import sys,re;s=sys.stdin.read()
s=re.sub(r'truth := .*?\n\s+= the_representation.middle_table \(cellA i.val\) \(cellB i.val\)', 'truth := ∀ i : Fin $n, True', s, flags=re.S)
print(s)" > "$out/ctrl_$n.lean"
done
for n in 1 64; do python3 "$here/gen_t.py" $n > "$out/t_$n.lean"; python3 "$here/gen_t.py" $n c > "$out/tc_$n.lean"; done
