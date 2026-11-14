#!/bin/sh
# usage: run_t.sh <CARD_2 dir> <probe dir>
cd "$1" || exit 1
export PATH=$HOME/.elan/bin:$PATH
sysctl -n machdep.cpu.brand_string
for r in 1 2 3 4 5 6 7 8 9 10; do
  for f in t_64 tc_64 t_1 tc_1; do lake env lean "$2/$f.lean" 2>&1 | grep TIMED; done
done
