#!/bin/sh
# usage: run_routes.sh <CARD_2 dir> <probe> <runs>   (one fresh process per run)
cd "$1" || exit 1
export PATH=$HOME/.elan/bin:$PATH
sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -m
for r in $(seq 1 ${3:-5}); do echo "RUN $r"; lake env lean "$2" 2>&1 | grep -E "^(info: .*)?(BLANK|HALVING|CRANK|MEET) " ; done
