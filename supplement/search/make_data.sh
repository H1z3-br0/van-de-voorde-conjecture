#!/bin/sh
set -e
cd "$(dirname "$0")"
${CC:-cc} -O2 -std=c99 -Wall -o bsw_search bsw_search.c
for q in 7 11 19 23 31; do ./bsw_search $q 1 -fullcheck > ../data/q_$q.txt; done
./bsw_search 3 3 1 2 0 -fullcheck > ../data/q_27.txt
rm -f bsw_search
grep -h '^q=' ../data/q_*.txt | cut -d' ' -f1,6-9
