#!/usr/bin/env bash
# Time each generated benchmark; TSV to stdout: family n variant wall_s status
set -u
cd "$(dirname "$0")/.."
python3 bench/gen.py bench/generated > /dev/null
lake build Kraken KrakenTactics > /dev/null 2>&1
echo -e "family\tn\tvariant\twall_s\tstatus"
for f in bench/generated/*.lean; do
  base=$(basename "$f" .lean)
  fam=$(echo "$base" | sed 's/[0-9].*//')
  n=$(echo "$base" | sed 's/[a-z]*\([0-9]*\)_.*/\1/')
  variant=${base##*_}
  start=$(date +%s.%N)
  if timeout 120 lake env lean "$f" > /dev/null 2>&1; then st=ok; else st=FAIL; fi
  end=$(date +%s.%N)
  printf "%s\t%s\t%s\t%.2f\t%s\n" "$fam" "$n" "$variant" "$(echo "$end $start" | awk '{print $1-$2}')" "$st"
done
