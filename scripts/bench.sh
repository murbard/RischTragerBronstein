#!/bin/bash
# Run the standard integrals of tests/integrals.txt through the `rtb` executable, one process per
# formula, and report the answer, whether it is the expected one, and the wall time.
#   usage: scripts/bench.sh [time limit per formula in seconds, default 20] [test file]
cd "$(dirname "$0")/.."
R=.lake/build/bin/rtb
LIM=${1:-20}
FILE=${2:-tests/integrals.txt}
[ -x "$R" ] || { echo "build the tool first: lake build rtb"; exit 2; }
ok=0; bad=0; slow=0; unk=0
printf '%-8s %-5s %9s  %s\n' result want time formula
while IFS= read -r line; do
  case "$line" in ''|'#'*) [ -n "$line" ] && echo "$line"; continue;; esac
  want=${line%%|*}; want=${want// /}
  f=${line#*|}; f=${f# }
  s=$(date +%s.%N)
  out=$(timeout "$LIM" "$R" "$f" 2>&1); rc=$?
  t=$(echo "$(date +%s.%N) - $s" | bc)
  if [ $rc -eq 124 ]; then got=TIMEOUT
  elif echo "$out" | grep -q "not elementary"; then got=N
  elif echo "$out" | grep -q "elementary"; then got=E
  elif echo "$out" | grep -q "no answer"; then got=NOANS
  else got=REJECT; fi
  if [ "$got" = "$want" ]; then st=ok; ok=$((ok+1))
  elif [ "$got" = TIMEOUT ]; then st=SLOW; slow=$((slow+1))
  elif [ "$got" = NOANS ] || [ "$got" = REJECT ]; then st=$got; unk=$((unk+1))
  else st=WRONG; bad=$((bad+1)); fi
  printf '%-8s %-5s %8.3fs  %s\n' "$st" "$want" "$t" "$f"
done < "$FILE"
echo "ok $ok, wrong $bad, timeout(${LIM}s) $slow, no answer/rejected $unk"
[ $bad -eq 0 ]
