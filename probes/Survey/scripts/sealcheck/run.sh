#!/bin/zsh
S=${SCRATCH:?set SCRATCH to your scratch dir}
cd "$(dirname "$0")/../../../.." || exit 1
OUT=$S/sealcheck/results.tsv
EXTRA=""
for f in "$@"; do
  if [ "$f" = "--arch" ]; then EXTRA="-i $S/sealcheck/arch"; continue; fi
  L=$S/sealcheck/log-$f.txt
  T0=$(date +%s)
  /usr/bin/time -l agda --library-file=$S/libraries -i src -i probes $(echo $EXTRA) probes/OCF/Align/$f.lagda.md +RTS -M12G -RTS > $L 2>&1
  E=$?
  T1=$(date +%s)
  RSS=$(grep 'maximum resident set size' $L | awk '{print $1}')
  ERR=$(grep -m1 -n -E 'error|Error|Heap exhausted' $L | head -c 200 | tr '\t\n' '  ')
  CHK=$(grep -c '^ *Checking' $L)
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$f" "$E" "$((T1-T0))" "$RSS" "$CHK" "$ERR" >> $OUT
done
echo done
