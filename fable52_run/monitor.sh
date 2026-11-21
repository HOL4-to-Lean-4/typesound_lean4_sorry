#!/bin/bash
# Logs remaining sorry tokens per workspace every 10 min; snapshots and pushes hourly.
W=/home/claude/work; R=/home/claude/candle-hol4-lean4-study; D=$R/fable52_typesound_test
export GIT_AUTHOR_NAME=Lee-Juntong GIT_AUTHOR_EMAIL=2310266421@qq.com GIT_COMMITTER_NAME=Lee-Juntong GIT_COMMITTER_EMAIL=2310266421@qq.com
declare -A FILES=( [A]="Misc Mlstring NamespaceProps Evaluate EvaluateProps SemanticPrimitivesProps" [B]="TypeSysProps" [C]="Weakening" [D]="TypeSound" )
i=0
while true; do
  line="$(date -u +%Y-%m-%dT%H:%M:%SZ)"; total=0
  for a in A B C D; do
    n=0
    for f in ${FILES[$a]}; do
      c=$(python3 -c "
import sys,re
sys.path.insert(0,'$W/benchtools')
from count_translation_progress import strip_lean_comments
print(len(re.findall(r'\bsorry\b', strip_lean_comments(open('$W/ws$a/LeanTypeSound/$f.lean').read()))))" 2>/dev/null || echo 999)
      n=$((n+c))
    done
    line="$line\t$n"; total=$((total+n))
  done
  echo -e "$line\t$total" >> $W/progress.tsv
  cp $W/progress.tsv /mnt/project-files/fable52_typesound_test/sorry_tokens_over_time.tsv 2>/dev/null
  i=$((i+1)); sleep 600
done
