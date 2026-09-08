#!/usr/bin/env bash

set -uo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
status=0

while IFS= read -r -d '' source; do
  relative="${source#"$repo_root"/}"
  if (cd "$repo_root" && agda "$relative"); then
    printf 'PASS %s\n' "$relative"
  else
    printf 'FAIL %s\n' "$relative" >&2
    status=1
  fi
done < <(find "$repo_root/src" -type f \
  \( -name '*.agda' -o -name '*.lagda.md' \) -print0 | sort -z)

exit "$status"
