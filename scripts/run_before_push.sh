#!/usr/bin/env bash
# Pre-push checks (static, no Lean): static gates, their tests, and a release
# scan for private paths in files changed relative to a base ref.
# Usage: scripts/run_before_push.sh [base-ref]
#   default base: origin/main, else main, else the branch's upstream, else HEAD.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
status=0

echo "== static gates"
python3 scripts/static_gates.py || status=1

echo "== static gate tests"
python3 -m unittest scripts/tests/test_static_gates.py || status=1

base=""
for cand in "${1:-}" origin/main main '@{upstream}' HEAD; do
  [ -n "$cand" ] || continue
  if git rev-parse --verify --quiet "$cand^{commit}" >/dev/null 2>&1; then base="$cand"; break; fi
done
if [ "$base" = "HEAD" ]; then
  echo "warning: no base ref found (origin/main, main, upstream); committed changes are not scanned"
fi
echo "== private-path scan of changed files (base: $base)"

# Private-path patterns (one place).  Lines carrying the marker
# `release-scan: allow` are exempt, but only in the files listed in
# marker_files (where the patterns themselves are documented).
private_re='/Users/|/home/[A-Za-z]|(^|[^A-Za-z0-9_])\.local/|/private/tmp|/private/var|/var/folders/'  # release-scan: allow
allow_marker='release-scan: allow'
marker_files='|scripts/run_before_push.sh|.github/pull_request_template.md|'

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
{
  git -c core.quotepath=off diff -z --name-only --diff-filter=ACMR "$base"...HEAD 2>/dev/null || true
  git -c core.quotepath=off diff -z --name-only --diff-filter=ACMR HEAD 2>/dev/null || true
  git -c core.quotepath=off ls-files -z --others --exclude-standard
} > "$tmp"

hits=0
seen=""
while IFS= read -r -d '' f; do
  [ -n "$f" ] || continue
  case "$seen" in *"|$f|"*) continue;; esac
  seen="$seen|$f|"
  case "$f" in .local/*|.claude/*) echo "private file would be committed: $f"; hits=1; continue;; esac  # release-scan: allow
  [ -f "$f" ] || continue
  [ "$f" = .gitignore ] && continue  # ignore rules legitimately name private paths
  matches="$(grep -nI -E "$private_re" -- "$f" 2>/dev/null || true)"
  case "$marker_files" in *"|$f|"*)
    matches="$(printf '%s\n' "$matches" | grep -v -F "$allow_marker" || true)";;
  esac
  if [ -n "$matches" ]; then
    printf '%s\n' "$matches" | sed -n '1,5p' | sed "s|^|$f:|"
    hits=1
  fi
done < "$tmp"
if [ "$hits" -ne 0 ]; then
  echo "FAIL: private paths found in changed files"
  status=1
else
  echo "ok: no private paths in changed files"
fi
exit "$status"
