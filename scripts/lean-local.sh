#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$repo_root"
if [[ ! -x .local/lean ]]; then
  exec lake env lean "$@"
fi
project_lean_path="$repo_root/.lake/build/lib/lean"
for package_dir in .lake/packages/*; do
  if [[ -d "$package_dir/.lake/build/lib/lean" ]]; then
    project_lean_path="$project_lean_path:$repo_root/$package_dir/.lake/build/lib/lean"
  fi
done
export LEAN_PATH="$project_lean_path"
exec .local/lean "$@"
