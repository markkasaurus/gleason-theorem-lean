#!/usr/bin/env bash

set -euo pipefail

repo_root="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

cd "$repo_root"

build_log="$tmpdir/build.log"
axioms_log="$tmpdir/axioms.log"
normalized_axioms_log="$tmpdir/normalized-axioms.log"
expected_axioms_log="$tmpdir/expected-axioms.log"

echo "[1/6] Building the repository"
lake build 2>&1 | tee "$build_log"
if grep -nE "warning:|error:" "$build_log" >/dev/null; then
  echo "Build output contains warnings or errors." >&2
  grep -nE "warning:|error:" "$build_log" >&2
  exit 1
fi

echo
echo "[2/6] Checking axiom dependencies"
lake env lean Verification/Axioms.lean 2>&1 | tee "$axioms_log"
if grep -n "sorryAx" "$axioms_log" >/dev/null; then
  echo "Unexpected sorryAx dependency found." >&2
  exit 1
fi
awk '
  /depends on axioms:/ {
    record = $0
    while (record !~ /]$/ && getline > 0) record = record " " $0
    gsub(/[[:space:]]+/, " ", record)
    print record
  }
' "$axioms_log" > "$normalized_axioms_log"
cat > "$expected_axioms_log" <<'EOF'
'ClassicalGleason.Separable.gleason_theorem_verified' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalGleason.Separable.gleason_theorem_separable' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalGleason.Separable.gleason_theorem_separable_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalGleason.Separable.gleason_theorem_separable_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalGleason.finite_gleason_statement_from_oscillation' depends on axioms: [propext, Classical.choice, Quot.sound]
EOF
if ! diff -u "$expected_axioms_log" "$normalized_axioms_log"; then
  echo "Unexpected axiom dependency found." >&2
  exit 1
fi

echo
echo "[3/6] Scanning for placeholders"
placeholder_pattern='(^|[^[:alnum:]_])(sorry|admit|sorryAx)([^[:alnum:]_]|$)'
if grep -RInE "$placeholder_pattern" --include="*.lean" \
    --exclude-dir=".lake" --exclude-dir=".git" . >/dev/null; then
  echo "Unexpected placeholder token found." >&2
  grep -RInE "$placeholder_pattern" --include="*.lean" \
    --exclude-dir=".lake" --exclude-dir=".git" . >&2
  exit 1
fi

echo
echo "[4/6] Scanning for declaration escape hatches"
escape_pattern='^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable)[[:space:]]+)*(axiom|postulate|unsafe|opaque|partial|extern)[[:space:]]|implemented_by'
if grep -RInE "$escape_pattern" \
    --include="*.lean" --exclude-dir=".lake" --exclude-dir=".git" . >/dev/null; then
  echo "Unexpected declaration form found." >&2
  grep -RInE "$escape_pattern" \
    --include="*.lean" --exclude-dir=".lake" --exclude-dir=".git" . >&2
  exit 1
fi

echo
echo "[5/6] Scanning for development artifacts"
if find . -path './.lake' -prune -o -path './.git' -prune -o -print |
    grep -Ei '(^|/)(_scratch|scratch|backup|archive|tmp|output)([._/-]|$)' >/dev/null; then
  echo "Provisional path found." >&2
  exit 1
fi
if grep -RInE "_scratch|GleasonCore\\.Part|^import [A-Z][0-9]$" \
    --include="*.lean" --exclude-dir=".lake" --exclude-dir=".git" . >/dev/null; then
  echo "Provisional source reference found." >&2
  exit 1
fi

echo
echo "[6/6] Checking the statement import boundary"
if grep -E '^import ' GleasonStatement.lean | grep -vE '^import Mathlib([.]|$)' >/dev/null; then
  echo "GleasonStatement.lean imports a non-Mathlib module." >&2
  exit 1
fi

echo
echo "Verification completed successfully."
