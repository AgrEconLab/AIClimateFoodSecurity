#!/usr/bin/env bash
# Independent verification for the AIClimateFoodSecurity project.
#
# Usage: ./verify.sh
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$ROOT/env.sh"
mkdir -p "$ROOT/logs"
LOG="$ROOT/logs/verify-$(date +%Y%m%d-%H%M%S).log"

fail() {
  echo "[verify] ERROR: $*" >&2
  exit 1
}

# The project manifest is seeded from the workspace Mathlib manifest. When the
# build cache is present, link it so the first build works offline.
if [ ! -e "$ROOT/.lake/packages" ] &&
   [ -d "$ROOT/../../mathlib4-master/.lake/packages" ]; then
  case "$(uname -s)" in
    MINGW*|MSYS*|CYGWIN*)
      powershell.exe -NoProfile -Command \
        "New-Item -ItemType Junction -Path '$(cygpath -w "$ROOT/.lake/packages")' -Target '$(cygpath -w "$ROOT/../../mathlib4-master/.lake/packages")' | Out-Null" \
        >/dev/null 2>&1 || true
      ;;
    *)
      ln -s "$ROOT/../../mathlib4-master/.lake/packages" "$ROOT/.lake/packages"
      ;;
  esac
fi

{
  echo "[verify] project: $ROOT"
  echo "[verify] log:     $LOG"

  lake build || fail "lake build failed"

  errors="$(grep -c 'error:' "$LOG" || true)"
  sorry="$(grep -Ec 'declaration uses .?sorry.?' "$LOG" || true)"
  warnings="$(grep -c 'warning:' "$LOG" || true)"
  echo "[verify] errors:   $errors"
  echo "[verify] sorry:    $sorry"
  echo "[verify] warnings: $warnings"
  [ "$errors" -eq 0 ] || fail "build log contains an error"
  [ "$sorry" -eq 0 ] || fail "build log contains sorry"

  "$ROOT/../../.claude/skills/econ-modeling/scripts/model-check.sh" \
    "$ROOT/Models/AIClimateFoodSecurity.lean" --axioms ||
    fail "model-check --axioms failed"

  echo "[verify] PASSED"
} 2>&1 | tee "$LOG"

rc=${PIPESTATUS[0]}
exit "$rc"
