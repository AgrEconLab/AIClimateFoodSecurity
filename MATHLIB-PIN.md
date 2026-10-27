# Mathlib and toolchain pin

This repository is a **public** supplementary copy. It does not claim
independent reproducibility and has no DOI.

## Pinned versions

| Component | Pin |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.36.0-rc1` (see `projects/AIClimateFoodSecurity/lean-toolchain`) |
| Mathlib checkout | `f9894516e15785af295d7a14e4760b61e67a6d8e` (EconLean workspace `mathlib4-master`, clean worktree) |

The numerical illustration's QuantEcon.py 0.11.4 pin is in the paper's
supplementary package; this Lean-only repository does not include it. The
Mathlib checkout is the EconLean workspace version, which includes
MathEconLib integration commits; it is **not** a standard upstream Mathlib
clone. A reader cannot rebuild the Lean module from this repository alone
without that checkout.

## Build context

`projects/AIClimateFoodSecurity/lakefile.toml` uses a path dependency:

```toml
[[require]]
name = "mathlib"
path = "../../mathlib4-master"
```

`projects/AIClimateFoodSecurity/lake-manifest.json` is the workspace's
dependency snapshot. To rebuild, place the project inside an EconLean
workspace with the pinned `mathlib4-master/` next to `projects/`, then:

```bash
cd projects/AIClimateFoodSecurity
source env.sh
lake build
./verify.sh
```

## Verification identity

The Lean source covered by the paper's model-check and axiom logs has SHA-256:

```text
f56f2797ad367b73337dfde70ccf552b42115bcbbcce67d9f1a5205ebf800453
```

The logs are in `projects/AIClimateFoodSecurity/verification/`.

## What this pin does and does not establish

- It records the exact toolchain and Mathlib checkout used for the recorded
  verification run.
- It does **not** turn this public repository into a public reproducibility
  benchmark.
- It does **not** support a claim of one-click or independent external rebuild.
  The paper's Section 6 limitation remains accurate: the build depends on the
  workspace-local Mathlib path.
