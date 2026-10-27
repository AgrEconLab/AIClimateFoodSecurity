# AIClimateFoodSecurity — Lean formalization

Public Lean 4 formalization for the manuscript:

> **What Formalization and Internal Review Changed: A Case Study in
> Subsistence-Risk Adoption**
>
> Taotao Tu, College of Economics and Management and Laboratory for Intelligent
> Food Security Governance, Huazhong Agricultural University.

This repository contains **only the paper's Lean source, build configuration,
declaration inventory, and verification logs**. The numerical scripts, scenario
data, and curated case record are in the paper's supplementary package. The
repository is public and has no DOI; it does not claim one-click or independent
external reproducibility.

## Contents

| Path | What it is |
|---|---|
| `projects/AIClimateFoodSecurity/Models/AIClimateFoodSecurity.lean` | The paper's Lean 4 module: primitives, farmer problem, gross-output and net-income benchmarks, two two-state examples, binding-liquidity variant, single-crossing results. |
| `projects/AIClimateFoodSecurity/Models.lean` | Umbrella module. |
| `projects/AIClimateFoodSecurity/DECLARATIONS.md` | Source-order inventory of the 135 declarations (111 theorems/lemmas + 24 definitions). |
| `projects/AIClimateFoodSecurity/verification/` | `model-check.log` (0 errors, 0 `sorry`, PASSED), `axioms.log` (111 entries; standard axioms only), and a README. |
| `projects/AIClimateFoodSecurity/lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake package configuration. |
| `projects/AIClimateFoodSecurity/env.sh`, `verify.sh` | Local build and verification helpers. |
| `projects/AIClimateFoodSecurity/README.md`, `CITATION.cff` | Project overview and citation metadata. |
| `MATHLIB-PIN.md` | Lean/Mathlib pin and build context. |

## Lean build

The module targets **Lean 4.36.0-rc1** and imports the workspace Mathlib. The
`lakefile.toml` uses a path dependency:

```toml
[[require]]
name = "mathlib"
path = "../../mathlib4-master"
```

To rebuild, place `projects/AIClimateFoodSecurity/` in an EconLean workspace
with the pinned `mathlib4-master/` checkout next to `projects/`, then:

```bash
cd projects/AIClimateFoodSecurity
source env.sh
lake build
./verify.sh
```

The paper discloses that the build depends on a workspace-local Mathlib path;
an external reader cannot rebuild it from this repository alone without that
checkout.

## Verification

The recorded logs report:

- 0 errors, 0 `sorry`, 0 new axioms;
- every audited declaration depends only on `propext`, `Classical.choice`, and
  `Quot.sound`;
- source SHA-256:
  `f56f2797ad367b73337dfde70ccf552b42115bcbbcce67d9f1a5205ebf800453`.

## Scope

- `AIClimateFoodSecurity.lean` is the verified core.
- The numerical illustration is in the paper's supplementary package, not this
  repository.
- A4 (the technology lowers climate sensitivity), A8 (no insurance or trade),
  and A10 (a representative farmer) are explicit benchmark assumptions and
  scope limitations, not empirical findings.

## Citation and license

Citation metadata is in `projects/AIClimateFoodSecurity/CITATION.cff`. The code
is released under the Apache License 2.0; see `LICENSE`.

## Contact

Taotao Tu — `tutaotao_hust@126.com` — ORCID
[0000-0002-7328-0424](https://orcid.org/0000-0002-7328-0424).
