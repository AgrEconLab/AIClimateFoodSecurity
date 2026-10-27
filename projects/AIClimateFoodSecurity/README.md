# AI, Extreme Climate, and Subsistence Income Risk

A finite-state theoretical model of AI-enabled risk-reducing technology adoption
under climate risk and its effects on subsistence income security (a
food-security proxy).

## Question

Does AI-enabled risk-reducing technology improve subsistence income security
when climate extremes create tail risk? The model separates:

- a productivity effect: technology raises mean yield;
- a risk-reduction effect: technology lowers climate sensitivity;
- an adoption-cost effect: cost can offset gains, especially for poor or
  liquidity-constrained farmers;
- a liquidity effect: feasible adoption requires `k(a) ≤ W`.

Food security is measured by the shortage probability and expected shortfall
relative to a net-income requirement. It is a **subsistence income risk proxy**,
not food affordability, nutrition, or distribution.

## Model

A liquidity-constrained representative farmer chooses adoption intensity
`a ∈ F(W) = {a ∈ [0,1] : k(a) ≤ W}`, then climate state `i` realizes. Yield and
net income are

```text
Y(a,i) = μ(a) - σ(a) * g(i)
N(a,i) = Y(a,i) - k(a)
a* ∈ argmax_{a ∈ F(W)} U(a).
```

The objective is the piecewise-linear subsistence utility

```text
U(a) = E[N] - λ * E[max(Nbar - N, 0)].
```

Voluntary adoption `a*` is the farmer's optimum. A separate expected-yield
benchmark chooses `aP ∈ argmax_{a ∈ F(W)} E[Y](a)`. The "higher yield, lower
objective" result is an objective-benchmark comparison, not a voluntary
equilibrium and not a credit-constraint result.

## Build and verify

Place `projects/AIClimateFoodSecurity/` in an EconLean workspace with the pinned
`mathlib4-master/` checkout next to `projects/`, then:

```bash
cd projects/AIClimateFoodSecurity
source env.sh
lake build
./verify.sh
```

The project has a seeded manifest and links the workspace Mathlib package cache,
so it builds offline. Do not run `lake update` while `.lake/packages` is linked.

## Write-up and verification

- Declaration inventory: `DECLARATIONS.md`
- Verification logs: `verification/`

## Main results

- AI raises yield in every climate state under monotone mean and climate
  sensitivity assumptions.
- If the discrete yield gain net of the climate-sensitivity change covers the
  cost increment in every state, net income rises and both shortage
  probability and expected shortfall fall.
- The food-security weight decomposes the objective change; with nondecreasing
  net income the objective is nondecreasing for every `λ ≥ 0`. No claim is made
  that `λ` changes the argmax.
- If net income at some adoption intensity (not necessarily the maximum) is
  below the food-security line in some state, expected shortfall is still
  positive.
- Under the liquidity constraint, a feasible optimal adoption `a*` exists and
  maximizes the objective (T7); higher liquid wealth weakly raises the optimal
  value (T8).
- Gross-output and net-income benchmarks are each weakly opposed to the farmer
  (T9): `E[Y](a*) ≤ E[Y](aP)`, `E[N](a*) ≤ E[N](aN)`, and `U(aP) ≤ U(a*)`,
  `U(aN) ≤ U(a*)`. This is a cross-optimality lemma; it follows from the two
  argmax definitions. A two-state parametric example proves the actual selected
  optima are strictly separated in both directions: the gross-output benchmark
  chooses `a=1` and over-adopts, the net-income benchmark chooses `a=2/3` and
  under-adopts (paper-level FOC), and the farmer's optimum differs from both.
  At the net-income benchmark (`a=2/3`): `E[Y]=8/9`, `U=41/300`, `E[N]=1/6`;
  at the gross-output benchmark (`a=1`): `E[Y]=3/2`, `U=-129/800`; the farmer's
  optimum is approximately `0.671`. This is an objective benchmark, not a
  voluntary equilibrium.
- T10 gives a single-crossing result: if `ES(b) < ES(a)`, a higher shortfall
  weight cannot reverse a preference for `b`. The implied price
  `(E[N](a)-E[N](b))/(ES(a)-ES(b))` is a diagnostic, not a primitive condition;
  the threshold equality is the objective identity rearranged. The risk-channel
  implied price is Lean-proved to be `6/7`, below its `λ=3`.
- T11 is a binding-liquidity variant of the risk example: `W=16/25=k(4/5)<k(1)`.
  The farmer is at the cap `4/5`, the net-income benchmark's `3/4` remains
  feasible, and the net-income/farmer separation survives; the gross-output
  benchmark coincides with the farmer. This is a verified example, not a
  general comparative static in `W`.
- A second two-state example makes the risk channel load-bearing: the
  net-income benchmark chooses `a=3/4`, the farmer `a=9/10`, and the gross-output
  benchmark `a=1`. The farmer sacrifices expected net income (`9/16` to `27/50`)
  to reduce expected shortfall (`13/160` to `11/200`); with `λ=3` the shortfall
  term (`63/800`) dominates the net-income loss (`9/400`).
- Scope note: A4 (AI lowers climate sensitivity), A8 (no insurance/trade), and
  A10 (representative farmer) are explicit benchmark assumptions, not empirical
  findings. The artifact does not claim real-world AI effects or a full
  food-security outcome.

## Layout

- `Models/AIClimateFoodSecurity.lean` — formal model and theorems.
- `Models.lean` — aggregator.
- `verification/` — model-check and axiom logs.
- `CITATION.cff` — citation metadata.
