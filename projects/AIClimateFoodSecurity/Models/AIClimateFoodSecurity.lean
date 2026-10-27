/-
Copyright (c) 2026 The EconLean Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EconLean contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# AI, extreme climate, and food security

A finite-state representative-farmer model. AI adoption `a` raises mean yield
`μ(a)` and lowers climate sensitivity `σ(a)`. Climate state `i` has damage
`g i` and probability `p i`. Yield and net income are

`yield a i = μ a - σ a * g i`
`net a i = yield a i - k a`

Food security is measured by the shortage probability and expected shortfall
relative to a net-income requirement `Nbar`. The objective is the piecewise-
linear subsistence utility

`E[net] - λ * E[shortfall]`.

The file formalizes monotonicity, expected-shortfall, objective decomposition,
optimal adoption with a liquidity constraint, gross-output and net-income
planner benchmarks, and two two-state parametric examples (cost-channel
and risk-channel) with strict planner–farmer separation.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace AIClimateFoodSecurity

/-- A finite-state agricultural economy with AI adoption, climate damage, and
a food-security requirement. -/
structure Model (ι : Type*) [Fintype ι] where
  /-- Probability of each climate state. -/
  p : ι → ℝ
  /-- Climate-state probabilities are positive. -/
  p_pos : ∀ i, 0 < p i
  /-- Climate-state probabilities sum to one. -/
  p_sum : ∑ i, p i = 1
  /-- Mean yield as a function of AI adoption. -/
  μ : ℝ → ℝ
  /-- Climate sensitivity of yield. -/
  σ : ℝ → ℝ
  /-- Damage index of each climate state. -/
  g : ι → ℝ
  /-- AI adoption cost. -/
  k : ℝ → ℝ
  /-- Liquid wealth available to pay the AI adoption cost. -/
  W : ℝ
  /-- Liquid wealth is nonnegative. -/
  W_nonneg : 0 ≤ W
  /-- The adoption cost at zero is zero. -/
  k_zero : k 0 = 0
  /-- Mean yield is continuous. -/
  μ_cont : Continuous μ
  /-- Climate sensitivity is continuous. -/
  σ_cont : Continuous σ
  /-- The adoption cost is continuous. -/
  k_cont : Continuous k
  /-- Net-income food-security requirement. -/
  Nbar : ℝ
  /-- The food-security requirement is positive. -/
  Nbar_pos : 0 < Nbar
  /-- Social/utility weight on expected shortfall. -/
  lam : ℝ
  /-- The shortfall weight is nonnegative. -/
  lam_nonneg : 0 ≤ lam

namespace Model

variable {ι : Type*} [Fintype ι] (M : Model ι)

/-- Yield in climate state `i` under AI adoption `a`. -/
def yield (a : ℝ) (i : ι) : ℝ :=
  M.μ a - M.σ a * M.g i

/-- Net income: yield minus AI adoption cost. -/
def net (a : ℝ) (i : ι) : ℝ :=
  M.yield a i - M.k a

/-- Shortfall of net income relative to the food-security requirement. -/
def shortfall (a : ℝ) (i : ι) : ℝ :=
  max (M.Nbar - M.net a i) 0

/-- Climate states in which net income falls below the food-security line. -/
def shortageSet (a : ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => M.net a i < M.Nbar)

/-- Probability of a food-security shortfall. -/
def shortageProb (a : ℝ) : ℝ :=
  Finset.sum (M.shortageSet a) (fun i => M.p i)

/-- Expected shortfall. -/
def expectedShortfall (a : ℝ) : ℝ :=
  ∑ i, M.p i * M.shortfall a i

/-- Piecewise-linear subsistence objective `E[net] - λ E[shortfall]`. -/
def objective (a : ℝ) : ℝ :=
  ∑ i, M.p i * (M.net a i - M.lam * M.shortfall a i)

/-- Yield is continuous in adoption when `μ` and `σ` are continuous. -/
theorem continuous_yield (i : ι) : Continuous fun a => M.yield a i := by
  unfold yield
  exact M.μ_cont.sub (M.σ_cont.mul continuous_const)

/-- Net income is continuous in adoption. -/
theorem continuous_net (i : ι) : Continuous fun a => M.net a i := by
  unfold net
  exact (M.continuous_yield i).sub M.k_cont

/-- Shortfall is continuous in adoption. -/
theorem continuous_shortfall (i : ι) : Continuous fun a => M.shortfall a i := by
  unfold shortfall
  exact (continuous_const.sub (M.continuous_net i)).max continuous_const

/-- The objective is continuous in adoption. -/
theorem continuous_objective : Continuous M.objective := by
  unfold objective
  apply continuous_finsetSum Finset.univ
  intro i _
  exact continuous_const.mul
    ((M.continuous_net i).sub (continuous_const.mul (M.continuous_shortfall i)))

/-- Adoption intensities feasible under liquid wealth `W`: the unit interval
intersected with the liquidity constraint `k a ≤ W`. -/
def feasibleSetAt (W : ℝ) : Set ℝ :=
  Set.Icc 0 1 ∩ {a | M.k a ≤ W}

/-- Feasible adoption intensities at the farmer's liquid wealth. -/
def feasibleSet : Set ℝ := M.feasibleSetAt M.W

/-- The feasible set is compact when the adoption cost is continuous. -/
theorem isCompact_feasibleSetAt (W : ℝ) : IsCompact (M.feasibleSetAt W) := by
  unfold feasibleSetAt
  exact isCompact_Icc.inter_right (isClosed_le M.k_cont continuous_const)

/-- Zero adoption is feasible when wealth is nonnegative and `k 0 = 0`. -/
theorem feasibleSetAt_nonempty {W : ℝ} (hW : 0 ≤ W) :
    (M.feasibleSetAt W).Nonempty := by
  refine ⟨0, ?_⟩
  simp [feasibleSetAt, M.k_zero, hW]

/-- The feasible set at the farmer's wealth is nonempty. -/
theorem feasibleSet_nonempty : M.feasibleSet.Nonempty :=
  M.feasibleSetAt_nonempty M.W_nonneg

/-- A larger liquid wealth weakly expands the feasible set. -/
theorem feasibleSetAt_mono {W₁ W₂ : ℝ} (h : W₁ ≤ W₂) :
    M.feasibleSetAt W₁ ⊆ M.feasibleSetAt W₂ := by
  rintro a ⟨haI, hak⟩
  rcases haI with ⟨ha0, ha1⟩
  exact ⟨⟨ha0, ha1⟩, le_trans hak h⟩

/-- A continuous objective attains a maximum on the compact feasible set. -/
theorem exists_optimalAt (W : ℝ) (hW : 0 ≤ W) :
    ∃ a ∈ M.feasibleSetAt W,
      ∀ b ∈ M.feasibleSetAt W, M.objective b ≤ M.objective a := by
  exact (isCompact_feasibleSetAt M W).exists_isMaxOn
    (M.feasibleSetAt_nonempty hW) M.continuous_objective.continuousOn

/-- The farmer's problem has an optimal adoption intensity. -/
theorem exists_optimal :
    ∃ a ∈ M.feasibleSet,
      ∀ b ∈ M.feasibleSet, M.objective b ≤ M.objective a :=
  M.exists_optimalAt M.W M.W_nonneg

/-- A selected optimal adoption intensity at wealth `W`. -/
noncomputable def optimalAdoptionAt (W : ℝ) (hW : 0 ≤ W) : ℝ :=
  Classical.choose (M.exists_optimalAt W hW)

/-- The selected optimum is feasible. -/
theorem optimalAdoptionAt_mem (W : ℝ) (hW : 0 ≤ W) :
    M.optimalAdoptionAt W hW ∈ M.feasibleSetAt W :=
  (Classical.choose_spec (M.exists_optimalAt W hW)).1

/-- The selected optimum maximizes the objective on the feasible set. -/
theorem optimalAdoptionAt_max (W : ℝ) (hW : 0 ≤ W) {b : ℝ}
    (hb : b ∈ M.feasibleSetAt W) :
    M.objective b ≤ M.objective (M.optimalAdoptionAt W hW) :=
  (Classical.choose_spec (M.exists_optimalAt W hW)).2 b hb

/-- The farmer's selected optimal adoption intensity. -/
noncomputable def optimalAdoption : ℝ :=
  M.optimalAdoptionAt M.W M.W_nonneg

/-- The farmer's selected optimum is feasible. -/
theorem optimalAdoption_mem : M.optimalAdoption ∈ M.feasibleSet :=
  M.optimalAdoptionAt_mem M.W M.W_nonneg

/-- The farmer's selected optimum maximizes the objective. -/
theorem optimalAdoption_max {b : ℝ} (hb : b ∈ M.feasibleSet) :
    M.objective b ≤ M.objective M.optimalAdoption :=
  M.optimalAdoptionAt_max M.W M.W_nonneg hb

/-- The optimal value at the farmer's wealth. -/
noncomputable def optimalValue : ℝ :=
  M.objective M.optimalAdoption

/-- Higher liquid wealth weakly raises the optimal value: the feasible set
expands, so the farmer cannot be worse off. -/
theorem optimalValueAt_mono {W₁ W₂ : ℝ} (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂)
    (h : W₁ ≤ W₂) :
    M.objective (M.optimalAdoptionAt W₁ hW₁) ≤
      M.objective (M.optimalAdoptionAt W₂ hW₂) := by
  have hmem : M.optimalAdoptionAt W₁ hW₁ ∈ M.feasibleSetAt W₂ :=
    M.feasibleSetAt_mono h (M.optimalAdoptionAt_mem W₁ hW₁)
  exact M.optimalAdoptionAt_max W₂ hW₂ hmem

/-! ### Planner benchmark: expected-yield maximization -/

/-- Expected yield under adoption `a`: `E[Y](a) = ∑ i, p i * yield a i`. -/
def expectedYield (a : ℝ) : ℝ :=
  ∑ i, M.p i * M.yield a i

/-- Expected yield is continuous in adoption. -/
theorem continuous_expectedYield : Continuous M.expectedYield := by
  unfold expectedYield
  exact continuous_finsetSum Finset.univ fun i _ =>
    continuous_const.mul (M.continuous_yield i)

/-- Expected yield decomposes into mean yield minus climate sensitivity times
expected damage: `E[Y](a) = μ(a) - σ(a) * ∑ i, p i * g i`. -/
theorem expectedYield_eq (a : ℝ) :
    M.expectedYield a = M.μ a - M.σ a * ∑ i, M.p i * M.g i := by
  unfold expectedYield yield
  have h : ∀ i, M.p i * (M.μ a - M.σ a * M.g i)
      = M.p i * M.μ a - M.p i * (M.σ a * M.g i) := fun i => by ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, M.p_sum, one_mul,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Under monotone mean yield and nonincreasing climate sensitivity, expected
yield is nondecreasing in adoption. Hence, when the feasible set is an interval,
the planner chooses the largest feasible adoption intensity. -/
theorem expectedYield_mono (hμ : Monotone M.μ) (hσ : Antitone M.σ)
    (hg : 0 ≤ ∑ i, M.p i * M.g i) {a a' : ℝ} (ha : a ≤ a') :
    M.expectedYield a ≤ M.expectedYield a' := by
  rw [M.expectedYield_eq, M.expectedYield_eq]
  have hmu : M.μ a ≤ M.μ a' := hμ ha
  have hsig : M.σ a' ≤ M.σ a := hσ ha
  have hmul : M.σ a' * (∑ i, M.p i * M.g i) ≤
      M.σ a * (∑ i, M.p i * M.g i) :=
    mul_le_mul_of_nonneg_right hsig hg
  linarith

/-- The planner's expected-yield problem has a solution at wealth `W`. -/
theorem exists_plannerOptimalAt (W : ℝ) (hW : 0 ≤ W) :
    ∃ a ∈ M.feasibleSetAt W,
      ∀ b ∈ M.feasibleSetAt W, M.expectedYield b ≤ M.expectedYield a :=
  (isCompact_feasibleSetAt M W).exists_isMaxOn
    (M.feasibleSetAt_nonempty hW) M.continuous_expectedYield.continuousOn

/-- A selected expected-yield-maximizing adoption intensity at wealth `W`. -/
noncomputable def plannerAdoptionAt (W : ℝ) (hW : 0 ≤ W) : ℝ :=
  Classical.choose (M.exists_plannerOptimalAt W hW)

/-- The planner's selected optimum is feasible. -/
theorem plannerAdoptionAt_mem (W : ℝ) (hW : 0 ≤ W) :
    M.plannerAdoptionAt W hW ∈ M.feasibleSetAt W :=
  (Classical.choose_spec (M.exists_plannerOptimalAt W hW)).1

/-- The planner's selected optimum maximizes expected yield. -/
theorem plannerAdoptionAt_max (W : ℝ) (hW : 0 ≤ W) {b : ℝ}
    (hb : b ∈ M.feasibleSetAt W) :
    M.expectedYield b ≤ M.expectedYield (M.plannerAdoptionAt W hW) :=
  (Classical.choose_spec (M.exists_plannerOptimalAt W hW)).2 b hb

/-- The planner's selected adoption intensity at the farmer's wealth. -/
noncomputable def plannerAdoption : ℝ :=
  M.plannerAdoptionAt M.W M.W_nonneg

/-- The planner's selected optimum is feasible. -/
theorem plannerAdoption_mem : M.plannerAdoption ∈ M.feasibleSet :=
  M.plannerAdoptionAt_mem M.W M.W_nonneg

/-- The planner's selected optimum maximizes expected yield. -/
theorem plannerAdoption_max {b : ℝ} (hb : b ∈ M.feasibleSet) :
    M.expectedYield b ≤ M.expectedYield M.plannerAdoption :=
  M.plannerAdoptionAt_max M.W M.W_nonneg hb

/-- The planner's value: maximal expected yield. -/
noncomputable def plannerValue : ℝ := M.expectedYield M.plannerAdoption

/-- Planner and farmer choices are weakly opposed. The planner's choice yields
at least as much expected yield, and the farmer's choice yields at least as much
subsistence welfare. Both rankings are derived from the corresponding
optimality property, not assumed. -/
theorem planner_farmer_weak_separation :
    M.expectedYield M.optimalAdoption ≤ M.expectedYield M.plannerAdoption ∧
      M.objective M.plannerAdoption ≤ M.objective M.optimalAdoption :=
  ⟨M.plannerAdoption_max M.optimalAdoption_mem,
    M.optimalAdoption_max M.plannerAdoption_mem⟩

/-- The farmer's welfare loss from implementing the planner's choice. -/
noncomputable def plannerWelfareLoss : ℝ :=
  M.objective M.optimalAdoption - M.objective M.plannerAdoption

/-- The farmer is never better off under the planner's choice. -/
theorem plannerWelfareLoss_nonneg : 0 ≤ M.plannerWelfareLoss :=
  sub_nonneg.mpr M.planner_farmer_weak_separation.2

/-- Strict planner–farmer separation. If the farmer's optimum is not
expected-yield-maximal and the planner's optimum is not welfare-maximal, then
the planner's choice strictly raises expected yield and strictly lowers the
farmer's objective. -/
theorem planner_farmer_strict_separation
    (hy : ∃ b ∈ M.feasibleSet,
      M.expectedYield M.optimalAdoption < M.expectedYield b)
    (hw : ∃ b ∈ M.feasibleSet,
      M.objective M.plannerAdoption < M.objective b) :
    M.expectedYield M.optimalAdoption < M.expectedYield M.plannerAdoption ∧
      M.objective M.plannerAdoption < M.objective M.optimalAdoption := by
  constructor
  · obtain ⟨b, hb, hbY⟩ := hy
    exact lt_of_lt_of_le hbY (M.plannerAdoption_max hb)
  · obtain ⟨b, hb, hbU⟩ := hw
    exact lt_of_lt_of_le hbU (M.optimalAdoption_max hb)

/-! ### Net-income planner benchmark -/

/-- Expected net income under adoption `a`. -/
def expectedNet (a : ℝ) : ℝ :=
  ∑ i, M.p i * M.net a i

/-- Expected net income is expected yield minus the adoption cost. -/
theorem expectedNet_eq (a : ℝ) :
    M.expectedNet a = M.expectedYield a - M.k a := by
  unfold expectedNet expectedYield net
  have h : ∀ i, M.p i * (M.yield a i - M.k a)
      = M.p i * M.yield a i - M.p i * M.k a := fun i => by ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, M.p_sum, one_mul]

/-- The subsistence objective is expected net income minus the shortfall
weight times expected shortfall. -/
theorem objective_eq_expectedNet_sub (a : ℝ) :
    M.objective a = M.expectedNet a - M.lam * M.expectedShortfall a := by
  unfold objective expectedNet expectedShortfall
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The objective as a function of the shortfall weight, holding the model's
other primitives fixed. -/
def objectiveWith (lam : ℝ) (a : ℝ) : ℝ :=
  M.expectedNet a - lam * M.expectedShortfall a

/-- At the model's own shortfall weight, `objectiveWith` is the objective. -/
theorem objectiveWith_lam (a : ℝ) :
    M.objectiveWith M.lam a = M.objective a := by
  rw [objectiveWith, objective_eq_expectedNet_sub]

/-- Single crossing in the shortfall weight: if `b` has strictly lower expected
shortfall than `a`, and the farmer weakly prefers `b` at `λ`, then the farmer
weakly prefers `b` at every `λ' ≥ λ`. Equivalently, a higher shortfall weight
cannot reverse a preference for the lower-shortfall action. -/
theorem farmer_preference_single_crossing
    {a b : ℝ} (hES : M.expectedShortfall b < M.expectedShortfall a)
    {lam lam' : ℝ} (hlam : lam ≤ lam')
    (hpref : M.objectiveWith lam a ≤ M.objectiveWith lam b) :
    M.objectiveWith lam' a ≤ M.objectiveWith lam' b := by
  unfold objectiveWith at hpref ⊢
  have hnonneg : 0 ≤ (lam' - lam) *
      (M.expectedShortfall a - M.expectedShortfall b) :=
    mul_nonneg (sub_nonneg.mpr hlam) (sub_nonneg.mpr (le_of_lt hES))
  nlinarith

/-- Expected net income is continuous in adoption. -/
theorem continuous_expectedNet : Continuous M.expectedNet := by
  unfold expectedNet
  exact continuous_finsetSum Finset.univ fun i _ =>
    continuous_const.mul (M.continuous_net i)

/-- The net-income planner's problem has a solution at wealth `W`. -/
theorem exists_netPlannerOptimalAt (W : ℝ) (hW : 0 ≤ W) :
    ∃ a ∈ M.feasibleSetAt W,
      ∀ b ∈ M.feasibleSetAt W, M.expectedNet b ≤ M.expectedNet a :=
  (isCompact_feasibleSetAt M W).exists_isMaxOn
    (M.feasibleSetAt_nonempty hW) M.continuous_expectedNet.continuousOn

/-- A selected expected-net-income-maximizing adoption intensity at wealth `W`. -/
noncomputable def netPlannerAdoptionAt (W : ℝ) (hW : 0 ≤ W) : ℝ :=
  Classical.choose (M.exists_netPlannerOptimalAt W hW)

/-- The net-income planner's selected optimum is feasible. -/
theorem netPlannerAdoptionAt_mem (W : ℝ) (hW : 0 ≤ W) :
    M.netPlannerAdoptionAt W hW ∈ M.feasibleSetAt W :=
  (Classical.choose_spec (M.exists_netPlannerOptimalAt W hW)).1

/-- The net-income planner's selected optimum maximizes expected net income. -/
theorem netPlannerAdoptionAt_max (W : ℝ) (hW : 0 ≤ W) {b : ℝ}
    (hb : b ∈ M.feasibleSetAt W) :
    M.expectedNet b ≤ M.expectedNet (M.netPlannerAdoptionAt W hW) :=
  (Classical.choose_spec (M.exists_netPlannerOptimalAt W hW)).2 b hb

/-- The net-income planner's selected adoption intensity. -/
noncomputable def netPlannerAdoption : ℝ :=
  M.netPlannerAdoptionAt M.W M.W_nonneg

/-- The net-income planner's selected optimum is feasible. -/
theorem netPlannerAdoption_mem : M.netPlannerAdoption ∈ M.feasibleSet :=
  M.netPlannerAdoptionAt_mem M.W M.W_nonneg

/-- The net-income planner's selected optimum maximizes expected net income. -/
theorem netPlannerAdoption_max {b : ℝ} (hb : b ∈ M.feasibleSet) :
    M.expectedNet b ≤ M.expectedNet M.netPlannerAdoption :=
  M.netPlannerAdoptionAt_max M.W M.W_nonneg hb

/-- The net-income planner and the farmer are weakly opposed: the planner's
choice gives weakly higher expected net income, and the farmer's choice gives
weakly higher subsistence welfare. -/
theorem netPlanner_farmer_weak_separation :
    M.expectedNet M.optimalAdoption ≤ M.expectedNet M.netPlannerAdoption ∧
      M.objective M.netPlannerAdoption ≤ M.objective M.optimalAdoption :=
  ⟨M.netPlannerAdoption_max M.optimalAdoption_mem,
    M.optimalAdoption_max M.netPlannerAdoption_mem⟩

/-! ### Risk–return threshold for strict separation

The weak separation above is a cross-optimality property. The next two lemmas
give a genuine economic sufficient condition: if a feasible action `b` has
lower expected net income and lower expected shortfall than an action `a`, the
farmer prefers `b` exactly when the shortfall weight exceeds the ratio of the
expected-net-income loss to the expected-shortfall reduction. Applying this to
the net-income planner's choice yields a checkable condition for strict
planner–farmer separation that does not assume the conclusion. -/

/-- Pairwise risk–return decomposition. The farmer ranks `b` above `a` exactly
when the expected-net-income loss from `a` to `b` is smaller than the shortfall
weight times the expected-shortfall reduction. -/
theorem farmer_prefers_low_shortfall_iff
    {a b : ℝ} :
    M.objective a < M.objective b ↔
      M.expectedNet a - M.expectedNet b <
        M.lam * (M.expectedShortfall a - M.expectedShortfall b) := by
  rw [M.objective_eq_expectedNet_sub, M.objective_eq_expectedNet_sub]
  constructor <;> intro h <;> linarith

/-- The same threshold expressed as a ratio. The denominator is positive when
`b` strictly lowers expected shortfall. In the empirically relevant case where
`b` also lowers expected net income, the ratio is the net-income cost per unit
of shortfall reduction. -/
theorem farmer_prefers_low_shortfall_iff_threshold
    {a b : ℝ}
    (hD : M.expectedShortfall b < M.expectedShortfall a) :
    M.objective a < M.objective b ↔
      (M.expectedNet a - M.expectedNet b) /
        (M.expectedShortfall a - M.expectedShortfall b) < M.lam := by
  rw [M.farmer_prefers_low_shortfall_iff]
  have hden : 0 < M.expectedShortfall a - M.expectedShortfall b :=
    sub_pos.mpr hD
  rw [div_lt_iff₀ hden]

/-- A risk–return sufficient condition for strict net-planner/farmer
separation. If a feasible `b` has lower expected shortfall than the net-income
planner's choice, and the shortfall weight exceeds the ratio of the net-income
difference to the shortfall reduction, then the farmer strictly prefers `b`,
so the net-income planner's choice is strictly worse than the farmer's selected
optimum. The ratio is positive when `b` also has lower expected net income. -/
theorem netPlanner_strict_farmer_separation_of_threshold
    {b : ℝ} (hb : b ∈ M.feasibleSet)
    (hD : M.expectedShortfall b < M.expectedShortfall M.netPlannerAdoption)
    (hlam : (M.expectedNet M.netPlannerAdoption - M.expectedNet b) /
        (M.expectedShortfall M.netPlannerAdoption -
          M.expectedShortfall b) < M.lam) :
    M.objective M.netPlannerAdoption < M.objective M.optimalAdoption := by
  have hpref : M.objective M.netPlannerAdoption < M.objective b :=
    (M.farmer_prefers_low_shortfall_iff_threshold hD).2 hlam
  exact lt_of_lt_of_le hpref (M.optimalAdoption_max hb)

/-! ### Parametric example: strict planner–farmer conflict

Two equally likely climate states with damage `g 0 = 0` and `g 1 = 2`. Mean
yield is `3a - a²`, climate sensitivity is `1 - a/2`, the adoption cost is
`(13/8)a²`, the food-security line is `1/10`, and the shortfall weight is
`1/10`. Expected yield is `(7/2)a - a² - 1`, so it is increasing on `[0,1]` and
the planner chooses `a = 1`. At `a = 2/3` and `a = 1` the two criteria rank the
points oppositely: expected yield rises from `8/9` to `3/2`, while the farmer's
objective falls from `41/300` to `-129/800`. The net-income planner chooses
`a = 2/3`, where expected net income is `1/6` and the farmer's objective is
`41/300`. -/

/-- The two-state parametric example used in the paper. -/
noncomputable def exampleModel : Model (Fin 2) where
  p _ := 1 / 2
  p_pos _ := by norm_num
  p_sum := by
    norm_num [Fin.sum_univ_two]
  μ a := 3 * a - a ^ 2
  σ a := 1 - (1 / 2) * a
  g i := 2 * (i : ℕ)
  k a := (13 / 8) * a ^ 2
  W := 2
  W_nonneg := by norm_num
  k_zero := by norm_num
  μ_cont := (continuous_const.mul continuous_id).sub (continuous_id.pow 2)
  σ_cont := continuous_const.sub (continuous_const.mul continuous_id)
  k_cont := continuous_const.mul (continuous_id.pow 2)
  Nbar := 1 / 10
  Nbar_pos := by norm_num
  lam := 1 / 10
  lam_nonneg := by norm_num

/-- `a = 1` is feasible in the example: `k 1 = 13/8 ≤ 2 = W`. -/
theorem example_feasible_one : (1 : ℝ) ∈ exampleModel.feasibleSet := by
  simp only [Model.feasibleSet, Model.feasibleSetAt, Set.mem_inter_iff,
    Set.mem_Icc, Set.mem_ofPred_eq, exampleModel]
  norm_num

/-- `a = 2/3` is feasible in the example: `k (2/3) = 13/18 ≤ 2`. -/
theorem example_feasible_two_thirds :
    (2 / 3 : ℝ) ∈ exampleModel.feasibleSet := by
  simp only [Model.feasibleSet, Model.feasibleSetAt, Set.mem_inter_iff,
    Set.mem_Icc, Set.mem_ofPred_eq, exampleModel]
  norm_num

/-- Expected yield at `a = 2/3` is `8/9`. -/
theorem example_expectedYield_two_thirds :
    exampleModel.expectedYield (2 / 3) = 8 / 9 := by
  simp only [Model.expectedYield, Model.yield, exampleModel, Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one]
  norm_num

/-- Expected yield at `a = 1` is `3/2`. -/
theorem example_expectedYield_one :
    exampleModel.expectedYield 1 = 3 / 2 := by
  simp only [Model.expectedYield, Model.yield, exampleModel, Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one]
  norm_num

/-- The farmer's objective at `a = 2/3` is `41/300`. -/
theorem example_objective_two_thirds :
    exampleModel.objective (2 / 3) = 41 / 300 := by
  simp only [Model.objective, Model.net, Model.yield, Model.shortfall,
    exampleModel, Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  norm_num

/-- The farmer's objective at `a = 1` is `-129/800`. -/
theorem example_objective_one :
    exampleModel.objective 1 = -129 / 800 := by
  simp only [Model.objective, Model.net, Model.yield, Model.shortfall,
    exampleModel, Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  norm_num

/-- `a = 67/100` is feasible in the example. -/
theorem example_feasible_67 :
    (67 / 100 : ℝ) ∈ exampleModel.feasibleSet := by
  simp only [Model.feasibleSet, Model.feasibleSetAt, Set.mem_inter_iff,
    Set.mem_Icc, Set.mem_ofPred_eq, exampleModel]
  norm_num

/-- The farmer's objective is strictly higher at `a = 67/100` than at
`a = 2/3`; the latter is therefore not a farmer optimum. -/
theorem example_objective_two_thirds_lt_67 :
    exampleModel.objective (2 / 3) < exampleModel.objective (67 / 100) := by
  simp only [Model.objective, Model.net, Model.yield, Model.shortfall,
    exampleModel, Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  norm_num

/-- In the parametric example, moving from `a = 2/3` to `a = 1` raises expected
yield while lowering the farmer's objective. This witnesses that the strict
planner–farmer conflict is non-vacuous. -/
theorem example_conflict :
    exampleModel.expectedYield (2 / 3) < exampleModel.expectedYield 1 ∧
      exampleModel.objective 1 < exampleModel.objective (2 / 3) := by
  rw [example_expectedYield_two_thirds, example_expectedYield_one,
    example_objective_one, example_objective_two_thirds]
  norm_num

/-- Expected yield in the example has the closed form `(7/2)a - a² - 1`. -/
theorem example_expectedYield_eq (a : ℝ) :
    exampleModel.expectedYield a = 7 / 2 * a - a ^ 2 - 1 := by
  simp only [Model.expectedYield, Model.yield, exampleModel, Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one]
  ring

/-- Expected net income at `a = 2/3` is `1/6`. -/
theorem example_expectedNet_two_thirds :
    exampleModel.expectedNet (2 / 3) = 1 / 6 := by
  rw [Model.expectedNet_eq, example_expectedYield_two_thirds]
  simp [exampleModel]
  norm_num

/-- Expected net income at `a = 1` is `-1/8`. -/
theorem example_expectedNet_one :
    exampleModel.expectedNet 1 = -1 / 8 := by
  rw [Model.expectedNet_eq, example_expectedYield_one]
  simp [exampleModel]
  norm_num

/-- Expected net income in the example has the closed form
`(7/2)a - (21/8)a² - 1`. -/
theorem example_expectedNet_eq (a : ℝ) :
    exampleModel.expectedNet a = 7 / 2 * a - 21 / 8 * a ^ 2 - 1 := by
  rw [Model.expectedNet_eq, example_expectedYield_eq]
  simp [exampleModel]
  ring

/-- Expected net income is maximized at `a = 2/3` on the feasible interval. -/
theorem example_expectedNet_le_two_thirds {a : ℝ} (_ha0 : 0 ≤ a) (_ha1 : a ≤ 1) :
    exampleModel.expectedNet a ≤ exampleModel.expectedNet (2 / 3) := by
  rw [example_expectedNet_eq, example_expectedNet_two_thirds]
  nlinarith [sq_nonneg (a - 2 / 3)]

/-- Expected net income is strictly increasing up to `a = 2/3` and strictly
decreasing after it; `a = 2/3` is the unique maximizer. -/
theorem example_expectedNet_lt_two_thirds {a : ℝ} (_ha0 : 0 ≤ a) (_ha1 : a ≤ 1)
    (hne : a ≠ 2 / 3) :
    exampleModel.expectedNet a < exampleModel.expectedNet (2 / 3) := by
  rw [example_expectedNet_eq, example_expectedNet_two_thirds]
  have h : 0 < (a - 2 / 3) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  nlinarith

/-- The net-income planner's selected adoption intensity is `a = 2/3`. -/
theorem example_netPlannerAdoption_eq_two_thirds :
    exampleModel.netPlannerAdoption = 2 / 3 := by
  have hmem := exampleModel.netPlannerAdoption_mem
  have hge0 : 0 ≤ exampleModel.netPlannerAdoption := hmem.1.1
  have hle1 : exampleModel.netPlannerAdoption ≤ 1 := hmem.1.2
  have hmax : exampleModel.expectedNet (2 / 3) ≤
      exampleModel.expectedNet exampleModel.netPlannerAdoption :=
    exampleModel.netPlannerAdoption_max example_feasible_two_thirds
  have hle : exampleModel.expectedNet exampleModel.netPlannerAdoption ≤
      exampleModel.expectedNet (2 / 3) :=
    example_expectedNet_le_two_thirds hge0 hle1
  have heq : exampleModel.expectedNet exampleModel.netPlannerAdoption =
      exampleModel.expectedNet (2 / 3) := le_antisymm hle hmax
  by_contra hne
  have hstrict := example_expectedNet_lt_two_thirds hge0 hle1 hne
  linarith

/-- Expected yield is nondecreasing on the feasible interval and maximal at
`a = 1`. -/
theorem example_expectedYield_le_one {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    exampleModel.expectedYield a ≤ exampleModel.expectedYield 1 := by
  rw [example_expectedYield_eq, example_expectedYield_one]
  nlinarith [mul_nonneg (sub_nonneg.mpr ha1)
    (sub_nonneg.mpr (by linarith : a ≤ 5 / 2))]

/-- Expected yield is strictly increasing on `[0,1)`, so `a = 1` is the unique
maximizer. -/
theorem example_expectedYield_lt_one {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a < 1) :
    exampleModel.expectedYield a < exampleModel.expectedYield 1 := by
  rw [example_expectedYield_eq, example_expectedYield_one]
  have h : 0 < (1 - a) * (5 / 2 - a) :=
    mul_pos (sub_pos.mpr ha1) (by linarith)
  nlinarith

/-- The planner's selected adoption intensity in the example is `a = 1`. -/
theorem example_plannerAdoption_eq_one : exampleModel.plannerAdoption = 1 := by
  have hmem := exampleModel.plannerAdoption_mem
  have hge0 : 0 ≤ exampleModel.plannerAdoption := hmem.1.1
  have hle1 : exampleModel.plannerAdoption ≤ 1 := hmem.1.2
  have hmax : exampleModel.expectedYield (1 : ℝ) ≤
      exampleModel.expectedYield exampleModel.plannerAdoption :=
    exampleModel.plannerAdoption_max example_feasible_one
  have hle : exampleModel.expectedYield exampleModel.plannerAdoption ≤
      exampleModel.expectedYield 1 :=
    example_expectedYield_le_one hge0 hle1
  have heq : exampleModel.expectedYield exampleModel.plannerAdoption =
      exampleModel.expectedYield 1 := le_antisymm hle hmax
  by_contra hne
  have hlt : exampleModel.plannerAdoption < 1 := lt_of_le_of_ne hle1 hne
  have hstrict := example_expectedYield_lt_one hge0 hlt
  linarith

/-- The farmer's selected adoption intensity in the example is not `a = 1`:
`a = 2/3` already gives a strictly higher objective. -/
theorem example_optimalAdoption_ne_one : exampleModel.optimalAdoption ≠ 1 := by
  intro h
  have h2 := exampleModel.optimalAdoption_max example_feasible_two_thirds
  rw [h] at h2
  have hlt : exampleModel.objective 1 < exampleModel.objective (2 / 3) :=
    example_conflict.2
  linarith

/-- The actual selected planner and farmer optima in the example are strictly
separated: the planner chooses `a = 1`, the farmer does not, expected yield is
strictly higher under the planner, and the farmer's objective is strictly
higher under the farmer's choice. -/
theorem example_strict_planner_farmer_separation :
    exampleModel.expectedYield exampleModel.optimalAdoption <
        exampleModel.expectedYield exampleModel.plannerAdoption ∧
      exampleModel.objective exampleModel.plannerAdoption <
        exampleModel.objective exampleModel.optimalAdoption := by
  constructor
  · rw [example_plannerAdoption_eq_one]
    have hmem := exampleModel.optimalAdoption_mem
    have hge0 : 0 ≤ exampleModel.optimalAdoption := hmem.1.1
    have hle1 : exampleModel.optimalAdoption ≤ 1 := hmem.1.2
    have hlt : exampleModel.optimalAdoption < 1 :=
      lt_of_le_of_ne hle1 example_optimalAdoption_ne_one
    exact example_expectedYield_lt_one hge0 hlt
  · rw [example_plannerAdoption_eq_one]
    exact lt_of_lt_of_le example_conflict.2
      (exampleModel.optimalAdoption_max example_feasible_two_thirds)

/-- The farmer's selected optimum is not `a = 2/3`: `a = 67/100` gives a
strictly higher objective. -/
theorem example_optimalAdoption_ne_two_thirds :
    exampleModel.optimalAdoption ≠ 2 / 3 := by
  intro h
  have h2 := exampleModel.optimalAdoption_max example_feasible_67
  rw [h] at h2
  have hlt := example_objective_two_thirds_lt_67
  linarith

/-- The actual net-income planner and farmer optima in the example are strictly
separated: the planner chooses `a = 2/3`, the farmer does not, expected net
income is strictly higher under the planner, and the farmer's objective is
strictly higher under the farmer's choice. -/
theorem example_netPlanner_strict_farmer_separation :
    exampleModel.expectedNet exampleModel.optimalAdoption <
        exampleModel.expectedNet exampleModel.netPlannerAdoption ∧
      exampleModel.objective exampleModel.netPlannerAdoption <
        exampleModel.objective exampleModel.optimalAdoption := by
  constructor
  · rw [example_netPlannerAdoption_eq_two_thirds]
    have hmem := exampleModel.optimalAdoption_mem
    have hge0 : 0 ≤ exampleModel.optimalAdoption := hmem.1.1
    have hle1 : exampleModel.optimalAdoption ≤ 1 := hmem.1.2
    exact example_expectedNet_lt_two_thirds hge0 hle1
      example_optimalAdoption_ne_two_thirds
  · rw [example_netPlannerAdoption_eq_two_thirds]
    exact lt_of_lt_of_le example_objective_two_thirds_lt_67
      (exampleModel.optimalAdoption_max example_feasible_67)

/-! ### Second parametric example: the subsistence-risk channel is load-bearing

Two equally likely states with damage `g 0 = 0` and `g 1 = 2`. Mean yield is
`1 + a`, climate sensitivity is `1 - a/2`, the adoption cost is `a²`, the
food-security line is `1/10`, and the shortfall weight is `3`. The net-income
planner chooses `a = 3/4`, the gross-output planner chooses `a = 1`, and the
farmer chooses `a = 9/10`. The farmer sacrifices expected net income relative to
the net-income planner to reduce expected shortfall; the shortfall term is the
load-bearing part of the comparison. -/

/-- The risk-channel two-state example. -/
noncomputable def riskExampleModel : Model (Fin 2) where
  p _ := 1 / 2
  p_pos _ := by norm_num
  p_sum := by
    norm_num [Fin.sum_univ_two]
  μ a := 1 + a
  σ a := 1 - (1 / 2) * a
  g i := 2 * (i : ℕ)
  k a := a ^ 2
  W := 2
  W_nonneg := by norm_num
  k_zero := by norm_num
  μ_cont := continuous_const.add continuous_id
  σ_cont := continuous_const.sub (continuous_const.mul continuous_id)
  k_cont := continuous_id.pow 2
  Nbar := 1 / 10
  Nbar_pos := by norm_num
  lam := 3
  lam_nonneg := by norm_num

/-- The risk-channel example with a binding liquidity constraint at the
farmer's optimum: the same primitives as `riskExampleModel`, but
`W = 16/25 = k(4/5) < k(1) = 1`. The feasible maximum is `4/5`. -/
noncomputable def riskExampleTightModel : Model (Fin 2) :=
  { riskExampleModel with
    W := 16 / 25
    W_nonneg := by norm_num }

/-- Feasibility in the tight-liquidity variant: `a ∈ [0,1]` and `a² ≤ 16/25`. -/
theorem riskExampleTight_feasible {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hk : a ^ 2 ≤ 16 / 25) : a ∈ riskExampleTightModel.feasibleSet := by
  simp only [Model.feasibleSet, Model.feasibleSetAt, Set.mem_inter_iff,
    Set.mem_Icc, Set.mem_ofPred_eq, riskExampleTightModel, riskExampleModel]
  exact ⟨⟨ha0, ha1⟩, hk⟩

/-- The tight-liquidity variant has the same objective as the risk example. -/
theorem riskExampleTight_objective_eq (a : ℝ) :
    riskExampleTightModel.objective a = riskExampleModel.objective a := rfl

/-- Every `a ∈ [0,1]` is feasible in the risk-channel example. -/
theorem riskExample_feasible {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a ∈ riskExampleModel.feasibleSet := by
  simp only [Model.feasibleSet, Model.feasibleSetAt, Set.mem_inter_iff,
    Set.mem_Icc, Set.mem_ofPred_eq, riskExampleModel]
  constructor
  · exact ⟨ha0, ha1⟩
  · nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]

/-- Expected yield in the risk-channel example is `(3/2)a`. -/
theorem riskExample_expectedYield_eq (a : ℝ) :
    riskExampleModel.expectedYield a = 3 / 2 * a := by
  simp only [Model.expectedYield, Model.yield, riskExampleModel, Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one]
  ring

/-- The tight-liquidity variant has the same expected yield. -/
theorem riskExampleTight_expectedYield_eq (a : ℝ) :
    riskExampleTightModel.expectedYield a = 3 / 2 * a := by
  rw [show riskExampleTightModel.expectedYield a =
    riskExampleModel.expectedYield a from rfl,
    riskExample_expectedYield_eq]

/-- Expected yield is maximized at `a = 1`. -/
theorem riskExample_expectedYield_le_one {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    riskExampleModel.expectedYield a ≤ riskExampleModel.expectedYield 1 := by
  rw [riskExample_expectedYield_eq, riskExample_expectedYield_eq]
  norm_num
  linarith

/-- Expected yield is strictly increasing on `[0,1)`. -/
theorem riskExample_expectedYield_lt_one {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a < 1) :
    riskExampleModel.expectedYield a < riskExampleModel.expectedYield 1 := by
  rw [riskExample_expectedYield_eq, riskExample_expectedYield_eq]
  norm_num
  linarith

/-- The gross-output planner's selected adoption intensity is `a = 1`. -/
theorem riskExample_plannerAdoption_eq_one :
    riskExampleModel.plannerAdoption = 1 := by
  have hmem := riskExampleModel.plannerAdoption_mem
  have hge0 : 0 ≤ riskExampleModel.plannerAdoption := hmem.1.1
  have hle1 : riskExampleModel.plannerAdoption ≤ 1 := hmem.1.2
  have hmax : riskExampleModel.expectedYield (1 : ℝ) ≤
      riskExampleModel.expectedYield riskExampleModel.plannerAdoption :=
    riskExampleModel.plannerAdoption_max (riskExample_feasible (by norm_num) (by norm_num))
  have hle : riskExampleModel.expectedYield riskExampleModel.plannerAdoption ≤
      riskExampleModel.expectedYield 1 :=
    riskExample_expectedYield_le_one hge0 hle1
  have heq : riskExampleModel.expectedYield riskExampleModel.plannerAdoption =
      riskExampleModel.expectedYield 1 := le_antisymm hle hmax
  by_contra hne
  have hlt : riskExampleModel.plannerAdoption < 1 := lt_of_le_of_ne hle1 hne
  have hstrict := riskExample_expectedYield_lt_one hge0 hlt
  linarith

/-- Expected net income in the risk-channel example is `(3/2)a - a²`. -/
theorem riskExample_expectedNet_eq (a : ℝ) :
    riskExampleModel.expectedNet a = 3 / 2 * a - a ^ 2 := by
  rw [Model.expectedNet_eq, riskExample_expectedYield_eq]
  simp [riskExampleModel]

/-- The tight-liquidity variant has the same expected net income. -/
theorem riskExampleTight_expectedNet_eq (a : ℝ) :
    riskExampleTightModel.expectedNet a = 3 / 2 * a - a ^ 2 := by
  rw [Model.expectedNet_eq, riskExampleTight_expectedYield_eq]
  simp [riskExampleTightModel, riskExampleModel]

/-- Expected net income is maximized at `a = 3/4`. -/
theorem riskExample_expectedNet_le_three_quarters (a : ℝ) :
    riskExampleModel.expectedNet a ≤
      riskExampleModel.expectedNet (3 / 4) := by
  rw [riskExample_expectedNet_eq, riskExample_expectedNet_eq]
  nlinarith [sq_nonneg (a - 3 / 4)]

/-- Expected net income is strictly higher at `a = 3/4` than at any other `a`. -/
theorem riskExample_expectedNet_lt_three_quarters {a : ℝ} (hne : a ≠ 3 / 4) :
    riskExampleModel.expectedNet a <
      riskExampleModel.expectedNet (3 / 4) := by
  rw [riskExample_expectedNet_eq, riskExample_expectedNet_eq]
  have h : 0 < (a - 3 / 4) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  nlinarith

/-- The net-income planner's selected adoption intensity is `a = 3/4`. -/
theorem riskExample_netPlannerAdoption_eq_three_quarters :
    riskExampleModel.netPlannerAdoption = 3 / 4 := by
  have hmem := riskExampleModel.netPlannerAdoption_mem
  have hge0 : 0 ≤ riskExampleModel.netPlannerAdoption := hmem.1.1
  have hle1 : riskExampleModel.netPlannerAdoption ≤ 1 := hmem.1.2
  have hmax : riskExampleModel.expectedNet (3 / 4) ≤
      riskExampleModel.expectedNet riskExampleModel.netPlannerAdoption :=
    riskExampleModel.netPlannerAdoption_max
      (riskExample_feasible (by norm_num) (by norm_num))
  have hle : riskExampleModel.expectedNet riskExampleModel.netPlannerAdoption ≤
      riskExampleModel.expectedNet (3 / 4) :=
    riskExample_expectedNet_le_three_quarters _
  have heq : riskExampleModel.expectedNet riskExampleModel.netPlannerAdoption =
      riskExampleModel.expectedNet (3 / 4) := le_antisymm hle hmax
  by_contra hne
  have hstrict := riskExample_expectedNet_lt_three_quarters hne
  linarith

/-- In the risk-channel example, the benign state never has a shortfall. -/
theorem riskExample_shortfall_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    riskExampleModel.shortfall a 0 = 0 := by
  unfold Model.shortfall Model.net Model.yield
  simp only [riskExampleModel, Fin.val_zero]
  have hsq : a ^ 2 ≤ a := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  rw [max_eq_right (by linarith)]

/-- In the risk-channel example, the bad state always has a shortfall on `[0,1]`. -/
theorem riskExample_shortfall_one {a : ℝ} (_ha0 : 0 ≤ a) (_ha1 : a ≤ 1) :
    riskExampleModel.shortfall a 1 = 11 / 10 - 2 * a + a ^ 2 := by
  unfold Model.shortfall Model.net Model.yield
  simp only [riskExampleModel, Fin.val_one, Nat.cast_one, mul_one]
  have hsq : 2 * a - a ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (a - 1)]
  rw [max_eq_left]
  · ring
  · linarith

/-- The farmer's objective in the risk-channel example has the closed form
`-(5/2)a² + (9/2)a - 33/20` on `[0,1]`. -/
theorem riskExample_objective_eq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    riskExampleModel.objective a = -(5 / 2) * a ^ 2 + (9 / 2) * a - 33 / 20 := by
  simp only [Model.objective, Model.net, Model.yield, Model.shortfall,
    riskExampleModel, Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [max_eq_right (by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]),
    max_eq_left (by nlinarith [sq_nonneg (a - 1)])]
  ring

/-- The farmer's objective is maximized at `a = 9/10` on `[0,1]`. -/
theorem riskExample_objective_le_nine_tenths {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    riskExampleModel.objective a ≤
      riskExampleModel.objective (9 / 10) := by
  rw [riskExample_objective_eq ha0 ha1,
    riskExample_objective_eq (by norm_num) (by norm_num)]
  nlinarith [sq_nonneg (a - 9 / 10)]

/-- The farmer's objective is strictly lower away from `a = 9/10`. -/
theorem riskExample_objective_lt_nine_tenths {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hne : a ≠ 9 / 10) :
    riskExampleModel.objective a <
      riskExampleModel.objective (9 / 10) := by
  rw [riskExample_objective_eq ha0 ha1,
    riskExample_objective_eq (by norm_num) (by norm_num)]
  have h : 0 < (a - 9 / 10) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  nlinarith

/-- The farmer's selected adoption intensity in the risk-channel example is
`a = 9/10`. -/
theorem riskExample_optimalAdoption_eq_nine_tenths :
    riskExampleModel.optimalAdoption = 9 / 10 := by
  have hmem := riskExampleModel.optimalAdoption_mem
  have hge0 : 0 ≤ riskExampleModel.optimalAdoption := hmem.1.1
  have hle1 : riskExampleModel.optimalAdoption ≤ 1 := hmem.1.2
  have hmax : riskExampleModel.objective (9 / 10) ≤
      riskExampleModel.objective riskExampleModel.optimalAdoption :=
    riskExampleModel.optimalAdoption_max
      (riskExample_feasible (by norm_num) (by norm_num))
  have hle : riskExampleModel.objective riskExampleModel.optimalAdoption ≤
      riskExampleModel.objective (9 / 10) :=
    riskExample_objective_le_nine_tenths hge0 hle1
  have heq : riskExampleModel.objective riskExampleModel.optimalAdoption =
      riskExampleModel.objective (9 / 10) := le_antisymm hle hmax
  by_contra hne
  have hstrict := riskExample_objective_lt_nine_tenths hge0 hle1 hne
  linarith

/-- Values in the risk-channel example at `a = 3/4`. -/
theorem riskExample_values_three_quarters :
    riskExampleModel.expectedYield (3 / 4) = 9 / 8 ∧
      riskExampleModel.expectedNet (3 / 4) = 9 / 16 ∧
      riskExampleModel.objective (3 / 4) = 51 / 160 := by
  constructor
  · rw [riskExample_expectedYield_eq]; norm_num
  constructor
  · rw [riskExample_expectedNet_eq]; norm_num
  · rw [riskExample_objective_eq (by norm_num) (by norm_num)]; norm_num

/-- Values in the risk-channel example at `a = 9/10`. -/
theorem riskExample_values_nine_tenths :
    riskExampleModel.expectedYield (9 / 10) = 27 / 20 ∧
      riskExampleModel.expectedNet (9 / 10) = 27 / 50 ∧
      riskExampleModel.objective (9 / 10) = 3 / 8 := by
  constructor
  · rw [riskExample_expectedYield_eq]; norm_num
  constructor
  · rw [riskExample_expectedNet_eq]; norm_num
  · rw [riskExample_objective_eq (by norm_num) (by norm_num)]; norm_num

/-- Values in the risk-channel example at `a = 1`. -/
theorem riskExample_values_one :
    riskExampleModel.expectedYield 1 = 3 / 2 ∧
      riskExampleModel.expectedNet 1 = 1 / 2 ∧
      riskExampleModel.objective 1 = 7 / 20 := by
  constructor
  · rw [riskExample_expectedYield_eq]; norm_num
  constructor
  · rw [riskExample_expectedNet_eq]; norm_num
  · rw [riskExample_objective_eq (by norm_num) (by norm_num)]; norm_num

/-- In the risk-channel example, the gross-output planner strictly over-adopts
relative to the farmer. -/
theorem riskExample_strict_planner_farmer_separation :
    riskExampleModel.expectedYield riskExampleModel.optimalAdoption <
        riskExampleModel.expectedYield riskExampleModel.plannerAdoption ∧
      riskExampleModel.objective riskExampleModel.plannerAdoption <
        riskExampleModel.objective riskExampleModel.optimalAdoption := by
  constructor
  · rw [riskExample_plannerAdoption_eq_one]
    rw [riskExample_optimalAdoption_eq_nine_tenths]
    rw [riskExample_expectedYield_eq, riskExample_expectedYield_eq]
    norm_num
  · rw [riskExample_plannerAdoption_eq_one]
    rw [riskExample_optimalAdoption_eq_nine_tenths]
    rw [riskExample_objective_eq (by norm_num) (by norm_num),
      riskExample_objective_eq (by norm_num) (by norm_num)]
    norm_num

/-- In the risk-channel example, the net-income planner strictly under-adopts
relative to the farmer and the farmer sacrifices expected net income to reduce
expected shortfall. -/
theorem riskExample_netPlanner_strict_farmer_separation :
    riskExampleModel.expectedNet riskExampleModel.optimalAdoption <
        riskExampleModel.expectedNet riskExampleModel.netPlannerAdoption ∧
      riskExampleModel.objective riskExampleModel.netPlannerAdoption <
        riskExampleModel.objective riskExampleModel.optimalAdoption := by
  constructor
  · rw [riskExample_optimalAdoption_eq_nine_tenths,
      riskExample_netPlannerAdoption_eq_three_quarters]
    rw [riskExample_expectedNet_eq, riskExample_expectedNet_eq]
    norm_num
  · rw [riskExample_optimalAdoption_eq_nine_tenths,
      riskExample_netPlannerAdoption_eq_three_quarters]
    rw [riskExample_objective_eq (by norm_num) (by norm_num),
      riskExample_objective_eq (by norm_num) (by norm_num)]
    norm_num

/-- Expected shortfall in the risk-channel example at `a = 3/4`, recovered
from the objective identity. -/
theorem riskExample_expectedShortfall_three_quarters :
    riskExampleModel.expectedShortfall (3 / 4) = 13 / 160 := by
  have h := riskExampleModel.objective_eq_expectedNet_sub (3 / 4)
  rw [riskExample_values_three_quarters.2.2,
    riskExample_values_three_quarters.2.1] at h
  change 51 / 160 = 9 / 16 - 3 *
    riskExampleModel.expectedShortfall (3 / 4) at h
  nlinarith

/-- Expected shortfall in the risk-channel example at `a = 9/10`. -/
theorem riskExample_expectedShortfall_nine_tenths :
    riskExampleModel.expectedShortfall (9 / 10) = 11 / 200 := by
  have h := riskExampleModel.objective_eq_expectedNet_sub (9 / 10)
  rw [riskExample_values_nine_tenths.2.2,
    riskExample_values_nine_tenths.2.1] at h
  change 3 / 8 = 27 / 50 - 3 *
    riskExampleModel.expectedShortfall (9 / 10) at h
  nlinarith

/-- The risk–return threshold between the net-income planner's choice
`a = 3/4` and the farmer's optimum `a = 9/10` is `6/7`: the farmer gives up
`9/400` of expected net income for `21/800` of expected-shortfall reduction. -/
theorem riskExample_farmer_threshold :
    (riskExampleModel.expectedNet (3 / 4) -
        riskExampleModel.expectedNet (9 / 10)) /
      (riskExampleModel.expectedShortfall (3 / 4) -
        riskExampleModel.expectedShortfall (9 / 10)) = 6 / 7 := by
  rw [riskExample_expectedNet_eq, riskExample_expectedNet_eq,
    riskExample_expectedShortfall_three_quarters,
    riskExample_expectedShortfall_nine_tenths]
  norm_num

/-- The risk-channel example satisfies the general threshold condition with
`λ = 3 > 6/7`, so the net-income planner's choice is strictly worse for the
farmer than `a = 9/10`. -/
theorem riskExample_threshold_separation :
    riskExampleModel.objective (3 / 4) <
      riskExampleModel.objective (9 / 10) := by
  have hD : riskExampleModel.expectedShortfall (9 / 10) <
      riskExampleModel.expectedShortfall (3 / 4) := by
    rw [riskExample_expectedShortfall_nine_tenths,
      riskExample_expectedShortfall_three_quarters]
    norm_num
  have hlam : (riskExampleModel.expectedNet (3 / 4) -
        riskExampleModel.expectedNet (9 / 10)) /
      (riskExampleModel.expectedShortfall (3 / 4) -
        riskExampleModel.expectedShortfall (9 / 10)) <
        riskExampleModel.lam := by
    rw [riskExample_farmer_threshold]
    norm_num [riskExampleModel]
  have hD' : riskExampleModel.expectedShortfall (9 / 10) <
      riskExampleModel.expectedShortfall riskExampleModel.netPlannerAdoption := by
    simpa [riskExample_netPlannerAdoption_eq_three_quarters] using hD
  have hlam' : (riskExampleModel.expectedNet
          riskExampleModel.netPlannerAdoption -
        riskExampleModel.expectedNet (9 / 10)) /
      (riskExampleModel.expectedShortfall
          riskExampleModel.netPlannerAdoption -
        riskExampleModel.expectedShortfall (9 / 10)) <
        riskExampleModel.lam := by
    simpa [riskExample_netPlannerAdoption_eq_three_quarters] using hlam
  have h := riskExampleModel.netPlanner_strict_farmer_separation_of_threshold
    (b := 9 / 10) (riskExample_feasible (by norm_num) (by norm_num)) hD' hlam'
  simpa [riskExample_netPlannerAdoption_eq_three_quarters,
    riskExample_optimalAdoption_eq_nine_tenths] using h

/-- The tight-liquidity cap binds at the farmer's optimum:
`k(4/5) = W = 16/25`, while `a = 1` is infeasible (`k(1) = 1 > W`). -/
theorem riskExampleTight_binding :
    riskExampleTightModel.k (4 / 5) = riskExampleTightModel.W ∧
      riskExampleTightModel.W < riskExampleTightModel.k 1 := by
  norm_num [riskExampleTightModel, riskExampleModel]

/-- Every feasible adoption in the tight variant is at most `4/5`. -/
theorem riskExampleTight_le_four_fifths {a : ℝ}
    (ha : a ∈ riskExampleTightModel.feasibleSet) : a ≤ 4 / 5 := by
  have hmem := ha
  simp only [Model.feasibleSet, Model.feasibleSetAt, Set.mem_inter_iff,
    Set.mem_Icc, Set.mem_ofPred_eq, riskExampleTightModel, riskExampleModel] at hmem
  have hk : a ^ 2 ≤ 16 / 25 := hmem.2
  have ha0 : 0 ≤ a := hmem.1.1
  nlinarith [sq_nonneg (a - 4 / 5)]

/-- Difference of the risk example's objective from its value at `4/5`. -/
theorem riskExample_objective_four_fifths_sub (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    riskExampleModel.objective (4 / 5) - riskExampleModel.objective a =
      (1 / 2) * (5 * a - 4) * (a - 1) := by
  rw [riskExample_objective_eq (by norm_num) (by norm_num),
    riskExample_objective_eq ha0 ha1]
  ring

/-- In the tight variant, `4/5` maximizes the farmer's objective on the
feasible set. -/
theorem riskExampleTight_objective_le_four_fifths {a : ℝ}
    (ha : a ∈ riskExampleTightModel.feasibleSet) :
    riskExampleTightModel.objective a ≤ riskExampleTightModel.objective (4 / 5) := by
  have hle : a ≤ 4 / 5 := riskExampleTight_le_four_fifths ha
  have ha0 : 0 ≤ a := ha.1.1
  have ha1 : a ≤ 1 := ha.1.2
  rw [riskExampleTight_objective_eq, riskExampleTight_objective_eq]
  have hdiff := riskExample_objective_four_fifths_sub a ha0 ha1
  have h1 : 5 * a - 4 ≤ 0 := by linarith
  have h2 : a - 1 ≤ 0 := by linarith
  have hprod : 0 ≤ (1 / 2 : ℝ) * (5 * a - 4) * (a - 1) := by
    have h34 : 0 ≤ (5 * a - 4) * (a - 1) :=
      mul_nonneg_of_nonpos_of_nonpos h1 h2
    nlinarith
  linarith

/-- Away from `4/5`, the farmer's objective is strictly lower on the tight
feasible set. -/
theorem riskExampleTight_objective_lt_four_fifths {a : ℝ}
    (ha : a ∈ riskExampleTightModel.feasibleSet) (hne : a ≠ 4 / 5) :
    riskExampleTightModel.objective a < riskExampleTightModel.objective (4 / 5) := by
  have hle : a ≤ 4 / 5 := riskExampleTight_le_four_fifths ha
  have hlt : a < 4 / 5 := lt_of_le_of_ne hle hne
  have ha0 : 0 ≤ a := ha.1.1
  have ha1 : a ≤ 1 := ha.1.2
  rw [riskExampleTight_objective_eq, riskExampleTight_objective_eq]
  have hdiff := riskExample_objective_four_fifths_sub a ha0 ha1
  have h1 : 5 * a - 4 < 0 := by linarith
  have h2 : a - 1 < 0 := by linarith
  have hprod : 0 < (1 / 2 : ℝ) * (5 * a - 4) * (a - 1) := by
    have h34 : 0 < (5 * a - 4) * (a - 1) :=
      mul_pos_of_neg_of_neg h1 h2
    nlinarith
  linarith

/-- In the tight variant the farmer chooses the cap `a = 4/5`. -/
theorem riskExampleTight_optimalAdoption_eq_four_fifths :
    riskExampleTightModel.optimalAdoption = 4 / 5 := by
  have hfeas : (4 / 5 : ℝ) ∈ riskExampleTightModel.feasibleSet :=
    riskExampleTight_feasible (by norm_num) (by norm_num) (by norm_num)
  have hmax := riskExampleTightModel.optimalAdoption_max hfeas
  have hmem := riskExampleTightModel.optimalAdoption_mem
  have hle := riskExampleTight_objective_le_four_fifths hmem
  have heq := le_antisymm hle hmax
  by_contra hne
  have hstrict := riskExampleTight_objective_lt_four_fifths hmem hne
  linarith

/-- The cap binds exactly at the farmer's chosen intensity. -/
theorem riskExampleTight_binding_at_optimum :
    riskExampleTightModel.k riskExampleTightModel.optimalAdoption =
      riskExampleTightModel.W := by
  rw [riskExampleTight_optimalAdoption_eq_four_fifths]
  exact riskExampleTight_binding.1

/-- The net-income planner still chooses `a = 3/4`; that intensity remains
feasible under the cap. -/
theorem riskExampleTight_netPlannerAdoption_eq_three_quarters :
    riskExampleTightModel.netPlannerAdoption = 3 / 4 := by
  have hfeas : (3 / 4 : ℝ) ∈ riskExampleTightModel.feasibleSet :=
    riskExampleTight_feasible (by norm_num) (by norm_num) (by norm_num)
  have hmax := riskExampleTightModel.netPlannerAdoption_max hfeas
  have hmem := riskExampleTightModel.netPlannerAdoption_mem
  have hle : riskExampleTightModel.expectedNet riskExampleTightModel.netPlannerAdoption ≤
      riskExampleTightModel.expectedNet (3 / 4) := by
    rw [riskExampleTight_expectedNet_eq, riskExampleTight_expectedNet_eq]
    have h := riskExample_expectedNet_le_three_quarters
      riskExampleTightModel.netPlannerAdoption
    rw [riskExample_expectedNet_eq, riskExample_expectedNet_eq] at h
    exact h
  have heq := le_antisymm hle hmax
  by_contra hne
  have hstrict : riskExampleTightModel.expectedNet riskExampleTightModel.netPlannerAdoption <
      riskExampleTightModel.expectedNet (3 / 4) := by
    rw [riskExampleTight_expectedNet_eq, riskExampleTight_expectedNet_eq]
    have h := riskExample_expectedNet_lt_three_quarters hne
    rw [riskExample_expectedNet_eq, riskExample_expectedNet_eq] at h
    exact h
  linarith

/-- The gross-output planner also chooses the cap `a = 4/5`, so the
gross-output/farmer separation collapses under the binding cap. -/
theorem riskExampleTight_plannerAdoption_eq_four_fifths :
    riskExampleTightModel.plannerAdoption = 4 / 5 := by
  have hfeas : (4 / 5 : ℝ) ∈ riskExampleTightModel.feasibleSet :=
    riskExampleTight_feasible (by norm_num) (by norm_num) (by norm_num)
  have hmax := riskExampleTightModel.plannerAdoption_max hfeas
  have hmem := riskExampleTightModel.plannerAdoption_mem
  have hle : riskExampleTightModel.plannerAdoption ≤ 4 / 5 :=
    riskExampleTight_le_four_fifths hmem
  have hge : (4 / 5 : ℝ) ≤ riskExampleTightModel.plannerAdoption := by
    rw [riskExampleTight_expectedYield_eq, riskExampleTight_expectedYield_eq] at hmax
    nlinarith
  exact le_antisymm hle hge

/-- The gross-output benchmark and the farmer coincide at the cap. -/
theorem riskExampleTight_planner_eq_farmer :
    riskExampleTightModel.plannerAdoption = riskExampleTightModel.optimalAdoption := by
  rw [riskExampleTight_plannerAdoption_eq_four_fifths,
    riskExampleTight_optimalAdoption_eq_four_fifths]

/-- The net-income/farmer separation survives the binding cap: the farmer
chooses `4/5`, the net-income planner `3/4`, and the farmer's welfare is
strictly higher despite lower expected net income. -/
theorem riskExampleTight_netPlanner_strict_farmer_separation :
    riskExampleTightModel.expectedNet riskExampleTightModel.optimalAdoption <
        riskExampleTightModel.expectedNet riskExampleTightModel.netPlannerAdoption ∧
      riskExampleTightModel.objective riskExampleTightModel.netPlannerAdoption <
        riskExampleTightModel.objective riskExampleTightModel.optimalAdoption := by
  constructor
  · rw [riskExampleTight_optimalAdoption_eq_four_fifths,
      riskExampleTight_netPlannerAdoption_eq_three_quarters,
      riskExampleTight_expectedNet_eq, riskExampleTight_expectedNet_eq]
    norm_num
  · rw [riskExampleTight_optimalAdoption_eq_four_fifths,
      riskExampleTight_netPlannerAdoption_eq_three_quarters,
      riskExampleTight_objective_eq, riskExampleTight_objective_eq,
      riskExample_objective_eq (by norm_num) (by norm_num),
      riskExample_objective_eq (by norm_num) (by norm_num)]
    norm_num

/-- AI raises yield in every climate state when it raises mean yield, lowers
climate sensitivity, and climate damage is nonnegative. -/
theorem yield_mono (hμ : Monotone M.μ) (hσ : Antitone M.σ)
    (hg : ∀ i, 0 ≤ M.g i) {a a' : ℝ} (ha : a ≤ a') (i : ι) :
    M.yield a i ≤ M.yield a' i := by
  unfold yield
  have hmu : M.μ a ≤ M.μ a' := hμ ha
  have hsig : M.σ a' ≤ M.σ a := hσ ha
  have hg' : 0 ≤ M.g i := hg i
  have hmul : M.σ a' * M.g i ≤ M.σ a * M.g i :=
    mul_le_mul_of_nonneg_right hsig hg'
  linarith

/-- If the discrete yield gain covers the discrete AI cost increment in every climate
state, then net income is nondecreasing in AI adoption. -/
theorem net_mono_of_cost_condition {a a' : ℝ}
    (hcost : ∀ i, M.k a' - M.k a ≤
      (M.μ a' - M.μ a) - (M.σ a' - M.σ a) * M.g i) :
    ∀ i, M.net a i ≤ M.net a' i := by
  intro i
  unfold net yield
  nlinarith [hcost i]

/-- Conversely, if net income is nondecreasing, the discrete cost condition
holds. Together with `net_mono_of_cost_condition`, this makes T2 a
characterization rather than a one-way sufficient condition. -/
theorem cost_condition_of_net_mono {a a' : ℝ}
    (hnet : ∀ i, M.net a i ≤ M.net a' i) :
    ∀ i, M.k a' - M.k a ≤
      (M.μ a' - M.μ a) - (M.σ a' - M.σ a) * M.g i := by
  intro i
  unfold net yield at hnet
  nlinarith [hnet i]

/-- If net income rises, the shortfall in every state falls. -/
theorem shortfall_anti {a a' : ℝ}
    (hnet : ∀ i, M.net a i ≤ M.net a' i) (i : ι) :
    M.shortfall a' i ≤ M.shortfall a i := by
  unfold shortfall
  exact max_le_max (sub_le_sub_left (hnet i) M.Nbar) le_rfl

/-- Expected shortfall is nonincreasing in AI adoption when net income is
nondecreasing. -/
theorem expectedShortfall_anti {a a' : ℝ}
    (hnet : ∀ i, M.net a i ≤ M.net a' i) :
    M.expectedShortfall a' ≤ M.expectedShortfall a := by
  unfold expectedShortfall
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_left (M.shortfall_anti hnet i) (le_of_lt (M.p_pos i))

/-- The shortage probability is nonincreasing in AI adoption when net income
is nondecreasing: the set of shortage states shrinks. -/
theorem shortageProb_anti {a a' : ℝ}
    (hnet : ∀ i, M.net a i ≤ M.net a' i) :
    M.shortageProb a' ≤ M.shortageProb a := by
  classical
  unfold shortageProb shortageSet
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_le_of_lt (hnet i) hi
  · intro i _ _
    exact le_of_lt (M.p_pos i)

/-- Difference decomposition: the objective change equals the expected net
income gain plus the shortfall weight times the expected shortfall reduction. -/
theorem objective_sub (a a' : ℝ) :
    M.objective a' - M.objective a =
      (∑ i, M.p i * (M.net a' i - M.net a i))
      + M.lam * (∑ i, M.p i * (M.shortfall a i - M.shortfall a' i)) := by
  unfold objective
  rw [← Finset.sum_sub_distrib (s := Finset.univ)]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- If net income is nondecreasing, the food-security-weighted objective is
nondecreasing; the shortfall term reinforces adoption. -/
theorem objective_mono_of_net_mono {a a' : ℝ}
    (hnet : ∀ i, M.net a i ≤ M.net a' i) :
    M.objective a ≤ M.objective a' := by
  have hN : 0 ≤ ∑ i, M.p i * (M.net a' i - M.net a i) := by
    refine Finset.sum_nonneg fun i _ => ?_
    exact mul_nonneg (le_of_lt (M.p_pos i)) (sub_nonneg.mpr (hnet i))
  have hD : 0 ≤ ∑ i, M.p i * (M.shortfall a i - M.shortfall a' i) := by
    refine Finset.sum_nonneg fun i _ => ?_
    exact mul_nonneg (le_of_lt (M.p_pos i))
      (sub_nonneg.mpr (M.shortfall_anti hnet i))
  have hid := M.objective_sub a a'
  nlinarith [hN, hD, M.lam_nonneg, hid]

/-- If net income at some adoption intensity (not necessarily the maximum)
leaves a climate state below the food-security line, expected shortfall is
strictly positive. This is the shortfall-positivity lemma; a primitive
adaptation-limit statement would need an extra condition on the primitives. -/
theorem expectedShortfall_pos_of_shortfall {a : ℝ} {i : ι}
    (hi : M.net a i < M.Nbar) :
    0 < M.expectedShortfall a := by
  unfold expectedShortfall
  have hterm : 0 < M.p i * M.shortfall a i := by
    refine mul_pos (M.p_pos i) ?_
    unfold shortfall
    have hpos : 0 < M.Nbar - M.net a i := sub_pos.mpr hi
    rw [max_eq_left (le_of_lt hpos)]
    exact hpos
  refine Finset.sum_pos' ?_ ⟨i, Finset.mem_univ i, hterm⟩
  intro j _
  exact mul_nonneg (le_of_lt (M.p_pos j)) (by
    unfold shortfall
    exact le_max_right _ _)

end Model

end AIClimateFoodSecurity
