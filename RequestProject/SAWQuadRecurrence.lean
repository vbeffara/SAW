/-
# Abstract quadratic recurrence for bridge lower bound

Formalization of the Case 2 argument from the proof of Theorem 1:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## The argument

If `c_α xc B_{T+1}² + B_{T+1} ≥ B_T` and `B_T ∈ (0, 1]` for all T ≥ 1,
then `B_T ≥ min(B_1, 1/(c_α xc)) / T` for all T ≥ 1.

This is purely a real-analysis argument about sequences satisfying
a quadratic recurrence relation.
-/

import Mathlib

open Real

noncomputable section

/-! ## The quadratic recurrence bound

Given a sequence B : ℕ → ℝ with:
  (1) 0 < B T ≤ 1 for all T ≥ 1
  (2) α · B(T+1)² + B(T+1) ≥ B(T) for all T ≥ 1
where α > 0, we prove B(T) ≥ c/T for c = min(B(1), 1/α).
-/

/-
If x > 0 and α·x² + x ≥ y > 0, and x ≤ 1, then x ≥ y/(1 + α·y).
-/
lemma quadratic_lower_step {α x y : ℝ} (hα : 0 < α) (hx_pos : 0 < x)
    (hx_le : x ≤ 1) (hy_pos : 0 < y)
    (hrec : α * x ^ 2 + x ≥ y) :
    x ≥ y / (1 + α * y) := by
  -- Since $1 + \alpha * y > 0$, we can multiply both sides of the inequality by $1 + \alpha * y$ without changing the direction of the inequality.
  have h_mul : x * (1 + α * y) ≥ y := by
    nlinarith [ mul_le_mul_of_nonneg_left hx_le hα.le, mul_le_mul_of_nonneg_left hy_pos.le hα.le, mul_le_mul_of_nonneg_left hx_le hy_pos.le, mul_le_mul_of_nonneg_left hy_pos.le hy_pos.le, sq_nonneg ( x - y ), sq_nonneg ( x - 1 ), sq_nonneg ( y - 1 ) ] ;
  rwa [ ge_iff_le, div_le_iff₀ ( by positivity ) ]

/-
The abstract quadratic recurrence bound.
    If B(T) satisfies the quadratic recurrence and is bounded in (0, 1],
    then B(T) ≥ min(B(1), 1/α) / T.
-/
theorem quadratic_recurrence_lower_bound
    {α : ℝ} (hα : 0 < α)
    {B : ℕ → ℝ}
    (hB_pos : ∀ T, 1 ≤ T → 0 < B T)
    (hB_le : ∀ T, 1 ≤ T → B T ≤ 1)
    (hB_rec : ∀ T, 1 ≤ T → α * (B (T + 1)) ^ 2 + B (T + 1) ≥ B T) :
    ∀ T, 1 ≤ T → min (B 1) (1 / α) / T ≤ B T := by
  intro T hT; rw [ div_le_iff₀ ] <;> norm_num <;> induction' hT with k hk <;> norm_num at *;
  -- By the induction hypothesis, we know that either $B 1 \leq B k * k$ or $\alpha^{-1} \leq B k * k$.
  cases' ‹B 1 ≤ B k * ↑k ∨ α⁻¹ ≤ B k * ↑k› with h h;
  · contrapose! hB_rec;
    exact ⟨ k, hk, by nlinarith [ hB_pos k hk, hB_pos ( k + 1 ) ( by linarith ), hB_le k hk, hB_le ( k + 1 ) ( by linarith ), mul_inv_cancel₀ ( ne_of_gt hα ), mul_pos hα ( hB_pos ( k + 1 ) ( by linarith ) ) ] ⟩;
  · contrapose! h;
    nlinarith [ inv_pos.2 hα, mul_inv_cancel₀ hα.ne', hB_pos k hk, hB_pos ( k + 1 ) ( by linarith ), hB_le k hk, hB_le ( k + 1 ) ( by linarith ), hB_rec k hk, mul_pos hα ( hB_pos ( k + 1 ) ( by linarith ) ) ]

/-
Corollary: if the recurrence holds, then ∃ c > 0, B(T) ≥ c/T.
-/
theorem quadratic_recurrence_exists_lower
    {α : ℝ} (hα : 0 < α)
    {B : ℕ → ℝ}
    (hB_pos : ∀ T, 1 ≤ T → 0 < B T)
    (hB_le : ∀ T, 1 ≤ T → B T ≤ 1)
    (hB_rec : ∀ T, 1 ≤ T → α * (B (T + 1)) ^ 2 + B (T + 1) ≥ B T) :
    ∃ c > 0, ∀ T, 1 ≤ T → c / T ≤ B T := by
  -- Set $c$ to be $\min(B(1), 1/\alpha)$.
  set c := min (B 1) (1 / α) with hc_def;
  refine' ⟨ c, _, _ ⟩;
  · exact lt_min ( hB_pos 1 le_rfl ) ( one_div_pos.mpr hα );
  · exact?

end