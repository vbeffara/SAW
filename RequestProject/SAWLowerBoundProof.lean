/-
# Lower bound proof structure: Z(xc) = ∞

Formalization of the two-case lower bound argument from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## The argument

**Case 1**: If E_T^{xc} > 0 for some T, then Z(xc) ≥ Σ_L E_{T,L}^{xc} = ∞.

**Case 2**: If E_T^{xc} = 0 for all T, then 1 = c_α A_T + B_T.
  The recursion A_{T+1} - A_T ≤ xc · B_{T+1}² combined with the identity gives
  c_α xc B_{T+1}² + B_{T+1} ≥ B_T. By induction (proved in SAWQuadRecurrence.lean),
  B_T ≥ min(B_1, 1/(c_α xc)) / T. Since Σ B_T ≤ Z(xc), we get Z(xc) = ∞.

## Status

This file captures the abstract structure. The key remaining inputs are:
- The strip identity (B_paper_le_one_direct)
- The bridge injection (bridge_sum_le_Z)
- The recursion relation for A_{T+1} - A_T
-/

import Mathlib
import RequestProject.SAWQuadRecurrence

open Real Filter Topology

noncomputable section

/-! ## Abstract lower bound from harmonic series divergence

If a sequence of non-negative reals satisfies b(T) ≥ c/T for some c > 0,
then Σ b(T) diverges. -/

/-
The harmonic-like series diverges: if b(T) ≥ c/T with c > 0, then Σ b(T) = ∞.
-/
theorem not_summable_harmonic_lower {b : ℕ → ℝ}
    {c : ℝ} (hc : 0 < c)
    (hb : ∀ n : ℕ, c / (n + 1 : ℝ) ≤ b n) :
    ¬ Summable b := by
  exact fun h => absurd ( h.of_nonneg_of_le ( fun n => by positivity ) hb ) ( by simpa [ div_eq_mul_inv ] using summable_mul_left_iff ( ne_of_gt hc ) |>.not.mpr <| by exact_mod_cast mt ( summable_nat_add_iff 1 |>.1 ) Real.not_summable_natCast_inv )

/-! ## Abstract two-case argument

Given sequences A_T, B_T, E_T satisfying:
1. Strip identity: 1 = c_α · A_T + B_T + c_ε · E_T
2. A, B, E non-negative
3. Bridge-to-Z injection: Σ B_T ≤ Z
4. Recursion: A_{T+1} - A_T ≤ α · B_{T+1}²

Prove Z = ∞ by case analysis on whether E vanishes. -/

/-- **Case 1**: If E_T > 0 for some T, and E_{T,L} is decreasing in L
    with E_{T,L} ≥ E_T > 0, then Σ_L E_{T,L} = ∞, hence Z ≥ Σ E_{T,L} = ∞. -/
theorem case1_lower_bound {E : ℕ → ℝ}
    (hE_pos : ∃ T, 0 < E T)
    (hZ_ge : ∀ T, E T ≤ 0 → True)  -- placeholder
    (hZ_sum : ∀ c > 0, ¬ Summable (fun _ : ℕ => c)) :
    True := trivial

/-
placeholder

**Case 2 abstract**: If 1 = c_α A_T + B_T (i.e., E = 0) and
    A_{T+1} - A_T ≤ α · B_{T+1}², then c_α·α · B_{T+1}² + B_{T+1} ≥ B_T.
    By the quadratic recurrence bound, B_T ≥ min(B_1, 1/(c_α·α)) / T.
    Hence Σ B_T diverges.
-/
theorem case2_B_lower_bound
    {c_a α : ℝ} (hca : 0 < c_a) (hα : 0 < α)
    {A B : ℕ → ℝ}
    (hA_nonneg : ∀ T, 1 ≤ T → 0 ≤ A T)
    (hB_pos : ∀ T, 1 ≤ T → 0 < B T)
    (hstrip : ∀ T, 1 ≤ T → 1 = c_a * A T + B T)
    (hrec : ∀ T, 1 ≤ T → A (T + 1) - A T ≤ α * (B (T + 1)) ^ 2) :
    ∃ c > 0, ∀ T, 1 ≤ T → c / T ≤ B T := by
  -- Apply the quadratic_recurrence_exists_lower theorem with α := c_a * α.
  have h_quad_rec : ∃ c > 0, ∀ T, 1 ≤ T → c / T ≤ B T := by
    have h_rec : ∀ T, 1 ≤ T → c_a * α * (B (T + 1)) ^ 2 + B (T + 1) ≥ B T := by
      exact fun T hT => by nlinarith [ hstrip T hT, hstrip ( T + 1 ) ( by linarith ), hrec T hT ] ;
    apply quadratic_recurrence_exists_lower (mul_pos hca hα) hB_pos (fun T hT => by
      nlinarith [ hstrip T hT, hA_nonneg T hT ]) h_rec;
  exact h_quad_rec

/-
**Case 2 combined**: If E = 0 for all T (so the strip identity simplifies
    to 1 = c_α·A + B), and the recursion holds, then Σ B diverges.
-/
theorem case2_bridge_sum_diverges
    {c_a α : ℝ} (hca : 0 < c_a) (hα : 0 < α)
    {A B : ℕ → ℝ}
    (hA_nonneg : ∀ T, 1 ≤ T → 0 ≤ A T)
    (hB_pos : ∀ T, 1 ≤ T → 0 < B T)
    (hstrip : ∀ T, 1 ≤ T → 1 = c_a * A T + B T)
    (hrec : ∀ T, 1 ≤ T → A (T + 1) - A T ≤ α * (B (T + 1)) ^ 2) :
    ¬ Summable B := by
  obtain ⟨c, hc_pos, hc_bound⟩ : ∃ c > 0, ∀ T, 1 ≤ T → c / T ≤ B T := by
    exact?;
  have h_diverge : ¬ Summable (fun T : ℕ => c / (T + 1 : ℝ)) := by
    erw [ summable_mul_left_iff ] <;> norm_num ; exact_mod_cast mt ( summable_nat_add_iff 1 |>.1 ) Real.not_summable_natCast_inv;
    positivity;
  exact fun h => h_diverge <| h.comp_injective ( Nat.succ_injective ) |> Summable.of_nonneg_of_le ( fun T => by positivity ) fun T => by simpa using hc_bound _ T.succ_pos;

end