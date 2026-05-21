/-
# Quadratic recurrence lower bound and harmonic divergence

Key abstract results used in the proof of μ = √(2+√2):
- `quadratic_recurrence_lower_bound`: B_T ≥ c/T from the quadratic recurrence
- `not_summable_of_lower_bound`: a series dominating the harmonic series diverges
-/

import RequestProject.SAWBridge

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Harmonic divergence -/

/-- If a_n ≥ c/(n+1) for some c > 0, then Σ a_n diverges. -/
theorem not_summable_of_lower_bound {a : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (ha : ∀ n : ℕ, c / ((n : ℝ) + 1) ≤ a n) :
    ¬ Summable a := by
  by_contra h_summable
  have h_comparison : Summable (fun n : ℕ => c / (n + 1 : ℝ)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) ha h_summable
  exact absurd h_comparison (by
    erw [summable_mul_left_iff (by positivity)]
    exact_mod_cast mt (summable_nat_add_iff 1 |>.mp) Real.not_summable_natCast_inv)

/-! ## Quadratic recurrence lower bound

From B_T ≤ α·B_{T+1}² + B_{T+1} with 0 ≤ B_T and α > 0,
we prove B_T ≥ min(B_1, 1/α) / T for all T ≥ 1.

The induction (going from T to T+1): suppose B_{T+1} < c/(T+1).
Then α·B_{T+1}² + B_{T+1} < α·c²/(T+1)² + c/(T+1).
Since αc ≤ 1 (by c ≤ 1/α), this is < c/T, contradicting B_T ≥ c/T.
-/

/-- If B satisfies B_T ≤ α·B_{T+1}² + B_{T+1} with B_1 > 0 and α > 0,
    then B_T ≥ min(B_1, 1/α) / T for all T ≥ 1. -/
theorem quadratic_recurrence_lower_bound
    {B : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hB_nn : ∀ T, 0 ≤ B T)
    (hrecur : ∀ T, B T ≤ α * B (T + 1) ^ 2 + B (T + 1))
    (hB1 : 0 < B 1) :
    ∀ T : ℕ, 1 ≤ T → min (B 1) (1 / α) / T ≤ B T := by
  intro T hT
  set c := min (B 1) (1 / α) with hc
  have hc_pos : 0 < c := lt_min hB1 (one_div_pos.mpr hα)
  have hc_le_one : c ≤ 1 / α := min_le_right _ _
  have hc_le : ∀ T, 1 ≤ T → c / T ≤ B T := by
    intro T hT; induction' hT with T hT ih <;> norm_num [div_le_iff₀] at *; aesop
    contrapose! ih
    rw [lt_div_iff₀] at * <;> norm_num <;> try linarith
    nlinarith [hrecur T, hB_nn T, hB_nn (T + 1), mul_inv_cancel₀ (ne_of_gt hα),
      mul_le_mul_of_nonneg_left hc_le_one (hB_nn (T + 1)),
      mul_le_mul_of_nonneg_left ih.le (hB_nn (T + 1))]
  exact hc_le T hT

end
