/-
# Connective constant via Fekete's lemma

Establishes that the connective constant is a limit and is positive,
using submultiplicativity (SAWSubmult.lean) and Fekete's lemma.
-/

import RequestProject.SAWSubmult
import RequestProject.SAWStrip

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Connective constant as limit of c_n^{1/n} -/

/-- The connective constant equals the limit of c_n^{1/n} as n → ∞.
    Uses Fekete's lemma with the proved submultiplicativity. -/
theorem connective_constant_is_limit' :
    Filter.Tendsto (fun n => (saw_count n : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds connective_constant) := by
  have ha_pos : ∀ n, (0 : ℝ) < (saw_count n : ℝ) := fun n => Nat.cast_pos.mpr (saw_count_pos n)
  have ha_submult : ∀ n m, (saw_count (n + m) : ℝ) ≤ (saw_count n : ℝ) * (saw_count m : ℝ) :=
    fun n m => by exact_mod_cast saw_count_submult' n m
  obtain ⟨μ, hμ⟩ := fekete_submultiplicative ha_pos ha_submult
  suffices h : μ = connective_constant by rw [← h]; exact hμ
  apply le_antisymm
  · refine' le_csInf _ _ <;> norm_num
    intro n hn
    have h_le : ∀ k ≥ 1, (saw_count (k * n) : ℝ) ^ (1 / (k * n : ℝ)) ≤ (saw_count n : ℝ) ^ (1 / (n : ℝ)) := by
      intro k hk
      have h_le : (saw_count (k * n) : ℝ) ≤ (saw_count n : ℝ) ^ k := by
        induction hk <;> simp_all +decide [Nat.succ_mul, pow_succ']
        exact le_trans (ha_submult _ _) (by nlinarith [show (0 : ℝ) < saw_count n from Nat.cast_pos.mpr (ha_pos n)])
      convert Real.rpow_le_rpow (by positivity) h_le _ using 1
      · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; ring_nf; norm_num [show k ≠ 0 by linarith]
      · positivity
    have h_lim_le : Filter.Tendsto (fun k : ℕ => (saw_count (k * n) : ℝ) ^ (1 / (k * n : ℝ))) Filter.atTop (nhds μ) := by
      convert hμ.comp (Filter.tendsto_id.atTop_mul_const' <| Nat.cast_pos.mpr hn) using 2; norm_num
    exact le_of_tendsto h_lim_le (Filter.eventually_atTop.mpr ⟨1, fun k hk => by simpa using h_le k hk⟩) |> le_trans <| by norm_num
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hμ
      (Filter.eventually_atTop.mpr ⟨1, fun n hn =>
        csInf_le ⟨0, Set.forall_mem_image.mpr fun n hn => Real.rpow_nonneg (Nat.cast_nonneg _) _⟩ ⟨n, hn, rfl⟩⟩)

/-- The connective constant is positive. -/
theorem connective_constant_pos' : 0 < connective_constant := by
  refine' lt_of_lt_of_le zero_lt_one (le_csInf _ _) <;> norm_num
  exact fun n hn => Real.one_le_rpow (mod_cast saw_count_pos n) (by positivity)

end
