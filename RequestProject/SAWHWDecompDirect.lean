/-
# Helper lemmas for the Hammersley-Welsh decomposition bound

These lemmas contribute toward proving paper_bridge_decomp_injection.
-/

import Mathlib
import RequestProject.SAWPaperChain

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## The RHS is at least 2 -/

lemma rhs_ge_two' {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (2 : ℝ) ≤ 2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  refine' le_mul_of_one_le_right ( by positivity ) ( one_le_pow₀ _ );
  refine' le_trans _ ( Finset.single_le_sum ( fun S _ => Finset.prod_nonneg fun T _ => _ ) ( Finset.mem_powerset.mpr <| Finset.empty_subset _ ) ) <;> norm_num;
  exact tsum_nonneg fun _ => pow_nonneg hx.le _

/-! ## SAW count at 0 -/

lemma saw_count_zero' : saw_count 0 = 1 := by
  convert Fintype.card_eq_one_iff.mpr _;
  use ⟨ hexOrigin, ⟨ SimpleGraph.Walk.nil, by simp +decide [ SimpleGraph.Walk.isPath_def ] ⟩, rfl ⟩;
  rintro ⟨ w, ⟨ p, hp ⟩, l ⟩;
  cases p <;> aesop

/-! ## Simple case N = 0 -/

lemma decomp_injection_N0' {x : ℝ} (hx : 0 < x) (hxc : x < xc) :
    ∑ n ∈ Finset.range 1, (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range 0).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  norm_num [ saw_count_zero' ]

/-! ## Powerset product identity -/

/-
The powerset sum equals the product of (1 + β_T) over T.
-/
lemma powerset_prod_eq' {N : ℕ} {β : ℕ → ℝ} :
    ∑ S ∈ (Finset.range N).powerset, ∏ T ∈ S, β T =
    ∏ T ∈ Finset.range N, (1 + β T) := by
  simp +decide [ add_comm, Finset.prod_add ]

/-! ## Second bridge of width 1 -/

/-- A second PaperBridge of width 1: paperStart → (0, -1, false). -/
noncomputable def paperBridge_width1b : PaperBridge 1 where
  end_v := (0, -1, false)
  walk := ⟨SimpleGraph.Walk.cons (by decide : hexGraph.Adj paperStart (0, -1, false)) .nil,
           by simp [SimpleGraph.Walk.cons_isPath_iff, paperStart]⟩
  end_right := by constructor <;> decide
  in_strip := by intro v hv; simp at hv; rcases hv with rfl | rfl <;> decide

/-
The two width-1 bridges are distinct.
-/
lemma paperBridge_width1_ne_width1b : paperBridge_width1 ≠ paperBridge_width1b := by
  exact ne_of_apply_ne ( fun b => b.end_v ) ( by simp +decide [ paperBridge_width1, paperBridge_width1b ] )

end