/-
# Hammersley-Welsh Bridge Decomposition: Helper Lemmas

Helper lemmas for the bridge decomposition inequality.
-/

import Mathlib
import RequestProject.SAWPaperChain

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-- For A ≥ 1: A ≤ 2 * A ^ 2. -/
lemma le_two_mul_sq_of_one_le {A : ℝ} (hA : 1 ≤ A) : A ≤ 2 * A ^ 2 := by
  nlinarith [sq_nonneg (A - 1)]

/-- The powerset-product sum is ≥ 1 (the empty set contributes 1). -/
lemma powerset_prod_ge_one' (N : ℕ) {x : ℝ} (hx : 0 < x) :
    1 ≤ ∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x := by
  have h_empty : ∅ ∈ (Finset.range N).powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
  have h_nn : ∀ S ∈ (Finset.range N).powerset, 0 ≤ ∏ T ∈ S, paper_bridge_partition (T + 1) x :=
    fun S _ => Finset.prod_nonneg fun T _ => paper_bridge_partition_nonneg (T + 1) x hx
  have := Finset.single_le_sum h_nn h_empty
  simp at this
  linarith

/-- Bridge partition is summable for x ≤ xc and T ≥ 1. -/
lemma bridge_summable_x (T : ℕ) (hT : 1 ≤ T) {x : ℝ} (hx : 0 < x) (hxc : x ≤ xc) :
    Summable (fun b : PaperBridge T => x ^ b.walk.1.length) :=
  Summable.of_nonneg_of_le (fun _ => pow_nonneg hx.le _)
    (fun b => pow_le_pow_left₀ hx.le hxc _) (paper_bridge_summable T hT)

private def bridge1a : PaperBridge 1 where
  end_v := (-1, 0, false)
  walk := ⟨SimpleGraph.Walk.cons (by decide : hexGraph.Adj paperStart (-1, 0, false)) .nil,
           by simp [SimpleGraph.Walk.cons_isPath_iff, paperStart]⟩
  end_right := by constructor <;> decide
  in_strip := by intro v hv; simp at hv; rcases hv with rfl | rfl <;> decide

private def bridge1b : PaperBridge 1 where
  end_v := (0, -1, false)
  walk := ⟨SimpleGraph.Walk.cons (by decide : hexGraph.Adj paperStart (0, -1, false)) .nil,
           by simp [SimpleGraph.Walk.cons_isPath_iff, paperStart]⟩
  end_right := by constructor <;> decide
  in_strip := by intro v hv; simp at hv; rcases hv with rfl | rfl <;> decide

private lemma bridge1a_ne_bridge1b : bridge1a ≠ bridge1b := by
  intro h; have := congr_arg PaperBridge.end_v h; simp [bridge1a, bridge1b] at this

private lemma bridge1a_len : bridge1a.walk.1.length = 1 := rfl
private lemma bridge1b_len : bridge1b.walk.1.length = 1 := rfl

/-- B_1(x) ≥ 2x for 0 < x ≤ xc. -/
lemma bridge_partition_one_ge_2x {x : ℝ} (hx : 0 < x) (hxc : x ≤ xc) :
    2 * x ≤ paper_bridge_partition 1 x := by
  have h_summable : Summable (fun b : PaperBridge 1 => x ^ b.walk.1.length) := by
    apply bridge_summable_x 1 (by norm_num) hx hxc;
  have h_two_bridges : x ^ bridge1a.walk.1.length + x ^ bridge1b.walk.1.length ≤ paper_bridge_partition 1 x := by
    have h_two_bridges : x ^ bridge1a.walk.1.length + x ^ bridge1b.walk.1.length ≤ ∑' b : PaperBridge 1, x ^ b.walk.1.length := by
      have h_finite : Set.Finite ({bridge1a, bridge1b} : Set (PaperBridge 1)) := by
        exact Set.toFinite { bridge1a, bridge1b }
      have h_two_bridges : ∑ b ∈ h_finite.toFinset, x ^ b.walk.1.length ≤ ∑' b : PaperBridge 1, x ^ b.walk.1.length := by
        exact Summable.sum_le_tsum _ ( fun _ _ => by positivity ) h_summable;
      convert h_two_bridges using 1;
      rw [ Finset.sum_eq_add ] <;> norm_num [ bridge1a_ne_bridge1b ];
    exact h_two_bridges;
  convert h_two_bridges using 1 ; norm_num [ bridge1a_len, bridge1b_len ] ; ring

/-- B_1(x) ≥ x for 0 < x ≤ xc. -/
lemma bridge_partition_one_ge_x {x : ℝ} (hx : 0 < x) (hxc : x ≤ xc) :
    x ≤ paper_bridge_partition 1 x := by
  linarith [bridge_partition_one_ge_2x hx hxc]

end
