/-
# Proof of extra_at_k_le_prod: the convolution bound for extra walks
-/

import Mathlib
import RequestProject.SAWHWStepHelpers
import RequestProject.SAWHWConvBoundBase
import RequestProject.SAWHWFiberCount

open Real Complex ComplexConjugate Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 8000000

/-- The main bound for k < n, using fiber_bound from SAWHWFiberCount. -/
lemma extra_at_k_le_prod_lt (W n k : ℕ) (hk : k ≤ n) (hk_lt : k < n) :
    extra_at_k W n k ≤ bridge_count_any (W + 1) k * narrow_suffix_count W (n - k) := by
  -- Define the bridge set and fiber map
  set B := Finset.univ.filter (fun b : SAW paperStart k =>
    b.w.1 + b.w.2.1 = -(↑(W + 1) : ℤ) ∧
    ∀ v ∈ b.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
  set E := Finset.univ.filter (fun s : SAW paperStart n =>
    (∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) ∧
    (∃ h : ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ),
      lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h = k))
  -- Define fiber: for each bridge b, the walks in E with matching take-k support
  set fib := fun b : SAW paperStart k =>
    E.filter (fun s => (s.p.1.take k).support = b.p.1.support)
  -- Step 1: E ⊆ biUnion over B of fiber
  have h_sub : E ⊆ B.biUnion fib := by
    intro s hs
    rw [Finset.mem_biUnion]
    have hm := (Finset.mem_filter.mp hs).2
    set b := extraPrefix W n k s hk
    have hb := extraPrefix_in_bridge W n k s hm.1 hm.2.1 hm.2.2 hk
    refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.1, hb.2⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨hs, rfl⟩
  -- Step 2: each fiber has ≤ narrow_suffix_count elements
  have h_fib : ∀ b ∈ B, (fib b).card ≤ narrow_suffix_count W (n - k) := by
    intro b hb
    have hb_props := (Finset.mem_filter.mp hb).2
    by_cases hb_false : b.w.2.2 = false
    · -- fib b = E.filter(...) = Finset.filter on Finset.filter = Finset.filter with And
      have : fib b = Finset.univ.filter (fun s : SAW paperStart n =>
        (∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) ∧
        (∃ h : ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ),
          lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h = k) ∧
        (s.p.1.take k).support = b.p.1.support) := by
        simp [fib, E, Finset.filter_filter]; congr 1; ext s; tauto
      rw [this]
      exact fiber_bound W n k hk_lt b hb_false hb_props.1
    · -- If b.w is TRUE, the fiber is empty
      suffices h : fib b = ∅ by simp [h]
      rw [← Finset.not_nonempty_iff_eq_empty]; intro ⟨s, hs⟩
      have ⟨hs_E, h_take_eq⟩ := Finset.mem_filter.mp hs
      have hm := (Finset.mem_filter.mp hs_E).2
      have ⟨hf, _⟩ := extraVertex_false W n k s hm.1 hm.2.1 hm.2.2 hk_lt
      have hv_eq := take_support_eq_endpoint n k s b hk h_take_eq
      rw [hv_eq] at hf
      exact hb_false hf
  -- Step 3: Combine
  calc extra_at_k W n k = E.card := rfl
    _ ≤ (B.biUnion fib).card := Finset.card_le_card h_sub
    _ ≤ B.card * narrow_suffix_count W (n - k) := Finset.card_biUnion_le_card_mul B fib _ h_fib
    _ = bridge_count_any (W + 1) k * narrow_suffix_count W (n - k) := by rfl

/-! ## Main bound -/

lemma extra_at_k_le_prod (W n k : ℕ) (hk : k ≤ n) :
    extra_at_k W n k ≤ bridge_count_any (W + 1) k * narrow_suffix_count W (n - k) := by
  by_cases h : k = n
  · subst h; simp [narrow_suffix_count]; exact extra_at_k_le_prod_eq W k
  · exact extra_at_k_le_prod_lt W n k hk (lt_of_le_of_ne hk h)

lemma extra_count_le_conv_nat (W n : ℕ) :
    extra_count W n ≤ ∑ k ∈ Finset.range (n + 1),
      bridge_count_any (W + 1) k * narrow_suffix_count W (n - k) := by
  rw [extra_count_eq_sum]
  exact Finset.sum_le_sum fun k hk =>
    extra_at_k_le_prod W n k (by exact Finset.mem_range_succ_iff.mp hk)

/-- The convolution bound cast to ℝ. -/
lemma extra_count_le_conv' (W n : ℕ) :
    (extra_count W n : ℝ) ≤
    ∑ k ∈ Finset.range (n + 1),
      (bridge_count_any (W + 1) k : ℝ) * (narrow_suffix_count W (n - k) : ℝ) := by
  exact_mod_cast extra_count_le_conv_nat W n

end
