/-
# Proof of extra_count_le_conv: the convolution bound for extra walks
-/

import Mathlib
import RequestProject.SAWHWStepHelpers

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Decomposition of extra walks at lastDCIndex -/

/-- The number of extra walks with a specific lastDCIndex value. -/
def extra_at_k (W n k : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun s : SAW paperStart n =>
    (∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) ∧
    (∃ h : ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ),
      lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h = k)))

/-- extra_count equals the sum of extra_at_k over k. -/
lemma extra_count_eq_sum (W n : ℕ) :
    extra_count W n = ∑ k ∈ Finset.range (n + 1), extra_at_k W n k := by
  unfold extra_count extra_at_k;
  rw [ ← Finset.card_biUnion ];
  · congr with s ; simp +decide [ Finset.mem_biUnion ];
    constructor <;> intro h;
    · exact ⟨ ⟨ by
        rcases h.2 with ⟨ a, b, h | h, h' ⟩ <;> simp_all +decide [ SimpleGraph.Walk.mem_support_iff_exists_getVert ]; all_goals grind, by
        exact le_trans ( lastDCIndex_le_length _ _ _ ) ( by simp +decide [ s.l ] ) ⟩, h.1 ⟩;
    · obtain ⟨ ⟨ j, hj₁, hj₂ ⟩, hj₃ ⟩ := h.1;
      refine' ⟨ h.2, _, _, _, _ ⟩;
      exact ( s.p.1.getVert j ).1;
      exact ( s.p.1.getVert j ).2.1;
      · cases h : ( s.p.1.getVert j ).2.2 <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
        · grind +suggestions;
        · exact Or.inr ( by rw [ SimpleGraph.Walk.mem_support_iff_exists_getVert ] ; aesop );
      · exact hj₂;
  · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;

/-! ## Bounding extra_at_k using bridge_count_any -/

/-- For each k, extra_at_k ≤ bridge_count_any × narrow_suffix_count. -/
lemma extra_at_k_le_prod (W n k : ℕ) (hk : k ≤ n) :
    extra_at_k W n k ≤ bridge_count_any (W + 1) k * narrow_suffix_count W (n - k) := by
  sorry

/-- The convolution bound in ℕ. -/
lemma extra_count_le_conv_nat (W n : ℕ) :
    extra_count W n ≤ ∑ k ∈ Finset.range (n + 1),
      bridge_count_any (W + 1) k * narrow_suffix_count W (n - k) := by
  rw [extra_count_eq_sum]
  exact Finset.sum_le_sum fun k hk =>
    extra_at_k_le_prod W n k (by exact Finset.mem_range_succ_iff.mp hk)

end
