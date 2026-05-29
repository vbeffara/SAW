/-
# Base definitions and lemmas for the convolution bound.
# Extracted from SAWHWConvBound to break circular imports.
-/

import Mathlib
import RequestProject.SAWHWStepHelpers

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 8000000

/-! ## Decomposition of extra walks at lastDCIndex -/

def extra_at_k (W n k : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun s : SAW paperStart n =>
    (∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) ∧
    (∃ h : ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ),
      lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h = k)))

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

lemma extra_at_k_le_prod_eq (W n : ℕ) :
    extra_at_k W n n ≤ bridge_count_any (W + 1) n := by
  refine Finset.card_mono ?_
  intro s hs
  obtain ⟨hs_strip, h_exists, hk_eq⟩ := Finset.mem_filter.mp hs |>.2
  have h_w : s.w.1 + s.w.2.1 = -(W + 1 : ℤ) := by
    have h_last_vert : s.p.1.getVert n = s.w := by
      convert s.l ▸ SimpleGraph.Walk.getVert_length _
    grind +suggestions
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, h_w, hs_strip⟩

lemma suffix_drop_narrow (W n k : ℕ) (s : SAW paperStart n)
    (hs_strip : ∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
    (h_exists : ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ))
    (hk_eq : lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h_exists = k)
    (hk_lt : k < n) (j : ℕ) (hj_pos : 0 < j) (hj_le : j ≤ n - k) :
    -(↑W : ℤ) ≤ ((s.p.1.drop k).getVert j).1 + ((s.p.1.drop k).getVert j).2.1 ∧
    ((s.p.1.drop k).getVert j).1 + ((s.p.1.drop k).getVert j).2.1 ≤ 0 := by
  convert suffix_after_lastDCIndex_in_narrow _ s.p.2 _ _ _ _ ( k + j ) _ _ using 1
  any_goals exact W
  any_goals assumption
  · simp +decide [ SimpleGraph.Walk.getVert ]
  · simp +decide [ SimpleGraph.Walk.getVert ]
  · exact hk_eq.symm ▸ by linarith [ s.l ]
  · linarith [ s.l, Nat.sub_add_cancel hk_lt.le ]
  · grind

lemma saw_eq_of_support (n : ℕ) (s₁ s₂ : SAW paperStart n)
    (h_support : s₁.p.1.support = s₂.p.1.support) :
    s₁ = s₂ := by
  have h_unique_support : ∀ p q : hexGraph.Path paperStart s₁.w, p.1.support = q.1.support → p = q := by
    intros p q hpq
    have h_unique_support : p.1 = q.1 := by
      exact?
    exact Subtype.ext h_unique_support;
  by_cases h : s₁.w = s₂.w <;> simp_all +decide [ Finset.ext_iff ];
  · cases s₁ ; cases s₂ ; aesop;
  · replace h_support := congr_arg List.getLast? h_support ; simp_all +decide [ List.getLast?_eq_some_getLast ] ;

lemma walk_support_take_drop {v w : HexVertex} (p : hexGraph.Walk v w) (k : ℕ)
    (hk : k ≤ p.length) :
    p.support = (p.take k).support ++ (p.drop k).support.tail := by
  convert congr_arg _ ( SimpleGraph.Walk.take_spec _ _ ) using 1;
  any_goals exact hexGraph;
  rotate_left;
  convert rfl;
  convert SimpleGraph.Walk.support_append _ _ using 1;
  exact inferInstance;
  exact p.getVert k;
  all_goals norm_num [ SimpleGraph.Walk.getVert ]

lemma suffix_fiber_injective (n k : ℕ)
    (s₁ s₂ : SAW paperStart n)
    (hk₁ : k ≤ s₁.p.1.length) (hk₂ : k ≤ s₂.p.1.length)
    (h_take_support : (s₁.p.1.take k).support = (s₂.p.1.take k).support)
    (h_drop_support : (s₁.p.1.drop k).support = (s₂.p.1.drop k).support) :
    s₁ = s₂ := by
  apply saw_eq_of_support;
  convert congr_arg₂ ( fun x y => x ++ List.tail y ) h_take_support h_drop_support using 1;
  · convert walk_support_take_drop _ _ hk₁ using 1;
  · convert walk_support_take_drop _ _ hk₂ using 1

end
