/-
# SAW sum bound via half-plane decomposition
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWHWStructural
import RequestProject.SAWHWLastVertex
import RequestProject.SAWHWMinDC
import RequestProject.SAWHWHalfPlane
import RequestProject.SAWHWExtraProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-- SAWs from paperStart staying in dc ≥ 0. -/
def saw_count_nonneg_dc (n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun s : SAW paperStart n =>
    ∀ v ∈ s.p.1.support, 0 ≤ v.1 + v.2.1))

/-- SAWs from paperStart that visit dc < 0. -/
def saw_count_neg_dc (n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun s : SAW paperStart n =>
    ∃ v ∈ s.p.1.support, v.1 + v.2.1 < 0))

lemma saw_count_split (n : ℕ) :
    saw_count n = saw_count_nonneg_dc n + saw_count_neg_dc n := by
  rw [ ← saw_count_vertex_independent ];
  swap;
  exact paperStart;
  unfold saw_count_nonneg_dc saw_count_neg_dc;
  rw [ ← Finset.card_union_of_disjoint ];
  · convert rfl;
    convert Finset.card_univ;
    grind;
  · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by obtain ⟨ v, hv₁, hv₂ ⟩ := ‹_›; linarith [ ‹∀ v ∈ ( _ : hexGraph.Walk _ _ ).support, 0 ≤ v.1 + v.2.1› v hv₁ ] ;

lemma saw_nonneg_le_hex_strip (N n : ℕ) (hn : n ≤ N) :
    saw_count_nonneg_dc n ≤ hex_origin_strip_count N n := by
  -- Define the function that maps a SAW from paperStart to hexOrigin via hexFlip.
  set f : SAW paperStart n → SAW hexOrigin n := fun s => ⟨hexFlip s.w, ⟨hexFlip_walk s.p.1, hexFlip_walk_isPath s.p.1 s.p.2⟩, by rw [hexFlip_walk_length]; exact s.l⟩;
  -- Show that $f$ maps SAWs from paperStart to hexOrigin via hexFlip.
  have hf_map : ∀ s : SAW paperStart n, (∀ v ∈ s.p.1.support, 0 ≤ v.1 + v.2.1) → (∀ v ∈ (f s).p.1.support, -(N : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) := by
    intro s hs v hv; rw [ hexFlip_walk_support ] at hv; obtain ⟨ u, hu, rfl ⟩ := List.mem_map.mp hv; specialize hs u hu; specialize hs; specialize hs; simp_all +decide [ hexFlip ] ;
    constructor <;> linarith [ saw_vertex_dc_bound s u hu ];
  convert Set.card_le_card ( show ( Set.image f { s : SAW paperStart n | ∀ v ∈ s.p.1.support, 0 ≤ v.1 + v.2.1 } ) ⊆ { s : SAW hexOrigin n | ∀ v ∈ s.p.1.support, -↑N ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0 } from ?_ ) using 1;
  · rw [ Set.card_image_of_injective ];
    · rw [ Fintype.card_of_subtype ];
      convert rfl;
      grind +splitImp;
    · intro s t h_eq;
      injection h_eq with h₁ h₂;
      exact saw_flip_injective ( show f s = f t from by cases s; cases t; aesop );
  · unfold hex_origin_strip_count; simp +decide [ Fintype.card_subtype ] ;
  · exact Set.image_subset_iff.mpr hf_map

/-- SAWs visiting dc < 0: convolution bound. -/
lemma saw_neg_le_hp_conv (N n : ℕ) (hn : n ≤ N) :
    (saw_count_neg_dc n : ℝ) ≤
    ∑ k ∈ Finset.range (n + 1), (hp_walk_count N k : ℝ) * (hp_walk_count N (n - k) : ℝ) := by
  sorry

/-
Derive saw_sum_le_hp_sq from the helpers.
-/
theorem saw_sum_le_hp_sq_proof {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (hp_sum N N x) ^ 2 := by
  sorry

end