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
import RequestProject.SAWHWStepHelpers
import RequestProject.SAWHWDecomp
import RequestProject.SAWHWDecompFresh
import RequestProject.SAWHWGFBound

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
  set f : SAW paperStart n → SAW hexOrigin n := fun s => ⟨hexFlip s.w, ⟨hexFlip_walk s.p.1, hexFlip_walk_isPath s.p.1 s.p.2⟩, by rw [hexFlip_walk_length]; exact s.l⟩;
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

/-! ## The neg_dc counting bound -/

/-- For a SAW visiting dc < 0, minDCVal is negative. -/
lemma minDCVal_neg_of_visits_neg {n : ℕ} (s : SAW paperStart n)
    (h : ∃ v ∈ s.p.1.support, v.1 + v.2.1 < 0) :
    minDCVal s.p.1 < 0 := by
  obtain ⟨v, hv, hvdc⟩ := h
  obtain ⟨k, hkv, hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
  exact lt_of_le_of_lt (minDCVal_le s.p.1 k hk) (hkv ▸ hvdc)

/-- SAWs visiting dc < 0: convolution bound. -/
lemma saw_neg_le_hp_conv (N n : ℕ) (hn : n ≤ N) :
    (saw_count_neg_dc n : ℝ) ≤
    ∑ k ∈ Finset.range (n + 1), (hp_walk_count N k : ℝ) * (hp_walk_count N (n - k) : ℝ) := by
  unfold saw_count_neg_dc
  exact_mod_cast saw_neg_dc_le_conv_nat N n hn

/-! ## Cauchy product inequality -/

lemma cauchy_product_le (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
      (∑ k ∈ Finset.range (n + 1), a k * b (n - k)) * x ^ n ≤
    (∑ n ∈ Finset.range (N + 1), a n * x ^ n) *
    (∑ n ∈ Finset.range (N + 1), b n * x ^ n) := by
  simp +decide only [mul_comm, Finset.sum_mul];
  have h_interchange : ∑ x_1 ∈ Finset.range (N + 1), x ^ x_1 * ∑ k ∈ Finset.range (x_1 + 1), a k * b (x_1 - k) = ∑ k ∈ Finset.range (N + 1), ∑ x_1 ∈ Finset.Ico k (N + 1), x ^ x_1 * a k * b (x_1 - k) := by
    simp +decide only [Finset.mul_sum _ _ _, mul_assoc];
    rw [ Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm ];
  rw [h_interchange];
  refine' Finset.sum_le_sum fun i hi => _;
  rw [ Finset.mul_sum _ _ _, Finset.sum_Ico_eq_sum_range ];
  simp +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.sub_le _ _ ) ) fun _ _ _ => mul_nonneg ( ha _ ) ( mul_nonneg ( hb _ ) ( mul_nonneg ( pow_nonneg hx _ ) ( pow_nonneg hx _ ) ) )

/-! ## SAW sum ≤ 2 · hp_sum² -/

lemma hp_walk_count_one_ge (W : ℕ) : 1 ≤ hp_walk_count W 1 := by
  refine' Finset.card_pos.mpr _;
  refine' ⟨ ⟨ ( 0, 0, false ), ⟨ SimpleGraph.Walk.cons ( by tauto ) SimpleGraph.Walk.nil, _ ⟩, _ ⟩, _ ⟩ <;> simp +decide [ SimpleGraph.Walk.cons ];
  norm_num [ paperStart ]

lemma hp_sum_ge_one_plus_x (N : ℕ) (hN : 1 ≤ N) (x : ℝ) (hx : 0 ≤ x) : 1 + x ≤ hp_sum N N x := by
  unfold hp_sum;
  rcases N with ( _ | N ) <;> simp_all +decide [ Finset.sum_range_succ' ];
  nlinarith [ show ( hp_walk_count ( N + 1 ) 1 : ℝ ) ≥ 1 by exact_mod_cast hp_walk_count_one_ge _, show ( hp_walk_count ( N + 1 ) 0 : ℝ ) = 1 by exact_mod_cast hp_walk_count_zero _, show ( ∑ k ∈ Finset.range N, ( hp_walk_count ( N + 1 ) ( k + 1 + 1 ) : ℝ ) * x ^ ( k + 1 + 1 ) ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx _ ) ]

theorem saw_sum_le_hp_sq {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (hp_sum N N x) ^ 2 := by
  by_cases hN : N = 0;
  · simp [hN, saw_count, hp_walk_count, hp_sum];
    norm_cast;
    refine' le_trans _ ( Nat.mul_le_mul_left _ <| Nat.one_le_pow _ _ <| Finset.card_pos.mpr _ );
    · refine' le_trans ( Fintype.card_le_one_iff.mpr _ ) _ <;> norm_num;
      rintro ⟨ a, ⟨ p, hp ⟩, hl ⟩ ⟨ b, ⟨ q, hq ⟩, hl' ⟩ ; cases p <;> cases q <;> aesop;
    · refine' ⟨ ⟨ paperStart, ⟨ SimpleGraph.Walk.nil, _ ⟩, _ ⟩, _ ⟩ <;> simp +decide [ hN ];
  · have h_nonneg : ∑ n ∈ Finset.range (N + 1), (saw_count_nonneg_dc n : ℝ) * x ^ n ≤ (1 + x) * hp_sum N N x := by
      refine' le_trans _ ( hex_origin_strip_sum_le N N x hx.le hx1.le );
      exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( mod_cast saw_nonneg_le_hex_strip N i ( Finset.mem_range_succ_iff.mp hi ) ) ( pow_nonneg hx.le _ );
    have h_neg : ∑ n ∈ Finset.range (N + 1), (saw_count_neg_dc n : ℝ) * x ^ n ≤ (hp_sum N N x) ^ 2 := by
      have h_neg : ∑ n ∈ Finset.range (N + 1), (saw_count_neg_dc n : ℝ) * x ^ n ≤ ∑ n ∈ Finset.range (N + 1), (∑ k ∈ Finset.range (n + 1), (hp_walk_count N k : ℝ) * (hp_walk_count N (n - k) : ℝ)) * x ^ n := by
        apply Finset.sum_le_sum;
        exact fun n hn => mul_le_mul_of_nonneg_right ( mod_cast saw_neg_le_hp_conv N n ( Finset.mem_range_succ_iff.mp hn ) ) ( pow_nonneg hx.le _ );
      convert h_neg.trans ( cauchy_product_le ( fun n => hp_walk_count N n ) ( fun n => hp_walk_count N n ) ( fun n => Nat.cast_nonneg _ ) ( fun n => Nat.cast_nonneg _ ) x hx.le N ) using 1 ; norm_num [ hp_sum ] ; ring;
    have h_split : ∀ n, (saw_count n : ℝ) = (saw_count_nonneg_dc n : ℝ) + (saw_count_neg_dc n : ℝ) := by
      exact_mod_cast saw_count_split;
    simp_all +decide [ add_mul, Finset.sum_add_distrib ];
    nlinarith [ hp_sum_ge_one_plus_x N ( Nat.pos_of_ne_zero hN ) x hx.le ]

/-! ## Combined bound -/

theorem hw_injection_bound_correct {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    8 * (∏ T ∈ Finset.range N, (1 + 12 * paper_bridge_partition (T + 1) x)) ^ 2 := by
  have hx1 : x < 1 := lt_trans hxc xc_lt_one
  calc ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n
      ≤ 2 * (hp_sum N N x) ^ 2 := saw_sum_le_hp_sq hx hx1 N
    _ ≤ 2 * (2 * ∏ T ∈ Finset.range N,
          (1 + 12 * paper_bridge_partition (T + 1) x)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pow_le_pow_left₀ (hp_sum_nonneg N N x hx.le)
          (hp_sum_le_prod' hx hxc N N) 2
    _ = 8 * (∏ T ∈ Finset.range N,
          (1 + 12 * paper_bridge_partition (T + 1) x)) ^ 2 := by ring

end
