/-
# Helper lemmas for the hp_sum_step proof
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary
import RequestProject.SAWHWStructural
import RequestProject.SAWHWBridgeExtractProof
import RequestProject.SAWHWBound
import RequestProject.SAWHWHalfPlane
import RequestProject.SAWHWLastVertex

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Splitting hp_walk_count -/

def extra_count (W n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun s : SAW paperStart n =>
    (∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) ∧
    (∃ v ∈ s.p.1.support, v.1 + v.2.1 = -(↑(W + 1) : ℤ))))

lemma hp_walk_count_split (W n : ℕ) :
    hp_walk_count (W + 1) n = hp_walk_count W n + extra_count W n := by
  unfold hp_walk_count extra_count;
  rw [ ← Finset.card_union_of_disjoint ];
  · congr with s; grind
  · simp +contextual [ Finset.disjoint_left ]; grind

lemma hp_sum_split (W N : ℕ) (x : ℝ) :
    hp_sum (W + 1) N x = hp_sum W N x +
    ∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n := by
  simp only [hp_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by
    rw [hp_walk_count_split]; push_cast; ring

/-! ## hexOrigin neighbors in strip -/

lemma hexOrigin_only_neighbor_in_strip {w : HexVertex}
    (h : hexGraph.Adj hexOrigin w) (hw : w.1 + w.2.1 ≤ 0) :
    w = paperStart := by
  unfold hexGraph hexOrigin at *; simp at h
  rcases w with ⟨w1, w2, wb⟩
  rcases h with ⟨_, _, h3 | h3 | h3⟩ | ⟨_, _, _⟩
  all_goals simp_all [paperStart]; all_goals omega

/-! ## Walk.copy helper -/

lemma walk_copy_isPath {G : SimpleGraph V} {u v u' v' : V}
    (p : G.Walk u v) (hu : u = u') (hv : v = v') (hp : p.IsPath) :
    (p.copy hu hv).IsPath := by
  subst hu; subst hv; rwa [SimpleGraph.Walk.copy_rfl_rfl]

/-! ## hex_origin_strip_count and injection -/

def hex_origin_strip_count (W m : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun s : SAW hexOrigin m =>
    ∀ v ∈ s.p.1.support, -(W : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0))

lemma hex_origin_strip_zero (W : ℕ) : hex_origin_strip_count W 0 = 1 := by
  refine' Finset.card_eq_one.mpr _
  use ⟨ hexOrigin, ⟨ SimpleGraph.Walk.nil, by
    simp +decide [ SimpleGraph.Walk.isPath_def ] ⟩, rfl ⟩
  generalize_proofs at *
  ext ⟨ w, p, l ⟩ ; simp +decide [ SAW ]
  rcases p with ⟨ _ | ⟨ _, _ ⟩, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.length ]
  unfold hexOrigin; aesop

/-- The injection: drop the first step from a strip-constrained SAW from hexOrigin. -/
def dropFirstHexSub (W m : ℕ) :
    { s : SAW hexOrigin (m + 1) //
      ∀ v ∈ s.p.1.support, -(W : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0 } →
    { s : SAW paperStart m //
      ∀ v ∈ s.p.1.support, -(W : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0 } := by
  intro ⟨⟨w, ⟨p, hp⟩, hl⟩, hs⟩
  cases p with
  | nil => exfalso; simp at hl
  | cons hadj rest =>
    rename_i u
    have hu : u = paperStart :=
      hexOrigin_only_neighbor_in_strip hadj
        (hs u (List.mem_cons.mpr (Or.inr (SimpleGraph.Walk.start_mem_support rest)))).2
    subst hu
    refine ⟨⟨w, ⟨rest, ((SimpleGraph.Walk.cons_isPath_iff hadj rest).mp hp).1⟩,
      by simp at hl; omega⟩, ?_⟩
    intro v hv
    exact hs v (List.mem_cons.mpr (Or.inr hv))

/-- The injection is injective. -/
lemma dropFirstHexSub_injective (W m : ℕ) :
    Function.Injective (dropFirstHexSub W m) := by
  intro ⟨ s₁, hs₁ ⟩ ⟨ s₂, hs₂ ⟩ h_eq
  obtain ⟨w₁, ⟨p₁, hp₁⟩, hl₁⟩ := s₁
  obtain ⟨w₂, ⟨p₂, hp₂⟩, hl₂⟩ := s₂
  cases p₁ with
  | nil => simp at hl₁
  | cons hadj₁ rest₁ =>
    cases p₂ with
    | nil => simp at hl₂
    | cons hadj₂ rest₂ =>
      rename_i u₁ u₂_eq;
      have hu₁ : u₁ = paperStart := by
        apply hexOrigin_only_neighbor_in_strip hadj₁ (hs₁ u₁ (by simp)).2
      have hu₂_eq : u₂_eq = paperStart := by
        apply hexOrigin_only_neighbor_in_strip hadj₂ (hs₂ u₂_eq (by simp [SimpleGraph.Walk.support_cons])).2
      subst hu₁
      subst hu₂_eq;
      grind +locals

/-- hex_origin_strip_count(W, m) ≤ hp_walk_count(W, m-1) for m ≥ 1. -/
lemma hex_origin_strip_le_hp (W : ℕ) (m : ℕ) (hm : 1 ≤ m) :
    hex_origin_strip_count W m ≤ hp_walk_count W (m - 1) := by
  rcases m with _ | m; · omega
  simp only [hex_origin_strip_count, hp_walk_count]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_le_of_injective (dropFirstHexSub W m) (dropFirstHexSub_injective W m)

/-! ## hp_sum_step -/

/-
hp_walk_count(W, 0) = 1 (the trivial walk).
-/
lemma hp_walk_count_zero (W : ℕ) : hp_walk_count W 0 = 1 := by
  convert Finset.card_eq_one.mpr _;
  use ⟨ paperStart, ⟨ .nil, by
    exact? ⟩, rfl ⟩
  generalize_proofs at *;
  ext ⟨w, ⟨p, hp⟩, hl⟩; simp [paperStart];
  rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> simp_all +decide

/-
hp_sum(W, N, x) ≥ 1 for x ≥ 0.
-/
lemma hp_sum_ge_one (W N : ℕ) (x : ℝ) (hx : 0 ≤ x) : 1 ≤ hp_sum W N x := by
  refine' le_trans _ ( Finset.single_le_sum ( fun n _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx n ) ) ( Finset.mem_range.mpr ( Nat.succ_pos N ) ) );
  norm_num [ hp_walk_count_zero ]

/-! ## Bridge/suffix infrastructure for extra_sum_le -/

/-- From FALSE(a,b), the only TRUE neighbor at dc ≤ a+b is (a,b,true). -/
lemma false_only_true_neighbor_at_dc_le' {a b : ℤ} {w : HexVertex}
    (h : hexGraph.Adj (a, b, false) w) (hdc : w.1 + w.2.1 ≤ a + b) :
    w = (a, b, true) := by
  rcases w with ⟨ w₁, w₂, w₃ ⟩ ; rcases h with ( ( h₁ | h₁ | h₁ ) | ( h₁ | h₁ | h₁ ) ) ; simp_all +decide ;
  omega

/-- Injection: SAW from TRUE w at dc=-W in [-W,0] → SAW from hexOrigin in [-W,0]. -/
def contToHexOrigin' (W : ℕ) (w : HexVertex) (hw_true : w.2.2 = true)
    (hw_dc : w.1 + w.2.1 = -(↑W : ℤ)) (s : ℕ)
    (t : SAW w s) : SAW hexOrigin s :=
  ⟨hexFlip (hexTranslate (-w.1) (-w.2.1) t.w),
   ⟨(hexFlip_walk (hexTranslate_walk (-w.1) (-w.2.1) t.p.1)).copy
      (by rcases w with ⟨w1, w2, w3⟩; subst hw_true; simp [hexTranslate, hexFlip, hexOrigin]) rfl,
    by apply walk_copy_isPath; exact hexFlip_walk_isPath _
        (hexTranslate_walk_isPath _ _ _ t.p.2)⟩,
   by simp [hexFlip_walk_length, hexTranslate_walk_length]; exact t.l⟩

/-- The injection preserves the strip constraint. -/
lemma contToHexOrigin_strip' (W : ℕ) (w : HexVertex) (hw_true : w.2.2 = true)
    (hw_dc : w.1 + w.2.1 = -(↑W : ℤ)) (s : ℕ) (t : SAW w s)
    (ht : ∀ u ∈ t.p.1.support, -(↑W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0) :
    ∀ u ∈ (contToHexOrigin' W w hw_true hw_dc s t).p.1.support,
      -(↑W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0 := by
  unfold contToHexOrigin';
  simp +decide [ hexFlip, hexTranslate, hexTranslate_walk_support, hexFlip_walk_support ];
  grind

/-- The injection is injective. -/
lemma contToHexOrigin_injective' (W : ℕ) (w : HexVertex) (hw_true : w.2.2 = true)
    (hw_dc : w.1 + w.2.1 = -(↑W : ℤ)) (s : ℕ) :
    Function.Injective (contToHexOrigin' W w hw_true hw_dc s) := by
  intro x y hxy
  obtain ⟨hx, hy⟩ := x;
  cases y ; simp_all +decide [ SimpleGraph.Walk.copy ];
  unfold contToHexOrigin' at hxy ; simp_all +decide [ SimpleGraph.Walk.copy ];
  have h_walk_eq : hexTranslate (-w.1) (-w.2.1) hx = hexTranslate (-w.1) (-w.2.1) ‹_› := by
    exact hexFlip_injective hxy.1;
  have h_walk_eq : hx = ‹_› := by
    exact hexTranslate_injective _ _ h_walk_eq;
  grind +suggestions

/-- From TRUE w at dc=-W, strip-constrained SAWs of length s map injectively
    to hex_origin_strip walks. -/
lemma continuation_from_true_le' (W : ℕ) (w : HexVertex) (hw_true : w.2.2 = true)
    (hw_dc : w.1 + w.2.1 = -(↑W : ℤ)) (s : ℕ) :
    Finset.card (Finset.univ.filter (fun t : SAW w s =>
      ∀ u ∈ t.p.1.support, -(↑W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0)) ≤
    hex_origin_strip_count W s := by
  have h_image : (Finset.image (contToHexOrigin' W w hw_true hw_dc s) (Finset.univ.filter (fun t : SAW w s => ∀ u ∈ t.p.1.support, -(W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0))).card ≤ hex_origin_strip_count W s := by
    exact Finset.card_le_card fun x hx => by obtain ⟨ t, ht, rfl ⟩ := Finset.mem_image.mp hx; exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, contToHexOrigin_strip' W w hw_true hw_dc s t ( Finset.mem_filter.mp ht |>.2 ) ⟩ ;
  rwa [ Finset.card_image_of_injective _ ( contToHexOrigin_injective' _ _ _ _ _ ) ] at h_image

/-! ## Narrow suffix infrastructure -/

/-- Suffix count bound from FALSE vertex at dc=-(W+1). -/
def narrow_suffix_count (W s : ℕ) : ℕ :=
  if s = 0 then 1 else 2 * hex_origin_strip_count W (s - 1)

/-
From FALSE(a,b) at dc=-(W+1), the valid TRUE neighbors staying in [-W, 0]
    are exactly (a+1,b,true) and (a,b+1,true), both at dc=-W.
-/
lemma false_neighbors_in_strip (W : ℕ) (v : HexVertex)
    (hv_false : v.2.2 = false) (hv_dc : v.1 + v.2.1 = -(↑(W + 1) : ℤ))
    {w : HexVertex} (hadj : hexGraph.Adj v w)
    (hw_strip : -(↑W : ℤ) ≤ w.1 + w.2.1 ∧ w.1 + w.2.1 ≤ 0) :
    w = (v.1 + 1, v.2.1, true) ∨ w = (v.1, v.2.1 + 1, true) := by
  rcases v with ⟨ a, b, v ⟩ ; rcases w with ⟨ c, d, w ⟩ ; (rcases hadj with ⟨ hadj₁ | hadj₁ | hadj₁ | hadj₁, hadj₂ ⟩ ) <;> simp_all +decide [ hexGraph ] ;
  omega

/-
Number of SAWs of length s from any FALSE v at dc=-(W+1) staying in [-W, 0]
    is at most narrow_suffix_count(W, s).
-/
lemma suffix_from_false_le (W s : ℕ) (v : HexVertex)
    (hv_false : v.2.2 = false) (hv_dc : v.1 + v.2.1 = -(↑(W + 1) : ℤ)) :
    Finset.card (Finset.univ.filter (fun t : SAW v s =>
      ∀ u ∈ t.p.1.support, -(↑W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0)) ≤
    narrow_suffix_count W s := by
  by_cases hs : s = 0;
  · subst hs;
    rw [ Finset.card_eq_zero.mpr ];
    · exact Nat.zero_le _;
    · ext ⟨ w, ⟨ p, hp ⟩, hl ⟩ ; simp_all +decide [ SimpleGraph.Walk.support ];
      cases p <;> aesop;
  · -- For any FALSE v at dc = -(W+1), the first step from v must be to either (v.1 + 1, v.2.1, true) or (v.1, v.2.1 + 1, true).
    have h_first_step : ∀ t : SAW v s, (∀ u ∈ t.p.1.support, -(W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0) → t.p.1.length > 0 → t.p.1.getVert 1 = (v.1 + 1, v.2.1, true) ∨ t.p.1.getVert 1 = (v.1, v.2.1 + 1, true) := by
      intro t ht ht_pos
      obtain ⟨w, hw⟩ : ∃ w, t.p.1.getVert 1 = w ∧ hexGraph.Adj v w ∧ -(W : ℤ) ≤ w.1 + w.2.1 ∧ w.1 + w.2.1 ≤ 0 := by
        rcases t with ⟨ w, ⟨ p, hp ⟩, hl ⟩ ; rcases p with ( _ | ⟨ hadj, p ⟩ ) <;> simp_all +decide ;
      have := false_neighbors_in_strip W v hv_false hv_dc hw.2.1 hw.2.2; aesop;
    -- By partitioning the set of SAWs based on the first step, we can bound the cardinality.
    have h_partition : Finset.card (Finset.filter (fun t : SAW v s => ∀ u ∈ t.p.1.support, -(W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0) Finset.univ) ≤ Finset.card (Finset.filter (fun t : SAW (v.1 + 1, v.2.1, true) (s - 1) => ∀ u ∈ t.p.1.support, -(W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0) Finset.univ) + Finset.card (Finset.filter (fun t : SAW (v.1, v.2.1 + 1, true) (s - 1) => ∀ u ∈ t.p.1.support, -(W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0) Finset.univ) := by
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact ∅;
      · intro t ht; specialize h_first_step t; simp_all +decide [ Finset.subset_iff ] ;
        specialize ht v.1 v.2.1 ; simp_all +decide [ SimpleGraph.Walk.support ];
        exact ht.1 ( by cases t ; aesop );
      · norm_num;
    convert h_partition.trans _ using 1;
    convert add_le_add ( continuation_from_true_le' W ( v.1 + 1, v.2.1, true ) rfl ?_ ( s - 1 ) ) ( continuation_from_true_le' W ( v.1, v.2.1 + 1, true ) rfl ?_ ( s - 1 ) ) using 1 <;> norm_num [ hv_false, hv_dc ];
    · unfold narrow_suffix_count; cases s <;> simp +decide [ * ] ; ring;
      · contradiction;
      · ring;
    · grind;
    · grind

/-! ## Generating function bounds -/

/-- hp_walk_count is monotone in width. -/
lemma hp_walk_count_mono' {W W' : ℕ} (h : W ≤ W') (n : ℕ) :
    hp_walk_count W n ≤ hp_walk_count W' n := by
  refine' Finset.card_le_card _; grind

/-
The hex_origin_strip GF ≤ (1+x) · hp_sum.
-/
lemma hex_origin_strip_sum_le' (W N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑ k ∈ Finset.range (N + 1), (hex_origin_strip_count W k : ℝ) * x ^ k ≤
    (1 + x) * hp_sum W N x := by
  -- Split the sum: k=0 term equals 1 (by hex_origin_strip_zero).
  have h_split : ∑ k ∈ Finset.range (N + 1), (hex_origin_strip_count W k : ℝ) * x ^ k = 1 + ∑ k ∈ Finset.Ico 1 (N + 1), (hex_origin_strip_count W k : ℝ) * x ^ k := by
    rw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ hex_origin_strip_zero ];
  -- For k ≥ 1, use hex_origin_strip_le_hp to get hex_origin_strip_count(W, k) ≤ hp_walk_count(W, k-1).
  have h_bound : ∑ k ∈ Finset.Ico 1 (N + 1), (hex_origin_strip_count W k : ℝ) * x ^ k ≤ x * ∑ k ∈ Finset.Ico 1 (N + 1), (hp_walk_count W (k - 1) : ℝ) * x ^ (k - 1) := by
    rw [ Finset.mul_sum _ _ _ ];
    refine Finset.sum_le_sum fun i hi => ?_;
    rw [ show x ^ i = x * x ^ ( i - 1 ) by rw [ ← pow_succ', Nat.sub_add_cancel ( Finset.mem_Ico.mp hi |>.1 ) ] ];
    nlinarith only [ show ( hex_origin_strip_count W i : ℝ ) ≤ hp_walk_count W ( i - 1 ) by exact_mod_cast hex_origin_strip_le_hp W i ( Finset.mem_Ico.mp hi |>.1 ), show 0 ≤ x * x ^ ( i - 1 ) by positivity ];
  -- Factor out x and compare with hp_sum.
  have h_factor : ∑ k ∈ Finset.Ico 1 (N + 1), (hp_walk_count W (k - 1) : ℝ) * x ^ (k - 1) ≤ hp_sum W N x := by
    rw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, hp_sum ] ;
    exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.le_succ _ ) ) fun _ _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx _ );
  nlinarith [ hp_sum_ge_one W N x hx ]

/-
The narrow suffix GF ≤ 6 · hp_sum.
-/
lemma narrow_suffix_gf_le' (W N : ℕ) (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    ∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s ≤
    6 * hp_sum W N x := by
  -- Split the sum: s=0 term is 1. For s≥1: narrow_suffix_count(W,s) = 2*hex_origin_strip_count(W,s-1).
  have h_split : ∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s = 1 + 2 * x * ∑ k ∈ Finset.range N, (hex_origin_strip_count W k : ℝ) * x ^ k := by
    norm_num [ Finset.sum_range_succ', narrow_suffix_count ];
    simp +decide only [pow_succ', mul_left_comm, mul_assoc, add_comm, Finset.mul_sum _ _ _];
  -- By hex_origin_strip_sum_le', Σ hex_origin_strip_count(W,k)*x^k ≤ (1+x)*hp_sum.
  have h_hex_origin_strip_sum_le : ∑ k ∈ Finset.range N, (hex_origin_strip_count W k : ℝ) * x ^ k ≤ (1 + x) * hp_sum W N x := by
    exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.le_succ _ ) ) fun _ _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ ) ) ( hex_origin_strip_sum_le' W N x hx.le hx1.le );
  nlinarith [ mul_le_mul_of_nonneg_left hx1.le hx.le, hp_sum_ge_one W N x hx.le, mul_le_mul_of_nonneg_left hx1.le ( show 0 ≤ hp_sum W N x from hp_sum_nonneg W N x hx.le ) ]

/-! ## Bridge infrastructure -/

/-- The number of SAWs from paperStart of length k that are "bridge-like":
    endpoint at dc=-T (FALSE), all vertices in [-(T:ℤ), 0]. -/
def bridge_count (T k : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun s : SAW paperStart k =>
    s.w.1 + s.w.2.1 = -(T : ℤ) ∧ s.w.2.2 = false ∧
    ∀ v ∈ s.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0))

/-- Construct a PaperBridge from a bridge-type SAW. -/
def saw_to_bridge (T : ℕ) (hT : 1 ≤ T) (k : ℕ) (s : SAW paperStart k)
    (hs_dc : s.w.1 + s.w.2.1 = -(T : ℤ))
    (hs_false : s.w.2.2 = false)
    (hs_strip : ∀ v ∈ s.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) :
    PaperBridge T :=
  ⟨s.w, s.p, ⟨hs_dc, hs_false⟩,
   bridge_satisfies_paper_inf_strip T hT s.p hs_false hs_dc hs_strip⟩

/-
saw_to_bridge is injective.
-/
lemma saw_to_bridge_injective (T : ℕ) (hT : 1 ≤ T) (k : ℕ)
    (s₁ s₂ : SAW paperStart k)
    (h₁_dc : s₁.w.1 + s₁.w.2.1 = -(T : ℤ)) (h₂_dc : s₂.w.1 + s₂.w.2.1 = -(T : ℤ))
    (h₁_f : s₁.w.2.2 = false) (h₂_f : s₂.w.2.2 = false)
    (h₁_s : ∀ v ∈ s₁.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
    (h₂_s : ∀ v ∈ s₂.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
    (h_eq : saw_to_bridge T hT k s₁ h₁_dc h₁_f h₁_s =
            saw_to_bridge T hT k s₂ h₂_dc h₂_f h₂_s) :
    s₁ = s₂ := by
  cases s₁ ; cases s₂ ; simp_all +decide [ saw_to_bridge ]

/-
Bridge partition is summable for x ≤ xc.
-/
lemma bridge_summable (T : ℕ) (hT : 1 ≤ T) (x : ℝ) (hx : 0 < x) (hxc : x ≤ xc) :
    Summable (fun b : PaperBridge T => x ^ b.walk.1.length) := by
  -- Since $x \leq xc$, we have $x^b.length \leq xc^b.length$ for all $b$.
  have h_le : ∀ b : PaperBridge T, x ^ (b.walk.1.length) ≤ xc ^ (b.walk.1.length) := by
    exact fun b => pow_le_pow_left₀ hx.le hxc _;
  refine' Summable.of_nonneg_of_le ( fun b => by positivity ) ( fun b => h_le b ) _;
  refine' summable_of_sum_le _ _;
  exact 1 / xc;
  · exact fun _ => pow_nonneg ( by exact div_nonneg zero_le_one ( by positivity ) ) _;
  · convert paper_bridge_partial_sum_le T hT using 1

/-- For each k, there exists a Finset of PaperBridges matching bridge_count. -/
lemma bridge_inject_paper (T k : ℕ) (hT : 1 ≤ T) :
    ∃ F : Finset (PaperBridge T), F.card = bridge_count T k ∧
    ∀ b ∈ F, b.walk.1.length = k := by
  classical
  let BS := Finset.univ.filter (fun s : SAW paperStart k =>
    s.w.1 + s.w.2.1 = -(T : ℤ) ∧ s.w.2.2 = false ∧
    ∀ v ∈ s.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
  let f : { s // s ∈ BS } → PaperBridge T := fun ⟨s, hs⟩ =>
    let h := (Finset.mem_filter.mp hs).2
    saw_to_bridge T hT k s h.1 h.2.1 h.2.2
  refine ⟨BS.attach.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective]
    · simp [BS, bridge_count]
    · intro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ h_eq
      simp only [f] at h_eq
      exact Subtype.ext (saw_to_bridge_injective T hT k s₁ s₂
        (Finset.mem_filter.mp hs₁).2.1 (Finset.mem_filter.mp hs₂).2.1
        (Finset.mem_filter.mp hs₁).2.2.1 (Finset.mem_filter.mp hs₂).2.2.1
        (Finset.mem_filter.mp hs₁).2.2.2 (Finset.mem_filter.mp hs₂).2.2.2
        h_eq)
  · intro b hb
    obtain ⟨⟨s, hs⟩, _, rfl⟩ := Finset.mem_image.mp hb
    simp only [f, saw_to_bridge]
    exact s.l

/-- Finite bridge sum ≤ paper_bridge_partition. -/
lemma bridge_gf_le_partition (T : ℕ) (hT : 1 ≤ T) (N : ℕ) (x : ℝ)
    (hx : 0 < x) (hxc : x ≤ xc) :
    ∑ k ∈ Finset.range (N + 1), (bridge_count T k : ℝ) * x ^ k ≤
    paper_bridge_partition T x := by
  classical
  choose F hF_card hF_len using fun k => bridge_inject_paper T k hT
  have h_disj : Set.PairwiseDisjoint (↑(Finset.range (N + 1))) F := by
    intro k₁ hk₁ k₂ hk₂ hne
    simp [Finset.disjoint_left]
    intro b hb₁ hb₂
    exact hne (by have := hF_len k₁ b hb₁; have := hF_len k₂ b hb₂; omega)
  have h_sum_eq : ∑ b ∈ (Finset.range (N + 1)).biUnion F,
      x ^ b.walk.1.length =
      ∑ k ∈ Finset.range (N + 1), (bridge_count T k : ℝ) * x ^ k := by
    rw [Finset.sum_biUnion h_disj]
    exact Finset.sum_congr rfl fun k hk => by
      conv_rhs => rw [← hF_card k]
      rw [Finset.sum_congr rfl fun b hb => by rw [hF_len k b hb]]
      simp [Finset.sum_const]
  rw [← h_sum_eq]
  exact Summable.sum_le_tsum _ (fun _ _ => pow_nonneg hx.le _) (bridge_summable T hT x hx hxc)

/-! ## Extra walk convolution bound -/

-- ExtraAtK not needed; the proof uses extra_count_le_conv directly.

/-- Convert support membership to getVert condition. -/
lemma extra_walk_exists_getVert (W n : ℕ) (s : SAW paperStart n)
    (hs : (∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) ∧
          (∃ v ∈ s.p.1.support, v.1 + v.2.1 = -(↑(W + 1) : ℤ))) :
    ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ) := by
  sorry

/-- The prefix of an extra walk at lastDCIndex satisfies bridge conditions. -/
lemma extra_prefix_bridge (W n : ℕ) (hW : 0 < W) (s : SAW paperStart n)
    (hs_strip : ∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
    (h_exists : ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ))
    (h_not_last : lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h_exists < s.p.1.length) :
    let k := lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h_exists
    ∃ (b : SAW paperStart k),
      b.w.1 + b.w.2.1 = -(↑(W + 1) : ℤ) ∧
      b.w.2.2 = false ∧
      (∀ v ∈ b.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) ∧
      b.p.1.support = (s.p.1.take k).support := by
  sorry

/-- extra_count(W, n) ≤ Σ_k bridge_count(W+1, k) · narrow_suffix_count(W, n-k). -/
lemma extra_count_le_conv (W n : ℕ) :
    (extra_count W n : ℝ) ≤
    ∑ k ∈ Finset.range (n + 1),
      (bridge_count (W + 1) k : ℝ) * (narrow_suffix_count W (n - k) : ℝ) := by
  sorry

/-! ## Cauchy product -/

lemma cauchy_product_le' (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
      (∑ k ∈ Finset.range (n + 1), a k * b (n - k)) * x ^ n ≤
    (∑ n ∈ Finset.range (N + 1), a n * x ^ n) *
    (∑ n ∈ Finset.range (N + 1), b n * x ^ n) := by
  -- Apply the Cauchy product formula to the series.
  have h_cauchy : ∑ n ∈ Finset.range (N + 1), (∑ k ∈ Finset.range (n + 1), a k * b (n - k)) * x ^ n ≤ ∑ k ∈ Finset.range (N + 1), ∑ n ∈ Finset.Ico k (N + 1), a k * b (n - k) * x ^ n := by
    simp +decide only [Finset.sum_mul _ _ _];
    rw [ Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm ];
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ k ∈ Finset.range (N + 1), ∑ n ∈ Finset.Ico k (N + 1), a k * b (n - k) * x ^ n = ∑ k ∈ Finset.range (N + 1), a k * x ^ k * ∑ j ∈ Finset.range (N - k + 1), b j * x ^ j := by
    simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, pow_add, Finset.sum_Ico_eq_sum_range ];
    exact Finset.sum_congr rfl fun i hi => by rw [ Nat.sub_add_comm ( Finset.mem_range_succ_iff.mp hi ) ] ;
  refine le_trans h_cauchy <| h_fubini.le.trans ?_;
  rw [ Finset.sum_mul _ _ _ ];
  exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.succ_le_succ ( Nat.sub_le _ _ ) ) ) fun _ _ _ => mul_nonneg ( hb _ ) ( pow_nonneg hx _ ) ) ( mul_nonneg ( ha _ ) ( pow_nonneg hx _ ) )

/-! ## The main extra sum bound -/

/-- The key generating function bound for extra walks.
    Requires x < xc for bridge partition summability. -/
private lemma extra_sum_le_placeholder (W N : ℕ) (x : ℝ) (hx : 0 < x) (hxc : x < xc) :
    ∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n ≤
    6 * paper_bridge_partition (W + 1) x * hp_sum W N x := by
  have hx1 : x < 1 := lt_trans hxc xc_lt_one
  -- Step 1: extra_count ≤ convolution of bridge_count and narrow_suffix_count
  have h_conv : ∀ n ∈ Finset.range (N + 1),
      (extra_count W n : ℝ) * x ^ n ≤
      (∑ k ∈ Finset.range (n + 1),
        (bridge_count (W + 1) k : ℝ) * (narrow_suffix_count W (n - k) : ℝ)) * x ^ n := by
    intro n _; exact mul_le_mul_of_nonneg_right (extra_count_le_conv W n) (pow_nonneg hx.le _)
  -- Step 2: Apply Cauchy product
  have h_cauchy :
      ∑ n ∈ Finset.range (N + 1),
        (∑ k ∈ Finset.range (n + 1),
          (bridge_count (W + 1) k : ℝ) * (narrow_suffix_count W (n - k) : ℝ)) * x ^ n ≤
      (∑ k ∈ Finset.range (N + 1), (bridge_count (W + 1) k : ℝ) * x ^ k) *
      (∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s) :=
    cauchy_product_le' (fun k => (bridge_count (W + 1) k : ℝ))
      (fun s => (narrow_suffix_count W s : ℝ))
      (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _) x hx.le N
  -- Step 3: Bound bridge GF by paper_bridge_partition
  have h_bridge : ∑ k ∈ Finset.range (N + 1), (bridge_count (W + 1) k : ℝ) * x ^ k ≤
      paper_bridge_partition (W + 1) x :=
    bridge_gf_le_partition (W + 1) (by omega) N x hx hxc.le
  -- Step 4: Bound narrow suffix GF
  have h_suffix : ∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s ≤
      6 * hp_sum W N x :=
    narrow_suffix_gf_le' W N x hx hx1
  -- Combine
  have h_bridge_nn : 0 ≤ paper_bridge_partition (W + 1) x :=
    tsum_nonneg fun _ => pow_nonneg hx.le _
  have h_suffix_nn : 0 ≤ ∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.le _)
  have h_hp_nn : 0 ≤ hp_sum W N x := hp_sum_nonneg W N x hx.le
  calc ∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n
      ≤ ∑ n ∈ Finset.range (N + 1),
          (∑ k ∈ Finset.range (n + 1),
            (bridge_count (W + 1) k : ℝ) * (narrow_suffix_count W (n - k) : ℝ)) * x ^ n :=
        Finset.sum_le_sum h_conv
    _ ≤ (∑ k ∈ Finset.range (N + 1), (bridge_count (W + 1) k : ℝ) * x ^ k) *
        (∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s) := h_cauchy
    _ ≤ paper_bridge_partition (W + 1) x *
        (∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s) :=
        mul_le_mul_of_nonneg_right h_bridge h_suffix_nn
    _ ≤ paper_bridge_partition (W + 1) x * (6 * hp_sum W N x) :=
        mul_le_mul_of_nonneg_left h_suffix h_bridge_nn
    _ = 6 * paper_bridge_partition (W + 1) x * hp_sum W N x := by ring

/-- **Key inductive step** (with constant 6):
    hp_sum(W+1) ≤ (1 + 6 · B_{W+1}) · hp_sum(W). -/
lemma hp_sum_step {x : ℝ} (hx : 0 < x) (hxc : x < xc) (W N : ℕ) :
    hp_sum (W + 1) N x ≤
    (1 + 6 * paper_bridge_partition (W + 1) x) * hp_sum W N x := by
  rw [hp_sum_split]
  have h1 := extra_sum_le_placeholder W N x hx hxc
  have h2 := hp_sum_nonneg W N x hx.le
  nlinarith

/-! ## The inductive bound (product form) -/

/-- Half-plane walk bound:
    hp_sum(W) ≤ 2 · ∏_{T=1}^W (1 + 6·B_T(x)). -/
theorem hp_sum_le_prod {x : ℝ} (hx : 0 < x) (hxc : x < xc) (W N : ℕ) :
    hp_sum W N x ≤
    2 * ∏ T ∈ Finset.range W, (1 + 6 * paper_bridge_partition (T + 1) x) := by
  induction W with
  | zero =>
    simp
    have hx1 : x < 1 := lt_trans hxc xc_lt_one
    linarith [hp_sum_zero_le N x hx.le hx1.le]
  | succ W ih =>
    rw [Finset.prod_range_succ]
    have hB_nn : 0 ≤ paper_bridge_partition (W + 1) x :=
      tsum_nonneg fun _ => pow_nonneg hx.le _
    have hF : 0 ≤ 1 + 6 * paper_bridge_partition (W + 1) x := by linarith
    have hstep := hp_sum_step hx hxc W N
    have h1 : hp_sum (W + 1) N x ≤ (1 + 6 * paper_bridge_partition (W + 1) x) *
        (2 * ∏ T ∈ Finset.range W, (1 + 6 * paper_bridge_partition (T + 1) x)) :=
      le_trans hstep (mul_le_mul_of_nonneg_left ih hF)
    linarith [mul_comm (∏ T ∈ Finset.range W, (1 + 6 * paper_bridge_partition (T + 1) x))
      (1 + 6 * paper_bridge_partition (W + 1) x)]

end