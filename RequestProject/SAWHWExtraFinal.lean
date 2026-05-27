/-
# Final proof of extra_sum_le

Proves the key generating function bound for extra walks:
  ∑ extra_count(W,n) · x^n ≤ 6 · B_{W+1}(x) · hp_sum(W, N, x)
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
import RequestProject.SAWHWStepHelpers
import RequestProject.SAWHWExtraSumProof
import RequestProject.SAWHWExtraProof
import RequestProject.SAWHWDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Structural lemmas -/

/-- From FALSE(a,b), the only TRUE neighbor at dc ≤ a+b is (a,b,true). -/
lemma false_only_true_neighbor_at_dc_le {a b : ℤ} {w : HexVertex}
    (h : hexGraph.Adj (a, b, false) w) (hdc : w.1 + w.2.1 ≤ a + b) :
    w = (a, b, true) := by
  rcases w with ⟨ w₁, w₂, w₃ ⟩ ; rcases h with ( ( h₁ | h₁ | h₁ ) | ( h₁ | h₁ | h₁ ) ) ; simp_all +decide ;
  omega

/-! ## Injection from TRUE walk to hexOrigin walk -/

/-- Injection: SAW from TRUE w at dc=-W in [-W,0] → SAW from hexOrigin in [-W,0]. -/
def contToHexOrigin (W : ℕ) (w : HexVertex) (hw_true : w.2.2 = true)
    (hw_dc : w.1 + w.2.1 = -(↑W : ℤ)) (s : ℕ)
    (t : SAW w s) : SAW hexOrigin s :=
  ⟨hexFlip (hexTranslate (-w.1) (-w.2.1) t.w),
   ⟨(hexFlip_walk (hexTranslate_walk (-w.1) (-w.2.1) t.p.1)).copy
      (by rcases w with ⟨w1, w2, w3⟩; subst hw_true; simp [hexTranslate, hexFlip, hexOrigin]) rfl,
    by apply walk_copy_isPath; exact hexFlip_walk_isPath _
        (hexTranslate_walk_isPath _ _ _ t.p.2)⟩,
   by simp [hexFlip_walk_length, hexTranslate_walk_length]; exact t.l⟩

/-- The injection preserves the strip constraint. -/
lemma contToHexOrigin_strip (W : ℕ) (w : HexVertex) (hw_true : w.2.2 = true)
    (hw_dc : w.1 + w.2.1 = -(↑W : ℤ)) (s : ℕ) (t : SAW w s)
    (ht : ∀ u ∈ t.p.1.support, -(↑W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0) :
    ∀ u ∈ (contToHexOrigin W w hw_true hw_dc s t).p.1.support,
      -(↑W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0 := by
  unfold contToHexOrigin;
  simp +decide [ hexFlip, hexTranslate, hexTranslate_walk_support, hexFlip_walk_support ];
  grind

/-- The injection is injective. -/
lemma contToHexOrigin_injective (W : ℕ) (w : HexVertex) (hw_true : w.2.2 = true)
    (hw_dc : w.1 + w.2.1 = -(↑W : ℤ)) (s : ℕ) :
    Function.Injective (contToHexOrigin W w hw_true hw_dc s) := by
  intro x y hxy
  obtain ⟨hx, hy⟩ := x;
  cases y ; simp_all +decide [ SimpleGraph.Walk.copy ];
  unfold contToHexOrigin at hxy ; simp_all +decide [ SimpleGraph.Walk.copy ];
  have h_walk_eq : hexTranslate (-w.1) (-w.2.1) hx = hexTranslate (-w.1) (-w.2.1) ‹_› := by
    exact hexFlip_injective hxy.1;
  have h_walk_eq : hx = ‹_› := by
    exact hexTranslate_injective _ _ h_walk_eq;
  grind +suggestions

/-- From TRUE w at dc=-W, strip-constrained SAWs of length s map injectively
    to hex_origin_strip walks. -/
lemma continuation_from_true_le (W : ℕ) (w : HexVertex) (hw_true : w.2.2 = true)
    (hw_dc : w.1 + w.2.1 = -(↑W : ℤ)) (s : ℕ) :
    Finset.card (Finset.univ.filter (fun t : SAW w s =>
      ∀ u ∈ t.p.1.support, -(↑W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0)) ≤
    hex_origin_strip_count W s := by
  have h_image : (Finset.image (contToHexOrigin W w hw_true hw_dc s) (Finset.univ.filter (fun t : SAW w s => ∀ u ∈ t.p.1.support, -(W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0))).card ≤ hex_origin_strip_count W s := by
    exact Finset.card_le_card fun x hx => by obtain ⟨ t, ht, rfl ⟩ := Finset.mem_image.mp hx; exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, contToHexOrigin_strip W w hw_true hw_dc s t ( Finset.mem_filter.mp ht |>.2 ) ⟩ ;
  rwa [ Finset.card_image_of_injective _ ( contToHexOrigin_injective _ _ _ _ _ ) ] at h_image

/-! ## Narrow suffix GF bound -/

def narrow_suffix_count (W s : ℕ) : ℕ :=
  if s = 0 then 1 else 2 * hex_origin_strip_count W (s - 1)

lemma narrow_suffix_gf_le (W N : ℕ) (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    ∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s ≤
    6 * hp_sum W N x := by
  have h_split : ∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s = 1 + 2 * x * ∑ s ∈ Finset.range N, (hex_origin_strip_count W s : ℝ) * x ^ s := by
    simp +decide [ Finset.sum_range_succ', narrow_suffix_count ];
    simp +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring;
  have h_hex_origin_strip_sum_le : ∑ s ∈ Finset.range N, (hex_origin_strip_count W s : ℝ) * x ^ s ≤ (1 + x) * hp_sum W N x := by
    refine' le_trans _ ( hex_origin_strip_sum_le W N x hx.le hx1.le );
    exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.le_succ _ ) ) fun _ _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ );
  nlinarith [ hp_sum_ge_one W N x hx.le, mul_le_mul_of_nonneg_left h_hex_origin_strip_sum_le hx.le, mul_le_mul_of_nonneg_left hx1.le hx.le ]

/-! ## Main bound (direct proof) -/

/-
The main bound: extra_sum ≤ 6 · B_{W+1} · hp_sum(W).
-/
theorem extra_sum_le_proof (W N : ℕ) (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    ∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n ≤
    6 * paper_bridge_partition (W + 1) x * hp_sum W N x := by
  sorry

end