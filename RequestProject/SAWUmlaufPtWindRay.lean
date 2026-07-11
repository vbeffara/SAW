/-
# Branch-cut telescoping and the avoiding-ray vanishing of `ptWind`

This file develops a strictly more general vanishing criterion for the
point-winding number `ptWind` (from `RequestProject.SAWUmlaufPtWind`) than the
convex half-plane criterion `ptWind_eq_zero_of_halfplane`
(`RequestProject.SAWUmlaufPtWindHalfPlane`).

## The idea

The winding of a closed polygon `V` around `x` is the sweep-angle sum
`ptTurn x (V ++ V.take 1) = Σ arg ((vᵢ₊₁ - x)/(vᵢ - x))`.  If we fix a direction
`e ≠ 0` and every closed edge `(vᵢ, vᵢ₊₁)`, viewed in the rotated coordinates
`w ↦ (w - x)/e`, has the *exact* argument-subtraction property

  `arg ((vᵢ₊₁ - x)/(vᵢ - x)) = arg ((vᵢ₊₁ - x)/e) - arg ((vᵢ - x)/e)`      (R)

(no `2π` wrap), then the closed sweep sum **telescopes to `0`**.  Geometrically
(R) holds for every edge whose segment, in the rotated coordinates, avoids the
non-positive real ray — i.e. every edge of the polygon that does not cross the
ray from `x` in the fixed direction `e`.  This is the "there is a ray from `x`
escaping to infinity without meeting the polygon ⟹ winding `0`" tool, valid for
non-convex polygons (the half-plane criterion is the special case where a whole
open half-plane of directions escapes).

## Contents

* `argSubRel` — the per-edge exact argument-subtraction relation `R` above.
* `ptTurn_telescope_branch` — telescoping of `ptTurn` along a chain of edges each
  satisfying `R`.
* `ptWind_eq_zero_of_chain` — if every closed edge of `V` satisfies `R`, then
  `ptWind x V = 0`.
* `arg_sub_mem_Ioo_of_segment_avoids_neg` — the planar crux (proved): a segment
  avoiding the non-positive real ray subtends `< π` at the origin.
* `argSubRel_of_segment_avoids_neg` — the geometric bridge (proved): `R` holds
  for an edge whose rotated segment avoids the non-positive real ray.
* `ptWind_eq_zero_of_ray_avoids` — the packaged avoiding-ray vanishing lemma.

## Downstream use (NOT a dead branch)

This file is imported by `RequestProject.SAWUmlaufPolygon`.  It is the intended
strengthening of the winding-vanishing step used by the two point-in-polygon
atoms `clipped_ear_ptWind_zero` and `chord_ear_other_ptWind_zero`: a vertex `x`
of the *other* chord piece admits a ray escaping through its own piece without
meeting `P`, so `ptWind x P = 0` even when no separating *line* exists (the
non-convex hull-interior case the half-plane tool cannot reach).
-/

import Mathlib
import RequestProject.SAWUmlaufPtWind
import RequestProject.SAWUmlaufPtWindJordan
import RequestProject.SAWUmlaufPtWindHalfPlane

open Real Complex

noncomputable section

namespace HexArea

set_option maxHeartbeats 4000000

/-- `getLastD` of a two-or-more element list is independent of the supplied
    default (the list is nonempty, so the last element is genuine). -/
lemma getLastD_cons_cons (a b : ℂ) (L : List ℂ) :
    (a :: b :: L).getLastD a = (b :: L).getLastD b := by
  induction L generalizing a b with
  | nil => simp
  | cons c L ih => simp at *; simp [ih]

/-- The per-edge exact argument-subtraction relation, relative to a base point
    `x` and a fixed nonzero direction `e`: the principal sweep argument of the
    edge `(a, b)` from `x` equals the difference of the two rotated position
    arguments (no `2π` wrap). -/
def argSubRel (x e : ℂ) (a b : ℂ) : Prop :=
  Complex.arg ((b - x) / (a - x)) = Complex.arg ((b - x) / e) - Complex.arg ((a - x) / e)

/-- **Telescoping of `ptTurn` along a chain of edges satisfying `argSubRel`.**
    If every consecutive pair of the open chain `a :: L` satisfies the exact
    argument-subtraction relation, the sweep-angle sum collapses to the endpoint
    difference `arg ((last - x)/e) - arg ((a - x)/e)`. -/
lemma ptTurn_telescope_branch (x e : ℂ) :
    ∀ (a : ℂ) (L : List ℂ), List.IsChain (argSubRel x e) (a :: L) →
      ptTurn x (a :: L)
        = Complex.arg (((a :: L).getLastD a - x) / e) - Complex.arg ((a - x) / e) := by
  intro a L
  induction L generalizing a with
  | nil => intro _; simp [ptTurn]
  | cons b L ih =>
      intro hchain
      rw [ptTurn_cons_cons]
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hR, hchain'⟩ := hchain
      rw [hR, ih b hchain', getLastD_cons_cons]
      ring

/-- **Chain vanishing of `ptWind`.**  If every closed edge of the cycle `V`
    (including the wrap-around edge) satisfies the exact argument-subtraction
    relation relative to `(x, e)`, then the winding of `V` around `x` is `0`:
    the closed telescoping sum returns to its starting argument. -/
lemma ptWind_eq_zero_of_chain (x e : ℂ) (V : List ℂ)
    (hchain : List.IsChain (argSubRel x e) (V ++ V.take 1)) :
    ptWind x V = 0 := by
  cases V with
  | nil => simp [ptWind]
  | cons a V =>
      unfold ptWind
      have hform : (a :: V) ++ (a :: V).take 1 = a :: (V ++ [a]) := by
        simp [List.take]
      rw [hform] at hchain ⊢
      rw [ptTurn_telescope_branch x e a (V ++ [a]) hchain]
      have hlast : ((a :: (V ++ [a])).getLastD a) = a := by
        have h2 : a :: (V ++ [a]) = (a :: V) ++ [a] := by simp
        rw [h2, List.getLastD_concat]
      rw [hlast]
      ring

/-
**Isolated planar crux.**  If both endpoints `A, B` are nonzero and the
    segment `[A, B]` avoids the non-positive real ray `{z | z.im = 0 ∧ z.re ≤ 0}`
    (equivalently, the whole segment lies in `Complex.slitPlane`), then the
    *signed* argument difference `B.arg - A.arg` stays strictly within
    `(-π, π)`.  Geometrically a straight segment not meeting the branch cut
    subtends less than a half-turn at the origin.

    **Status: proved.**  The former single planar residue of the avoiding-ray
    winding tool, now discharged by a cross-product / sweep-angle argument.
    Consumed immediately by `argSubRel_of_segment_avoids_neg`.
-/
lemma arg_sub_mem_Ioo_of_segment_avoids_neg (A B : ℂ) (hA : A ≠ 0) (hB : B ≠ 0)
    (havoid : ∀ z ∈ segment ℝ A B, ¬ (z.im = 0 ∧ z.re ≤ 0)) :
    B.arg - A.arg ∈ Set.Ioo (-Real.pi) Real.pi := by
  constructor <;> norm_num at *;
  · by_cases hA_im : A.im < 0;
    · by_cases hB_im : B.im > 0;
      · -- Since $A.im < 0$ and $B.im > 0$, we have $A.arg < 0$ and $B.arg > 0$.
        have hA_arg_neg : A.arg < 0 := by
          rw [ Complex.arg ];
          split_ifs <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
          · exact div_neg_of_neg_of_pos hA_im ( Real.sqrt_pos.mpr ( by nlinarith ) );
          · linarith;
          · linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( -A.im / Real.sqrt ( A.re * A.re + A.im * A.im ) ) ]
        have hB_arg_pos : 0 < B.arg := by
          rw [ Complex.arg ];
          split_ifs <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
          · nlinarith;
          · linarith [ Real.neg_pi_div_two_le_arcsin ( -B.im / Real.sqrt ( B.re * B.re + B.im * B.im ) ), Real.arcsin_le_pi_div_two ( -B.im / Real.sqrt ( B.re * B.re + B.im * B.im ) ), Real.pi_pos ];
          · linarith;
        linarith [ Real.pi_pos ];
      · by_cases hB_im : B.im < 0;
        · linarith [ Complex.neg_pi_lt_arg A, Complex.arg_le_pi A, Complex.neg_pi_lt_arg B, Complex.arg_le_pi B, show Complex.arg A < 0 from Complex.arg_neg_iff.mpr hA_im, show Complex.arg B < 0 from Complex.arg_neg_iff.mpr hB_im ];
        · have := havoid B ( right_mem_segment ℝ A B ) ; simp_all +decide [ Complex.arg ];
          cases lt_or_eq_of_le ‹B.im ≤ 0› <;> first | linarith | simp_all +decide [ Complex.ext_iff ] ;
          split_ifs <;> linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( A.im / ‖A‖ ), Real.neg_pi_div_two_le_arcsin ( A.im / ‖A‖ ), Real.arcsin_le_pi_div_two ( -A.im / ‖A‖ ), Real.neg_pi_div_two_le_arcsin ( -A.im / ‖A‖ ) ];
    · by_cases hB_im : B.im < 0;
      · -- Since $B.im < 0$, there exists $t \in [0, 1]$ such that $(1 - t) * A.im + t * B.im = 0$.
        obtain ⟨t, ht⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) * A.im + t * B.im = 0 := by
          apply_rules [ intermediate_value_Icc' ] <;> norm_num;
          · fun_prop;
          · constructor <;> linarith;
        contrapose! havoid; simp_all +decide [ segment_eq_image ] ;
        refine' ⟨ t, ht.1, ht.2, _ ⟩;
        have h_arg_diff : Real.sin (A.arg - B.arg) ≤ 0 := by
          rw [ ← Real.cos_sub_pi_div_two ] ; exact Real.cos_nonpos_of_pi_div_two_le_of_le ( by linarith ) ( by linarith [ Real.pi_pos, Complex.neg_pi_lt_arg A, Complex.arg_le_pi A, Complex.neg_pi_lt_arg B, Complex.arg_le_pi B ] ) ;
        rw [ Real.sin_sub ] at h_arg_diff;
        rw [ Complex.cos_arg, Complex.sin_arg, Complex.cos_arg, Complex.sin_arg ] at h_arg_diff <;> try assumption;
        field_simp at h_arg_diff;
        cases lt_or_ge 0 ( A.re ) <;> cases lt_or_ge 0 ( B.re ) <;> nlinarith [ norm_pos_iff.mpr hA, norm_pos_iff.mpr hB, Complex.normSq_apply A, Complex.normSq_apply B, Complex.sq_norm A, Complex.sq_norm B ];
      · by_cases hA_arg : A.arg = Real.pi;
        · simp_all +decide [ Complex.arg_eq_pi_iff ];
          exact absurd ( havoid A ( left_mem_segment _ _ _ ) hA_arg.2 ) ( by norm_num; linarith );
        · by_cases hB_arg : B.arg = Real.pi;
          · linarith [ Complex.neg_pi_lt_arg A, Complex.arg_le_pi A ];
          · cases lt_or_gt_of_ne hA_arg <;> cases lt_or_gt_of_ne hB_arg <;> linarith [ Complex.neg_pi_lt_arg A, Complex.arg_le_pi A, Complex.neg_pi_lt_arg B, Complex.arg_le_pi B, Complex.arg_nonneg_iff.mpr ( show 0 ≤ A.im from le_of_not_gt hA_im ), Complex.arg_nonneg_iff.mpr ( show 0 ≤ B.im from le_of_not_gt hB_im ) ];
  · by_contra h_contra;
    -- Since $B.arg - A.arg \geq \pi$, we have $B.arg \geq A.arg + \pi$. This implies that $B$ lies in the upper half-plane and $A$ lies in the lower half-plane.
    have hB_upper : 0 < B.im := by
      by_cases hB_neg : B.arg = Real.pi;
      · simp_all +decide [ Complex.arg_eq_pi_iff ];
        exact absurd ( havoid B ( right_mem_segment _ _ _ ) hB_neg.2 ) ( by linarith );
      · have hB_upper : 0 < B.arg := by
          linarith [ Complex.neg_pi_lt_arg A, Complex.arg_le_pi A, Complex.neg_pi_lt_arg B, Complex.arg_le_pi B, lt_of_le_of_ne ( Complex.arg_le_pi B ) hB_neg ];
        rw [ ← Complex.norm_mul_sin_arg ] ; exact mul_pos ( norm_pos_iff.mpr hB ) ( Real.sin_pos_of_pos_of_lt_pi hB_upper ( lt_of_le_of_ne ( Complex.arg_le_pi _ ) hB_neg ) )
    have hA_lower : A.im < 0 := by
      by_cases hA_nonneg : 0 ≤ A.im;
      · have hA_arg_nonneg : 0 ≤ A.arg := by
          rw [ Complex.arg_nonneg_iff ] ; aesop
        have hB_arg_lt_pi : B.arg < Real.pi := by
          rw [ Complex.arg_lt_pi_iff ] ; aesop
        linarith [Real.pi_pos];
      · linarith;
    -- Let $t = \frac{A.im}{A.im - B.im}$. Then $t \in [0, 1]$ and the point $P = A + t(B - A)$ lies in the segment $[A, B]$ with $P.im = 0$.
    set t : ℝ := A.im / (A.im - B.im)
    have ht_bounds : 0 ≤ t ∧ t ≤ 1 := by
      exact ⟨ div_nonneg_of_nonpos hA_lower.le ( by linarith ), div_le_one_of_ge ( by linarith ) ( by linarith ) ⟩
    have hP_segment : A + t • (B - A) ∈ segment ℝ A B := by
      rw [ segment_eq_image ];
      exact ⟨ t, ht_bounds, by simpa using by ring ⟩
    have hP_im_zero : (A + t • (B - A)).im = 0 := by
      norm_cast; simp +decide [ *, mul_div_cancel₀, sub_ne_zero.mpr ( ne_of_lt ( by linarith : A.im < B.im ) ) ] ;
      grind;
    -- Since $B.arg - A.arg \geq \pi$, we have $B.arg \geq A.arg + \pi$. This implies that $B$ lies in the upper half-plane and $A$ lies in the lower half-plane. Therefore, $c = A.re * B.im - A.im * B.re > 0$.
    have hc_pos : A.re * B.im - A.im * B.re > 0 := by
      have hc_pos : A.re * B.im - A.im * B.re = -A.im / t * (A + t • (B - A)).re := by
        norm_cast at *; simp_all +decide [ sub_eq_iff_eq_add, div_eq_mul_inv ] ;
        grind;
      exact hc_pos.symm ▸ mul_pos ( div_pos ( neg_pos.mpr hA_lower ) ( div_pos_of_neg_of_neg hA_lower ( by linarith ) ) ) ( havoid _ hP_segment hP_im_zero );
    have hc_neg : A.re * B.im - A.im * B.re ≤ 0 := by
      have h_sin_neg : Real.sin (B.arg - A.arg) ≤ 0 := by
        rw [ ← Real.cos_sub_pi_div_two ];
        refine' Real.cos_nonpos_of_pi_div_two_le_of_le _ _ <;> linarith [ Real.pi_pos, Complex.neg_pi_lt_arg A, Complex.arg_le_pi A, Complex.neg_pi_lt_arg B, Complex.arg_le_pi B ]
      rw [ Real.sin_sub ] at h_sin_neg;
      rw [ ← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg, ← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg ] at *;
      nlinarith [ show 0 < ‖A‖ * ‖B‖ by positivity ];
    linarith

/-- **Geometric bridge.**  The exact argument-subtraction relation
    `argSubRel x e a b` holds whenever the segment joining the rotated position
    vectors `(a - x)/e` and `(b - x)/e` avoids the non-positive real ray — i.e.
    the edge `(a, b)` does not cross the ray from `x` in the fixed direction `e`.

    Proved from the isolated crux `arg_sub_mem_Ioo_of_segment_avoids_neg` by
    pinning the wrap integer of `Complex.arg_div_coe_angle` to `0`.  NOT a dead
    branch — consumed by `ptWind_eq_zero_of_ray_avoids` below. -/
lemma argSubRel_of_segment_avoids_neg (x e : ℂ) (he : e ≠ 0) (a b : ℂ)
    (ha : a ≠ x) (hb : b ≠ x)
    (havoid : ∀ z ∈ segment ℝ ((a - x) / e) ((b - x) / e),
        ¬ (z.im = 0 ∧ z.re ≤ 0)) :
    argSubRel x e a b := by
  have hA : (a - x) / e ≠ 0 := div_ne_zero (sub_ne_zero.mpr ha) he
  have hB : (b - x) / e ≠ 0 := div_ne_zero (sub_ne_zero.mpr hb) he
  have hbound := arg_sub_mem_Ioo_of_segment_avoids_neg ((a - x) / e) ((b - x) / e) hA hB havoid
  unfold argSubRel
  have hratio : (b - x) / (a - x) = ((b - x) / e) / ((a - x) / e) := by
    field_simp
  rw [hratio]
  set A := (a - x) / e
  set B := (b - x) / e
  have hangle : ((B / A).arg : Real.Angle) = (B.arg : Real.Angle) - (A.arg : Real.Angle) :=
    Complex.arg_div_coe_angle hB hA
  rw [← Real.Angle.coe_sub, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hangle
  obtain ⟨k, hk⟩ := hangle
  have h1 := Complex.neg_pi_lt_arg (B / A)
  have h2 := Complex.arg_le_pi (B / A)
  obtain ⟨hl, hr⟩ := hbound
  have hpi := Real.pi_pos
  have hkr : (-1 : ℝ) < (k : ℝ) ∧ (k : ℝ) < 1 := by
    constructor <;> nlinarith [hk, h1, h2, hl, hr, hpi]
  have hk0 : k = 0 := by
    have : (-1 : ℤ) < k ∧ k < 1 := by exact_mod_cast hkr
    omega
  rw [hk0] at hk
  push_cast at hk
  linarith

/-- The closed-edge list of `V` is an `argSubRel`-chain, provided every closed
    edge avoids the ray in direction `e`. -/
lemma isChain_argSubRel_of_edges (x e : ℂ) (he : e ≠ 0) :
    ∀ (W : List ℂ), (∀ v ∈ W, v ≠ x) →
      (∀ p ∈ W.zip (W.drop 1),
          ∀ z ∈ segment ℝ ((p.1 - x) / e) ((p.2 - x) / e), ¬ (z.im = 0 ∧ z.re ≤ 0)) →
      List.IsChain (argSubRel x e) W := by
  intro W
  induction W with
  | nil => intro _ _; exact List.IsChain.nil
  | cons a t ih =>
      intro hxW hedge
      cases t with
      | nil => exact List.IsChain.singleton a
      | cons b t =>
          rw [List.isChain_cons_cons]
          refine ⟨?_, ?_⟩
          · apply argSubRel_of_segment_avoids_neg x e he a b
              (hxW a (by simp)) (hxW b (by simp))
            intro z hz
            exact hedge (a, b) (by simp) z hz
          · apply ih
            · intro v hv; exact hxW v (List.mem_cons_of_mem _ hv)
            · intro p hp z hz
              apply hedge p ?_ z hz
              have hd : (a :: b :: t).drop 1 = b :: t := rfl
              rw [hd, List.zip_cons_cons]
              exact List.mem_cons_of_mem _ hp

/-- **Avoiding-ray vanishing of the point-winding.**  Fix a direction `e ≠ 0`.
    If `x` is off every vertex of the closed cycle `V` and, for every closed edge
    `(a, b)` of `V`, the rotated segment `[(a-x)/e, (b-x)/e]` avoids the
    non-positive real ray, then `ptWind x V = 0`.

    This is the "escaping ray ⟹ winding `0`" separation tool, strictly more
    general than the convex half-plane criterion `ptWind_eq_zero_of_halfplane`:
    it applies to non-convex polygons and hull-interior points, provided a single
    ray from `x` in direction `e` escapes without meeting the polygon. -/
lemma ptWind_eq_zero_of_ray_avoids (x e : ℂ) (he : e ≠ 0) (V : List ℂ)
    (hx : ∀ v ∈ V, v ≠ x)
    (hedge : ∀ p ∈ (V ++ V.take 1).zip ((V ++ V.take 1).drop 1),
        ∀ z ∈ segment ℝ ((p.1 - x) / e) ((p.2 - x) / e),
        ¬ (z.im = 0 ∧ z.re ≤ 0)) :
    ptWind x V = 0 := by
  apply ptWind_eq_zero_of_chain x e V
  apply isChain_argSubRel_of_edges x e he (V ++ V.take 1) ?_ hedge
  intro v hv
  rw [List.mem_append] at hv
  rcases hv with h | h
  · exact hx v h
  · exact hx v (List.mem_of_mem_take h)

end HexArea

end