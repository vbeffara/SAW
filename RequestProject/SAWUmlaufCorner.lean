/-
# Ear-existence geometry, part VII: the Jordan-segment "corner crossing" core

This file isolates and (incrementally) proves the **pure-geometry, list-free
heart** of the planar-simplicity half of an ear clip — the lemma
`seg_diagonal_disjoint_of_corner` in `RequestProject.SAWUmlaufPolygon`.

The mathematical content is a discrete intermediate-value / "crossing" argument:
in a non-degenerate corner triangle `a, b, c`, a chord `u–w` that misses the two
polygon edges `a–b` and `b–c`, and whose endpoints are neither strictly inside
the triangle nor on the closed base diagonal `a–c`, cannot cross the base
diagonal `a–c` either.  The proof is *constructive*: every "side" function is
affine, so the first crossing of an edge happens at an explicitly computable
parameter `τ*`, and at that parameter the moving point lands on a closed
triangle edge — contradicting edge-disjointness.

This file provides the reusable algebraic building blocks that make that
constructive argument go through:

* `exists_real_smul_of_cross_zero` — two complex numbers with vanishing 2-D
  cross product are `ℝ`-linearly dependent (a point on a carrier line has an
  explicit real affine parameter).
* `mem_segment_ab_of_cross` / `mem_segment_bc_of_cross` — a point on the carrier
  line of an edge whose two "adjacent" side tests have the correct (orientation-
  agnostic, product-form) signs actually lies on the *closed segment* of that
  edge.
* `corner_exit_point` — the constructive crossing core: a moving point that
  starts in the relative interior of edge `a–c` (apex-side functions positive,
  base side zero) and ends at an endpoint that is on the apex side of `a–c` but
  *not* strictly inside the triangle must, somewhere along the way, hit the
  closed edge `a–b` or `b–c`.

These are designed to be consumed by `seg_diagonal_disjoint_of_corner`.  This
file is imported by `RequestProject.SAWUmlaufPolygon` (hence transitively from
`RequestProject.SAWFinal`); it is **preparation**, recorded partial progress,
not a dead branch.
-/

import Mathlib
import RequestProject.SAWUmlaufEar
import RequestProject.SAWUmlaufSegment

open Complex

noncomputable section

namespace HexArea

/-! ## A point on a carrier line has a real affine parameter -/

/-
Two complex numbers with vanishing 2-D cross product are `ℝ`-linearly
    dependent: if `z ≠ 0` and `cross z w = 0`, then `w = λ • z` for some real
    `λ`.  (The 2-D cross product is the determinant `[z w]`; vanishing
    determinant with `z ≠ 0` means `w` is a real multiple of `z`.)
-/
lemma exists_real_smul_of_cross_zero (z w : ℂ) (hz : z ≠ 0) (h : cross z w = 0) :
    ∃ l : ℝ, w = l • z := by
  unfold cross at h;
  norm_num [ Complex.ext_iff ] at *;
  by_cases hz_re : z.re = 0;
  · exact ⟨ w.im / z.im, by simp_all +decide [ div_mul_cancel₀ ], by simp +decide [ *, mul_div_cancel₀ ] ⟩;
  · exact ⟨ w.re / z.re, by rw [ div_mul_cancel₀ _ hz_re ], by rw [ div_mul_eq_mul_div, eq_div_iff hz_re ] ; linarith ⟩

/-! ## Carrier-line membership upgrades to closed-segment membership

In each lemma `O := cross (b - a) (c - b)` is the corner orientation; the
hypotheses are stated in *product form* (`… * O`) so they are valid for both
orientations of the triangle. -/

/-
A point `y` on the carrier line of edge `a–b` (`cross (b-a) (y-a) = 0`)
    whose two adjacent side tests have the correct product signs lies on the
    closed segment `a–b`.  Concretely, writing `y = a + λ•(b-a)`, the side test
    against `c–b` gives `(1-λ)·O²` and the one against `a–c` gives `λ·O²`, so the
    two `≥ 0` product hypotheses force `0 ≤ λ ≤ 1`.
-/
lemma mem_segment_ab_of_cross (a b c y : ℂ)
    (hO : cross (b - a) (c - b) ≠ 0)
    (hline : cross (b - a) (y - a) = 0)
    (hbc : 0 ≤ cross (c - b) (y - b) * cross (b - a) (c - b))
    (hca : 0 ≤ cross (a - c) (y - c) * cross (b - a) (c - b)) :
    y ∈ segment ℝ a b := by
  obtain ⟨l, hl⟩ : ∃ l : ℝ, y = a + l • (b - a) := by
    convert HexArea.exists_real_smul_of_cross_zero ( b - a ) ( y - a ) ?_ hline using 1;
    · grind;
    · exact sub_ne_zero_of_ne <| by rintro rfl; simp_all +decide [ cross ] ;
  simp_all +decide [ cross ];
  rw [ segment_eq_image ];
  use l;
  exact ⟨ ⟨ by nlinarith [ mul_self_pos.2 hO ], by nlinarith [ mul_self_pos.2 hO ] ⟩, by simp +decide [ sub_smul, smul_sub ] ; ring ⟩

/-
A point `y` on the carrier line of edge `b–c` (`cross (c-b) (y-b) = 0`)
    whose two adjacent side tests have the correct product signs lies on the
    closed segment `b–c`.  Writing `y = b + μ•(c-b)`, the side test against `b-a`
    gives `μ·O²` and the one against `a–c` gives `(1-μ)·O²`, so the two `≥ 0`
    product hypotheses force `0 ≤ μ ≤ 1`.
-/
lemma mem_segment_bc_of_cross (a b c y : ℂ)
    (hO : cross (b - a) (c - b) ≠ 0)
    (hline : cross (c - b) (y - b) = 0)
    (hab : 0 ≤ cross (b - a) (y - a) * cross (b - a) (c - b))
    (hca : 0 ≤ cross (a - c) (y - c) * cross (b - a) (c - b)) :
    y ∈ segment ℝ b c := by
  obtain ⟨l, hl⟩ : ∃ l : ℝ, y - b = l • (c - b) := by
    convert HexArea.exists_real_smul_of_cross_zero ( c - b ) ( y - b ) _ hline using 1;
    contrapose! hO; simp_all +decide [ sub_eq_iff_eq_add ] ;
    unfold cross; norm_num;
  simp_all +decide [ sub_eq_iff_eq_add, segment_eq_image ];
  refine' ⟨ l, _, _ ⟩;
  · unfold cross at *;
    constructor <;> norm_num [ Complex.ext_iff ] at * <;> cases lt_or_gt_of_ne hO <;> nlinarith [ mul_self_pos.mpr hO ];
  · ring

/-! ## The constructive crossing core -/

/-
**Constructive corner crossing.**  Move along the chord from a point `z` in
    the *relative interior* of the base edge `a–c` (its two apex-side tests are
    strictly positive in product form, `hzab`/`hzbc`, and its base side test
    vanishes, `hzac`) towards an endpoint `u` that lies strictly on the apex
    (`b`) side of `a–c` (`huac`) but is *not* strictly inside the triangle
    (`hunot`).  Then somewhere along the segment `z–u` the moving point hits the
    closed edge `a–b` or the closed edge `b–c`.

    Proof idea (constructive, no analysis needed): every side test is *affine*
    along `z + τ•(u-z)`.  Because `u` is not strictly inside but is on the apex
    side, at least one of the two edge side tests `PA := cross (b-a)(·-a)·O`,
    `PB := cross (c-b)(·-b)·O` is `≤ 0` at `u`, while both are `> 0` at `z` and
    the apex side test `PC := cross (a-c)(·-c)·O` is `> 0` for every `τ > 0`.
    The first of `PA`, `PB` to vanish does so at an explicit
    `τ⋆ = P(z)/(P(z)-P(u)) ∈ (0,1]`; at `τ⋆` the *other* edge test is still `≥ 0`
    and `PC > 0`, so by `mem_segment_ab_of_cross` / `mem_segment_bc_of_cross`
    the point lies on the corresponding closed edge.  Absent from Mathlib.
-/
lemma corner_exit_point (a b c z u : ℂ)
    (hO : cross (b - a) (c - b) ≠ 0)
    (hzab : 0 < cross (b - a) (z - a) * cross (b - a) (c - b))
    (hzbc : 0 < cross (c - b) (z - b) * cross (b - a) (c - b))
    (hzac : cross (a - c) (z - c) = 0)
    (huac : 0 < cross (a - c) (u - c) * cross (b - a) (c - b))
    (hunot : ¬ inTriangleStrict a b c u) :
    (∃ y ∈ segment ℝ z u, y ∈ segment ℝ a b) ∨
    (∃ y ∈ segment ℝ z u, y ∈ segment ℝ b c) := by
  -- Let $O := cross (b - a) (c - b)$.
  set O := cross (b - a) (c - b) with hO_def;
  -- By bilinearity each test is affine in `τ`:
  have hPA : ∀ τ : ℝ, cross (b - a) (z + τ • (u - z) - a) * O = (1 - τ) * cross (b - a) (z - a) * O + τ * cross (b - a) (u - a) * O := by
    unfold cross; norm_num [ Complex.ext_iff ] ; intros; ring;
  have hPB : ∀ τ : ℝ, cross (c - b) (z + τ • (u - z) - b) * O = (1 - τ) * cross (c - b) (z - b) * O + τ * cross (c - b) (u - b) * O := by
    unfold cross; norm_num; intros; ring;
  have hPC : ∀ τ : ℝ, cross (a - c) (z + τ • (u - z) - c) * O = τ * cross (a - c) (u - c) * O := by
    simp_all +decide [ cross ];
    grind;
  -- Case 1: `PA u ≤ 0` (and `PA z > 0`): let `t := PA z / (PA z - PA u)`.
  by_cases hPAu : cross (b - a) (u - a) * O ≤ 0;
  · -- Let `t := PA z / (PA z - PA u)`.
    set t := cross (b - a) (z - a) * O / (cross (b - a) (z - a) * O - cross (b - a) (u - a) * O) with ht_def;
    -- At `Y t`: `PA (Y t) = 0` (by choice of `t`), `PC (Y t) > 0 ≥ 0`.
    have ht_bounds : 0 < t ∧ t ≤ 1 := by
      exact ⟨ div_pos hzab ( by linarith ), div_le_one_of_le₀ ( by linarith ) ( by linarith ) ⟩
    have ht_PA : cross (b - a) (z + t • (u - z) - a) * O = 0 := by
      grind
    have ht_PC : 0 < cross (a - c) (z + t • (u - z) - c) * O := by
      rw [ hPC ] ; nlinarith [ mul_pos ht_bounds.1 huac ] ;
    -- Now subdivide on `PB u`:
    by_cases hPBu : cross (c - b) (u - b) * O ≥ 0;
    · refine Or.inl ⟨ z + t • ( u - z ), ?_, ?_ ⟩;
      · rw [ segment_eq_image ];
        exact ⟨ t, ⟨ by linarith, by linarith ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩;
      · apply mem_segment_ab_of_cross a b c (z + t • (u - z)) hO;
        · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO ht_PA;
        · nlinarith [ hPB t ];
        · exact le_of_lt ht_PC;
    · -- Let `s := PB z / (PB z - PB u)`, `0 < s ≤ 1`, `PB (Y s) = 0`.
      set s := cross (c - b) (z - b) * O / (cross (c - b) (z - b) * O - cross (c - b) (u - b) * O) with hs_def
      have hs_bounds : 0 < s ∧ s ≤ 1 := by
        exact ⟨ div_pos hzbc ( by linarith ), div_le_one_of_le₀ ( by linarith ) ( by linarith ) ⟩
      have hs_PB : cross (c - b) (z + s • (u - z) - b) * O = 0 := by
        grind
      have hs_PC : 0 < cross (a - c) (z + s • (u - z) - c) * O := by
        rw [ hPC ] ; nlinarith [ mul_pos hs_bounds.1 huac ];
      -- Compare `t` and `s`:
      by_cases hts : t ≤ s;
      · -- At `Y t`, `PB (Y t) = (1-t)*PB z + t*PB u ≥ 0` because `t ≤ s` is exactly the threshold where `PB` reaches 0 (so for `t ≤ s`, `PB(Y t) ≥ 0`); `PC(Y t)>0`.
        have ht_PB_nonneg : 0 ≤ cross (c - b) (z + t • (u - z) - b) * O := by
          rw [ hPB ];
          rw [ le_div_iff₀ ] at hts <;> nlinarith;
        left;
        use z + t • (u - z);
        apply And.intro;
        · rw [ segment_eq_image ];
          exact ⟨ t, ⟨ by linarith, by linarith ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩;
        · apply mem_segment_ab_of_cross a b c (z + t • (u - z)) hO;
          · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO ht_PA;
          · exact ht_PB_nonneg;
          · exact le_of_lt ht_PC;
      · -- At `Y s`, `PB (Y s)=0`, and `PA (Y s) = (1-s)*PA z + s*PA u ≥ 0` since `s < t` (the threshold where `PA` reaches 0, so for `s ≤ t`, `PA(Y s) ≥ 0`); `PC (Y s)=s*PC u>0`.
        have hs_PA : cross (b - a) (z + s • (u - z) - a) * O ≥ 0 := by
          rw [ hPA ];
          rw [ div_le_iff₀ ] at hts <;> nlinarith;
        refine Or.inr ⟨ z + s • ( u - z ), ?_, ?_ ⟩;
        · rw [ segment_eq_image ];
          exact ⟨ s, ⟨ by linarith, by linarith ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩;
        · apply mem_segment_bc_of_cross a b c (z + s • (u - z)) hO;
          · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO hs_PB;
          · exact hs_PA;
          · exact le_of_lt hs_PC;
  · -- Case 2: `PA u > 0` (so the disjunction forces `PB u ≤ 0`, and `PB z > 0`): let `s := PB z / (PB z - PB u)`.
    have hPBu : cross (c - b) (u - b) * O ≤ 0 := by
      contrapose! hunot; simp_all +decide [ inTriangleStrict ] ;
      cases lt_or_gt_of_ne hO <;> first | exact Or.inl ⟨ by nlinarith, by nlinarith, by nlinarith ⟩ | exact Or.inr ⟨ by nlinarith, by nlinarith, by nlinarith ⟩ ;
    set s := cross (c - b) (z - b) * O / (cross (c - b) (z - b) * O - cross (c - b) (u - b) * O) with hs_def
    have hs_pos : 0 < s := by
      exact div_pos hzbc ( by linarith )
    have hs_le_one : s ≤ 1 := by
      exact div_le_one_of_le₀ ( by linarith ) ( by linarith )
    have hPB_s : cross (c - b) (z + s • (u - z) - b) * O = 0 := by
      rw [ hPB, hs_def ] ; nlinarith [ mul_div_cancel₀ ( cross ( c - b ) ( z - b ) * O ) ( by linarith : ( cross ( c - b ) ( z - b ) * O - cross ( c - b ) ( u - b ) * O ) ≠ 0 ) ] ;
    generalize_proofs at *; (
    refine Or.inr ⟨ z + s • ( u - z ), ?_, ?_ ⟩
    all_goals generalize_proofs at *;
    · rw [ segment_eq_image ];
      exact ⟨ s, ⟨ hs_pos.le, hs_le_one ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩;
    · apply mem_segment_bc_of_cross a b c (z + s • (u - z)) hO (by
      exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO hPB_s) (by
      nlinarith [ hPA s ]) (by
      nlinarith [ hPC s ]))

/-! ## The degenerate (collinear) case -/

/-
**Collinear degenerate case.**  If both endpoints `u, w` of a chord lie on
    the *carrier line* of the base diagonal `a–c` (`cross (c-a)(·-a) = 0`) but
    *off* the closed segment `a–c`, while an interior point `z` of `a–c`
    (`z ≠ a`, `z ≠ c`) lies on the chord `u–w`, then the vertex `a` itself lies
    on the chord `u–w`.

    Reason: in the affine coordinate `g x` along `c-a` (so `g a = 0`, `g c = 1`),
    `z` has `g z ∈ (0,1)` while `g u, g w ∉ [0,1]`; a strict convex combination
    landing in `(0,1)` forces the two to *straddle* `[0,1]` (one `< 0`, one
    `> 1`), and then `0 = g a` lies strictly between them, so `a ∈ segment u w`.
    Used by `seg_diagonal_disjoint_of_corner` to dispatch the collinear case.
-/
lemma collinear_diag_a_mem (a c u w z : ℂ) (hac : c - a ≠ 0)
    (hu_line : cross (c - a) (u - a) = 0) (hw_line : cross (c - a) (w - a) = 0)
    (hz_ac : z ∈ segment ℝ a c) (hza : z ≠ a) (hzc : z ≠ c)
    (hz_uw : z ∈ segment ℝ u w)
    (hu_diag : u ∉ segment ℝ a c) (hw_diag : w ∉ segment ℝ a c) :
    a ∈ segment ℝ u w := by
  obtain ⟨l₁, hl₁⟩ : ∃ l₁ : ℝ, u - a = l₁ • (c - a) :=
    HexArea.exists_real_smul_of_cross_zero (c - a) (u - a) hac hu_line
  obtain ⟨l₂, hl₂⟩ : ∃ l₂ : ℝ, w - a = l₂ • (c - a) := by
    convert HexArea.exists_real_smul_of_cross_zero ( c - a ) ( w - a ) hac hw_line using 1
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = (1 - t) • a + t • c := by
    rw [ segment_eq_image ] at hz_ac; aesop;
  have hz_gt : 0 < t ∧ t < 1 := by
    exact ⟨ lt_of_le_of_ne ht.1 ( Ne.symm <| by rintro rfl; simp_all +decide [ sub_eq_iff_eq_add ] ), lt_of_le_of_ne ht.2.1 ( by rintro rfl; simp_all +decide [ sub_eq_iff_eq_add ] ) ⟩
  have hz_s_g : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (1 - s) • u + s • w := by
    rw [ segment_eq_image ] at hz_uw; obtain ⟨ s, hs, rfl ⟩ := hz_uw; exact ⟨ s, hs.1, hs.2, rfl ⟩ ;
  obtain ⟨s, hs⟩ := hz_s_g
  have hz_s_g_eq : (1 - s) * l₁ + s * l₂ = t := by
    simp_all +decide [ Complex.ext_iff, sub_eq_iff_eq_add ];
    grind
  have hz_s_g_cases : l₁ < 0 ∧ l₂ > 1 ∨ l₁ > 1 ∧ l₂ < 0 := by
    have hz_s_g_cases : l₁ ∉ Set.Icc 0 1 ∧ l₂ ∉ Set.Icc 0 1 := by
      constructor <;> contrapose! hu_diag <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · rw [ segment_eq_image ];
        exact ⟨ l₁, hu_diag, by simpa using by ring ⟩;
      · exact False.elim <| hw_diag <| by rw [ segment_eq_image ] ; exact ⟨ l₂, ⟨ by linarith, by linarith ⟩, by simp +decide [ mul_comm ] ; ring ⟩ ;
    cases lt_or_ge l₁ 0 <;> cases lt_or_ge l₂ 0 <;> simp_all +decide; all_goals nlinarith;
  have hz_s_g_cases : ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ (1 - r) * l₁ + r * l₂ = 0 := by
    cases' hz_s_g_cases with h_case1 h_case2;
    · exact ⟨ -l₁ / ( l₂ - l₁ ), by nlinarith [ mul_div_cancel₀ ( -l₁ ) ( by linarith : ( l₂ - l₁ ) ≠ 0 ) ], by nlinarith [ mul_div_cancel₀ ( -l₁ ) ( by linarith : ( l₂ - l₁ ) ≠ 0 ) ], by linarith [ mul_div_cancel₀ ( -l₁ ) ( by linarith : ( l₂ - l₁ ) ≠ 0 ) ] ⟩;
    · exact ⟨ l₁ / ( l₁ - l₂ ), by nlinarith [ mul_div_cancel₀ l₁ ( by linarith : ( l₁ - l₂ ) ≠ 0 ) ], by nlinarith [ mul_div_cancel₀ l₁ ( by linarith : ( l₁ - l₂ ) ≠ 0 ) ], by nlinarith [ mul_div_cancel₀ l₁ ( by linarith : ( l₁ - l₂ ) ≠ 0 ) ] ⟩;
  obtain ⟨ r, hr₀, hr₁, hr₂ ⟩ := hz_s_g_cases; rw [ segment_eq_image ] ; use r; simp_all +decide [ sub_eq_iff_eq_add ] ;
  convert congr_arg ( fun x : ℝ => x * ( c - a ) + a ) hr₂ using 1 <;> push_cast <;> ring

end HexArea

end