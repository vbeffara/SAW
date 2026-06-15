/-
# Ear-existence geometry, part III: the barycentric backbone of the triangle interior

This file continues the plane-geometry preparation begun in
`RequestProject.SAWUmlaufEar` and `RequestProject.SAWUmlaufEarExist` for the
single remaining topological core of the discrete Hopf Umlaufsatz, the two-ears
/ ear-existence theorem `exists_ear_clip` (in
`RequestProject.SAWUmlaufPolygon`).

Recall Meisters' ear-existence argument:

1. pick the *extreme* (leftmost, then lowest) vertex of the polygon; it is a
   convex corner;
2. if its neighbour-triangle contains no other vertex, it is an ear; otherwise
   pick the vertex *farthest from the base diagonal*; that vertex is a convex
   corner whose neighbour-triangle is empty, hence an ear;
3. clipping the ear preserves planar simplicity, non-degeneracy, turning and
   orientation.

Step 2 reasons about *which vertices lie inside a candidate ear triangle*.  The
strict-interior predicate `SAWUmlaufEar.inTriangleStrict` is phrased through the
three edge cross products; what the ear search actually needs is to convert
between that cross-product form and honest **barycentric / convex-combination**
coordinates, so that "x is inside the triangle" becomes "x is a strict convex
combination of the vertices".  That conversion is the genuinely reusable
geometric content isolated and **proved here**:

* `cross_bary_sum` — the three edge cross products of `x` against the triangle
  `a,b,c` sum to the triangle orientation `cross (b-a) (c-b)` (so the three
  sub-triangle areas tile the whole triangle);
* `cross_bary_recon` — the barycentric reconstruction identity:
  `area2 • x = (γ-weight) • a + (α-weight) • b + (β-weight) • c`, the affine
  identity expressing `x` through the three cross-product weights;
* `inTriangleStrict_pos_area` — a positively-oriented strict interior point
  forces the triangle orientation `cross (b-a) (c-b)` to be strictly positive;
* `inTriangleStrict_pos_convexCombo` — a positively-oriented strict interior
  point is a *strict convex combination* `α•a + β•b + γ•c` with positive
  weights summing to `1`;
* `convexCombo_pos_inTriangleStrict` — the converse: a strict convex
  combination of a positively-oriented triangle's vertices lies in its strict
  interior;
* `inTriangleStrict_pos_iff_convexCombo` — the resulting characterization,
  bundling the two directions.

This file is **preparation**: it is imported by
`RequestProject.SAWUmlaufPolygon` (hence transitively from
`RequestProject.SAWFinal`), so it is part of the build chain.  Its lemmas are
designed to be consumed by the eventual proof of `exists_ear_clip`; they are not
yet referenced by another declaration only because the core they feed is still
open.  This is intentional, recorded partial progress, not a dead branch.
-/

import Mathlib
import RequestProject.SAWUmlaufEar
import RequestProject.SAWUmlaufEarExist

open Complex

noncomputable section

namespace HexArea

/-! ## The barycentric backbone

For a triangle `a, b, c` and a point `x`, the three oriented edge cross products
`cross (b-a) (x-a)`, `cross (c-b) (x-b)`, `cross (a-c) (x-c)` are (twice) the
signed areas of the three sub-triangles `x` cuts the triangle into.  They tile
the whole triangle (`cross_bary_sum`) and reconstruct `x` affinely
(`cross_bary_recon`); dividing by the total area `cross (b-a) (c-b)` turns them
into honest barycentric coordinates. -/

/-
The three edge cross products of `x` against the triangle `a,b,c` sum to the
    triangle orientation `cross (b-a) (c-b)`: the three sub-triangles tile the
    whole triangle.
-/
lemma cross_bary_sum (a b c x : ℂ) :
    cross (b - a) (x - a) + cross (c - b) (x - b) + cross (a - c) (x - c)
      = cross (b - a) (c - b) := by
  unfold cross; simpa using by ring;

/-
**Barycentric reconstruction.**  Scaling `x` by the triangle orientation
    `cross (b-a) (c-b)` expresses it through the three edge cross-product weights:
    the weight of `a` is `cross (c-b) (x-b)`, of `b` is `cross (a-c) (x-c)`, of
    `c` is `cross (b-a) (x-a)`.
-/
lemma cross_bary_recon (a b c x : ℂ) :
    (cross (b - a) (c - b)) • x
      = (cross (c - b) (x - b)) • a + (cross (a - c) (x - c)) • b
        + (cross (b - a) (x - a)) • c := by
  unfold cross; norm_num [ Complex.ext_iff ] ; ring;
  grind

/-! ## From the strict interior to a strict convex combination -/

/-
A positively-oriented strict interior point forces the triangle to be
    positively oriented: `cross (b-a) (c-b) > 0`.  (Immediate from
    `cross_bary_sum`: the orientation is the sum of three positive terms.)
-/
lemma inTriangleStrict_pos_area (a b c x : ℂ)
    (h1 : 0 < cross (b - a) (x - a)) (h2 : 0 < cross (c - b) (x - b))
    (h3 : 0 < cross (a - c) (x - c)) :
    0 < cross (b - a) (c - b) := by
  linarith [ cross_bary_sum a b c x ]

/-
A point in the (positively-oriented) strict interior of the triangle
    `a,b,c` is a *strict convex combination* of its vertices: there are positive
    weights `α, β, γ` summing to `1` with `x = α•a + β•b + γ•c`.  This is the
    bridge from the cross-product interior test to honest convex-hull
    membership, used to reason about which polygon vertices fall inside a
    candidate ear triangle.
-/
lemma inTriangleStrict_pos_convexCombo (a b c x : ℂ)
    (h1 : 0 < cross (b - a) (x - a)) (h2 : 0 < cross (c - b) (x - b))
    (h3 : 0 < cross (a - c) (x - c)) :
    ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
      x = α • a + β • b + γ • c := by
  refine' ⟨ cross ( c - b ) ( x - b ) / cross ( b - a ) ( c - b ), cross ( a - c ) ( x - c ) / cross ( b - a ) ( c - b ), cross ( b - a ) ( x - a ) / cross ( b - a ) ( c - b ), _, _, _, _, _ ⟩;
  · exact div_pos h2 ( inTriangleStrict_pos_area a b c x h1 h2 h3 );
  · exact div_pos h3 ( inTriangleStrict_pos_area a b c x h1 h2 h3 );
  · exact div_pos h1 ( by linarith [ cross_bary_sum a b c x ] );
  · rw [ ← add_div, ← add_div, div_eq_iff ] <;> linarith [ inTriangleStrict_pos_area a b c x h1 h2 h3, cross_bary_sum a b c x ];
  · convert congr_arg ( fun z => ( cross ( b - a ) ( c - b ) ) ⁻¹ • z ) ( cross_bary_recon a b c x ) using 1;
    · rw [ smul_smul, inv_mul_cancel₀ ( ne_of_gt ( inTriangleStrict_pos_area a b c x h1 h2 h3 ) ), one_smul ];
    · simp +decide [ div_eq_inv_mul, smul_add, smul_smul ];
      ring

/-
Converse of `inTriangleStrict_pos_convexCombo`: a strict convex combination
    `α•a + β•b + γ•c` (positive weights summing to `1`) of the vertices of a
    positively-oriented triangle (`cross (b-a) (c-b) > 0`) lies in its strict
    interior.
-/
lemma convexCombo_pos_inTriangleStrict (a b c : ℂ) (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = 1)
    (harea : 0 < cross (b - a) (c - b)) :
    inTriangleStrict a b c (α • a + β • b + γ • c) := by
  refine Or.inl ⟨ ?_, ?_, ?_ ⟩ <;> simp_all +decide [ cross ]; all_goals rw [ ← eq_sub_iff_add_eq' ] at hsum ; subst_vars ; nlinarith

/-
**Characterization of the positively-oriented strict triangle interior.**
    For a positively-oriented triangle (`cross (b-a) (c-b) > 0`), a point lies
    strictly inside (the positive disjunct of `inTriangleStrict`) iff it is a
    strict convex combination of the vertices.
-/
lemma inTriangleStrict_pos_iff_convexCombo (a b c x : ℂ)
    (harea : 0 < cross (b - a) (c - b)) :
    (0 < cross (b - a) (x - a) ∧ 0 < cross (c - b) (x - b) ∧ 0 < cross (a - c) (x - c))
      ↔ ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
          x = α • a + β • b + γ • c := by
  constructor <;> intro h;
  · apply inTriangleStrict_pos_convexCombo a b c x h.left h.right.left h.right.right;
  · obtain ⟨ α, β, γ, hα, hβ, hγ, hsum, rfl ⟩ := h;
    simp_all +decide [ Complex.ext_iff, cross ];
    rw [ ← eq_sub_iff_add_eq' ] at hsum ; subst_vars ; exact ⟨ by nlinarith, by nlinarith, by nlinarith ⟩

end HexArea

end