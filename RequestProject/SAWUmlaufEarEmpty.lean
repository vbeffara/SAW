/-
# Ear-existence geometry, part IV: sub-triangle orientation, nesting, and the empty-region maximality

This file continues the plane-geometry preparation begun in
`RequestProject.SAWUmlaufEar`, `RequestProject.SAWUmlaufEarExist` and
`RequestProject.SAWUmlaufEarConvex` for the single remaining topological core of
the discrete Hopf Umlaufsatz, the two-ears / ear-existence theorem
`exists_ear_clip` (in `RequestProject.SAWUmlaufPolygon`).

Recall Meisters' ear-existence argument:

1. pick the *extreme* (leftmost, then lowest) vertex `v` of the polygon; it is a
   convex corner;
2. with neighbours `a, c`, look at the corner triangle `a, v, c`.  If it
   contains no other vertex, `v` is an ear.  Otherwise, among the vertices
   strictly inside `a, v, c` pick the one `q` *farthest from the base diagonal*
   `a–c`; then `v–q` is a diagonal because the region of `a, v, c` strictly
   *farther* from `a–c` than `q` contains no vertex, and one recurses on the two
   sub-polygons;
3. clipping an ear preserves planar simplicity, non-degeneracy, turning and
   orientation.

Step 2 needs three reusable geometric facts, all proved here and all consuming
the barycentric backbone of `RequestProject.SAWUmlaufEarConvex` (so that file is
no longer only feeding the open core — it is now consumed here):

* `subTri_axc_orient_pos` — if `x` is in the positively-oriented strict interior
  of `a, b, c`, then the sub-triangle `a, x, c` is itself positively oriented
  (`0 < cross (x-a) (c-x)`): the barycentric weight of `b` is the positive
  proportionality factor.  This is what makes the *sub-triangle* `a, q, c`
  (with `q` an interior vertex) a genuine positively-oriented triangle, so the
  strict-interior test applies to it.
* `inTriangleStrict_pos_nest` — strict interiors nest: a point strictly inside
  the positively-oriented sub-triangle `a, q, c` (with `q` strictly inside
  `a, b, c`) is strictly inside `a, b, c`.  This is the convexity/transitivity
  fact that lets the ear search recurse into the smaller triangle while keeping
  control of which polygon vertices are involved.
* `farthest_region_empty` — the maximality clause: a vertex of the candidate
  list cannot be *strictly farther* from the base line `a–c` than the chosen
  farthest vertex `q` (`exists_max_cross` of `SAWUmlaufEarExist` supplies `q`).
  This is the emptiness of the region beyond `q` that makes `v–q` a diagonal.

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
import RequestProject.SAWUmlaufEarConvex

open Complex

noncomputable section

namespace HexArea

/-! ## Sub-triangle orientation

If `x` lies in the positively-oriented strict interior of `a, b, c`, the
sub-triangle `a, x, c` is itself positively oriented.  Writing `x` in
barycentric coordinates `x = α•a + β•b + γ•c` (all positive, summing to `1`,
from `inTriangleStrict_pos_convexCombo`), a direct bilinear computation gives
`cross (x-a) (c-x) = β · cross (b-a) (c-b)`, which is positive. -/

/-
The sub-triangle `a, x, c` cut off by a positively-oriented strict interior
    point `x` of `a, b, c` is positively oriented.
-/
lemma subTri_axc_orient_pos (a b c x : ℂ)
    (h1 : 0 < cross (b - a) (x - a)) (h2 : 0 < cross (c - b) (x - b))
    (h3 : 0 < cross (a - c) (x - c)) :
    0 < cross (x - a) (c - x) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ :=
    inTriangleStrict_pos_convexCombo a b c x h1 h2 h3
  simp_all +decide [ cross ];
  rw [ ← eq_sub_iff_add_eq' ] at hsum ; subst_vars ; nlinarith

/-! ## Nesting of strict interiors

A point strictly inside the positively-oriented sub-triangle `a, q, c` (where
`q` is itself strictly inside the positively-oriented `a, b, c`) is strictly
inside `a, b, c`.  Proof: both points are strict convex combinations (via
`inTriangleStrict_pos_convexCombo`); substituting `q`'s combination into `x`'s
gives `x` as a strict convex combination of `a, b, c`, and
`convexCombo_pos_inTriangleStrict` (with `subTri_axc_orient_pos` supplying the
orientation of `a, q, c`) closes it. -/

/-
Strict interiors nest: if `q` is in the positively-oriented strict interior
    of `a, b, c` and `x` is in the positively-oriented strict interior of the
    sub-triangle `a, q, c`, then `x` is in the (positively-oriented) strict
    interior of `a, b, c`.
-/
lemma inTriangleStrict_pos_nest (a b c q x : ℂ)
    (hq1 : 0 < cross (b - a) (q - a)) (hq2 : 0 < cross (c - b) (q - b))
    (hq3 : 0 < cross (a - c) (q - c))
    (hx1 : 0 < cross (q - a) (x - a)) (hx2 : 0 < cross (c - q) (x - q))
    (hx3 : 0 < cross (a - c) (x - c)) :
    0 < cross (b - a) (x - a) ∧ 0 < cross (c - b) (x - b)
      ∧ 0 < cross (a - c) (x - c) := by
  unfold cross at *;
  refine' ⟨ _, _, _ ⟩ <;> contrapose! hq1;
  · norm_num [ Complex.ext_iff ] at * ; nlinarith;
  · norm_num [ Complex.ext_iff ] at * ; nlinarith;
  · linarith

/-! ## Emptiness of the region beyond the farthest vertex

The farthest-from-`a–c` vertex `q` chosen in Step 2 (via `exists_max_cross`)
has the property that no candidate vertex is *strictly farther* from the base
line `a–c`.  The signed distance of a point `z` from the line `a–c` is, up to
the positive factor `‖c-a‖`, the cross product `cross (c-a) (z-a)`. -/

/-
Maximality of the farthest vertex `q`: no vertex `y` of the candidate list
    `S` is strictly farther from the base line `a–c` than `q`.  This is the
    emptiness of the region of the corner triangle lying strictly beyond `q`,
    which makes the diagonal `v–q` of Meisters' Step 2 valid.
-/
lemma farthest_region_empty (a c q : ℂ) (S : List ℂ)
    (hmax : ∀ z ∈ S, cross (c - a) (z - a) ≤ cross (c - a) (q - a))
    (y : ℂ) (hy : y ∈ S) :
    ¬ (cross (c - a) (q - a) < cross (c - a) (y - a)) := by
  exact not_lt_of_ge ( hmax y hy )

end HexArea

end