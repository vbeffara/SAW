/-
# Ear-existence geometry, part VI: segment non-crossing from same-side cross signs

This file continues the plane-geometry preparation begun in
`RequestProject.SAWUmlaufEar`, `RequestProject.SAWUmlaufEarExist`,
`RequestProject.SAWUmlaufEarConvex`, `RequestProject.SAWUmlaufEarEmpty` and
`RequestProject.SAWUmlaufEarExtreme` for the single remaining topological core
of the discrete Hopf Umlaufsatz, the two-ears / ear-existence theorem
`exists_ear_clip` (in `RequestProject.SAWUmlaufPolygon`).

Recall Meisters' ear-existence argument:

1. pick the *extreme* (leftmost, then lowest) vertex `v` of the polygon; it is a
   convex corner;
2. if its neighbour-triangle `a, v, c` contains no other vertex, `v` is an ear;
   otherwise pick the vertex farthest from the base diagonal and recurse;
3. clipping the ear (replacing the two edges `a–v`, `v–c` by the single diagonal
   `a–c`) preserves planar simplicity, non-degeneracy, turning and orientation.

The genuinely topological half of Step 3 — that the **new diagonal `a–c` does
not cross any other polygon edge**, so `PolygonSimple` is preserved — rests on a
purely algebraic, fully reusable plane-geometry fact: *two segments are disjoint
as soon as both endpoints of one lie strictly on the same side of the line
through the other*.  The 2-D cross product `HexArea.cross` is exactly the signed
side test, so this is a clean `cross`-bilinearity computation.  This file
isolates and **proves** that fact and its companions:

* `cross_combo_segment` — for a point `u` on `segment ℝ p q`, the side test
  `cross (q - p) (u - p)` vanishes (the segment lies on its own carrier line);
  the symmetric building block of all the disjointness arguments.
* `segment_disjoint_of_strictSameSide` — if
  `0 < cross (q-p) (r-p) * cross (q-p) (s-p)` (i.e. `r` and `s` are strictly on
  the *same* side of the line `p–q`), then `segment ℝ p q` and `segment ℝ r s`
  are disjoint.  This is exactly the test used to show the clipped diagonal does
  not meet the far edges of the polygon.
* `inTriangleStrict_diag_side` — a strict interior point `x` of the corner
  triangle `a, b, c` lies strictly on the **same side of the base diagonal
  `a–c` as the apex `b`**: `0 < cross (c-a) (x-a) * cross (c-a) (b-a)`.  Via the
  barycentric backbone (`inTriangleStrict_convexCombo`) the apex weight is the
  positive proportionality factor.  This links the empty-triangle / interior
  machinery of the earlier parts to the same-side disjointness test above.

This file is **preparation**: it is imported by
`RequestProject.SAWUmlaufPolygon` (hence transitively from
`RequestProject.SAWFinal`), so it is part of the build chain.  Its lemmas are
designed to be consumed by the eventual proof of `exists_ear_clip`; they are not
yet referenced by another declaration only because the core they feed is still
open.  This is intentional, recorded partial progress, not a dead branch.
-/

import Mathlib
import RequestProject.SAWUmlaufEar
import RequestProject.SAWUmlaufEarConvex
import RequestProject.SAWUmlaufEarExtreme

open Complex

noncomputable section

namespace HexArea

/-! ## The carrier-line side test vanishes on the segment -/

/-- A point `u` on `segment ℝ p q` lies on the line through `p` and `q`: its
    side test `cross (q - p) (u - p)` vanishes.  (Just `cross_eq_zero_of_mem_segment`
    re-exported under the `p, q` naming used by the disjointness lemmas.) -/
lemma cross_combo_segment (p q u : ℂ) (hu : u ∈ segment ℝ p q) :
    cross (q - p) (u - p) = 0 :=
  cross_eq_zero_of_mem_segment p q u hu

/-! ## Same-side disjointness of segments -/

/-
**Same-side disjointness.**  If both endpoints `r` and `s` of one segment lie
    strictly on the *same* side of the line through the other segment's endpoints
    `p, q` — i.e. the two side tests `cross (q-p) (r-p)` and `cross (q-p) (s-p)`
    have a strictly positive product (same nonzero sign) — then the two segments
    `segment ℝ p q` and `segment ℝ r s` are disjoint.

    This is the algebraic heart of the planar-simplicity-preservation half of an
    ear clip: it lets one conclude that the clipped diagonal `a–c` misses any
    edge whose two endpoints lie strictly on one side of the line `a–c`.
-/
lemma segment_disjoint_of_strictSameSide (p q r s : ℂ)
    (h : 0 < cross (q - p) (r - p) * cross (q - p) (s - p)) :
    Disjoint (segment ℝ p q) (segment ℝ r s) := by
  refine' Set.disjoint_left.mpr _;
  intro x hx₁ hx₂; rcases hx₁ with ⟨ u, v, hu, hv, huv, rfl ⟩ ; rcases hx₂ with ⟨ w, z, hw, hz, hwz, hx ⟩ ; simp_all +decide ;
  -- By the properties of the cross product, we can expand and simplify the expression.
  have h_expand : w * cross (q - p) (r - p) + z * cross (q - p) (s - p) = v * cross (q - p) (q - p) := by
    simp_all +decide [ Complex.ext_iff, cross ];
    grind +ring;
  simp_all +decide [ cross_eq_zero_self ];
  cases le_or_gt 0 ( cross ( q - p ) ( r - p ) ) <;> cases le_or_gt 0 ( cross ( q - p ) ( s - p ) ) <;> nlinarith [ mul_self_pos.mpr ( show cross ( q - p ) ( r - p ) ≠ 0 from fun h' => by norm_num [ h' ] at h ), mul_self_pos.mpr ( show cross ( q - p ) ( s - p ) ≠ 0 from fun h' => by norm_num [ h' ] at h ) ]

/-! ## A strict interior point lies on the apex side of the base diagonal -/

/-
A strict interior point `x` of the corner triangle `a, b, c` lies strictly
    on the **same side of the base diagonal `a–c` as the apex `b`**:
    `0 < cross (c-a) (x-a) * cross (c-a) (b-a)`.

    Writing `x = α•a + β•b + γ•c` as a strict convex combination
    (`inTriangleStrict_convexCombo`), the side test telescopes to
    `cross (c-a) (x-a) = β · cross (c-a) (b-a)` with `β > 0`, so the product is
    `β · (cross (c-a) (b-a))² > 0` (the square is nonzero because a
    strict-interior triangle is non-degenerate, `inTriangleStrict_nondeg`).
-/
lemma inTriangleStrict_diag_side (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    0 < cross (c - a) (x - a) * cross (c - a) (b - a) := by
  unfold inTriangleStrict at h;
  unfold cross at *;
  cases h <;> norm_num at * <;> nlinarith

end HexArea

end