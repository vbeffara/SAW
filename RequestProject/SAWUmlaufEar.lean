/-
# Ear-existence preparation for the planar-polygon Umlaufsatz

This file develops **reusable plane-geometry building blocks** for the single
remaining topological core of the discrete Hopf Umlaufsatz, the two-ears /
ear-existence theorem `exists_ear_clip` (in
`RequestProject.SAWUmlaufPolygon`).

Meisters' proof of ear existence proceeds in three steps:

1. pick the *extreme* (leftmost, then lowest) vertex of the polygon; it is a
   convex corner;
2. either its neighbour-triangle contains no other vertex (then it is an ear),
   or the vertex farthest from the base diagonal yields a splitting diagonal and
   one recurses;
3. clipping the ear preserves planar simplicity, non-degeneracy, turning and
   orientation.

The genuinely irreducible topological content (`exists_ear_clip`) is still a
`sorry`, but the elementary geometric facts those three steps rest on are
isolated and **proved here**:

* `cross`-bilinearity / `smul` lemmas (`HexArea.cross_smul_left`,
  `HexArea.cross_sub_right`, `HexArea.cross_sub_left`) — the algebra of the
  2-D cross product used for every orientation computation;
* `cross_edges_eq_shoelace2_triple` — the orientation of the corner triangle
  `a,b,c` equals its signed area `HexArea.shoelace2 [a,b,c]` (the Step-1/Step-3
  bridge between convexity of a corner and the sign of the area it cuts off);
* `cross_eq_zero_of_mem_segment` / `collinear_of_mem_segment` — a point on the
  segment `[a,b]` is collinear with `a,b` (used to detect when a candidate
  diagonal is degenerate);
* `exists_lex_min_mem` — every nonempty vertex list has a lexicographically
  minimal (leftmost-lowest) vertex, the convex extreme vertex Step 1 starts
  from.

This file is **preparation**: it is imported by
`RequestProject.SAWUmlaufPolygon` (hence transitively from
`RequestProject.SAWFinal`), so it is part of the build chain, and its lemmas are
designed to be consumed by the eventual proof of `exists_ear_clip`.  They are
not yet referenced by another declaration because the core they feed is still
open; this is intentional, recorded partial progress, not a dead branch.
-/

import Mathlib
import RequestProject.SAWSignedArea

open Complex

noncomputable section

namespace HexArea

/-! ## Bilinearity of the 2-D cross product

`cross z w = z.re * w.im - z.im * w.re` is `ℝ`-bilinear and antisymmetric.
`cross_add_left/right` are already in `RequestProject.SAWSignedArea`; here we add
the scalar and subtraction variants needed for orientation arithmetic. -/

/-- Scaling the left argument scales the cross product. -/
lemma cross_smul_left (t : ℝ) (z w : ℂ) :
    cross (t • z) w = t * cross z w := by
  simp [cross]; ring

/-- Scaling the right argument scales the cross product. -/
lemma cross_smul_right (t : ℝ) (z w : ℂ) :
    cross z (t • w) = t * cross z w := by
  simp [cross]; ring

/-- The cross product distributes over subtraction in the right argument. -/
lemma cross_sub_right (z w v : ℂ) :
    cross z (w - v) = cross z w - cross z v := by
  simp [cross]; ring

/-- The cross product distributes over subtraction in the left argument. -/
lemma cross_sub_left (z w v : ℂ) :
    cross (z - w) v = cross z v - cross w v := by
  simp [cross]; ring

/-! ## Corner orientation equals the signed area of the corner triangle -/

/-- The orientation of the corner `a → b → c` (the cross product of its two edge
    vectors) equals the signed area `shoelace2 [a,b,c]` of the triangle it cuts
    off.  This is the bridge between *convexity of a corner* (sign of the edge
    cross product) and the *signed area* the corner contributes, used in Step 1
    (the extreme vertex is convex, so its corner triangle has the polygon's
    orientation) and Step 3 (orientation is preserved under ear removal). -/
lemma cross_edges_eq_shoelace2_triple (a b c : ℂ) :
    cross (b - a) (c - b) = shoelace2 [a, b, c] := by
  rw [shoelace2_triple]; simp [cross]; ring

/-! ## Collinearity of points on a segment -/

/-
A point on the segment `[a,b]` is collinear with `a` and `b`: the cross
    product `cross (b-a) (x-a)` vanishes.  Used to recognise degenerate
    (collinear) candidate diagonals in the ear search.
-/
lemma cross_eq_zero_of_mem_segment (a b x : ℂ) (hx : x ∈ segment ℝ a b) :
    cross (b - a) (x - a) = 0 := by
  simp_all +decide [ segment_eq_image, Complex.ext_iff, cross ];
  grind

/-
A point on the segment `[a,b]` is collinear with `a` and `b`.
-/
lemma collinear_of_mem_segment (a b x : ℂ) (hx : x ∈ segment ℝ a b) :
    Collinear ℝ ({a, b, x} : Set ℂ) := by
  obtain ⟨ u, v, hu, hv, huv, rfl ⟩ := hx;
  rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use a ; norm_num;
  refine' ⟨ b - a, ⟨ 1, by norm_num ⟩, ⟨ v, _ ⟩ ⟩ ; rw [ ← eq_sub_iff_add_eq' ] at huv ; push_cast [ huv ] ; ring

/-! ## Strict interior of an oriented triangle

The ear search (Step 2) tests whether the corner triangle `a,b,c` contains any
other polygon vertex, and, if so, picks the one *farthest from the base line*
`a-c`.  Both are phrased through the 2-D cross product: a point `x` is strictly
inside the triangle iff the three edge-orientation cross products all share the
triangle's orientation sign, and the signed distance of `x` from the line `a-c`
is `cross (c-a) (x-a)` (up to the positive factor `‖c-a‖`). -/

/-- `x` is strictly inside the oriented triangle `a,b,c`: the three edge
    cross products `cross (b-a) (x-a)`, `cross (c-b) (x-b)`, `cross (a-c) (x-c)`
    are all strictly positive or all strictly negative (the two cases are the
    two orientations of `a,b,c`). -/
def inTriangleStrict (a b c x : ℂ) : Prop :=
    (0 < cross (b - a) (x - a) ∧ 0 < cross (c - b) (x - b) ∧ 0 < cross (a - c) (x - c)) ∨
    (cross (b - a) (x - a) < 0 ∧ cross (c - b) (x - b) < 0 ∧ cross (a - c) (x - c) < 0)

/-- A point strictly inside the triangle `a,b,c` is distinct from the vertex `a`
    (its first cross product with the `a`-edge would vanish otherwise). -/
lemma inTriangleStrict_ne_a (a b c x : ℂ) (h : inTriangleStrict a b c x) : x ≠ a := by
  rintro rfl
  rcases h with ⟨h1, _, _⟩ | ⟨h1, _, _⟩ <;> simp [cross] at h1

/-- A point strictly inside the triangle `a,b,c` is distinct from the vertex `b`. -/
lemma inTriangleStrict_ne_b (a b c x : ℂ) (h : inTriangleStrict a b c x) : x ≠ b := by
  rintro rfl
  rcases h with ⟨_, h2, _⟩ | ⟨_, h2, _⟩ <;> simp [cross] at h2

/-- A point strictly inside the triangle `a,b,c` is distinct from the vertex `c`. -/
lemma inTriangleStrict_ne_c (a b c x : ℂ) (h : inTriangleStrict a b c x) : x ≠ c := by
  rintro rfl
  rcases h with ⟨_, _, h3⟩ | ⟨_, _, h3⟩ <;> simp [cross] at h3

/-
If the triangle `a,b,c` has a strict interior point then it is
    non-degenerate: its orientation `cross (b-a) (c-b)` is nonzero.  (Sum of the
    three interior cross products equals the triangle orientation
    `cross (b-a) (c-b) = shoelace2 [a,b,c]`, and they share a strict sign.)
-/
lemma inTriangleStrict_nondeg (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    cross (b - a) (c - b) ≠ 0 := by
  cases h <;> simp_all +decide [ inTriangleStrict ];
  · unfold cross at * ; norm_num at * ; linarith;
  · unfold cross at *; norm_num [ Complex.ext_iff ] at *; linarith;

/-! ## The extreme (leftmost-lowest) vertex -/

/-
Every nonempty list of complex points has a *lexicographically minimal*
    element: a point `z` that is leftmost (smallest real part), with ties broken
    by lowest (smallest imaginary part).  This is the convex extreme vertex from
    which Meisters' ear search begins (Step 1).
-/
lemma exists_lex_min_mem (L : List ℂ) (hL : L ≠ []) :
    ∃ z ∈ L, ∀ w ∈ L, z.re < w.re ∨ (z.re = w.re ∧ z.im ≤ w.im) := by
  induction' L using List.reverseRecOn with a L ih <;> simp_all +decide;
  by_cases ha : a = [] <;> simp_all +decide;
  grind

end HexArea

end