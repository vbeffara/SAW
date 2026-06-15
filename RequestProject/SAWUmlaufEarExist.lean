/-
# Ear-existence geometry, part II: collinearity, extrema and triangle symmetry

This file continues the plane-geometry preparation begun in
`RequestProject.SAWUmlaufEar` for the single remaining topological core of the
discrete Hopf Umlaufsatz, the two-ears / ear-existence theorem
`exists_ear_clip` (in `RequestProject.SAWUmlaufPolygon`).

Recall Meisters' ear-existence argument:

1. pick the *extreme* (leftmost, then lowest) vertex `z` of the polygon; it is a
   convex corner (`SAWUmlaufEar.exists_lex_min_mem` supplies `z`);
2. if its neighbour-triangle `p, z, n` contains no other vertex, it is an ear;
   otherwise pick the vertex *farthest from the base diagonal* `p–n`; that
   vertex is a convex corner whose neighbour-triangle is empty, hence an ear;
3. clipping the ear preserves planar simplicity, non-degeneracy, turning and
   orientation.

Step 2 rests on two purely geometric facts, both proved here, both reusable:

* `collinear_iff_cross_eq_zero` — three points are collinear iff the cross
  product of their edge vectors vanishes (the degeneracy test for a candidate
  diagonal);
* `exists_max_cross` — over a nonempty list of points there is one maximizing
  the signed distance `cross d (·)` to a fixed direction `d` (the *farthest*
  vertex from the base diagonal, picked in Step 2).

We also record the symmetry/distinctness facts of the strict-interior predicate
`SAWUmlaufEar.inTriangleStrict`:

* `inTriangleStrict_cyclic` — invariance under cyclic relabeling `a,b,c ↦ b,c,a`
  of the triangle (the three edges play symmetric roles);
* `inTriangleStrict_ne_ab/bc/ca` — a triangle with a strict interior point has
  three pairwise distinct vertices.

This file is **preparation**: it is imported by
`RequestProject.SAWUmlaufPolygon` (hence transitively from
`RequestProject.SAWFinal`), so it is part of the build chain.  Its lemmas are
designed to be consumed by the eventual proof of `exists_ear_clip`; they are not
yet referenced by another declaration only because the core they feed is still
open.  This is intentional, recorded partial progress, not a dead branch.
-/

import Mathlib
import RequestProject.SAWUmlaufEar

open Complex

noncomputable section

namespace HexArea

/-! ## Collinearity ↔ vanishing cross product

For the ear search a candidate diagonal `a–c` is *degenerate* exactly when some
third point `x` is collinear with `a, c`.  In the plane this is detected by the
2-D cross product: `cross (c - a) (x - a) = 0`. -/

/-
Three points `a, c, x` in `ℂ` are collinear iff the cross product of the two
    edge vectors from `a` vanishes.  (If `a = c` both sides hold trivially: two
    points are always collinear and `cross 0 _ = 0`.)
-/
lemma collinear_iff_cross_eq_zero (a c x : ℂ) :
    Collinear ℝ ({a, c, x} : Set ℂ) ↔ cross (c - a) (x - a) = 0 := by
  constructor <;> intro h;
  · rw [ collinear_iff_exists_forall_eq_smul_vadd ] at h;
    obtain ⟨ p₀, v, h ⟩ := h; obtain ⟨ r₁, hr₁ ⟩ := h a ( by norm_num ) ; obtain ⟨ r₂, hr₂ ⟩ := h c ( by norm_num ) ; obtain ⟨ r₃, hr₃ ⟩ := h x ( by norm_num ) ; simp_all +decide [ Complex.ext_iff, cross ] ;
    ring;
  · rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; use a ; norm_num;
    by_cases hca : c = a;
    · exact ⟨ x - a, ⟨ 0, by simp +decide [ hca ] ⟩, ⟨ 1, by simp +decide ⟩ ⟩;
    · -- Since $c \neq a$, we can take $v = c - a$.
      use c - a;
      simp_all +decide [ Complex.ext_iff, cross ];
      by_cases hca : c.re = a.re;
      · simp_all +decide [ sub_eq_iff_eq_add ];
        exact ⟨ ⟨ 1, by ring ⟩, ⟨ ( x.im - a.im ) / ( c.im - a.im ), by rw [ div_mul_cancel₀ _ ( sub_ne_zero_of_ne ‹_› ) ] ; ring ⟩ ⟩;
      · exact ⟨ ⟨ 1, by ring, by ring ⟩, ⟨ ( x.re - a.re ) / ( c.re - a.re ), by rw [ div_mul_cancel₀ _ ( sub_ne_zero_of_ne hca ) ] ; ring, by rw [ div_mul_eq_mul_div, eq_comm ] ; rw [ div_add', div_eq_iff ] <;> cases lt_or_gt_of_ne hca <;> nlinarith ⟩ ⟩

/-! ## The farthest vertex from a base line -/

/-
Over a nonempty list `L` of points there is one maximizing the signed
    distance `cross d (· - a)` to the fixed direction `d` based at `a`.  Applied
    with `d = c - a` this selects the polygon vertex *farthest from the base
    diagonal* `a–c`, the pivot of Meisters' Step 2.
-/
lemma exists_max_cross (d a : ℂ) (L : List ℂ) (hL : L ≠ []) :
    ∃ x ∈ L, ∀ y ∈ L, cross d (y - a) ≤ cross d (x - a) := by
  obtain ⟨x, hx⟩ : ∃ x ∈ L.toFinset, ∀ y ∈ L.toFinset, cross d (y - a) ≤ cross d (x - a) := by
    exact Finset.exists_max_image _ _ ⟨ _, List.mem_toFinset.mpr ( Classical.choose_spec ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr hL ) ) ) ⟩;
  aesop

/-! ## Symmetry and distinctness of the strict-interior predicate -/

/-- The strict-interior predicate is invariant under the cyclic relabeling
    `a, b, c ↦ b, c, a` of the triangle: the three oriented edges play
    symmetric roles. -/
lemma inTriangleStrict_cyclic (a b c x : ℂ) :
    inTriangleStrict a b c x ↔ inTriangleStrict b c a x := by
  unfold inTriangleStrict
  constructor <;> rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  · exact Or.inl ⟨h2, h3, h1⟩
  · exact Or.inr ⟨h2, h3, h1⟩
  · exact Or.inl ⟨h3, h1, h2⟩
  · exact Or.inr ⟨h3, h1, h2⟩

/-- A triangle with a strict interior point has `a ≠ b`. -/
lemma inTriangleStrict_ne_ab (a b c x : ℂ) (h : inTriangleStrict a b c x) : a ≠ b := by
  rintro rfl
  rcases h with ⟨h1, _, _⟩ | ⟨h1, _, _⟩ <;> simp [cross] at h1

/-- A triangle with a strict interior point has `b ≠ c`. -/
lemma inTriangleStrict_ne_bc (a b c x : ℂ) (h : inTriangleStrict a b c x) : b ≠ c := by
  rintro rfl
  rcases h with ⟨_, h2, _⟩ | ⟨_, h2, _⟩ <;> simp [cross] at h2

/-- A triangle with a strict interior point has `c ≠ a`. -/
lemma inTriangleStrict_ne_ca (a b c x : ℂ) (h : inTriangleStrict a b c x) : c ≠ a := by
  rintro rfl
  rcases h with ⟨_, _, h3⟩ | ⟨_, _, h3⟩ <;> simp [cross] at h3

end HexArea

end