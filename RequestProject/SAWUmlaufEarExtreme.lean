/-
# Ear-existence geometry, part V: the extreme vertex is a convex-hull vertex

This file continues the plane-geometry preparation begun in
`RequestProject.SAWUmlaufEar`, `RequestProject.SAWUmlaufEarExist`,
`RequestProject.SAWUmlaufEarConvex` and `RequestProject.SAWUmlaufEarEmpty` for
the single remaining topological core of the discrete Hopf Umlaufsatz, the
two-ears / ear-existence theorem `exists_ear_clip` (in
`RequestProject.SAWUmlaufPolygon`).

Recall Meisters' ear-existence argument:

1. pick the *extreme* (leftmost, then lowest) vertex `v` of the polygon; it is a
   convex corner — equivalently, a vertex of the convex hull, so it is never in
   the interior of any triangle spanned by the other vertices;
2. if its neighbour-triangle contains no other vertex, `v` is an ear; otherwise
   pick the vertex *farthest from the base diagonal* and recurse;
3. clipping the ear preserves planar simplicity, non-degeneracy, turning and
   orientation.

Step 1 rests on the convexity of the extreme vertex.  The reusable geometric
content of that convexity, isolated and **proved here**, is that *a strict
interior point of a triangle is never lexicographically minimal among the
vertices* — an interior point is a strict convex combination, hence its
coordinates are strict weighted averages of the vertices' coordinates, so some
vertex strictly beats it in the (real part, then imaginary part) order.  Applied
to the lex-minimal vertex `v` of the polygon (supplied by
`SAWUmlaufEar.exists_lex_min_mem`) this says `v` is **never** in the strict
interior of any triangle spanned by polygon vertices — precisely the statement
that the extreme vertex is a convex-hull vertex, which is what makes Step 1's
chosen corner convex.

These lemmas **consume** the barycentric backbone of
`RequestProject.SAWUmlaufEarConvex` (`inTriangleStrict_pos_convexCombo`) and the
strict-interior predicate of `RequestProject.SAWUmlaufEar`
(`inTriangleStrict`), so those files are no longer feeding only the open core.

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

/-! ## A strict interior point is a strict convex combination (both orientations)

`SAWUmlaufEarConvex.inTriangleStrict_pos_convexCombo` extracts a strict convex
combination from the *positively*-oriented strict interior.  The negatively
oriented case `a, b, c` reduces to the positively oriented case for the
relabelling `a, c, b` (swapping `b` and `c` flips the orientation), so a strict
interior point of either orientation is a strict convex combination. -/

/-
A point in the strict interior (either orientation) of a triangle `a, b, c`
    is a strict convex combination of the three vertices: there are positive
    weights summing to `1` with `x = α•a + β•b + γ•c`.
-/
lemma inTriangleStrict_convexCombo (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
      x = α • a + β • b + γ • c := by
  simp_all +decide [ inTriangleStrict ];
  obtain h | h := h;
  · have := HexArea.inTriangleStrict_pos_convexCombo a b c x h.1 h.2.1 h.2.2; aesop;
  · obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hx⟩ : ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧ x = α • a + β • c + γ • b := by
      apply inTriangleStrict_pos_convexCombo;
      · unfold cross at *; norm_num [ Complex.ext_iff ] at *; linarith;
      · unfold cross at *; norm_num at *; linarith;
      · unfold cross at *; norm_num [ Complex.ext_iff ] at *; linarith;
    exact ⟨ α, hα, γ, hγ, β, hβ, by linarith, by simpa [ add_comm, add_left_comm, add_assoc ] using hx ⟩

/-! ## The extreme vertex is a convex-hull vertex -/

/-- The real and imaginary parts of a strict convex combination are the
    corresponding strict weighted averages.  A convenience unpacking used to run
    the lex-minimality argument. -/
lemma convexCombo_re_im (a b c : ℂ) (α β γ : ℝ) :
    (α • a + β • b + γ • c).re = α * a.re + β * b.re + γ * c.re ∧
    (α • a + β • b + γ • c).im = α * a.im + β * b.im + γ * c.im := by
  constructor <;> simp [Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im] <;> ring

/-
**A strict interior point is never lexicographically minimal among the
    triangle's vertices.**  If `x` lies strictly inside the triangle `a, b, c`,
    then it is *not* the case that `x` is `≤` every vertex in the
    (real part, then imaginary part) order: some vertex strictly precedes `x`.

    Proof: `x = α•a + β•b + γ•c` with positive weights summing to `1`
    (`inTriangleStrict_convexCombo`).  If every vertex `w` satisfied
    `x.re < w.re ∨ (x.re = w.re ∧ x.im ≤ w.im)`, then in particular each
    `w.re ≥ x.re`; as `x.re` is their strict positive-weight average this forces
    every `w.re = x.re`, whence each `w.im ≥ x.im` and `x.im` is their average,
    forcing every `w.im = x.im`, i.e. `a = b = c = x`, contradicting that the
    triangle is non-degenerate (`inTriangleStrict_nondeg`).
-/
lemma inTriangleStrict_not_lexMin (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    ¬ (∀ w ∈ [a, b, c], x.re < w.re ∨ (x.re = w.re ∧ x.im ≤ w.im)) := by
  obtain ⟨α, β, γ, hα_pos, hβ_pos, hγ_pos, h_sum, hx⟩ := inTriangleStrict_convexCombo a b c x h;
  -- Suppose for contradiction that `∀ w ∈ [a,b,c], x.re < w.re ∨ (x.re = w.re ∧ x.im ≤ w.im)`.
  by_contra h_contra
  have h_re : a.re = x.re ∧ b.re = x.re ∧ c.re = x.re := by
    have h_re_eq : α * (a.re - x.re) + β * (b.re - x.re) + γ * (c.re - x.re) = 0 := by
      grind +suggestions;
    have h_re_eq : a.re ≥ x.re ∧ b.re ≥ x.re ∧ c.re ≥ x.re := by
      grind;
    exact ⟨ by nlinarith, by nlinarith, by nlinarith ⟩;
  have h_im : a.im = x.im ∧ b.im = x.im ∧ c.im = x.im := by
    have h_im : x.im ≤ a.im ∧ x.im ≤ b.im ∧ x.im ≤ c.im := by
      grind;
    have h_im_eq : α * (a.im - x.im) + β * (b.im - x.im) + γ * (c.im - x.im) = 0 := by
      rw [hx]
      simp [Complex.ext_iff];
      linear_combination -h_sum * ( α * a.im + β * b.im + γ * c.im );
    exact ⟨ by nlinarith, by nlinarith, by nlinarith ⟩;
  unfold inTriangleStrict at h;
  unfold cross at h; norm_num [ Complex.ext_iff, h_re, h_im ] at h;

/-
**The extreme (lex-minimal) vertex is a convex-hull vertex.**  If `v` is
    lexicographically minimal (leftmost, then lowest) among all points of `L`,
    then `v` is never in the strict interior of a triangle spanned by three
    points of `L`.  This is exactly the convexity of the extreme vertex used in
    Meisters' Step 1.

    Proof: combine `inTriangleStrict_not_lexMin` (an interior point is not
    lex-minimal among its triangle's vertices, which all lie in `L`) with the
    hypothesis that `v` is lex-minimal over all of `L`.
-/
lemma lexMin_not_inTriangleStrict (L : List ℂ) (v : ℂ)
    (hv : ∀ w ∈ L, v.re < w.re ∨ (v.re = w.re ∧ v.im ≤ w.im))
    (a b c : ℂ) (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L)
    (h : inTriangleStrict a b c v) : False := by
  convert inTriangleStrict_not_lexMin a b c v h _;
  aesop

end HexArea

end