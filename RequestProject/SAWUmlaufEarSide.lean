/-
# Ear-existence geometry, part VI: interior points lie on the apex side of the diagonal

This file continues the plane-geometry preparation begun in
`RequestProject.SAWUmlaufEar`, `RequestProject.SAWUmlaufEarExist`,
`RequestProject.SAWUmlaufEarConvex`, `RequestProject.SAWUmlaufEarEmpty` and
`RequestProject.SAWUmlaufEarExtreme` for the single remaining topological core
of the discrete Hopf Umlaufsatz, the two-ears / ear-existence theorem
`exists_front_ear` (in `RequestProject.SAWUmlaufPolygon`).

Recall Meisters' ear-existence argument:

1. pick the *extreme* (leftmost, then lowest) vertex `v` of the polygon; it is a
   convex corner;
2. with neighbours `a, c`, look at the corner triangle `a, v, c`; if it contains
   no other vertex, `v` is an ear; otherwise pick the vertex *farthest from the
   base diagonal* `a–c` and split along the diagonal `v–(that vertex)`, then
   recurse;
3. clipping an ear preserves planar simplicity, non-degeneracy, turning and
   orientation.

A key geometric fact powering both the diagonal split of Step 2 and the
planar-simplicity preservation of Step 3 is that **the strict interior of the
corner triangle lies entirely strictly on the apex (`v`) side of the base
diagonal `a–c`**.  Concretely, the signed distance of an interior point `x` from
the line `a–c`, measured by the cross product `cross (c-a) (x-a)`, has the *same
nonzero sign* as the signed distance `cross (c-a) (b-a)` of the apex `b`.  This
is the reusable building block isolated and **proved here**:

* `inTriangleStrict_apex_sameSide` — a strict interior point `x` of the triangle
  `a, b, c` satisfies `0 < cross (c-a) (x-a) * cross (c-a) (b-a)` (so `x` and the
  apex `b` are strictly on the same side of the base line `a–c`).

  Proof: write `x = α•a + β•b + γ•c` as a strict convex combination
  (`SAWUmlaufEarExtreme.inTriangleStrict_convexCombo`); a direct bilinear
  computation collapses `cross (c-a) (x-a)` to `β · cross (c-a) (b-a)` (the
  `a`- and `c`-terms drop out, being parallel to the base), and `β > 0` together
  with non-degeneracy `cross (c-a) (b-a) ≠ 0` (from
  `SAWUmlaufEar.inTriangleStrict_nondeg`) gives the positive product.

This file is **preparation**: it is imported by
`RequestProject.SAWUmlaufPolygon` (hence transitively from
`RequestProject.SAWFinal`), so it is part of the build chain.  Its lemma is
designed to be consumed by the eventual proof of `exists_front_ear`; it is not
yet referenced by another declaration only because the core it feeds is still
open.  This is intentional, recorded partial progress, not a dead branch.
-/

import Mathlib
import RequestProject.SAWUmlaufEar
import RequestProject.SAWUmlaufEarConvex
import RequestProject.SAWUmlaufEarExtreme

open Complex

noncomputable section

namespace HexArea

/-- **An interior point lies strictly on the apex side of the base diagonal.**
    If `x` is in the strict interior of the triangle `a, b, c` then `x` and the
    apex `b` are strictly on the same side of the base line `a–c`: the signed
    distances `cross (c-a) (x-a)` and `cross (c-a) (b-a)` have the same nonzero
    sign, so their product is positive.

    This is the geometric content used in Meisters' diagonal split (the chosen
    interior vertex is strictly *inside*, hence strictly on the apex side, so the
    diagonal from the apex genuinely separates it from the base) and in the
    planar-simplicity preservation of an ear clip. -/
lemma inTriangleStrict_apex_sameSide (a b c x : ℂ)
    (h : inTriangleStrict a b c x) :
    0 < cross (c - a) (x - a) * cross (c - a) (b - a) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ := inTriangleStrict_convexCombo a b c x h
  have hnd : cross (b - a) (c - b) ≠ 0 := inTriangleStrict_nondeg a b c _ h
  have key : cross (c - a) ((α • a + β • b + γ • c) - a) = β * cross (c - a) (b - a) := by
    simp only [cross, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination ((c.re - a.re) * a.im - (c.im - a.im) * a.re) * hsum
  rw [key]
  have hflip : cross (b - a) (c - b) = - cross (c - a) (b - a) := by
    simp only [cross, Complex.sub_re, Complex.sub_im]; ring
  have hcab : cross (c - a) (b - a) ≠ 0 := by
    intro hh; apply hnd; rw [hflip, hh, neg_zero]
  have h2 : 0 < cross (c - a) (b - a) * cross (c - a) (b - a) := mul_self_pos.mpr hcab
  nlinarith [mul_pos hβ h2]

end HexArea

end
