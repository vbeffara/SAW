/-
# Exterior points of a polygon: convex-separation winding vanishing

This file develops a genuinely reusable "outside ⟹ winding `0`" tool for the
point-winding number `HexArea.ptWind`, strengthening the half-plane vanishing
criterion `HexArea.ptWind_eq_zero_of_halfplane`
(`RequestProject.SAWUmlaufPtWindHalfPlane`) from a *given* separating direction
to the intrinsic hypothesis "`x` is not in the convex hull of the vertices".

The main result `HexArea.ptWind_zero_of_not_mem_convexHull` says: if the point
`x` lies outside the (closed) convex hull of the vertex list `P`, then the
point-winding of the closed polygon `P` about `x` is `0`.  The proof separates
`x` from the compact convex hull by the geometric Hahn–Banach theorem
(`geometric_hahn_banach_point_closed`), turns the separating continuous
`ℝ`-linear functional `f : ℂ →L[ℝ] ℝ` into a complex test direction
`d = ⟨f 1, -(f I)⟩` (so that `f w = (w * d).re`), and feeds the resulting strict
half-plane bound into `ptWind_eq_zero_of_halfplane`.

This is the **convex base case** of the ear-clipping induction behind the two
remaining Jordan-separation residues of the discrete Umlaufsatz
(`clipped_ear_ptWind_zero`, `chord_ear_other_ptWind_zero` in
`RequestProject.SAWUmlaufPolygon`): a point strictly outside a *convex* polygon
(in particular a triangle) never winds around it.  It is imported by
`RequestProject.SAWUmlaufPolygon`, where it is documented as preparation for
those residues.  NOT a dead branch.
-/

import Mathlib
import RequestProject.SAWUmlaufPtWindHalfPlane

namespace HexArea

open Complex

/-- **Realise a continuous `ℝ`-linear functional on `ℂ` as a test direction.**
    For `f : ℂ →L[ℝ] ℝ` and `d := ⟨f 1, -(f Complex.I)⟩`, we have
    `f w = (w * d).re` for every `w`. -/
lemma linearFunctional_eq_mul_re (f : ℂ →L[ℝ] ℝ) (w : ℂ) :
    f w = (w * (⟨f 1, -(f Complex.I)⟩ : ℂ)).re := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul]
  simp only [smul_eq_mul, Complex.mul_re]
  ring

/-- **Outside the convex hull ⟹ winding `0` (the convex base case).**  If `x`
    does not lie in the convex hull of the vertex list `P`, then the point-winding
    number of the closed polygon `P` about `x` is `0`.  Proved by strictly
    separating `x` from the (compact, hence closed, convex) hull with
    `geometric_hahn_banach_point_closed`, converting the separating functional to
    a complex test direction via `linearFunctional_eq_mul_re`, and applying
    `ptWind_eq_zero_of_halfplane`. -/
lemma ptWind_zero_of_not_mem_convexHull (x : ℂ) (P : List ℂ)
    (hx : x ∉ convexHull ℝ (P.toFinset : Set ℂ)) :
    ptWind x P = 0 := by
  -- The convex hull of a finite set is compact, hence closed and convex.
  have hfin : (P.toFinset : Set ℂ).Finite := P.toFinset.finite_toSet
  have hconv : Convex ℝ (convexHull ℝ (P.toFinset : Set ℂ)) := convex_convexHull ℝ _
  have hclosed : IsClosed (convexHull ℝ (P.toFinset : Set ℂ)) :=
    (hfin.isCompact_convexHull).isClosed
  -- Separate `x` from the hull.
  obtain ⟨f, u, hfx, hfb⟩ := geometric_hahn_banach_point_closed hconv hclosed hx
  -- The test direction.
  set d : ℂ := ⟨f 1, -(f Complex.I)⟩ with hd
  refine ptWind_eq_zero_of_halfplane x d P ?_
  intro v hv
  have hvhull : v ∈ convexHull ℝ (P.toFinset : Set ℂ) := by
    apply subset_convexHull ℝ (P.toFinset : Set ℂ)
    simpa using hv
  have hfv : u < f v := hfb v hvhull
  -- `((v - x) * d).re = f (v - x) = f v - f x > 0`.
  have hkey : ((v - x) * d).re = f v - f x := by
    rw [← linearFunctional_eq_mul_re f (v - x), map_sub]
  rw [hkey]
  linarith
