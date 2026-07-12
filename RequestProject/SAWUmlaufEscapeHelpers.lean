/-
# Reusable geometric bricks for the escape-walk residues of the planar Umlaufsatz

This file collects small, fully general, `sorry`-free plane-geometry lemmas that
feed the two remaining *escape-walk* residues of the discrete Hopf Umlaufsatz in
`RequestProject.SAWUmlaufPolygon`:

* `clipped_ear_escape_walk` and `chord_ear_other_escape_walk`

Both of those lemmas must exhibit an edge-avoiding polyline from a forbidden
point out past the convex hull of a simple polygon.  Two of the atoms of that
construction are purely local and do **not** require any Jordan-curve content, so
they are isolated here as reusable bricks:

* `segment_apex_disjoint_base` — the segment from a strict interior point `x` of
  the corner triangle `a,b,c` to the apex `b` is disjoint from the base
  `a–c` (both `x` and `b` lie strictly on the same side of the base line).  This
  is the "avoid the ear base" clause of the escape walk.  Derived immediately
  from `HexArea.inTriangleStrict_diag_side` and
  `HexArea.segment_disjoint_of_strictSameSide`.

* `exists_far_not_mem_convexHull` — along any ray `p + T•d` (`d ≠ 0`) there is a
  parameter `T` whose point lies outside the convex hull of any finite point set
  `S` (the hull of a finite set is bounded).  This is the "reach past the convex
  hull" clause of the escape walk: it supplies the required hull-exterior
  endpoint.

**Status.**  Both lemmas are proved `sorry`-free.  They are *preparation* for the
two escape-walk residues (currently `sorry` in `SAWUmlaufPolygon`); this file is
imported by `RequestProject.SAWUmlaufPolygon` so the bricks are in scope for the
final construction.  It is **not** a dead branch.
-/

import Mathlib
import RequestProject.SAWUmlaufEar
import RequestProject.SAWUmlaufSegment

open Real Complex ComplexConjugate

noncomputable section

namespace HexArea

/-- **Segment to the apex avoids the base (escape-walk brick).**  If `x` is a
    strict interior point of the corner triangle `a, b, c`, then the segment from
    `x` to the apex `b` is disjoint from the base segment `a–c`.  Both `x` and `b`
    lie strictly on the same side of the base line `a–c`
    (`inTriangleStrict_diag_side`), so `segment_disjoint_of_strictSameSide`
    applies. -/
lemma segment_apex_disjoint_base (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    Disjoint (segment ℝ x b) (segment ℝ a c) := by
  have hside : 0 < cross (c - a) (x - a) * cross (c - a) (b - a) :=
    inTriangleStrict_diag_side a b c x h
  exact (segment_disjoint_of_strictSameSide a c x b hside).symm

/-
**A ray escapes any bounded (finite-hull) obstacle (escape-walk brick).**
    For a finite point set `S`, a base point `p`, and a nonzero direction `d`,
    some point `p + T•d` on the ray lies outside `convexHull ℝ S`.  The convex
    hull of a finite set is bounded, so a point far enough along the (unbounded)
    ray leaves it.
-/
lemma exists_far_not_mem_convexHull (S : Finset ℂ) (p d : ℂ) (hd : d ≠ 0) :
    ∃ T : ℝ, p + (T : ℂ) * d ∉ convexHull ℝ (S : Set ℂ) := by
  -- The convex hull of a finite set is bounded.
  have h_bounded : Bornology.IsBounded (convexHull ℝ (S : Set ℂ)) := by
    simp +zetaDelta at *;
    exact S.finite_toSet.isBounded;
  obtain ⟨ R, hR ⟩ := h_bounded.exists_pos_norm_le;
  -- Choose $T$ such that $|T| * ‖d‖ - ‖p‖ > R$.
  obtain ⟨ T, hT ⟩ : ∃ T : ℝ, |T| * ‖d‖ - ‖p‖ > R := by
    exact ⟨ ( R + ‖p‖ + 1 ) / ‖d‖, by rw [ abs_of_nonneg ( by exact div_nonneg ( by linarith [ norm_nonneg p ] ) ( norm_nonneg d ) ) ] ; rw [ div_mul_cancel₀ _ ( norm_ne_zero_iff.mpr hd ) ] ; linarith ⟩;
  refine' ⟨ T, fun h => _ ⟩;
  have := norm_add_le ( p + T * d ) ( -p ) ; simp_all +decide;
  linarith [ hR.2 _ h ]

/-- **Single-step reduction for escape walks (generic brick).**  To exhibit a
    walk `x :: zs` whose consecutive steps satisfy `R` and whose endpoint
    satisfies `P`, it suffices to give a single next point `y` with `R x y` and
    `P y`.  Both escape-walk residues in `SAWUmlaufPolygon`
    (`clipped_ear_escape_walk`, `chord_ear_other_escape_walk`) have exactly this
    shape (`R` = "the segment avoids every cycle edge", `P` = "outside the convex
    hull"), so this reduces the *walk* goal to producing one edge-avoiding
    segment from the forbidden point to a hull-exterior point.  Fully generic;
    `sorry`-free preparation for those residues. -/
lemma exists_walk_of_step {α : Type*} (R : α → α → Prop) (P : α → Prop)
    (x y : α) (hxy : R x y) (hy : P y) :
    ∃ zs : List α, List.IsChain R (x :: zs) ∧ P (zs.getLastD x) := by
  refine ⟨[y], ?_, ?_⟩
  · exact List.isChain_cons_cons.mpr ⟨hxy, List.IsChain.singleton y⟩
  · simpa using hy

end HexArea

end