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
import RequestProject.SAWUmlaufEarExtreme
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

/-- **Prepend one step to an escape walk (generic brick).**  If `R x y` and there
    is an `R`-walk from `y` reaching the predicate `P`, then there is an `R`-walk
    from `x` reaching `P`.  This is exactly what lets the clipped-ear escape walk
    first step from the interior point `x` to the ear apex `b'`, then continue
    with any escape walk that starts at `b'`. -/
lemma exists_walk_cons {α : Type*} (R : α → α → Prop) (P : α → Prop) (x y : α)
    (hxy : R x y)
    (h : ∃ zs : List α, List.IsChain R (y :: zs) ∧ P (zs.getLastD y)) :
    ∃ zs : List α, List.IsChain R (x :: zs) ∧ P (zs.getLastD x) := by
  obtain ⟨zs, hchain, hlast⟩ := h
  refine ⟨y :: zs, ?_, ?_⟩
  · exact List.isChain_cons_cons.mpr ⟨hxy, hchain⟩
  · cases zs with
    | nil => simpa using hlast
    | cons w ws => simpa [List.getLastD] using hlast

/-- **Two-step escape walk (generic brick).**  If `R x y`, `R y z` and `P z`,
    then there is an `R`-walk `x :: [y, z]` reaching `P`.  Matches the
    interior → apex → hull-exterior escape shape directly. -/
lemma exists_walk_of_two_steps {α : Type*} (R : α → α → Prop) (P : α → Prop)
    (x y z : α) (hxy : R x y) (hyz : R y z) (hz : P z) :
    ∃ zs : List α, List.IsChain R (x :: zs) ∧ P (zs.getLastD x) := by
  refine ⟨[y, z], ?_, ?_⟩
  · exact List.isChain_cons_cons.mpr
      ⟨hxy, List.isChain_cons_cons.mpr ⟨hyz, List.IsChain.singleton z⟩⟩
  · simpa using hz

/-- **Convex combination of three points lies in their convex hull.**  A generic
    reusable brick: any barycentric combination `α•a + β•b + γ•c` with
    nonnegative weights summing to `1` is in `convexHull ℝ {a,b,c}`. -/
lemma combo3_mem_convexHull (a b c : ℂ) (α β γ : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hsum : α + β + γ = 1) :
    α • a + β • b + γ • c ∈ convexHull ℝ ({a, b, c} : Set ℂ) := by
  have hconv := convex_convexHull ℝ ({a,b,c} : Set ℂ)
  have ha : a ∈ convexHull ℝ ({a,b,c} : Set ℂ) := subset_convexHull ℝ _ (by simp)
  have hb : b ∈ convexHull ℝ ({a,b,c} : Set ℂ) := subset_convexHull ℝ _ (by simp)
  have hc : c ∈ convexHull ℝ ({a,b,c} : Set ℂ) := subset_convexHull ℝ _ (by simp)
  by_cases hs : β + γ = 0
  · have hβ0 : β = 0 := by linarith
    have hγ0 : γ = 0 := by linarith
    have hα1 : α = 1 := by linarith
    simp only [hβ0, hγ0, hα1, zero_smul, add_zero, one_smul]; exact ha
  · have hs' : 0 < β + γ := lt_of_le_of_ne (by linarith) (Ne.symm hs)
    have hy : (β/(β+γ))•b + (γ/(β+γ))•c ∈ convexHull ℝ ({a,b,c} : Set ℂ) :=
      hconv hb hc (by positivity) (by positivity) (by field_simp)
    have hx : α•a + (β+γ)•((β/(β+γ))•b + (γ/(β+γ))•c) ∈ convexHull ℝ ({a,b,c} : Set ℂ) :=
      hconv ha hy hα (by linarith) (by linarith)
    have heq : α•a+β•b+γ•c = α•a + (β+γ)•((β/(β+γ))•b + (γ/(β+γ))•c) := by
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hs, mul_div_cancel₀ _ hs]; abel
    rw [heq]; exact hx

/-- **A strict interior point of a triangle lies in its (closed) convex hull.**
    Escape-walk brick: converts `inTriangleStrict` into hull membership via the
    barycentric backbone `inTriangleStrict_convexCombo`. -/
lemma inTriangleStrict_mem_convexHull (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    x ∈ convexHull ℝ ({a, b, c} : Set ℂ) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ := inTriangleStrict_convexCombo a b c x h
  exact combo3_mem_convexHull a b c α β γ hα.le hβ.le hγ.le hsum

/-- **The segment from a strict interior point to the apex stays in the triangle
    hull (escape-walk brick).**  Since both `x` (strict interior) and `b` (a
    vertex) lie in the convex hull `convexHull ℝ {a,b,c}`, the whole segment
    `x–b` does too.  This is the geometric core letting the escape walk's first
    step to the ear apex avoid any edge that is disjoint from the ear triangle. -/
lemma segment_apex_subset_hull (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    segment ℝ x b ⊆ convexHull ℝ ({a, b, c} : Set ℂ) := by
  have hx : x ∈ convexHull ℝ ({a,b,c} : Set ℂ) := inTriangleStrict_mem_convexHull a b c x h
  have hb : b ∈ convexHull ℝ ({a,b,c} : Set ℂ) := subset_convexHull ℝ _ (by simp)
  exact (convex_convexHull ℝ _).segment_subset hx hb

/-- **Step-to-apex avoids any hull-disjoint edge (escape-walk brick).**  If the
    edge segment `d–e` is disjoint from the ear triangle `convexHull ℝ {a,b,c}`,
    then the escape step `x–b` (from a strict interior point `x` to the apex `b`)
    is disjoint from it, since `x–b ⊆ convexHull ℝ {a,b,c}`. -/
lemma segment_apex_disjoint_of_hull_disjoint (a b c x d e : ℂ)
    (h : inTriangleStrict a b c x)
    (hde : Disjoint (segment ℝ d e) (convexHull ℝ ({a, b, c} : Set ℂ))) :
    Disjoint (segment ℝ x b) (segment ℝ d e) :=
  (hde.mono_right (segment_apex_subset_hull a b c x h)).symm

/-- **A far point on any ray lies outside a finite hull, with nonnegative
    parameter (escape-walk brick).**  Strengthening of
    `exists_far_not_mem_convexHull`: the escape parameter `T` can always be taken
    `≥ 0`, so the far point lies on the *forward* ray `{x + T•d : T ≥ 0}`.  This
    is what lets a straight forward-ray escape feed a single-step escape walk. -/
lemma exists_far_not_mem_convexHull_nonneg (S : Finset ℂ) (p d : ℂ) (hd : d ≠ 0) :
    ∃ T : ℝ, 0 ≤ T ∧ p + (T : ℂ) * d ∉ convexHull ℝ (S : Set ℂ) := by
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have h_bounded : Bornology.IsBounded (convexHull ℝ (S : Set ℂ)) := by
    simp +zetaDelta at *
    exact S.finite_toSet.isBounded
  obtain ⟨R, hR⟩ := h_bounded.exists_pos_norm_le
  have hTnn : (0:ℝ) ≤ (R + ‖p‖ + 1) / ‖d‖ :=
    div_nonneg (by linarith [hR.1, norm_nonneg p]) hdpos.le
  set T : ℝ := (R + ‖p‖ + 1) / ‖d‖ with hTdef
  refine ⟨T, hTnn, fun h => ?_⟩
  have hTd : T * ‖d‖ = R + ‖p‖ + 1 := by
    rw [hTdef, div_mul_cancel₀ _ (ne_of_gt hdpos)]
  have hnorm : ‖p + (T : ℂ) * d‖ ≤ R := hR.2 _ h
  have hnT : ‖(T : ℂ) * d‖ = T * ‖d‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hTnn]
  have hcancel : (p + (T : ℂ) * d) + (-p) = (T : ℂ) * d := by ring
  have h1 : ‖(T : ℂ) * d‖ ≤ ‖p + (T : ℂ) * d‖ + ‖p‖ := by
    have := norm_add_le (p + (T : ℂ) * d) (-p)
    rw [hcancel, norm_neg] at this
    exact this
  rw [hnT, hTd] at h1
  linarith

/-- **Single straight forward-ray escape walk (generic brick).**  If there is a
    nonzero direction `d` such that the escape relation `R` holds from `x` to
    *every* forward-ray point `x + T•d` (`T ≥ 0`), then there is an `R`-walk from
    `x` whose endpoint lies outside `convexHull ℝ S`.  Combines
    `exists_far_not_mem_convexHull_nonneg` (pick `T` large enough to leave the
    hull) with `exists_walk_of_step` (a single step suffices).  This is a
    reusable reduction of the escape-walk goal to *finding an escaping forward
    ray direction* — the shape shared by both escape-walk residues in
    `SAWUmlaufPolygon`.  (It only applies when a straight ray escapes, so it is
    banked preparation rather than a universal solver: a non-convex "pocket"
    point may need a genuine polyline.) -/
lemma exists_escape_walk_of_ray (S : Finset ℂ) (R : ℂ → ℂ → Prop) (x d : ℂ)
    (hd : d ≠ 0) (hstep : ∀ T : ℝ, 0 ≤ T → R x (x + (T : ℂ) * d)) :
    ∃ zs : List ℂ, List.IsChain R (x :: zs) ∧
      (zs.getLastD x) ∉ convexHull ℝ (S : Set ℂ) := by
  obtain ⟨T, hT0, hTout⟩ := exists_far_not_mem_convexHull_nonneg S x d hd
  exact exists_walk_of_step R (· ∉ convexHull ℝ (S : Set ℂ)) x (x + (T : ℂ) * d)
    (hstep T hT0) hTout

end HexArea

end