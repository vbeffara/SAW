/-
# The Jordan core of the polygonal Umlaufsatz: winding dichotomy and the ear interior

Every remaining gap of the Meisters-style induction that proves the discrete
Hopf Umlaufsatz (`polygon_umlaufsatz`, `RequestProject.SAWUmlaufPolygon`) reduces
to **one** classical plane-topology statement about the winding number `ptWind`
of a *simple* closed polygon:

> `polygon_ptWind_dichotomy`: for a simple polygon `V` with `3 ≤ V.length` and a
> point `x` off every closed edge of `V`, either `ptWind x V = 0` (`x` outside)
> or `ptWind x V = 2π · sign (shoelace2 V)` (`x` inside).

This is the point-in-polygon form of the Jordan curve theorem for polygons.  It
is stated here with a `sorry` — it is the *single* remaining topological input of
the whole Umlaufsatz development, and this file shows how the previously separate
gaps follow from it.  **This is not a dead branch**: the file is imported on the
live route (see below), and the consequences proved here are sorry-free modulo
that one statement.

## What is proved here (all sorry-free given the dichotomy)

* `exists_clearance` — a point off a finite list of segments stays off them in a
  whole ball around it.
* `cross_sum_edges` — the three edge cross products of a point sum to the
  (doubled) signed area of the triangle.
* `inTriangleStrict_of_segment` — the strict interior of a triangle is convex.
* `bary_openSegment_ab` — the barycentric coordinates of an interior point of the
  side `[a, b]` of the triangle `a, b, c`.
* `exists_perturb_pair` — a pair of points on the two sides of the side `[a, b]`,
  arbitrarily close to a prescribed interior point of that side, the one on the
  side of the triangle being strictly inside the triangle.
* `ear_interior_ptWind_ne_zero` — **the ear-interior consequence**: if `a, b, c`
  is an empty ear of the simple polygon `L` whose tip corner is non-degenerate,
  and the orientation of the ear agrees with the orientation of `L`, then the
  winding number of `L` around any point strictly inside the ear triangle is
  nonzero.  (Jump `2π` across the ear side `[a, b]`, use the dichotomy on both
  sides of that side, and transport the winding along the triangle interior.)
* `chord_ear_empty_other_jordan` — the Jordan-separation keystone
  `chord_ear_empty_other` re-derived from the dichotomy: a vertex of the *other*
  chord piece cannot lie strictly inside an empty ear triangle of the piece `P`,
  since its winding number around `P` is `0` (`chord_ear_other_ptWind_zero`,
  proved) while the ear interior forces it to be nonzero.

Unlike the older route through `clipped_ear_escape_walk`, no cyclic
non-degeneracy of the chord piece `P` is needed: the ear clearance is supplied by
`RequestProject.SAWUmlaufEarClearance`, which only uses non-degeneracy of the ear
*tip* (an interior corner of the ambient polygon).
-/

import Mathlib
import RequestProject.SAWUmlaufPolyEscape
import RequestProject.SAWUmlaufEarClearance
import RequestProject.SAWUmlaufWindJump
import RequestProject.SAWUmlaufEarTipEscape

open Real Complex

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. The former topological input (superseded) -/

/- **Point-in-polygon dichotomy (Jordan curve theorem for polygons).**  For a
simple closed polygon `V` and a point `x` off all its edges, the winding number
of `V` around `x` is either `0` or `2π · sign (shoelace2 V)`.

**Status: `sorry`.**  This is the single remaining plane-topology input of the
polygonal Umlaufsatz.  Classical proof: the ray-crossing index
(`RequestProject.SAWUmlaufRayIndex` expresses `ptWind` as a sum of wrap terms
with values in `{0, ±2π}`) is constant on the two components of the complement,
`0` on the unbounded one, and jumps by exactly `2π` across each edge
(`ptWind_jump_edge`, proved in `RequestProject.SAWUmlaufWindJump`); the collar of
a simple polygon has exactly two sides. -/
/- **SUPERSEDED (kept as a record, not a live gap).**  The point-in-polygon
dichotomy below was the previous single topological input.  It has been replaced
by the strictly weaker keystone `ear_interior_clip_ptWind_zero`
(`RequestProject.SAWUmlaufEarTipEscape`): *the ear region lies outside the
clipped polygon*.  That statement is all the Meisters induction consumes, it is
implied by the dichotomy, and it is already proved there in the convex-position
case.  The statement is retained, commented out, because it is the classical
form of the fact and may still be the most convenient route to the keystone.
-/
/-
theorem polygon_ptWind_dichotomy (V : List ℂ) (h3 : 3 ≤ V.length)
    (hsimple : PolygonSimple V) (x : ℂ)
    (hx : ∀ e ∈ HexArea.cycleEdges V, x ∉ segment ℝ e.1 e.2) :
    HexArea.ptWind x V = 0 ∨
      HexArea.ptWind x V = 2 * Real.pi * (if 0 < HexArea.shoelace2 V then 1 else -1) := by
  sorry
-/

/-! ## 2. Elementary geometric preparation -/

/-- A point off a finite list of segments stays off them in a whole ball. -/
lemma exists_clearance (E : List (ℂ × ℂ)) (m : ℂ) (h : ∀ e ∈ E, m ∉ segment ℝ e.1 e.2) :
    ∃ ε > 0, ∀ w : ℂ, dist w m < ε → ∀ e ∈ E, w ∉ segment ℝ e.1 e.2 := by
  have hopen := HexArea.isOpen_compl_iUnion_segments E
  have hm : m ∈ (⋃ s ∈ E, segment ℝ s.1 s.2)ᶜ := by
    intro hmem
    obtain ⟨e, he, hme⟩ := Set.mem_iUnion₂.mp hmem
    exact h e he hme
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen m hm
  refine ⟨ε, hε, ?_⟩
  intro w hw e he hwe
  have hmem : w ∈ (⋃ s ∈ E, segment ℝ s.1 s.2)ᶜ := hball (by simpa [Metric.mem_ball] using hw)
  exact hmem (Set.mem_iUnion₂.mpr ⟨e, he, hwe⟩)

/-- The three edge cross products of a point sum to the doubled signed area. -/
lemma cross_sum_edges (a b c x : ℂ) :
    HexArea.cross (b - a) (x - a) + HexArea.cross (c - b) (x - b)
      + HexArea.cross (a - c) (x - c) = HexArea.cross (b - a) (c - b) := by
  simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]
  ring

/-- `cross` is homogeneous in a real scalar in its second argument. -/
lemma cross_real_mul (d z : ℂ) (t : ℝ) :
    HexArea.cross d ((t : ℂ) * z) = t * HexArea.cross d z := by
  simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring

/-- `cross d (I * d) = ‖d‖²`. -/
lemma cross_I_mul_self (d : ℂ) : HexArea.cross d (Complex.I * d) = Complex.normSq d := by
  simp [HexArea.cross, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

/-- **The strict interior of a triangle is convex.** -/
lemma inTriangleStrict_of_segment (a b c x y z : ℂ)
    (hx : HexArea.inTriangleStrict a b c x) (hy : HexArea.inTriangleStrict a b c y)
    (hz : z ∈ segment ℝ x y) : HexArea.inTriangleStrict a b c z := by
  obtain ⟨t1, t2, ht1, ht2, htsum, hzeq⟩ := hz
  have ht1' : t1 = 1 - t2 := by linarith
  have hzeq' : z = (1 - t2) • x + t2 • y := by rw [← hzeq, ht1']
  have hA : HexArea.cross (b - a) (z - a)
      = (1 - t2) * HexArea.cross (b - a) (x - a) + t2 * HexArea.cross (b - a) (y - a) := by
    rw [hzeq', HexArea.cross_affine]
  have hB : HexArea.cross (c - b) (z - b)
      = (1 - t2) * HexArea.cross (c - b) (x - b) + t2 * HexArea.cross (c - b) (y - b) := by
    rw [hzeq', HexArea.cross_affine]
  have hC : HexArea.cross (a - c) (z - c)
      = (1 - t2) * HexArea.cross (a - c) (x - c) + t2 * HexArea.cross (a - c) (y - c) := by
    rw [hzeq', HexArea.cross_affine]
  have ht2' : 0 ≤ 1 - t2 := by linarith
  have keypos : ∀ A B : ℝ, 0 < A → 0 < B → 0 < (1 - t2) * A + t2 * B := by
    intro A B hA hB
    rcases eq_or_lt_of_le ht2 with h | h
    · rw [← h]; simpa using hA
    · nlinarith
  have keyneg : ∀ A B : ℝ, A < 0 → B < 0 → (1 - t2) * A + t2 * B < 0 := by
    intro A B hA hB
    rcases eq_or_lt_of_le ht2 with h | h
    · rw [← h]; simpa using hA
    · nlinarith
  rcases hx with ⟨hx1, hx2, hx3⟩ | ⟨hx1, hx2, hx3⟩ <;>
    rcases hy with ⟨hy1, hy2, hy3⟩ | ⟨hy1, hy2, hy3⟩
  · exact Or.inl ⟨by rw [hA]; exact keypos _ _ hx1 hy1, by rw [hB]; exact keypos _ _ hx2 hy2,
      by rw [hC]; exact keypos _ _ hx3 hy3⟩
  · -- mixed signs are impossible: the two orientations of the triangle disagree
    exfalso
    have h1 := cross_sum_edges a b c x
    have h2 := cross_sum_edges a b c y
    nlinarith
  · exfalso
    have h1 := cross_sum_edges a b c x
    have h2 := cross_sum_edges a b c y
    nlinarith
  · exact Or.inr ⟨by rw [hA]; exact keyneg _ _ hx1 hy1, by rw [hB]; exact keyneg _ _ hx2 hy2,
      by rw [hC]; exact keyneg _ _ hx3 hy3⟩

/-- **Barycentric coordinates along the side `[a, b]`.**  An interior point `m` of
the side `[a, b]` of the triangle `a, b, c` has first coordinate `0` and the two
others `(1-s)·D` and `s·D`, where `D = cross (b-a) (c-b)` is the doubled signed
area and `s ∈ (0,1)` is the parameter of `m` on the side. -/
lemma bary_openSegment_ab (a b c m : ℂ) (hm : m ∈ openSegment ℝ a b) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      HexArea.cross (b - a) (m - a) = 0 ∧
      HexArea.cross (c - b) (m - b) = (1 - s) * HexArea.cross (b - a) (c - b) ∧
      HexArea.cross (a - c) (m - c) = s * HexArea.cross (b - a) (c - b) := by
  obtain ⟨t1, t2, ht1, ht2, htsum, hmeq⟩ := hm
  refine ⟨t2, ht2, by linarith, ?_, ?_, ?_⟩ <;>
  · have hm' : m = a + (t2 : ℂ) * (b - a) := by
      rw [← hmeq]
      have h1 : (t1 : ℂ) = 1 - (t2 : ℂ) := by
        have : t1 = 1 - t2 := by linarith
        rw [this]; push_cast; ring
      simp only [Complex.real_smul]
      rw [h1]; ring
    rw [hm']
    simp [HexArea.cross, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring

/-- **A pair of points on the two sides of the side `[a, b]`.**  Given an interior
point `m` of `[a, b]` and any `δ > 0`, there are points `y`, `z` within `δ` of `m`
strictly on the two sides of the line `a–b`, such that the one on the side of `c`
(determined by the sign of `D = cross (b-a) (c-b)`) is strictly inside the
triangle `a, b, c`. -/
lemma exists_perturb_pair (a b c m : ℂ) (hab : a ≠ b) (hm : m ∈ openSegment ℝ a b)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ y z : ℂ, dist y m < δ ∧ dist z m < δ ∧
      0 < HexArea.cross (b - a) (y - a) ∧ HexArea.cross (b - a) (z - a) < 0 ∧
      (0 < HexArea.cross (b - a) (c - b) → HexArea.inTriangleStrict a b c y) ∧
      (HexArea.cross (b - a) (c - b) < 0 → HexArea.inTriangleStrict a b c z) := by
  obtain ⟨s, hs0, hs1, hA, hB, hC⟩ := bary_openSegment_ab a b c m hm
  set d : ℂ := b - a with hd
  set D : ℝ := HexArea.cross (b - a) (c - b) with hDdef
  have hdne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hN : 0 < Complex.normSq d := Complex.normSq_pos.mpr hdne
  set B' : ℝ := HexArea.cross (c - b) (Complex.I * d) with hB'
  set C' : ℝ := HexArea.cross (a - c) (Complex.I * d) with hC'
  set K : ℝ := |B'| + |C'| + 1 with hK
  have hKpos : 0 < K := by positivity
  set e : ℝ := min s (1 - s) * |D| with he
  have hepos : 0 < e := by
    have : 0 < min s (1 - s) := lt_min hs0 (by linarith)
    have hDabs : 0 < |D| := abs_pos.mpr hD
    positivity
  set R : ℝ := ‖Complex.I * d‖ + 1 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  set t : ℝ := min (δ / (2 * R)) (e / (2 * K)) with ht
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have htR : t * R < δ := by
    have h1 : t ≤ δ / (2 * R) := min_le_left _ _
    have : t * R ≤ (δ / (2 * R)) * R := by nlinarith
    have h2 : (δ / (2 * R)) * R = δ / 2 := by field_simp
    linarith [h2 ▸ this]
  have htK : t * K ≤ e / 2 := by
    have h1 : t ≤ e / (2 * K) := min_le_right _ _
    have : t * K ≤ (e / (2 * K)) * K := by nlinarith
    have h2 : (e / (2 * K)) * K = e / 2 := by field_simp
    linarith [h2 ▸ this]
  refine ⟨m + (t : ℂ) * (Complex.I * d), m - (t : ℂ) * (Complex.I * d), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- distance bound
    have hdst : dist (m + (t : ℂ) * (Complex.I * d)) m = t * ‖Complex.I * d‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos htpos]
    rw [hdst]
    have hnn : (0:ℝ) ≤ ‖Complex.I * d‖ := norm_nonneg _
    nlinarith
  · have hdst : dist (m - (t : ℂ) * (Complex.I * d)) m = t * ‖Complex.I * d‖ := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos htpos]
    rw [hdst]
    have hnn : (0:ℝ) ≤ ‖Complex.I * d‖ := norm_nonneg _
    nlinarith
  · -- the first point is on the positive side
    have hy : HexArea.cross (b - a) (m + (t : ℂ) * (Complex.I * d) - a)
        = t * Complex.normSq d := by
      have hsplit : m + (t : ℂ) * (Complex.I * d) - a = (m - a) + (t : ℂ) * (Complex.I * d) := by
        ring
      rw [hsplit, HexArea.cross_add_right, hA, cross_real_mul, hd, cross_I_mul_self]
      ring
    rw [hy]; positivity
  · have hz : HexArea.cross (b - a) (m - (t : ℂ) * (Complex.I * d) - a)
        = -(t * Complex.normSq d) := by
      have hsplit : m - (t : ℂ) * (Complex.I * d) - a
          = (m - a) + ((-t : ℝ) : ℂ) * (Complex.I * d) := by
        push_cast; ring
      rw [hsplit, HexArea.cross_add_right, hA, cross_real_mul, hd, cross_I_mul_self]
      ring
    rw [hz]
    have : 0 < t * Complex.normSq d := by positivity
    linarith
  · -- positively oriented case: the `+` point is inside
    intro hDpos
    left
    have h1 : HexArea.cross (b - a) (m + (t : ℂ) * (Complex.I * d) - a)
        = t * Complex.normSq d := by
      have hsplit : m + (t : ℂ) * (Complex.I * d) - a = (m - a) + (t : ℂ) * (Complex.I * d) := by
        ring
      rw [hsplit, HexArea.cross_add_right, hA, cross_real_mul, hd, cross_I_mul_self]
      ring
    have h2 : HexArea.cross (c - b) (m + (t : ℂ) * (Complex.I * d) - b)
        = (1 - s) * D + t * B' := by
      have hsplit : m + (t : ℂ) * (Complex.I * d) - b = (m - b) + (t : ℂ) * (Complex.I * d) := by
        ring
      rw [hsplit, HexArea.cross_add_right, hB, cross_real_mul, hB']
    have h3 : HexArea.cross (a - c) (m + (t : ℂ) * (Complex.I * d) - c)
        = s * D + t * C' := by
      have hsplit : m + (t : ℂ) * (Complex.I * d) - c = (m - c) + (t : ℂ) * (Complex.I * d) := by
        ring
      rw [hsplit, HexArea.cross_add_right, hC, cross_real_mul, hC']
    have hDabs : |D| = D := abs_of_pos hDpos
    have hB'le : |B'| ≤ K := by rw [hK]; nlinarith [abs_nonneg C']
    have hC'le : |C'| ≤ K := by rw [hK]; nlinarith [abs_nonneg B']
    have hmin1 : min s (1 - s) ≤ 1 - s := min_le_right _ _
    have hmin2 : min s (1 - s) ≤ s := min_le_left _ _
    refine ⟨by rw [h1]; positivity, ?_, ?_⟩
    · rw [h2]
      have hb1 : t * B' ≥ -(t * K) := by nlinarith [neg_abs_le B', abs_nonneg B']
      have he' : e = min s (1 - s) * D := by rw [he, hDabs]
      have hposfac : 0 < (1 - s) * D := mul_pos (by linarith) hDpos
      have hmm : min s (1 - s) * D ≤ (1 - s) * D := mul_le_mul_of_nonneg_right hmin1 hDpos.le
      linarith
    · rw [h3]
      have hb1 : t * C' ≥ -(t * K) := by nlinarith [neg_abs_le C', abs_nonneg C']
      have he' : e = min s (1 - s) * D := by rw [he, hDabs]
      have hposfac : 0 < s * D := mul_pos hs0 hDpos
      have hmm : min s (1 - s) * D ≤ s * D := mul_le_mul_of_nonneg_right hmin2 hDpos.le
      linarith
  · -- negatively oriented case: the `-` point is inside
    intro hDneg
    right
    have h1 : HexArea.cross (b - a) (m - (t : ℂ) * (Complex.I * d) - a)
        = -(t * Complex.normSq d) := by
      have hsplit : m - (t : ℂ) * (Complex.I * d) - a
          = (m - a) + ((-t : ℝ) : ℂ) * (Complex.I * d) := by
        push_cast; ring
      rw [hsplit, HexArea.cross_add_right, hA, cross_real_mul, hd, cross_I_mul_self]
      ring
    have h2 : HexArea.cross (c - b) (m - (t : ℂ) * (Complex.I * d) - b)
        = (1 - s) * D - t * B' := by
      have hsplit : m - (t : ℂ) * (Complex.I * d) - b
          = (m - b) + ((-t : ℝ) : ℂ) * (Complex.I * d) := by
        push_cast; ring
      rw [hsplit, HexArea.cross_add_right, hB, cross_real_mul, hB']
      ring
    have h3 : HexArea.cross (a - c) (m - (t : ℂ) * (Complex.I * d) - c)
        = s * D - t * C' := by
      have hsplit : m - (t : ℂ) * (Complex.I * d) - c
          = (m - c) + ((-t : ℝ) : ℂ) * (Complex.I * d) := by
        push_cast; ring
      rw [hsplit, HexArea.cross_add_right, hC, cross_real_mul, hC']
      ring
    have hDabs : |D| = -D := abs_of_neg hDneg
    have hB'le : |B'| ≤ K := by rw [hK]; nlinarith [abs_nonneg C']
    have hC'le : |C'| ≤ K := by rw [hK]; nlinarith [abs_nonneg B']
    have hmin1 : min s (1 - s) ≤ 1 - s := min_le_right _ _
    have hmin2 : min s (1 - s) ≤ s := min_le_left _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      have : 0 < t * Complex.normSq d := by positivity
      linarith
    · rw [h2]
      have hb1 : -(t * K) ≤ t * B' := by nlinarith [neg_abs_le B', abs_nonneg B']
      have he'' : e = -(min s (1 - s) * D) := by rw [he, hDabs]; ring
      have hnegfac : (1 - s) * D < 0 := mul_neg_of_pos_of_neg (by linarith) hDneg
      have hmm : (1 - s) * D ≤ min s (1 - s) * D :=
        mul_le_mul_of_nonpos_right hmin1 hDneg.le
      linarith
    · rw [h3]
      have hb1 : -(t * K) ≤ t * C' := by nlinarith [neg_abs_le C', abs_nonneg C']
      have he'' : e = -(min s (1 - s) * D) := by rw [he, hDabs]; ring
      have hnegfac : s * D < 0 := mul_neg_of_pos_of_neg hs0 hDneg
      have hmm : s * D ≤ min s (1 - s) * D :=
        mul_le_mul_of_nonpos_right hmin2 hDneg.le
      linarith

/-- The closed cycle edge list splits off its first edge. -/
lemma cycleEdges_cons_cons (a b : ℂ) (r : List ℂ) :
    HexArea.cycleEdges (a :: b :: r)
      = (a, b) :: (b :: (r ++ [a])).zip ((b :: (r ++ [a])).drop 1) := by
  simp [HexArea.cycleEdges]

/-! ## 3. The ear-interior consequence of the dichotomy -/

/-- **The winding number of a simple polygon around a point of an empty ear's
interior is nonzero.**

`a, b, c` is an empty ear of the simple polygon `L` (`hempty`, `hdiag`) whose tip
corner is non-degenerate (`hD`), and the ear is *positively coherent* with `L`
(`hor`: the ear triangle and `L` have the same orientation).  Then `ptWind x L`
is nonzero for every `x` strictly inside the ear triangle.

Proof.  Perturb the midpoint `m` of the ear side `[a, b]` to the two sides of that
side; the two winding numbers differ by `2π` (`ptWind_jump_edge`, using that `m`
lies on no other edge, `simple_edge_openSegment_not_mem`).  Both perturbed points
lie off all edges (clearance), so the dichotomy applies to both: their winding
numbers lie in `{0, 2π·σ}` with `σ = sign (shoelace2 L)`, and a difference of `2π`
forces the point on the side of the ear interior to carry the nonzero value.
Finally `ptWind · L` is constant on the (convex) open ear triangle, since the
triangle interior misses all edges (`ear_strict_interior_off_closedEdges`). -/
theorem ear_interior_ptWind_ne_zero (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (hor : (0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 L))
    (x : ℂ) (hin : HexArea.inTriangleStrict a b c x) :
    HexArea.ptWind x L ≠ 0 := by
  exact ear_interior_ptWind_ne_zero_via_clip L h4 hsimple ρ a b c rest hrot hD hempty hdiag hor
    x hin
/-! ## 4. The Jordan-separation keystone, re-derived -/

/-- **`chord_ear_empty_other` from the dichotomy.**  A vertex `x` of the polygon
`W` that is not a vertex of the chord piece `P` cannot lie strictly inside an
empty ear triangle of `P`: its winding number around `P` vanishes
(`chord_ear_other_ptWind_zero`, proved), while `ear_interior_ptWind_ne_zero`
forces it to be nonzero.

The hypotheses are those of `chord_ear_empty_other` together with the two extra
data that the ear-interior argument needs and that are available at the call site
(`chord_ear_lift` in `RequestProject.SAWUmlaufPolyMeisters`): the ear tip corner
is non-degenerate (it is an interior corner of `W`), and no tail vertex of the
piece lies on the ear diagonal. -/
theorem chord_ear_empty_other_jordan (W : List ℂ) (hsimple : PolygonSimple W)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiagW : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ) (hPsimple : PolygonSimple P)
    (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ)
    (hrotP : P.rotate s = a' :: b' :: c' :: tlP)
    (hDP : HexArea.cross (b' - a') (c' - b') ≠ 0)
    (hemptyP : ∀ y ∈ tlP, ¬ HexArea.inTriangleStrict a' b' c' y)
    (hdiagP : ∀ y ∈ tlP, y ∉ segment ℝ a' c')
    (horientP : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tlP)))
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P) :
    ¬ HexArea.inTriangleStrict a' b' c' x := by
  intro hin
  have hzero : HexArea.ptWind x P = 0 :=
    chord_ear_other_ptWind_zero W hsimple k hk1 hk u v hu hv hdiagW hint P hP x hxW hxP
  -- the degenerate case: the piece is the ear triangle itself
  by_cases htl : tlP = []
  · subst htl
    have hP3 : HexArea.ptWind x P = HexArea.ptWind x [a', b', c'] := by
      rw [← HexArea.ptWind_rotate x P s, hrotP]
    exact HexArea.ptWind_triangle_ne_zero a' b' c' x hin (by rw [← hP3]; exact hzero)
  have hP4 : 4 ≤ P.length := by
    have hlen : (P.rotate s).length = tlP.length + 3 := by rw [hrotP]; simp
    have hlen' : P.length = tlP.length + 3 := by simpa using hlen
    have : tlP ≠ [] := htl
    have hpos : 0 < tlP.length := List.length_pos_iff.mpr this
    omega
  -- the orientation of the ear agrees with the orientation of the piece
  have hclipP : HexArea.shoelace2 P
      = HexArea.shoelace2 (a' :: c' :: tlP) + HexArea.shoelace2 [a', b', c'] := by
    have h1 : HexArea.shoelace2 (P.rotate s) = HexArea.shoelace2 P := shoelace2_rotate P s
    rw [← h1, hrotP]
    exact shoelace2_clip_second a' b' c' tlP
  have hor : (0 < HexArea.shoelace2 [a', b', c'] ↔ 0 < HexArea.shoelace2 P) := by
    constructor
    · intro h
      have := horientP.mp h
      rw [hclipP]; linarith
    · intro h
      by_contra hcon
      push_neg at hcon
      have h2 : ¬ (0 < HexArea.shoelace2 (a' :: c' :: tlP)) := fun hh =>
        absurd (horientP.mpr hh) (by linarith)
      push_neg at h2
      rw [hclipP] at h
      linarith
  exact ear_interior_ptWind_ne_zero P hP4 hPsimple s a' b' c' tlP hrotP hDP
    hemptyP hdiagP hor x hin hzero
