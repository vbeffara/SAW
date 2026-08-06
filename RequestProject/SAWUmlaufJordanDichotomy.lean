import Mathlib
import RequestProject.SAWUmlaufEarClearance
import RequestProject.SAWUmlaufWindJump
import RequestProject.SAWUmlaufExterior

/-!
# `SAWUmlaufJordanDichotomy` — the point-in-polygon dichotomy and the ear keystone

This file isolates the **single remaining plane-topology input** of the polygonal
Umlaufsatz in its classical form,

> `polygon_ptWind_dichotomy` : for a simple closed polygon `V` and a point `x`
> lying on no closed edge of `V`, the winding number of `V` around `x` is either
> `0` (`x` outside) or `2π · sign (shoelace2 V)` (`x` inside),

and derives from it, **sorry-free**, the ear-region statement that the Meisters
ear-existence recursion actually consumes:

> `ear_interior_ptWind_eq` : the winding number of `V` around a point strictly
> inside an empty, coherently oriented ear triangle equals `2π · sign (shoelace2 V)`
> — in particular it is nonzero, and the *clip* `a :: c :: rest` does not wind
> around the ear region at all (`ear_interior_clip_ptWind_zero`,
> `RequestProject.SAWUmlaufEarTipEscape`).

Before this file, the keystone `ear_interior_clip_ptWind_zero` was itself a
`sorry`; it is now a theorem, and the whole Umlaufsatz development rests (apart
from the two lift residues `chord_piece_orient` and `empty_branch_bad_lift`) on
the one classical statement above.

## The proof of the keystone from the dichotomy

Let `a :: b :: c :: rest` be a rotation of `V` exhibiting an empty ear at the tip
`b`, coherently oriented with `V`.  Take the midpoint `m` of the ear side
`[a, b]`.  Because `V` is simple, `m` lies on no other closed edge
(`simple_edge_openSegment_not_mem`), so:

* the winding number jumps by exactly `2π` across that side
  (`HexArea.ptWind_jump_edge`, `RequestProject.SAWUmlaufWindJump`), between any
  two points close to `m` and strictly on opposite sides of the line `a–b`;
* such a pair exists with the point on the side of `c` lying strictly inside the
  ear triangle (`exists_perturb_pair`), and both points lie off *all* closed
  edges (`exists_clearance`).

The dichotomy applies to both points, so their winding numbers lie in
`{0, 2π·σ}`; a difference of exactly `2π` then forces the point on the ear side
to carry `2π·σ` and the other one `0` — the orientation hypothesis `hor` is
exactly what identifies which of the two points is the interior one.  Finally the
open ear triangle misses every closed edge
(`ear_strict_interior_off_closedEdges`) and is convex, so the winding number is
constant on it (`HexArea.ptWind_eq_of_segment_avoids`).

## The inductive route to the dichotomy itself (§4)

The dichotomy is *not* proved here, but the two halves of the classical
induction on the vertex count are (both sorry-free):

* `keystone_of_dichotomy_clip` — if the **clip** `C = a :: c :: rest` (one vertex
  shorter than `V`) satisfies the dichotomy, then the ear region of `V` is
  outside `C`: `ptWind x C = 0`.  This is the perturbation argument across the
  ear *base* `[a, c]` — an edge of `C` but not of `V` — combined with the ear
  coherence `0 < shoelace2 [a,b,c] ↔ 0 < shoelace2 C`.
* `dichotomy_of_keystone_clip` — conversely, if the clip satisfies the dichotomy
  and the ear region is outside the clip, then `V` satisfies the dichotomy.

Together they give the induction step `dichotomy(C) ⟹ dichotomy(V)` for a polygon
`V` possessing an empty coherently oriented ear.  What is still missing to close
the induction is the *ear existence* input at the same vertex count: the Meisters
chain proves it, but only after consuming the keystone for the (strictly shorter)
chord pieces, so closing the loop requires restating that chain relative to a
"keystone below `n`" hypothesis.  This is recorded in `PROOF_STATUS.md` as the
next task; the two lemmas above are the mathematical content of the step.

NOT a dead branch: imported by `RequestProject.SAWUmlaufEarTipEscape`, which lies
on the live route to `polygon_umlaufsatz`.
-/

open Real Complex

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. The dichotomy -/

/-- **The point-in-polygon dichotomy for the closed polygon `V`**, as a
predicate: for every point `x` off all closed edges of `V`, the winding number of
`V` around `x` is `0` or `2π · sign (shoelace2 V)`. -/
def PolyDichotomy (V : List ℂ) : Prop :=
  ∀ x : ℂ, (∀ e ∈ HexArea.cycleEdges V, x ∉ segment ℝ e.1 e.2) →
    HexArea.ptWind x V = 0 ∨
      HexArea.ptWind x V = 2 * Real.pi * (if 0 < HexArea.shoelace2 V then 1 else -1)

/-- **Point-in-polygon dichotomy (Jordan curve theorem for polygons).**

For a simple closed polygon `V` and a point `x` on no closed edge of `V`, the
winding number of `V` around `x` is either `0` or `2π · sign (shoelace2 V)`.

**Status: `sorry`.**  This is the single remaining plane-topology input of the
polygonal Umlaufsatz.  The classical proof is the ear induction whose two halves
are proved in §4 below (`keystone_of_dichotomy_clip`,
`dichotomy_of_keystone_clip`); closing it needs the ear-existence statement at
each vertex count, i.e. the Meisters chain restated relative to a "keystone for
shorter polygons" hypothesis.

NOT a dead branch: it is the sole input of `ear_interior_ptWind_eq` below, hence
of the keystone `ear_interior_clip_ptWind_zero` and of the whole ear-existence
recursion. -/
theorem polygon_ptWind_dichotomy (V : List ℂ) (h3 : 3 ≤ V.length)
    (hsimple : PolygonSimple V) : PolyDichotomy V := by
  sorry

/-! ## 2. Elementary geometric preparation

The lemmas of this section were previously located in
`RequestProject.SAWUmlaufJordanCore`; they are needed here, upstream of it. -/

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
  · exfalso
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
  · have hdst : dist (m + (t : ℂ) * (Complex.I * d)) m = t * ‖Complex.I * d‖ := by
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
  · have hy : HexArea.cross (b - a) (m + (t : ℂ) * (Complex.I * d) - a)
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
  · intro hDpos
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
  · intro hDneg
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

/-- **The path edges of a cycle presented as `a :: b :: r` are closed edges
distinct from the leading edge `(a, b)`** — provided `b` occurs only once, which
is guaranteed by `Nodup`. -/
lemma mem_closedEdges_of_mem_tail_zip (a b : ℂ) (r : List ℂ) (hnd : (a :: b :: r).Nodup)
    (p : ℂ × ℂ) (hp : p ∈ (b :: (r ++ [a])).zip ((b :: (r ++ [a])).drop 1)) :
    p ∈ closedEdges (a :: b :: r) ∧ ¬ (a = p.1 ∧ b = p.2) := by
  constructor
  · have h := cycleEdges_cons_cons a b r
    rw [HexArea.cycleEdges_eq_closedEdges] at h
    rw [h]
    exact List.mem_cons_of_mem _ hp
  · rintro ⟨-, hb⟩
    have h2 : p.2 ∈ (b :: (r ++ [a])).drop 1 := (List.of_mem_zip hp).2
    rw [← hb] at h2
    simp only [List.drop_succ_cons, List.drop_zero] at h2
    simp only [List.nodup_cons, List.mem_cons] at hnd
    rcases List.mem_append.mp h2 with h | h
    · exact hnd.2.1 h
    · simp only [List.mem_singleton] at h
      exact hnd.1 (Or.inl h.symm)

/-! ## 3. The ear-interior winding value, from the dichotomy -/

/-- **The winding number of a simple polygon around a point of an empty,
coherently oriented ear's interior is `2π · sign (shoelace2 L)`.**

This is the form of the point-in-polygon statement that the Meisters recursion
consumes; see the module docstring for the proof (jump across the ear side
`[a, b]`, dichotomy on both sides, constancy on the open ear triangle). -/
theorem ear_interior_ptWind_eq (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (hor : (0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 L))
    (x : ℂ) (hin : HexArea.inTriangleStrict a b c x) :
    HexArea.ptWind x L = 2 * Real.pi * (if 0 < HexArea.shoelace2 L then 1 else -1) := by
  classical
  -- the rotated presentation
  have hMsimple : PolygonSimple (a :: b :: c :: rest) := by
    rw [← hrot]; exact (PolygonSimple_rotate L ρ).mpr hsimple
  have hMlen : (a :: b :: c :: rest).length = L.length := by rw [← hrot]; simp
  have h4M : 4 ≤ (a :: b :: c :: rest).length := by omega
  have hMarea : HexArea.shoelace2 (a :: b :: c :: rest) = HexArea.shoelace2 L := by
    rw [← hrot]; exact shoelace2_rotate L ρ
  have hMwind : ∀ z : ℂ, HexArea.ptWind z (a :: b :: c :: rest) = HexArea.ptWind z L := by
    intro z; rw [← hrot]; exact HexArea.ptWind_rotate z L ρ
  have hnd : (a :: b :: c :: rest).Nodup := hMsimple.1
  have hab : a ≠ b := by
    simp only [List.nodup_cons, List.mem_cons] at hnd
    exact fun h => hnd.1 (Or.inl h)
  -- the leading edge and the midpoint of the ear side
  have habE : (a, b) ∈ closedEdges (a :: b :: c :: rest) := by
    have h := cycleEdges_cons_cons a b (c :: rest)
    rw [HexArea.cycleEdges_eq_closedEdges] at h
    rw [h]; exact List.mem_cons_self
  set m : ℂ := ((2⁻¹ : ℝ) : ℂ) * a + ((2⁻¹ : ℝ) : ℂ) * b with hmdef
  have hm : m ∈ openSegment ℝ a b := by
    refine ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num, ?_⟩
    simp [hmdef, Complex.real_smul]
  -- the path edges avoid `m`
  set T : List (ℂ × ℂ) :=
    (b :: ((c :: rest) ++ [a])).zip ((b :: ((c :: rest) ++ [a])).drop 1) with hT
  have hpath : ∀ p ∈ T, m ∉ segment ℝ p.1 p.2 := by
    intro p hp
    obtain ⟨hpE, hpne⟩ := mem_closedEdges_of_mem_tail_zip a b (c :: rest) hnd p hp
    exact simple_edge_openSegment_not_mem (a :: b :: c :: rest) h4M hMsimple a b p.1 p.2
      habE hpE hpne m hm
  -- the jump across the ear side
  obtain ⟨δ, hδpos, hjump⟩ :=
    HexArea.ptWind_jump_edge a b (c :: rest) m hab hm hpath
  obtain ⟨ε, hεpos, hclear⟩ := exists_clearance T m hpath
  obtain ⟨y, z, hym, hzm, hcy, hcz, hyin, hzin⟩ :=
    exists_perturb_pair a b c m hab hm hD (min δ ε) (lt_min hδpos hεpos)
  -- both perturbed points lie off all closed edges
  have hoff : ∀ w : ℂ, dist w m < min δ ε → HexArea.cross (b - a) (w - a) ≠ 0 →
      ∀ e ∈ HexArea.cycleEdges (a :: b :: c :: rest), w ∉ segment ℝ e.1 e.2 := by
    intro w hw hcw e he
    rw [cycleEdges_cons_cons] at he
    rcases List.mem_cons.mp he with rfl | he'
    · intro hmem
      exact hcw (HexArea.cross_combo_segment a b w hmem)
    · exact hclear w (lt_of_lt_of_le hw (min_le_right _ _)) e he'
  have hoffy : ∀ e ∈ HexArea.cycleEdges (a :: b :: c :: rest), y ∉ segment ℝ e.1 e.2 :=
    hoff y hym (ne_of_gt hcy)
  have hoffz : ∀ e ∈ HexArea.cycleEdges (a :: b :: c :: rest), z ∉ segment ℝ e.1 e.2 :=
    hoff z hzm (ne_of_lt hcz)
  have hvy : ∀ v ∈ (a :: b :: c :: rest), v ≠ y :=
    fun v hv => HexArea.vertices_ne_of_avoids_cycleEdges _ y hoffy v hv
  have hvz : ∀ v ∈ (a :: b :: c :: rest), v ≠ z :=
    fun v hv => HexArea.vertices_ne_of_avoids_cycleEdges _ z hoffz v hv
  have hjmp : HexArea.ptWind y (a :: b :: c :: rest)
      - HexArea.ptWind z (a :: b :: c :: rest) = 2 * Real.pi :=
    hjump y z (lt_of_lt_of_le hym (min_le_left _ _)) (lt_of_lt_of_le hzm (min_le_left _ _))
      hvy hvz hcy hcz
  -- the dichotomy on both sides
  have hdy := polygon_ptWind_dichotomy (a :: b :: c :: rest) (by omega) hMsimple y hoffy
  have hdz := polygon_ptWind_dichotomy (a :: b :: c :: rest) (by omega) hMsimple z hoffz
  have hpi : 0 < Real.pi := Real.pi_pos
  -- the orientation of the ear is the orientation of the polygon
  have htri : HexArea.shoelace2 [a, b, c] = HexArea.cross (b - a) (c - b) :=
    shoelace2_triple_eq_cross a b c
  -- identify the interior point and its winding number
  have key : ∃ w : ℂ, HexArea.inTriangleStrict a b c w ∧
      HexArea.ptWind w (a :: b :: c :: rest)
        = 2 * Real.pi * (if 0 < HexArea.shoelace2 (a :: b :: c :: rest) then 1 else -1) := by
    rcases lt_or_gt_of_ne hD with hDneg | hDpos
    · -- negatively oriented ear: the `-` point is inside
      have hnotpos : ¬ (0 < HexArea.shoelace2 (a :: b :: c :: rest)) := by
        rw [hMarea]
        intro hcon
        have := hor.mpr hcon
        rw [htri] at this
        linarith
      rw [if_neg hnotpos]
      refine ⟨z, hzin hDneg, ?_⟩
      rcases hdy with hy0 | hy1 <;> rcases hdz with hz0 | hz1
      · rw [hy0, hz0] at hjmp; linarith
      · rw [if_neg hnotpos] at hz1; exact hz1
      · rw [if_neg hnotpos] at hy1; rw [hy1, hz0] at hjmp; linarith
      · rw [if_neg hnotpos] at hy1 hz1; rw [hy1, hz1] at hjmp; linarith
    · -- positively oriented ear: the `+` point is inside
      have hpos : 0 < HexArea.shoelace2 (a :: b :: c :: rest) := by
        rw [hMarea]
        exact hor.mp (by rw [htri]; exact hDpos)
      rw [if_pos hpos]
      refine ⟨y, hyin hDpos, ?_⟩
      rcases hdy with hy0 | hy1 <;> rcases hdz with hz0 | hz1
      · rw [hy0, hz0] at hjmp; linarith
      · rw [if_pos hpos] at hz1; rw [hy0, hz1] at hjmp; linarith
      · rw [if_pos hpos] at hy1; exact hy1
      · rw [if_pos hpos] at hy1 hz1; rw [hy1, hz1] at hjmp; linarith
  obtain ⟨w, hwin, hwval⟩ := key
  -- transport the value along the (convex) open ear triangle
  have hxw : HexArea.ptWind x (a :: b :: c :: rest)
      = HexArea.ptWind w (a :: b :: c :: rest) := by
    refine HexArea.ptWind_eq_of_segment_avoids _ x w ?_
    intro p hp
    rw [Set.disjoint_left]
    intro q hq hqp
    have hqin : HexArea.inTriangleStrict a b c q :=
      inTriangleStrict_of_segment a b c x w q hin hwin hq
    rw [HexArea.cycleEdges_eq_closedEdges] at hp
    exact ear_strict_interior_off_closedEdges (a :: b :: c :: rest) h4M hMsimple 0 a b c rest
      (by simp) hD hempty hdiag q hqin p.1 p.2 hp hqp
  rw [← hMwind x, hxw, hwval, hMarea]

end
