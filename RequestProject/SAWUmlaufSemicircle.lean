import Mathlib

/-!
# Semicircular replacement arcs for the polygonal Umlaufsatz

This file is part of the live local-detour proof.  It is imported by
`SAWUmlaufArcDetour`, whose remaining crossing-replacement theorem feeds
`SAWUmlaufArcInduction → SAWUmlaufArcEscape → SAWUmlaufPolygon` and the main
Umlaufsatz.

When an old path crosses a newly adjoined straight edge, the replacement inside
a sufficiently small clearance disc is a semicircle.  The declarations here
formalize that local geometric primitive independently of the later finite
splicing bookkeeping: its endpoints are the ends of a diameter, every point is
at exactly the prescribed radius from the centre, and its open part lies
strictly on one side of the diameter line.  In particular, the open semicircle
cannot meet its diameter.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- The positively oriented semicircle of radius `r` about `c`, parametrized by
`t ∈ [0,1]`.  Its diameter is parallel to the nonzero direction `u`. -/
def semicirclePoint (c u : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  c + ((r : ℂ) / ‖u‖) * u *
    (Real.cos (Real.pi * t) + Real.sin (Real.pi * t) * Complex.I)

lemma semicirclePoint_zero (c u : ℂ) (r : ℝ) :
    semicirclePoint c u r 0 = c + ((r : ℂ) / ‖u‖) * u := by
  unfold semicirclePoint; aesop;

lemma semicirclePoint_one (c u : ℂ) (r : ℝ) :
    semicirclePoint c u r 1 = c - ((r : ℂ) / ‖u‖) * u := by
  unfold semicirclePoint; aesop;

lemma continuous_semicirclePoint (c u : ℂ) (r : ℝ) :
    Continuous (fun t : ℝ => semicirclePoint c u r t) := by
  unfold semicirclePoint; continuity;

/-- The semicircle packaged as an actual `Path`, ready for finite splicing into
an old path at a crossing interval. -/
def semicirclePath (c u : ℂ) (r : ℝ) :
    Path (c + ((r : ℂ) / ‖u‖) * u) (c - ((r : ℂ) / ‖u‖) * u) :=
  ⟨⟨fun t => semicirclePoint c u r t,
      (continuous_semicirclePoint c u r).comp continuous_subtype_val⟩,
    semicirclePoint_zero c u r, semicirclePoint_one c u r⟩

lemma semicirclePath_apply (c u : ℂ) (r : ℝ) (t : unitInterval) :
    semicirclePath c u r t = semicirclePoint c u r t := rfl

/-
Every point of the semicircle has the prescribed distance from its centre.
-/
lemma dist_semicirclePoint_center (c u : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hu : u ≠ 0) (t : ℝ) :
    dist (semicirclePoint c u r t) c = r := by
  unfold semicirclePoint;
  have := Complex.norm_cos_add_sin_mul_I ( Real.pi * t ) ; simp_all +decide [ abs_of_pos, norm_mul, norm_div ]

/-
Hence a semicircle of radius strictly below `ε` stays in the clearance ball
of radius `ε` around its centre.
-/
lemma semicirclePoint_mem_ball (c u : ℂ) {r ε : ℝ}
    (hr : 0 ≤ r) (hrε : r < ε) (hu : u ≠ 0) (t : ℝ) :
    semicirclePoint c u r t ∈ Metric.ball c ε := by
  convert Set.mem_setOf.mpr ( lt_of_eq_of_lt ( dist_semicirclePoint_center c u hr hu t ) hrε ) using 1

/-
After rotating and scaling so that `u` becomes the real direction, the open
semicircle has strictly positive imaginary coordinate.  This is the local
nonintersection fact used to replace a crossing of the diameter.
-/
lemma semicirclePoint_rotated_im_pos (c u : ℂ) {r t : ℝ}
    (hr : 0 < r) (hu : u ≠ 0) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < (((semicirclePoint c u r t - c) * star u).im) := by
  unfold semicirclePoint;
  simp +zetaDelta at *;
  norm_cast; ring_nf;
  nlinarith [ show 0 < r * ‖u‖⁻¹ * Real.sin ( Real.pi * t ) by exact mul_pos ( mul_pos hr ( inv_pos.mpr ( norm_pos_iff.mpr hu ) ) ) ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by nlinarith [ Real.pi_pos ] ) ), show u.re ^ 2 + u.im ^ 2 > 0 by exact not_le.mp fun h => hu <| by refine' Complex.ext _ _ <;> norm_num <;> nlinarith ]

/-
The open semicircle is disjoint from the complete affine line carrying its
diameter.  This is stronger than disjointness from the diameter segment and is
the exact elementary fact needed by each local crossing replacement.
-/
lemma semicirclePoint_not_mem_diameterLine (c u : ℂ) {r t : ℝ}
    (hr : 0 < r) (hu : u ≠ 0) (ht0 : 0 < t) (ht1 : t < 1) :
    semicirclePoint c u r t ∉ {z : ℂ | ∃ s : ℝ, z = c + s • u} := by
  by_contra h_contra
  obtain ⟨s, hs⟩ : ∃ s : ℝ, semicirclePoint c u r t = c + s • u := by
    exact h_contra
  convert HexArea.semicirclePoint_rotated_im_pos c u hr hu ht0 ht1 using 1
  simp_all +decide [mul_comm, mul_assoc, mul_left_comm]

/-
The packaged local replacement theorem used by the future finite splicing
step: the whole replacement stays in its clearance ball, and every nonendpoint
parameter avoids the entire diameter line.
-/
lemma semicirclePath_local_detour (c u : ℂ) {r ε : ℝ}
    (hr : 0 < r) (hrε : r < ε) (hu : u ≠ 0) :
    (∀ t : unitInterval, semicirclePath c u r t ∈ Metric.ball c ε) ∧
    (∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      semicirclePath c u r t ∉ {z : ℂ | ∃ s : ℝ, z = c + s • u}) := by
  constructor;
  · intro t;
    convert HexArea.semicirclePoint_mem_ball c u hr.le hrε hu t.val;
  · intro t ht₀ ht₁; rw [ semicirclePath_apply ] ; exact HexArea.semicirclePoint_not_mem_diameterLine c u hr hu ht₀ ht₁;

end HexArea