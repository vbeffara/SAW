import Mathlib
import RequestProject.SAWUmlaufLocalDetour

/-!
# Half-plane attachment for local Umlaufsatz detours

This file is part of the live finite-detour construction and is imported by
`SAWUmlaufDetourConstruction`, hence through arc induction and polygon topology
to the main Umlaufsatz.  It is not a detached branch.

The translated semicircle from `SAWUmlaufLocalDetour` already lies strictly on
one side of the line carrying the new edge.  To attach it to retained path
values, the straight connectors must remain on that same side.  The declarations
below isolate exactly this convex half-plane argument.  Their final package
removes the four connector-avoidance premises from
`connectedLiftedSemicircleDetour_avoids`: membership in one clearance ball and
one strict half-plane suffices.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- Signed normal coordinate relative to the oriented affine line through `c`
in direction `u`.  It vanishes on the line and is positive on the side used by
the translated semicircle. -/
def detourSide (c u z : ℂ) : ℝ := ((z - c) * star u).im

/-- The open side of the diameter line used for attaching a translated local
detour. -/
def detourPositiveSide (c u : ℂ) : Set ℂ := {z | 0 < detourSide c u z}

/-- The signed normal coordinate is affine along a straight connector. -/
lemma detourSide_affinePath (c u p q : ℂ) (t : unitInterval) :
    detourSide c u (affinePath p q t) =
      (1 - (t : ℝ)) * detourSide c u p + (t : ℝ) * detourSide c u q := by
  simp [detourSide, affinePath_apply]
  ring

/-- A straight connector between two points on the positive side remains
strictly on that side, including both endpoints. -/
lemma affinePath_mem_detourPositiveSide
    (c u p q : ℂ) (hp : p ∈ detourPositiveSide c u)
    (hq : q ∈ detourPositiveSide c u) :
    ∀ t, affinePath p q t ∈ detourPositiveSide c u := by
  intro t
  rw [detourPositiveSide, Set.mem_setOf_eq, detourSide_affinePath c u p q t]
  have ht0 : (0 : ℝ) ≤ t := t.prop.1
  have ht1 : (t : ℝ) ≤ 1 := t.prop.2
  unfold detourPositiveSide at hp hq
  rcases eq_or_lt_of_le ht0 with htz | htp
  · rw [← htz]
    norm_num
    exact hp
  · rcases eq_or_lt_of_le ht1 with hton | htlt
    · rw [hton]
      norm_num
      exact hq
    · have h1mt : (0 : ℝ) < 1 - t := by linarith
      apply add_pos_of_pos_of_nonneg
      · exact mul_pos h1mt hp
      · exact mul_nonneg ht0 (le_of_lt hq)

/-- The strict positive side is disjoint from the complete diameter line. -/
lemma detourPositiveSide_disjoint_diameterLine (c u : ℂ) :
    Disjoint (detourPositiveSide c u)
      {z : ℂ | ∃ s : ℝ, z = c + s • u} := by
  rw [Set.disjoint_left]
  intro z hz ⟨s, hs⟩
  unfold detourPositiveSide at hz
  unfold detourSide at hz
  rw [hs] at hz
  simp at hz
  linarith [mul_comm (u.im) (u.re)]

/-- Consequently a straight connector in the positive side avoids every subset
of the diameter line, in particular the newly adjoined segment. -/
lemma affinePath_avoids_of_mem_detourPositiveSide
    (c u p q : ℂ) (S : Set ℂ)
    (hp : p ∈ detourPositiveSide c u)
    (hq : q ∈ detourPositiveSide c u)
    (hS : S ⊆ {z : ℂ | ∃ s : ℝ, z = c + s • u}) :
    ∀ t, affinePath p q t ∉ S := by
  intro t
  have ht_mem : affinePath p q t ∈ detourPositiveSide c u :=
    affinePath_mem_detourPositiveSide c u p q hp hq t
  intro hS_t
  have h_diam : affinePath p q t ∈ {z : ℂ | ∃ s : ℝ, z = c + s • u} := hS hS_t
  exact Set.disjoint_left.mp (detourPositiveSide_disjoint_diameterLine c u) ht_mem h_diam

/-- Both endpoints of a positively translated semicircle lie in its attachment
half-plane. -/
lemma liftedSemicirclePath_endpoints_mem_detourPositiveSide
    (c u : ℂ) {r h : ℝ} (hh : 0 < h) (hu : u ≠ 0) :
    (liftedSemicirclePath c u r h 0 ∈ detourPositiveSide c u) ∧
      (liftedSemicirclePath c u r h 1 ∈ detourPositiveSide c u) := by
  have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hu_sq : u.re ^ 2 + u.im ^ 2 = ‖u‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; norm_cast; ring
  constructor
  · simp only [Set.mem_setOf_eq, detourPositiveSide, detourSide]
    simp [liftedSemicirclePath_apply, liftedSemicirclePoint_zero, detourSide, semicirclePoint_zero]
    field_simp
    nlinarith [sq_nonneg u.re, sq_nonneg u.im, mul_pos hh hu_norm, hu_sq]
  · simp only [Set.mem_setOf_eq, detourPositiveSide, detourSide]
    simp [liftedSemicirclePath_apply, liftedSemicirclePoint_one, detourSide, semicirclePoint_one]
    field_simp
    nlinarith [sq_nonneg u.re, sq_nonneg u.im, mul_pos hh hu_norm, hu_sq]

/-- **Attachment-ready local detour brick.**  Path values `p,q` in one
clearance ball and in the positive side can be connected by the translated
semicircle while avoiding both the new edge and old tail.  This is the exact
pointwise brick needed by the finite crossing-interval selection in
`exists_inner_avoiding_replacement`. -/
lemma exists_connected_local_detour
    (p q c u : ℂ) (newEdge oldTail : Set ℂ) {ε : ℝ}
    (hε : 0 < ε) (hu : u ≠ 0)
    (hpBall : p ∈ Metric.ball c ε) (hqBall : q ∈ Metric.ball c ε)
    (hpSide : p ∈ detourPositiveSide c u)
    (hqSide : q ∈ detourPositiveSide c u)
    (hnew : newEdge ⊆ {z : ℂ | ∃ s : ℝ, z = c + s • u})
    (hclear : Metric.ball c ε ∩ oldTail = ∅) :
    ∃ δ : Path p q,
      (∀ t, δ t ∉ newEdge) ∧ (∀ t, δ t ∉ oldTail) := by
  use affinePath p q
  constructor
  · intro t
    have ht_mem : affinePath p q t ∈ detourPositiveSide c u :=
      affinePath_mem_detourPositiveSide c u p q hpSide hqSide t
    have hdisj := detourPositiveSide_disjoint_diameterLine c u
    rw [Set.disjoint_left] at hdisj
    intro hx
    exact hdisj ht_mem (hnew hx)
  · apply path_avoids_of_mem_ball_of_ball_disjoint (affinePath p q) oldTail
    · intro t; exact (convex_ball c ε).segment_subset hpBall hqBall (affinePath_mem_segment p q t)
    · exact hclear

end HexArea
