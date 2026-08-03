import Mathlib
import RequestProject.SAWUmlaufArcCrossings
import RequestProject.SAWUmlaufHalfPlaneDetour

/-!
# Side-coordinate neighborhoods for the Umlaufsatz crossing construction

This file is an explicitly linked continuation of the finite-detour route.  It
is imported by `SAWUmlaufDetourConstruction` and therefore feeds the main
Umlaufsatz.  It is not a dead branch.

A finite cover by clearance balls is not by itself enough to splice local
replacements: one must choose parameter endpoints whose path values lie in the
same open half-plane of the new edge.  The signed coordinate `detourSide`
provides the right interface.  This file records continuity, the equation of
the carrier line, orientation reversal, and the parameter-neighborhood facts
needed to turn each selected crossing ball into an attachment interval.

A transverse crossing may approach from opposite sides, so the same-side
hypothesis in the final local lemma is intentional rather than hidden.  Future
finite assembly may either group such crossings or route around an endpoint of
the finite segment.  Keeping this distinction explicit avoids silently proving
a false local same-side assertion.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

lemma continuous_detourSide (c u : ℂ) :
    Continuous (detourSide c u) := by
  unfold detourSide
  continuity

/-- For a nonzero direction, vanishing signed normal coordinate is equivalent
to membership in the complete affine carrier line. -/
lemma detourSide_eq_zero_iff_mem_diameterLine
    (c u z : ℂ) (hu : u ≠ 0) :
    detourSide c u z = 0 ↔
      z ∈ {w : ℂ | ∃ s : ℝ, w = c + s • u} := by
  unfold detourSide
  rw [Complex.mul_im]
  simp only [Complex.star_def, conj_im, conj_re]
  constructor
  · intro h
    -- h : (z - c).re * -u.im + (z - c).im * u.re = 0
    -- i.e., (z - c).im * u.re = (z - c).re * u.im
    have h' : (z - c).im * u.re = (z - c).re * u.im := by linarith
    -- Since u ≠ 0, either u.re ≠ 0 or u.im ≠ 0
    rcases ne_or_eq u.re 0 with hu_re | hu_re
    · -- u.re ≠ 0: use s = (z - c).re / u.re
      use (z - c).re / u.re
      simp only [sub_re, sub_im] at h
      refine Complex.ext ?_ ?_
      · simp; field_simp [hu_re]; ring
      · simp; field_simp [hu_re]; linarith
    · -- u.re = 0: use s = (z - c).im / u.im
      have hu_im : u.im ≠ 0 := by
        intro h
        apply hu
        exact Complex.ext hu_re h
      use (z - c).im / u.im
      simp only [sub_re, sub_im] at h
      refine Complex.ext ?_ ?_
      · simp; field_simp [hu_im]; linarith
      · simp; field_simp [hu_im]; ring
  · intro ⟨s, hs⟩
    simp [hs]
    ring

/-- Reversing the line direction exchanges its two open sides.  This permits
the positive-side local detour package to handle either geometric side. -/
lemma detourSide_neg_direction (c u z : ℂ) :
    detourSide c (-u) z = -detourSide c u z := by
  simp [detourSide]

lemma detourPositiveSide_neg_direction (c u : ℂ) :
    detourPositiveSide c (-u) = {z | detourSide c u z < 0} := by
  ext z
  simp [detourPositiveSide, detourSide_neg_direction]

/-- The side coordinate along a path is continuous. -/
lemma continuous_detourSide_comp_path
    {x y : ℂ} (γ : Path x y) (c u : ℂ) :
    Continuous (fun t : unitInterval => detourSide c u (γ t)) := by
  exact continuous_detourSide c u |> Continuous.comp <| γ.continuous

/-- Continuity supplies a parameter neighborhood whose image remains in a
prescribed clearance ball around a selected crossing value. -/
lemma eventually_path_mem_crossing_ball
    {x y : ℂ} (γ : Path x y) (t : unitInterval) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 t, γ s ∈ Metric.ball (γ t) ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 γ.continuous.continuousAt ε hε
  exact Metric.ball_mem_nhds t hδ |> Filter.Eventually.mono <| h

/-- Open-ball control can be converted to an explicit relative interval around
an interior crossing parameter. -/
lemma exists_parameter_interval_mapsTo_crossing_ball
    {x y : ℂ} (γ : Path x y) (t : unitInterval) {ε : ℝ} (hε : 0 < ε)
    (ht0 : (0 : unitInterval) < t) (ht1 : t < (1 : unitInterval)) :
    ∃ l r : unitInterval,
      l < t ∧ t < r ∧
      ∀ s ∈ Set.Icc l r, γ s ∈ Metric.ball (γ t) ε := by
  -- Get δ from continuity of γ at t
  have hcont : ContinuousAt (fun s => γ s) t := (Path.continuous γ).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont ε hε
  -- Use δ' = min(t, 1-t, δ/2) to ensure l > 0 and r < 1
  let δ' := min (t : ℝ) (min (1 - (t : ℝ)) (δ / 2))
  have ht1' : (t : ℝ) < 1 := ht1
  have hδ'pos : 0 < δ' := by
    simp only [δ']
    apply lt_min
    · exact ht0
    · apply lt_min
      · linarith
      · linarith
  -- Define l = t - δ' and r = t + δ'
  have hmin_le_t : min (t : ℝ) (min (1 - (t : ℝ)) (δ / 2)) ≤ (t : ℝ) := min_le_left _ _
  have hmin_le_1t : min (t : ℝ) (min (1 - (t : ℝ)) (δ / 2)) ≤ min (1 - (t : ℝ)) (δ / 2) := min_le_right _ _
  have hmin_le_δ2 : min (t : ℝ) (min (1 - (t : ℝ)) (δ / 2)) ≤ δ / 2 := le_trans hmin_le_1t (min_le_right _ _)
  have hmin_le_1t' : min (t : ℝ) (min (1 - (t : ℝ)) (δ / 2)) ≤ 1 - (t : ℝ) := le_trans hmin_le_1t (min_le_left _ _)
  let hl : (t : ℝ) - δ' ≥ 0 := by simp only [δ']; linarith
  let hr : (t : ℝ) + δ' ≤ 1 := by simp only [δ']; linarith
  let l : unitInterval := ⟨(t : ℝ) - δ', ⟨hl, by linarith [hmin_le_t]⟩⟩
  let r : unitInterval := ⟨(t : ℝ) + δ', ⟨by linarith [hδ'pos], hr⟩⟩
  refine ⟨l, r, ?_, ?_, ?_⟩
  · -- l < t: (t : ℝ) - δ' < t since δ' > 0
    exact Subtype.mk_lt_mk.mpr (by simp only [δ']; linarith)
  · -- t < r: t < (t : ℝ) + δ' since δ' > 0
    exact Subtype.mk_lt_mk.mpr (by simp only [δ']; linarith)
  · -- For s ∈ [l, r], γ s ∈ ball (γ t) ε
    intro s hs
    apply hδ
    -- Need dist s t < δ
    simp only [Set.mem_Icc] at hs
    have hlt : l.val = (t : ℝ) - δ' := rfl
    have hrt : r.val = (t : ℝ) + δ' := rfl
    have hs_lower : (t : ℝ) - δ' ≤ s.val := by simpa [← hlt] using hs.1
    have hs_upper : s.val ≤ (t : ℝ) + δ' := by simpa [← hrt] using hs.2
    have habs : |s.val - t| ≤ δ' := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [show dist s t = |s.val - t| from rfl]
    simp only [δ'] at habs ⊢
    linarith

/-- A selected interval whose boundary values lie on one side of the edge and
whose image lies in a tail-clearance ball admits a complete local replacement.
This theorem directly combines the parameter-selection layer with
`exists_connected_local_detour`. -/
lemma exists_local_replacement_of_same_positive_side
    {x y : ℂ} (γ : Path x y) (a b : ℂ) (oldTail : Set ℂ)
    (t l r : unitInterval) {ε : ℝ}
    (hab : a ≠ b) (hε : 0 < ε)
    (hlt : l ≤ t) (htr : t ≤ r)
    (htEdge : γ t ∈ segment ℝ a b)
    (hlBall : γ l ∈ Metric.ball (γ t) ε)
    (hrBall : γ r ∈ Metric.ball (γ t) ε)
    (hlSide : γ l ∈ detourPositiveSide a (b - a))
    (hrSide : γ r ∈ detourPositiveSide a (b - a))
    (hclear : Metric.ball (γ t) ε ∩ oldTail = ∅) :
    ∃ δ : Path (γ l) (γ r),
      (∀ q, δ q ∉ segment ℝ a b) ∧
      (∀ q, δ q ∉ oldTail) := by
  -- Since γ t is on the segment, the positive side at a equals the positive side at γ t
  have hSideEq : detourPositiveSide a (b - a) = detourPositiveSide (γ t) (b - a) := by
    ext z
    simp [detourPositiveSide, detourSide]
    -- Use that γ t = a + s • (b - a) for some s, so (γ t - a) is parallel to (b - a)
    rw [segment_eq_image] at htEdge
    obtain ⟨s, hs, hsγ⟩ := htEdge
    have hre : (γ t).re = (1 - s) * a.re + s * b.re := by simp [← hsγ]
    have him : (γ t).im = (1 - s) * a.im + s * b.im := by simp [← hsγ]
    rw [hre, him]
    ring_nf
  -- Rewrite hlSide and hrSide to use γ t as center
  have hlSide' : γ l ∈ detourPositiveSide (γ t) (b - a) := hSideEq ▸ hlSide
  have hrSide' : γ r ∈ detourPositiveSide (γ t) (b - a) := hSideEq ▸ hrSide
  -- The segment ℝ a b lies in the diameter line through γ t
  have hnew : segment ℝ a b ⊆ {z : ℂ | ∃ s : ℝ, z = γ t + s • (b - a)} := by
    intro z hz
    rw [segment_eq_image] at hz
    have htEdge' : γ t ∈ (fun θ : ℝ => (1 - θ) • a + θ • b) '' Set.Icc 0 1 := by
      rw [segment_eq_image] at htEdge
      exact htEdge
    obtain ⟨s₁, hs₁, rfl⟩ := hz
    obtain ⟨s₂, _, hsγ⟩ := htEdge'
    refine ⟨s₁ - s₂, ?_⟩
    rw [← hsγ]
    simp [Complex.smul_re, Complex.smul_im]
    ring_nf
  -- Apply exists_connected_local_detour
  exact exists_connected_local_detour (γ l) (γ r) (γ t) (b - a) (segment ℝ a b) oldTail hε (sub_ne_zero.mpr hab.symm) hlBall hrBall hlSide' hrSide' hnew hclear

/-- Negative-side companion, obtained by reversing the edge direction.  It is
stated separately so the finite selector need not carry sign-normalization
bookkeeping. -/
lemma exists_local_replacement_of_same_negative_side
    {x y : ℂ} (γ : Path x y) (a b : ℂ) (oldTail : Set ℂ)
    (t l r : unitInterval) {ε : ℝ}
    (hab : a ≠ b) (hε : 0 < ε)
    (hlt : l ≤ t) (htr : t ≤ r)
    (htEdge : γ t ∈ segment ℝ a b)
    (hlBall : γ l ∈ Metric.ball (γ t) ε)
    (hrBall : γ r ∈ Metric.ball (γ t) ε)
    (hlSide : detourSide a (b - a) (γ l) < 0)
    (hrSide : detourSide a (b - a) (γ r) < 0)
    (hclear : Metric.ball (γ t) ε ∩ oldTail = ∅) :
    ∃ δ : Path (γ l) (γ r),
      (∀ q, δ q ∉ segment ℝ a b) ∧
      (∀ q, δ q ∉ oldTail) := by
  -- Since γ t is on the segment, the side function is invariant under shifting center along the line
  have hSideEq : detourPositiveSide a (b - a) = detourPositiveSide (γ t) (b - a) := by
    ext z
    simp [detourPositiveSide, detourSide]
    rw [segment_eq_image] at htEdge
    obtain ⟨s, _, hsγ⟩ := htEdge
    have hre : (γ t).re = (1 - s) * a.re + s * b.re := by simp [← hsγ]
    have him : (γ t).im = (1 - s) * a.im + s * b.im := by simp [← hsγ]
    rw [hre, him]
    ring_nf
  have hlSide' : γ l ∈ detourPositiveSide (γ t) (-(b - a)) := by
    have h1 : γ l ∈ detourPositiveSide a (-(b - a)) := by
      rw [detourPositiveSide]
      show 0 < detourSide a (-(b - a)) (γ l)
      rw [detourSide_neg_direction]
      exact neg_pos.mpr hlSide
    have hSideEq' : detourPositiveSide a (-(b - a)) = detourPositiveSide (γ t) (-(b - a)) := by
      ext z
      simp only [detourPositiveSide, detourSide]
      rw [segment_eq_image] at htEdge
      obtain ⟨s, _, hsγ⟩ := htEdge
      rw [← hsγ]
      simp
      ring_nf
    exact hSideEq' ▸ h1
  have hrSide' : γ r ∈ detourPositiveSide (γ t) (-(b - a)) := by
    have h1 : γ r ∈ detourPositiveSide a (-(b - a)) := by
      rw [detourPositiveSide]
      show 0 < detourSide a (-(b - a)) (γ r)
      rw [detourSide_neg_direction]
      exact neg_pos.mpr hrSide
    have hSideEq' : detourPositiveSide a (-(b - a)) = detourPositiveSide (γ t) (-(b - a)) := by
      ext z
      simp only [detourPositiveSide, detourSide]
      rw [segment_eq_image] at htEdge
      obtain ⟨s, _, hsγ⟩ := htEdge
      rw [← hsγ]
      simp
      ring_nf
    exact hSideEq' ▸ h1
  -- The segment ℝ a b lies in the diameter line through γ t
  have hnew : segment ℝ a b ⊆ {z : ℂ | ∃ s : ℝ, z = γ t + s • (-(b - a))} := by
    intro z hz
    rw [segment_eq_image] at hz
    have htEdge' : γ t ∈ (fun θ : ℝ => (1 - θ) • a + θ • b) '' Set.Icc 0 1 := by
      rw [segment_eq_image] at htEdge
      exact htEdge
    obtain ⟨s₁, hs₁, rfl⟩ := hz
    obtain ⟨s₂, _, hsγ⟩ := htEdge'
    refine ⟨s₂ - s₁, ?_⟩
    rw [← hsγ]
    simp [Complex.smul_re, Complex.smul_im]
    ring_nf
  exact exists_connected_local_detour (γ l) (γ r) (γ t) (-(b - a)) (segment ℝ a b) oldTail hε (neg_ne_zero.mpr (sub_ne_zero.mpr hab.symm)) hlBall hrBall hlSide' hrSide' hnew hclear

end HexArea
