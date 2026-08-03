import Mathlib
import RequestProject.SAWUmlaufAttachmentData
import RequestProject.SAWUmlaufLocalDetour

/-!
# Endpoint-escape blocks for the Umlaufsatz detour

This file is directly imported by `SAWUmlaufDetourConstruction`, hence lies on
the live chain to the polygonal Umlaufsatz.  It records the geometric case not
covered by same-side semicircular attachments.

A path may cross the newly adjoined segment an odd number of times.  Then one
replacement packet has boundary values on opposite sides of the supporting
line, so no same-side detour can join them without meeting that line.  The
replacement must instead pass around the free endpoint `a` of the new edge.
Because `a` is not on the old tail of a simple arc, compactness supplies a ball
about `a` disjoint from that tail.  Inside such a ball, the portion of `[a,b]`
is a radial slit; its punctured complement connects the two sides by going
around `a` without touching it.

The data structure and exact local output below preserve this remaining step in
Lean rather than leaving the odd-crossing case implicit.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- Parameter data for the exceptional block that escapes around the free
endpoint of the newly adjoined edge. -/
structure EndpointEscapeAttachment {x y : ℂ} (γ : Path x y) (a b : ℂ)
    (oldTail : Set ℂ) where
  left : unitInterval
  right : unitInterval
  left_le_right : left ≤ right
  radius : ℝ
  radius_pos : 0 < radius
  oldTail_clear : Metric.ball a radius ∩ oldTail = ∅
  left_in_ball : γ left ∈ Metric.ball a radius
  right_in_ball : γ right ∈ Metric.ball a radius
  left_off_edge : γ left ∉ segment ℝ a b
  right_off_edge : γ right ∉ segment ℝ a b
  oppositeSides :
    (detourSide a (b - a) (γ left) < 0 ∧
      0 < detourSide a (b - a) (γ right)) ∨
    (0 < detourSide a (b - a) (γ left) ∧
      detourSide a (b - a) (γ right) < 0)

/-- A point a controlled distance directly behind the free endpoint `a`,
opposite the direction of the new edge.  This is the common waypoint for the
two opposite-side connectors in the endpoint-escape construction. -/
def endpointEscapeBackpoint (a b : ℂ) (ρ : ℝ) : ℂ :=
  a - (ρ / (2 * ‖b - a‖)) • (b - a)

/-- The backpoint remains strictly inside the prescribed endpoint-clearance
ball. -/
lemma endpointEscapeBackpoint_mem_ball (a b : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hab : a ≠ b) :
    endpointEscapeBackpoint a b ρ ∈ Metric.ball a ρ := by
  simp [endpointEscapeBackpoint]
  have hba : ‖b - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab.symm)
  field_simp
  rw [abs_of_pos hρ]
  linarith

/-- The backpoint lies on the carrier line of the new edge. -/
lemma detourSide_endpointEscapeBackpoint (a b : ℂ) (ρ : ℝ) :
    detourSide a (b - a) (endpointEscapeBackpoint a b ρ) = 0 := by
  simp only [detourSide, endpointEscapeBackpoint]
  simp only [sub_sub_cancel_left]
  simp
  simp [Complex.div_re, Complex.div_im]
  ring_nf

/-- Since it lies strictly behind `a`, the backpoint is not on the forward
closed segment from `a` to `b`. -/
lemma endpointEscapeBackpoint_not_mem_segment (a b : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hab : a ≠ b) :
    endpointEscapeBackpoint a b ρ ∉ segment ℝ a b := by
  intro hmem
  have hdiam := segment_subset_diameterLine a b hmem
  obtain ⟨s, hs⟩ := hdiam
  simp [endpointEscapeBackpoint] at hs
  -- From hs: a - ρ / (2 * ‖b - a‖) * (b - a) = a + s * (b - a)
  -- This means s = -ρ / (2 * ‖b - a‖)
  have hba_ne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hs_eq : s = -(ρ / (2 * ‖b - a‖)) := by
    have h1 : a - ↑ρ / (2 * ↑‖b - a‖) * (b - a) = a + ↑s * (b - a) := hs
    have h2 : -(↑ρ / (2 * ↑‖b - a‖)) * (b - a) = ↑s * (b - a) := by linear_combination h1
    have h3 : (-(ρ / (2 * ‖b - a‖)) : ℂ) = ↑s := by
      exact mul_right_cancel₀ hba_ne h2
    have h3eq : (↑(-(ρ / (2 * ‖b - a‖))) : ℂ) = ↑s := by simpa using h3
    have h3' : -(ρ / (2 * ‖b - a‖)) = s := Complex.ofReal_inj.mp h3eq
    linarith
  -- s = -(ρ / (2 * ‖b - a‖)) < 0, but points on the segment have s ∈ [0, 1]
  have hs_neg : s < 0 := by
    rw [hs_eq]
    apply neg_neg_of_pos
    apply div_pos hρ
    linarith [norm_pos_iff.mpr hba_ne]
  -- The segment characterization
  rw [segment_eq_image] at hmem
  obtain ⟨θ, hθ_mem, hθ_eq⟩ := hmem
  -- Simplify the point on the segment
  simp at hθ_eq
  -- hθ_eq: (1 - θ) • a + θ • b = endpointEscapeBackpoint a b ρ
  -- We also have from hs: endpointEscapeBackpoint a b ρ = a + s • (b - a)
  -- And (1 - θ) • a + θ • b = a + θ • (b - a)
  have hsimp : (1 - ↑θ) * a + ↑θ * b = a + ↑θ * (b - a) := by ring
  rw [hsimp] at hθ_eq
  -- Now hθ_eq: a + θ • (b - a) = endpointEscapeBackpoint a b ρ
  simp [endpointEscapeBackpoint] at hθ_eq
  -- hθ_eq: a + θ • (b - a) = a + s • (b - a)
  have hs_eq' : θ = s := by
    have h1 := congr_arg (fun z => z - a) hθ_eq
    simp at h1
    -- h1: ↑θ * (b - a) = -(↑ρ / (2 * ↑‖b - a‖) * (b - a))
    have h2 : (↑θ : ℂ) = -(↑ρ / (2 * ↑‖b - a‖)) := mul_right_cancel₀ hba_ne (by linear_combination h1)
    have h2' : (↑θ : ℂ) = ↑(-(ρ / (2 * ‖b - a‖))) := by simpa using h2
    have h3 : (↑θ : ℂ) = ↑s := by rw [hs_eq]; exact h2'
    exact Complex.ofReal_inj.mp h3
  linarith [hθ_mem.1]

/-- A straight connector from a point strictly off a carrier line to an
off-segment endpoint on that line cannot meet a subset of the line.  This is
the elementary convex half-plane fact needed on each side of the endpoint
escape. -/
lemma affinePath_to_line_endpoint_avoids
    (c u p q : ℂ) (S : Set ℂ)
    (hp : detourSide c u p ≠ 0)
    (hqSide : detourSide c u q = 0)
    (hq : q ∉ S)
    (hS : S ⊆ {z : ℂ | ∃ s : ℝ, z = c + s • u}) :
    ∀ t, affinePath p q t ∉ S := by
  intro t ht
  -- From ht and hS, affinePath p q t is on the carrier line
  have h_on_line : affinePath p q t ∈ {z : ℂ | ∃ s : ℝ, z = c + s • u} := hS ht
  -- So detourSide c u (affinePath p q t) = 0
  have h_detour_zero : detourSide c u (affinePath p q t) = 0 := by
    obtain ⟨s, hs⟩ := h_on_line
    simp [detourSide, hs]; ring
  -- But detourSide c u (affinePath p q t) = (1 - t) * detourSide c u p + t * detourSide c u q
  rw [detourSide_affinePath c u p q t] at h_detour_zero
  -- Since detourSide c u q = 0, this simplifies to (1 - t) * detourSide c u p = 0
  simp only [hqSide, mul_zero, add_zero] at h_detour_zero
  -- Since detourSide c u p ≠ 0, we need t = 1
  have ht_eq_one : (t : ℝ) = 1 := by
    linarith [sub_eq_zero.mp (mul_eq_zero.mp h_detour_zero |>.resolve_right hp)]
  -- When t = 1, affinePath p q 1 = q
  have h_path_eq_q : affinePath p q t = q := by
    rw [affinePath_apply]
    simp [ht_eq_one]
  -- But q ∉ S
  exact hq (h_path_eq_q ▸ ht)

/-- Two points on opposite sides of the edge carrier line can be joined inside
an endpoint-clearance ball by the broken line through the backpoint.  The path
stays in the ball, misses the old tail, and meets the carrier line only at a
point strictly behind the free endpoint. -/
lemma exists_endpoint_escape_via_backpoint
    (a b p q : ℂ) (oldTail : Set ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hab : a ≠ b)
    (hclear : Metric.ball a ρ ∩ oldTail = ∅)
    (hpBall : p ∈ Metric.ball a ρ) (hqBall : q ∈ Metric.ball a ρ)
    (hpSide : detourSide a (b - a) p ≠ 0)
    (hqSide : detourSide a (b - a) q ≠ 0) :
    ∃ δ : Path p q,
      (∀ t, δ t ∉ segment ℝ a b) ∧
      (∀ t, δ t ∉ oldTail) := by
  let back := endpointEscapeBackpoint a b ρ
  use (affinePath p back).trans (affinePath back q)
  constructor
  · intro t
    simp [Path.trans_apply]
    split_ifs with ht
    · have hpback := affinePath_to_line_endpoint_avoids a (b - a) p back (segment ℝ a b) hpSide
        (detourSide_endpointEscapeBackpoint a b ρ) (endpointEscapeBackpoint_not_mem_segment a b hρ hab)
        (fun z hz => segment_subset_diameterLine a b hz)
      have heq : affinePath p back ⟨2 * t, by constructor <;> linarith [t.prop.1, t.prop.2]⟩
          = (1 - 2 * (t : ℝ)) * p + 2 * (t : ℝ) * back := by simp [affinePath_apply]
      rw [heq.symm]
      exact hpback ⟨2 * t, by constructor <;> linarith [t.prop.1, t.prop.2]⟩
    · -- Use affinePath back q, related to affinePath q back by time reversal
      have hqback := affinePath_to_line_endpoint_avoids a (b - a) q back (segment ℝ a b) hqSide
        (detourSide_endpointEscapeBackpoint a b ρ) (endpointEscapeBackpoint_not_mem_segment a b hρ hab)
        (fun z hz => segment_subset_diameterLine a b hz)
      have heq : (1 - (2 * (t : ℝ) - 1)) * back + (2 * (t : ℝ) - 1) * q
          = affinePath back q ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.prop.1, t.prop.2]⟩ := by
        simp [affinePath_apply]
      rw [heq]
      have hsym : affinePath back q ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.prop.1, t.prop.2]⟩
          = affinePath q back ⟨1 - (2 * (t : ℝ) - 1), by constructor <;> linarith [t.prop.1, t.prop.2]⟩ := by
        simp only [affinePath_apply]
        module
      rw [hsym]
      exact hqback ⟨1 - (2 * (t : ℝ) - 1), by constructor <;> linarith [t.prop.1, t.prop.2]⟩
  · intro t
    simp [Path.trans_apply]
    split_ifs with ht
    · have heq : (1 - 2 * (t : ℝ)) * p + 2 * (t : ℝ) * back = affinePath p back ⟨2 * (t : ℝ), by constructor <;> linarith [t.prop.1, t.prop.2]⟩ := by
        simp [affinePath_apply]
      rw [heq]
      apply path_avoids_of_mem_ball_of_ball_disjoint (affinePath p back) oldTail _ hclear
      intro s
      exact (convex_ball a ρ).segment_subset hpBall (endpointEscapeBackpoint_mem_ball a b hρ hab) (affinePath_mem_segment p back s)
    · have heq : (1 - (2 * (t : ℝ) - 1)) * back + (2 * (t : ℝ) - 1) * q = affinePath back q ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.prop.1, t.prop.2]⟩ := by
        simp [affinePath_apply]
      rw [heq]
      apply path_avoids_of_mem_ball_of_ball_disjoint (affinePath back q) oldTail _ hclear
      intro s
      exact (convex_ball a ρ).segment_subset (endpointEscapeBackpoint_mem_ball a b hρ hab) hqBall (affinePath_mem_segment back q s)

/-- **Odd-crossing endpoint escape (remaining local geometric brick).**  In a
ball about the free endpoint which misses the old tail, two off-edge points on
opposite sides can be joined around that endpoint while avoiding both the
closed new edge and the old tail.

This is intentionally retained as an honest partial theorem.  Its future proof
will use an explicit small circular arc around `a` plus same-side straight
attachments; it is the missing alternative that makes finite attachment
selection valid for odd as well as even crossing parity. -/
lemma EndpointEscapeAttachment.exists_replacement
    {x y : ℂ} {γ : Path x y} {a b : ℂ} {oldTail : Set ℂ}
    (A : EndpointEscapeAttachment γ a b oldTail)
    (hab : a ≠ b) :
    ∃ δ : Path (γ A.left) (γ A.right),
      (∀ q, δ q ∉ segment ℝ a b) ∧
      (∀ q, δ q ∉ oldTail) := by
  apply exists_endpoint_escape_via_backpoint a b (γ A.left) (γ A.right) oldTail A.radius_pos hab A.oldTail_clear A.left_in_ball A.right_in_ball
  · cases A.oppositeSides with
    | inl h => exact ne_of_lt h.1
    | inr h => exact ne_of_gt h.1
  · cases A.oppositeSides with
    | inl h => exact ne_of_gt h.2
    | inr h => exact ne_of_lt h.2

end HexArea
