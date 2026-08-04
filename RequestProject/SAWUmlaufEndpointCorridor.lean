import Mathlib
import RequestProject.SAWUmlaufEndpointEscape

/-!
# Corridor form of the exceptional Umlaufsatz endpoint detour

This file is directly imported by the mixed finite-selection layer and hence is
on the live route to the main Umlaufsatz.  A transverse crossing in the interior
of the new edge need not have boundary values inside a clearance ball about the
free endpoint.  The honest exceptional construction therefore has three parts:
travel on one side through a tail-free corridor to the endpoint ball, use the
proved backpoint escape there, and return through a corridor on the other side.

The structure below records exactly that geometry.  It prevents the global
selector from making the generally false demand that arbitrary crossing-block
endpoints already lie in one ball about the free endpoint.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- Geometric data for an exceptional block routed through a clearance corridor
to the free endpoint `a`. -/
structure EndpointCorridorAttachment {x y : ℂ} (γ : Path x y) (a b : ℂ)
    (oldTail : Set ℂ) where
  left : unitInterval
  right : unitInterval
  left_le_right : left ≤ right
  nearLeft : ℂ
  nearRight : ℂ
  leftLeg : Path (γ left) nearLeft
  rightLeg : Path nearRight (γ right)
  leftLeg_off_edge : ∀ q, leftLeg q ∉ segment ℝ a b
  rightLeg_off_edge : ∀ q, rightLeg q ∉ segment ℝ a b
  leftLeg_off_tail : ∀ q, leftLeg q ∉ oldTail
  rightLeg_off_tail : ∀ q, rightLeg q ∉ oldTail
  radius : ℝ
  radius_pos : 0 < radius
  oldTail_clear : Metric.ball a radius ∩ oldTail = ∅
  nearLeft_in_ball : nearLeft ∈ Metric.ball a radius
  nearRight_in_ball : nearRight ∈ Metric.ball a radius
  nearLeft_off_line : detourSide a (b - a) nearLeft ≠ 0
  nearRight_off_line : detourSide a (b - a) nearRight ≠ 0

namespace EndpointCorridorAttachment

/-- The two corridor legs and the local endpoint escape concatenate to the
replacement interface required by an ordered detour schedule. -/
lemma exists_replacement
    {x y : ℂ} {γ : Path x y} {a b : ℂ} {oldTail : Set ℂ}
    (A : EndpointCorridorAttachment γ a b oldTail)
    (hab : a ≠ b) :
    ∃ δ : Path (γ A.left) (γ A.right),
      (∀ q, δ q ∉ segment ℝ a b) ∧
      (∀ q, δ q ∉ oldTail) := by
  -- Handle with backpoint detour pattern
  let back := endpointEscapeBackpoint a b A.radius
  let inner := (affinePath A.nearLeft back).trans (affinePath back A.nearRight)
  let δ := A.leftLeg.trans (inner.trans A.rightLeg)
  use δ
  constructor
  · intro t
    simp only [δ, Path.trans_apply]
    split_ifs with ht₁ ht₂
    · -- Case t ≤ 1/2: A.leftLeg
      apply A.leftLeg_off_edge
    · -- Case 1/2 < t ≤ 3/4: inner = (affinePath nearLeft back).trans (affinePath back nearRight)
      simp only [inner, Path.trans_apply]
      split_ifs with hs
      · -- AffinePath nearLeft back
        have hpback := affinePath_to_line_endpoint_avoids a (b - a) A.nearLeft back (segment ℝ a b)
          A.nearLeft_off_line (detourSide_endpointEscapeBackpoint a b A.radius)
          (endpointEscapeBackpoint_not_mem_segment a b A.radius_pos hab)
          (fun z hz => segment_subset_diameterLine a b hz)
        have ht_mem : 2 * (2 * (2 * (t : ℝ) - 1)) ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [t.prop.1, t.prop.2, ht₁, ht₂, hs]
        exact hpback ⟨2 * (2 * (2 * t - 1)), ht_mem⟩
      · -- AffinePath back nearRight (use symmetry: affinePath back nearRight s = affinePath nearRight back (1 - s))
        have hqback := affinePath_to_line_endpoint_avoids a (b - a) A.nearRight back (segment ℝ a b)
          A.nearRight_off_line (detourSide_endpointEscapeBackpoint a b A.radius)
          (endpointEscapeBackpoint_not_mem_segment a b A.radius_pos hab)
          (fun z hz => segment_subset_diameterLine a b hz)
        -- u = 2 * (2 * (2 * t - 1)) - 1
        -- affinePath back nearRight u = affinePath nearRight back (1 - u)
        have ht_mem : 2 * (2 * (2 * (t : ℝ) - 1)) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [t.prop.1, t.prop.2, ht₁, ht₂, hs]
        let u : unitInterval := ⟨2 * (2 * (2 * (t : ℝ) - 1)) - 1, ht_mem⟩
        have ht1u_mem : 1 - (u : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [ht_mem.1, ht_mem.2]
        have hsym : affinePath back A.nearRight u = affinePath A.nearRight back ⟨1 - (u : ℝ), ht1u_mem⟩ := by
          simp [affinePath_apply]
          ring
        rw [hsym]
        exact hqback ⟨1 - (u : ℝ), ht1u_mem⟩
    · -- Case t > 3/4: A.rightLeg
      apply A.rightLeg_off_edge
  · intro t
    simp only [δ, Path.trans_apply]
    split_ifs with ht₁ ht₂
    · -- Case t ≤ 1/2: A.leftLeg
      apply A.leftLeg_off_tail
    · -- Case 1/2 < t ≤ 3/4: inner
      simp only [inner, Path.trans_apply]
      split_ifs with hs
      · -- AffinePath nearLeft back avoids oldTail
        apply path_avoids_of_mem_ball_of_ball_disjoint (affinePath A.nearLeft back) oldTail _ A.oldTail_clear
        intro s
        exact (convex_ball a A.radius).segment_subset A.nearLeft_in_ball
          (endpointEscapeBackpoint_mem_ball a b A.radius_pos hab) (affinePath_mem_segment _ _ s)
      · -- AffinePath back nearRight avoids oldTail
        apply path_avoids_of_mem_ball_of_ball_disjoint (affinePath back A.nearRight) oldTail _ A.oldTail_clear
        intro s
        exact (convex_ball a A.radius).segment_subset (endpointEscapeBackpoint_mem_ball a b A.radius_pos hab)
          A.nearRight_in_ball (affinePath_mem_segment _ _ s)
    · -- Case t > 3/4: A.rightLeg
      apply A.rightLeg_off_tail

end EndpointCorridorAttachment

end HexArea
