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
  sorry

end HexArea
