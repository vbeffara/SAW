import Mathlib
import RequestProject.SAWUmlaufSideCrossings

/-!
# Finite attachment data for the Umlaufsatz detour

This file is on the live route to `exists_inner_avoiding_replacement`: it is
imported by `SAWUmlaufDetourConstruction`, hence by arc induction, polygon
topology, and the main Umlaufsatz.  It is not a dead branch.

The analytic and local geometric work now produces replacements whenever two
attachment values lie in one clearance ball and on the same side of the new
edge.  The remaining global step is finite selection and ordering.  The
structures below preserve that exact interface in Lean: no future round needs
to reconstruct which inequalities, ball memberships, or side choices a local
block must carry.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- Ordered endpoints around one selected crossing time. -/
structure CrossingAttachment {x y : ℂ} (γ : Path x y) (a b : ℂ)
    (oldTail : Set ℂ) (ε : ℝ) where
  center : unitInterval
  left : unitInterval
  right : unitInterval
  left_le_center : left ≤ center
  center_le_right : center ≤ right
  center_on_edge : γ center ∈ segment ℝ a b
  left_in_ball : γ left ∈ Metric.ball (γ center) ε
  right_in_ball : γ right ∈ Metric.ball (γ center) ε
  clearance : Metric.ball (γ center) ε ∩ oldTail = ∅
  sameSide :
    (γ left ∈ detourPositiveSide a (b - a) ∧
      γ right ∈ detourPositiveSide a (b - a)) ∨
    (detourSide a (b - a) (γ left) < 0 ∧
      detourSide a (b - a) (γ right) < 0)

/-- Every valid attachment record yields the endpoint-correct local replacement
needed by an ordered detour schedule. -/
lemma CrossingAttachment.exists_replacement
    {x y : ℂ} {γ : Path x y} {a b : ℂ} {oldTail : Set ℂ} {ε : ℝ}
    (A : CrossingAttachment γ a b oldTail ε)
    (hab : a ≠ b) (hε : 0 < ε) :
    ∃ δ : Path (γ A.left) (γ A.right),
      (∀ q, δ q ∉ segment ℝ a b) ∧
      (∀ q, δ q ∉ oldTail) := by
  rcases A.sameSide with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · -- Both in positive side
    exact exists_local_replacement_of_same_positive_side γ a b oldTail A.center A.left A.right hab hε A.left_le_center A.center_le_right A.center_on_edge A.left_in_ball A.right_in_ball hl hr A.clearance
  · -- Both have negative detourSide
    exact exists_local_replacement_of_same_negative_side γ a b oldTail A.center A.left A.right hab hε A.left_le_center A.center_le_right A.center_on_edge A.left_in_ball A.right_in_ball hl hr A.clearance

/-- Parameter intervals of successive attachment blocks are ordered and
disjoint.  This is the finite combinatorial invariant required to erase the
blocks to `OrderedDetourSchedule`. -/
def AttachmentsOrdered {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ}
    (blocks : List (CrossingAttachment γ a b oldTail ε)) : Prop :=
  blocks.Pairwise fun A B => A.right ≤ B.left

/-- Every crossing time is captured by one selected attachment interval. -/
def AttachmentsCoverHitTimes {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ}
    (blocks : List (CrossingAttachment γ a b oldTail ε)) : Prop :=
  ∀ t ∈ pathHitTimes γ (segment ℝ a b),
    ∃ A ∈ blocks, A.left < t ∧ t < A.right

/-- **Remaining finite-selection interface.**  Compactness and uniform tail
clearance should produce finitely many ordered same-side attachment blocks
covering all crossings.  This statement is intentionally retained with a
`sorry`: it is the precise next global residue after the now-formalized local
geometry, and is directly imported by the theorem it will complete. -/
lemma exists_ordered_covering_attachments
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    {x y : ℂ} (γ : Path x y)
    (hγtail : ∀ q, γ q ∈ (chainCarrier (b :: L))ᶜ)
    (hx : x ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hy : y ∈ (chainCarrier (a :: b :: L))ᶜ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ blocks : List
        (CrossingAttachment γ a b (chainCarrier (b :: L)) ε),
        AttachmentsOrdered blocks ∧ AttachmentsCoverHitTimes blocks := by
  sorry

end HexArea
