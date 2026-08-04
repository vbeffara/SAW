import Mathlib
import RequestProject.SAWUmlaufCorridorPath

/-!
# The corridor replacement block

This file packages the connectivity result of `SAWUmlaufCorridorPath` into the
replacement interface consumed by the ordered detour schedule.  It is imported
by `SAWUmlaufMixedSchedule`, hence lies on the live route to the Umlaufsatz.

A corridor block records one parameter interval `[left, right]` whose two
boundary values lie in a corridor around the new edge, off the edge itself, the
corridor being disjoint from the old tail.  The proved connectivity of
`corridor \ edge` then supplies the required replacement path.

Unlike the same-side and endpoint-escape blocks, a corridor block imposes **no**
parity or side condition on its two boundary values: the corridor overhangs the
free endpoint `a`, so opposite sides are joined around `a`.  Consequently a
single corridor block can absorb *all* crossings at once.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- One replacement block realized inside a corridor around the new edge. -/
structure CorridorAttachment {x y : ℂ} (γ : Path x y) (a b : ℂ)
    (oldTail : Set ℂ) where
  left : unitInterval
  right : unitInterval
  left_le_right : left ≤ right
  /-- Right-hand coordinate bound of the corridor. -/
  reach : ℝ
  /-- Transverse half-width of the corridor. -/
  width : ℝ
  reach_pos : 0 < reach
  width_pos : 0 < width
  left_mem : γ left ∈ corridorSet a (b - a) reach width
  right_mem : γ right ∈ corridorSet a (b - a) reach width
  left_off : γ left ∉ segment ℝ a b
  right_off : γ right ∉ segment ℝ a b
  clear : ∀ z ∈ corridorSet a (b - a) reach width, z ∉ oldTail

namespace CorridorAttachment

/-- A corridor block supplies exactly the replacement interface required by an
ordered detour schedule. -/
lemma exists_replacement {x y : ℂ} {γ : Path x y} {a b : ℂ} {oldTail : Set ℂ}
    (A : CorridorAttachment γ a b oldTail) (hab : a ≠ b) :
    ∃ δ : Path (γ A.left) (γ A.right),
      (∀ q, δ q ∉ segment ℝ a b) ∧ (∀ q, δ q ∉ oldTail) := by
  have hu : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hseg : segment ℝ a (a + (b - a)) = segment ℝ a b := by
    rw [show a + (b - a) = b by ring]
  obtain ⟨δ, hδC, hδS⟩ :=
    exists_corridorPath a (b - a) hu A.reach A.width A.width_pos A.reach_pos
      (γ A.left) (γ A.right) A.left_mem (by rw [hseg]; exact A.left_off)
      A.right_mem (by rw [hseg]; exact A.right_off)
  refine ⟨δ, ?_, ?_⟩
  · intro q
    have := hδS q
    rwa [hseg] at this
  · intro q
    exact A.clear _ (hδC q)

end CorridorAttachment

end HexArea
