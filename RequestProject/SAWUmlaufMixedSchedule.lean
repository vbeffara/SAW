import Mathlib
import RequestProject.SAWUmlaufAttachmentSchedule
import RequestProject.SAWUmlaufEndpointEscape

/-!
# Mixed same-side and endpoint-escape schedules for the Umlaufsatz

This file is imported directly by `SAWUmlaufDetourConstruction` and is therefore
on the live route to the main Umlaufsatz.  It closes the bookkeeping gap between
the two local geometric constructions: an ordinary crossing block is replaced
inside one half-plane, while at most one exceptional opposite-side block is
replaced by the proved route behind the free endpoint.  Both kinds of blocks
are folded into the same `OrderedDetourSchedule` consumed by the finite path
realization machinery.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- One replacement block in the global finite selector: either an ordinary
same-side attachment or the exceptional endpoint escape. -/
inductive MixedDetourAttachment {x y : ℂ} (γ : Path x y) (a b : ℂ)
    (oldTail : Set ℂ) (ε : ℝ)
  | sameSide (A : CrossingAttachment γ a b oldTail ε)
  | endpointEscape (A : EndpointEscapeAttachment γ a b oldTail)

namespace MixedDetourAttachment

/-- Left parameter endpoint of a mixed block. -/
def left {x y : ℂ} {γ : Path x y} {a b : ℂ} {oldTail : Set ℂ} {ε : ℝ} :
    MixedDetourAttachment γ a b oldTail ε → unitInterval
  | .sameSide A => A.left
  | .endpointEscape A => A.left

/-- Right parameter endpoint of a mixed block. -/
def right {x y : ℂ} {γ : Path x y} {a b : ℂ} {oldTail : Set ℂ} {ε : ℝ} :
    MixedDetourAttachment γ a b oldTail ε → unitInterval
  | .sameSide A => A.right
  | .endpointEscape A => A.right

/-- Every mixed block is ordered from left to right. -/
lemma left_le_right {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ}
    (A : MixedDetourAttachment γ a b oldTail ε) : A.left ≤ A.right := by
  cases A with
  | sameSide A => exact le_trans A.left_le_center A.center_le_right
  | endpointEscape A => exact A.left_le_right

/-- Both local geometric constructions expose exactly the replacement interface
required by an ordered schedule. -/
lemma exists_replacement {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ}
    (A : MixedDetourAttachment γ a b oldTail ε)
    (hab : a ≠ b) (hε : 0 < ε) :
    ∃ δ : Path (γ A.left) (γ A.right),
      (∀ q, δ q ∉ segment ℝ a b) ∧ (∀ q, δ q ∉ oldTail) := by
  cases A with
  | sameSide A => exact A.exists_replacement hab hε
  | endpointEscape A => exact A.exists_replacement hab

end MixedDetourAttachment

/-- A left-to-right mixed schedule.  Retained gaps avoid the new edge; every
removed block carries either same-side or endpoint-escape geometry. -/
inductive MixedDetourSchedule {x y : ℂ} (γ : Path x y) (a b : ℂ)
    (oldTail : Set ℂ) (ε : ℝ) : unitInterval → Type
  | done (start : unitInterval)
      (suffixNew : ∀ q, γ.subpath start 1 q ∉ segment ℝ a b) :
      MixedDetourSchedule γ a b oldTail ε start
  | step (start : unitInterval)
      (attachment : MixedDetourAttachment γ a b oldTail ε)
      (hstart : start ≤ attachment.left)
      (keptNew : ∀ q, γ.subpath start attachment.left q ∉ segment ℝ a b)
      (rest : MixedDetourSchedule γ a b oldTail ε attachment.right) :
      MixedDetourSchedule γ a b oldTail ε start

namespace MixedDetourSchedule

/-- Fold a mixed geometric schedule into the already proved finite path
realization interface.  This is the promised explicit link showing that the
endpoint-escape branch is not dead preparation. -/
lemma toOrderedDetourSchedule {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ} {start : unitInterval}
    (hab : a ≠ b) (hε : 0 < ε)
    (S : MixedDetourSchedule γ a b oldTail ε start) :
    Nonempty (OrderedDetourSchedule γ (segment ℝ a b) oldTail start) := by
  induction S with
  | done start suffixNew =>
      exact OrderedDetourSchedule.done_of_suffix_avoids start suffixNew
  | step start A hstart keptNew rest ih =>
      obtain ⟨δ, hδNew, hδTail⟩ := A.exists_replacement hab hε
      exact ⟨OrderedDetourSchedule.step start A.left A.right hstart
        A.left_le_right δ keptNew hδNew hδTail ih.some⟩

end MixedDetourSchedule

end HexArea
