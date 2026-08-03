import Mathlib
import RequestProject.SAWUmlaufAttachmentData
import RequestProject.SAWUmlaufOrderedDetours
import RequestProject.SAWUmlaufCrossingIntervals

/-!
# Folding selected crossing attachments into an Umlaufsatz detour schedule

This file is part of the live Umlaufsatz route.  It is imported by
`SAWUmlaufDetourConstruction`, whose result is consumed by
`SAWUmlaufArcDetour → SAWUmlaufArcInduction → SAWUmlaufArcEscape →
SAWUmlaufPolygon`.  Thus the declarations here are preparation for the main
Umlaufsatz, not a dead branch.

`CrossingAttachment` supplies the local geometry around one crossing block.
The inductive type below adds precisely the global information needed while
walking from left to right along the original path: order of the next block,
avoidance on the retained gap, and eventual avoidance on the final suffix.
Unlike `OrderedDetourSchedule`, it does not store a chosen replacement path;
that path is produced from the geometric data only when the schedule is folded.
This separates finite interval selection from local semicircle construction.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- A left-to-right list of geometric crossing attachments, together with
certificates that every retained part of the original path misses the new edge.

The index `start` is the right endpoint of the previously processed block.
At a `step`, the next attachment begins no earlier than `start`; at `done`, the
remaining suffix misses the new edge. -/
inductive AttachmentDetourSchedule {x y : ℂ} (γ : Path x y) (a b : ℂ)
    (oldTail : Set ℂ) (ε : ℝ) : unitInterval → Type
  | done (start : unitInterval)
      (suffixNew : ∀ q, γ.subpath start 1 q ∉ segment ℝ a b) :
      AttachmentDetourSchedule γ a b oldTail ε start
  | step (start : unitInterval)
      (attachment : CrossingAttachment γ a b oldTail ε)
      (hstart : start ≤ attachment.left)
      (keptNew : ∀ q, γ.subpath start attachment.left q ∉ segment ℝ a b)
      (rest : AttachmentDetourSchedule γ a b oldTail ε attachment.right) :
      AttachmentDetourSchedule γ a b oldTail ε start

namespace AttachmentDetourSchedule

/-- Forget the avoidance proofs and read off the selected geometric blocks. -/
def blocks {x y : ℂ} {γ : Path x y} {a b : ℂ} {oldTail : Set ℂ} {ε : ℝ}
    {start : unitInterval} :
    AttachmentDetourSchedule γ a b oldTail ε start →
      List (CrossingAttachment γ a b oldTail ε)
  | .done _ _ => []
  | .step _ A _ _ rest => A :: rest.blocks

/-- The blocks recorded by an attachment schedule are globally ordered. -/
lemma blocks_ordered {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ} {start : unitInterval}
    (S : AttachmentDetourSchedule γ a b oldTail ε start) :
    AttachmentsOrdered S.blocks := by
  induction S with
  | done start suffixNew => simp [blocks]; exact List.Pairwise.nil
  | step start attachment hstart keptNew rest ih =>
    simp [blocks]
    refine List.pairwise_cons.mpr ⟨?_, ih⟩
    intro B hB
    have left_ge_start : ∀ {p} (S : AttachmentDetourSchedule γ a b oldTail ε p)
        (A : CrossingAttachment γ a b oldTail ε) (hA : A ∈ S.blocks), p ≤ A.left := fun S A hA => by
      induction S with
      | done start suffixNew => simp [blocks] at hA
      | step start att hstart keptNew rest ih =>
        simp [blocks] at hA
        cases hA with
        | inl hAeq => rw [hAeq]; exact hstart
        | inr hA' =>
            have h1 := CrossingAttachment.left_le_center att
            have h2 := CrossingAttachment.center_le_right att
            exact le_trans hstart (le_trans h1 (le_trans h2 (ih hA')))
    exact left_ge_start rest B hB

/-- The retained-gap invariant for a concrete list of selected attachments.
This is the non-geometric half of finite selection: it says exactly that the
original path is safe before the first block, between successive blocks, and
after the last block. -/
def AttachmentsRetainedAvoid {x y : ℂ} (γ : Path x y) (a b : ℂ)
    {oldTail : Set ℂ} {ε : ℝ} : unitInterval →
      List (CrossingAttachment γ a b oldTail ε) → Prop
  | start, [] => ∀ q, γ.subpath start 1 q ∉ segment ℝ a b
  | start, A :: rest =>
      start ≤ A.left ∧
      (∀ q, γ.subpath start A.left q ∉ segment ℝ a b) ∧
      AttachmentsRetainedAvoid γ a b A.right rest

/-- A list satisfying the retained-gap invariant is precisely enough to build
an attachment schedule.  The selected blocks themselves already carry all
local geometric data. -/
lemma schedule_of_blocks {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ} (start : unitInterval)
    (blocks : List (CrossingAttachment γ a b oldTail ε))
    (hsafe : AttachmentsRetainedAvoid γ a b start blocks) :
    ∃ S : AttachmentDetourSchedule γ a b oldTail ε start,
      S.blocks = blocks := by
  induction blocks generalizing start with
  | nil =>
      exact ⟨AttachmentDetourSchedule.done start hsafe, rfl⟩
  | cons A rest ih =>
      obtain ⟨hle, hkept, hrest⟩ := hsafe
      obtain ⟨S, hS⟩ := ih A.right hrest
      exact ⟨AttachmentDetourSchedule.step start A hle hkept S, by simp [blocks, hS]⟩

/-- Ordered attachment intervals covering every hit time automatically leave
safe retained gaps.  Consequently the finite-selection interface from
`SAWUmlaufAttachmentData` can be converted directly into the geometric schedule
consumed by the detour fold.  This lemma is the global combinatorial bridge:
all remaining work after it is the existence of the ordered covering blocks. -/
lemma exists_schedule_of_ordered_covering
    {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ}
    (blocks : List (CrossingAttachment γ a b oldTail ε))
    (hordered : AttachmentsOrdered blocks)
    (hcover : AttachmentsCoverHitTimes blocks) :
    Nonempty (AttachmentDetourSchedule γ a b oldTail ε 0) := by
  -- Generalized helper for arbitrary start point
  have hgen : ∀ (start : unitInterval) (bs : List (CrossingAttachment γ a b oldTail ε)),
      AttachmentsOrdered bs →
      (∀ t ∈ pathHitTimes γ (segment ℝ a b), start ≤ t → ∃ B ∈ bs, B.left < t ∧ t < B.right) →
      (∀ B ∈ bs, start ≤ B.left) →
      AttachmentsRetainedAvoid γ a b start bs := by
    intro start bs hbord hcover' hstart_le_all
    induction bs generalizing start with
    | nil =>
        simp only [AttachmentsRetainedAvoid]
        intro q hq
        -- γ.subpath start 1 q = γ (start + q * (1 - start)) which is ≥ start
        exfalso
        have hstart_le_one : start ≤ (1 : unitInterval) := le_top
        -- Use contrapositive of subpath_avoids_of_Icc_disjoint_hitTimes
        have hdisj : Disjoint (Set.Icc start 1) (pathHitTimes γ (segment ℝ a b)) := by
          rw [Set.disjoint_left]
          intro t ht ht'
          obtain ⟨B, hBin, _, _⟩ := hcover' t ht' ht.1
          cases hBin
        exact (subpath_avoids_of_Icc_disjoint_hitTimes γ (segment ℝ a b) start 1 hstart_le_one hdisj) q hq
    | cons A rest ih =>
        simp only [AttachmentsRetainedAvoid]
        have hle : start ≤ A.left := hstart_le_all A (List.Mem.head rest)
        refine ⟨hle, ?_, ?_⟩
        · -- Path from start to A.left avoids segment
          apply subpath_avoids_of_Icc_disjoint_hitTimes γ (segment ℝ a b) start A.left hle
          rw [Set.disjoint_left]
          intro t ht ht'
          -- t ∈ [start, A.left] ∩ pathHitTimes
          -- hcover' says t is covered by some B with B.left < t
          -- But t ≤ A.left, and all B ∈ A :: rest have B.left ≥ A.left ≥ t
          -- except possibly A if A.left < t. But t ≤ A.left, so A.left < t is false.
          obtain ⟨B, hBmem, hBleft, _⟩ := hcover' t ht' ht.1
          rcases List.mem_cons.mp hBmem with hBeq | hBinrest
          · rw [hBeq] at hBleft; exact not_le.mpr hBleft ht.2
          · -- B ∈ rest, so A.right ≤ B.left by ordering
            have hord : A.right ≤ B.left := by
              have hpw := hbord
              rw [AttachmentsOrdered] at hpw
              exact List.pairwise_cons.1 hpw |>.1 B hBinrest
            -- t ≤ A.left ≤ A.right ≤ B.left < t, contradiction
            have hAleAri : A.left ≤ A.right := le_trans A.left_le_center A.center_le_right
            have htle : (t : ℝ) ≤ A.left := ht.2
            have hAri : (A.left : ℝ) ≤ A.right := hAleAri
            have hOrd : (A.right : ℝ) ≤ B.left := hord
            have hBlt : (B.left : ℝ) < t := hBleft
            linarith
        · -- AttachmentsRetainedAvoid for rest starting at A.right
          apply ih A.right
          · -- AttachmentsOrdered rest
            have hpw := hbord
            rw [AttachmentsOrdered] at hpw
            exact List.pairwise_cons.1 hpw |>.2
          · -- Coverage for rest from A.right
            intro t ht htge
            have hstart_le_t : start ≤ t := by
              have hAleAri : A.left ≤ A.right := le_trans A.left_le_center A.center_le_right
              exact le_trans hle (le_trans hAleAri htge)
            specialize hcover' t ht hstart_le_t
            obtain ⟨B, hBmem, hBleft, hBright⟩ := hcover'
            rcases List.mem_cons.mp hBmem with hBeq | hBinrest
            · -- B = A, so t < A.right, contradicting t ≥ A.right
              rw [hBeq] at hBright
              have h1 : (t : ℝ) < A.right := hBright
              have h2 : (A.right : ℝ) ≤ t := htge
              linarith
            · exact ⟨B, hBinrest, hBleft, hBright⟩
          · -- ∀ B ∈ rest, A.right ≤ B.left
            intro B hB
            have hpw := hbord
            rw [AttachmentsOrdered] at hpw
            exact List.pairwise_cons.1 hpw |>.1 B hB
  have hsafe := hgen 0 blocks hordered (fun t ht _ => hcover t ht) (fun B _ => B.left.2.1)
  obtain ⟨S, _⟩ := schedule_of_blocks 0 blocks hsafe
  exact ⟨S⟩

/-- If the original path never meets the new edge, the empty attachment
schedule is available immediately.  This isolates the base case of the finite
geometric selector. -/
lemma done_zero_of_no_hitTimes {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ}
    (hno : pathHitTimes γ (segment ℝ a b) = ∅) :
    Nonempty (AttachmentDetourSchedule γ a b oldTail ε 0) := by
  refine ⟨AttachmentDetourSchedule.done 0 ?proof⟩
  intro q
  simp only [Path.subpath_zero_one]
  intro hq
  rw [pathHitTimes] at hno
  exact Set.notMem_empty q (hno ▸ Set.mem_preimage.mpr hq)

/-- A single attachment whose open parameter interval contains every crossing
already forms a complete attachment schedule.  This is the terminal geometric
case of the future finite selector: the prefix and suffix avoidance obligations
are obtained from the strict crossing bounds, not assumed separately. -/
lemma single_of_covers_all {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ}
    (A : CrossingAttachment γ a b oldTail ε)
    (hleft : (0 : unitInterval) ≤ A.left)
    (hright : A.right ≤ (1 : unitInterval))
    (hcover : ∀ t ∈ pathHitTimes γ (segment ℝ a b),
      A.left < t ∧ t < A.right) :
    Nonempty (AttachmentDetourSchedule γ a b oldTail ε 0) := by
  obtain ⟨hkept, hsuff⟩ := prefix_suffix_avoid_of_hitTimes_inner_bounds γ (segment ℝ a b) A.left A.right hleft hright hcover
  refine ⟨AttachmentDetourSchedule.step 0 A hleft hkept (AttachmentDetourSchedule.done A.right hsuff)⟩

/-- Every geometric attachment schedule folds to the lower-level ordered
schedule.  This is the exact bridge from selected same-side crossing blocks to
the existing finite path-realization machinery. -/
lemma toOrderedDetourSchedule {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ} {start : unitInterval}
    (hab : a ≠ b) (hε : 0 < ε)
    (S : AttachmentDetourSchedule γ a b oldTail ε start) :
    Nonempty (OrderedDetourSchedule γ (segment ℝ a b) oldTail start) := by
  induction S with
  | done start suffixNew =>
      exact OrderedDetourSchedule.done_of_suffix_avoids start suffixNew
  | step start A hstart hkeptNew rest ih =>
      obtain ⟨δ, hδNew, hδTail⟩ := A.exists_replacement hab hε
      exact ⟨OrderedDetourSchedule.step start A.left A.right hstart (le_trans A.left_le_center A.center_le_right) δ hkeptNew hδNew hδTail ih.some⟩

end AttachmentDetourSchedule

end HexArea
