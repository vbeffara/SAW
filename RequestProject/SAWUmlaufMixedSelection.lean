import Mathlib
import RequestProject.SAWUmlaufMixedSchedule
import RequestProject.SAWUmlaufCrossingIntervals
import RequestProject.SAWUmlaufEndpointCorridor
import RequestProject.SAWUmlaufCorridorSelect

/-!
# Finite selection interface for mixed Umlaufsatz detours

This file is imported by `SAWUmlaufDetourConstruction`, so every declaration
below lies on the live route
`SAWUmlaufDetourConstruction → SAWUmlaufArcDetour → SAWUmlaufArcInduction →
SAWUmlaufArcEscape → SAWUmlaufPolygon` to the main Umlaufsatz.

The local geometry has two constructors: ordinary same-side blocks and one
possible endpoint-escape block.  This file isolates the finite combinatorics
common to both.  `SAWUmlaufEndpointCorridor` is imported here as explicit
preparation for the geometric selector: it upgrades the endpoint escape to the
three-piece corridor form needed when a transverse crossing occurs far from the
free endpoint; it is not a dead branch.  An ordered list whose open intervals cover every hit time has
safe retained gaps and therefore folds into `MixedDetourSchedule`.  Thus the
only remaining geometric task is to produce such a finite ordered covering
list; no schedule bookkeeping is left implicit.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- Parameter intervals of successive mixed blocks are ordered and disjoint. -/
def MixedAttachmentsOrdered {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ}
    (blocks : List (MixedDetourAttachment γ a b oldTail ε)) : Prop :=
  blocks.Pairwise fun A B => A.right ≤ B.left

/-- Every hit time is strictly inside one selected mixed block. -/
def MixedAttachmentsCoverHitTimes {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ}
    (blocks : List (MixedDetourAttachment γ a b oldTail ε)) : Prop :=
  ∀ t ∈ pathHitTimes γ (segment ℝ a b),
    ∃ A ∈ blocks, A.left < t ∧ t < A.right

/-- The original path avoids the new edge on every retained gap. -/
def MixedAttachmentsRetainedAvoid {x y : ℂ} (γ : Path x y) (a b : ℂ)
    {oldTail : Set ℂ} {ε : ℝ} : unitInterval →
      List (MixedDetourAttachment γ a b oldTail ε) → Prop
  | start, [] => ∀ q, γ.subpath start 1 q ∉ segment ℝ a b
  | start, A :: rest =>
      start ≤ A.left ∧
      (∀ q, γ.subpath start A.left q ∉ segment ℝ a b) ∧
      MixedAttachmentsRetainedAvoid γ a b A.right rest

/-- Retained-gap data turns a concrete list into the inductive mixed schedule. -/
lemma mixedSchedule_of_blocks {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ} (start : unitInterval)
    (blocks : List (MixedDetourAttachment γ a b oldTail ε))
    (hsafe : MixedAttachmentsRetainedAvoid γ a b start blocks) :
    Nonempty (MixedDetourSchedule γ a b oldTail ε start) := by
  induction blocks generalizing start with
  | nil => exact ⟨.done start hsafe⟩
  | cons A rest ih =>
      have ⟨hstart, hkeptNew, hrest⟩ := hsafe
      exact ⟨.step start A hstart hkeptNew (ih A.right hrest).some⟩

/-- Ordered mixed intervals covering all hit times automatically have safe
retained gaps.  This is the finite combinatorial bridge consumed directly by
the remaining geometric selector in `SAWUmlaufDetourConstruction`. -/
lemma exists_mixedSchedule_of_ordered_covering
    {x y : ℂ} {γ : Path x y} {a b : ℂ}
    {oldTail : Set ℂ} {ε : ℝ}
    (blocks : List (MixedDetourAttachment γ a b oldTail ε))
    (hordered : MixedAttachmentsOrdered blocks)
    (hcover : MixedAttachmentsCoverHitTimes blocks) :
    Nonempty (MixedDetourSchedule γ a b oldTail ε 0) := by
  -- First prove MixedAttachmentsRetainedAvoid, then apply mixedSchedule_of_blocks
  have hsafe : MixedAttachmentsRetainedAvoid γ a b 0 blocks := by
    -- Generalized helper for arbitrary start point
    have hgen : ∀ (start : unitInterval) (bs : List (MixedDetourAttachment γ a b oldTail ε)),
        MixedAttachmentsOrdered bs →
        (∀ t ∈ pathHitTimes γ (segment ℝ a b), start ≤ t → ∃ B ∈ bs, B.left < t ∧ t < B.right) →
        (∀ B ∈ bs, start ≤ B.left) →
        MixedAttachmentsRetainedAvoid γ a b start bs := by
      intro start bs hbord hcover' hstart_le_all
      induction bs generalizing start with
      | nil =>
          simp only [MixedAttachmentsRetainedAvoid]
          intro q hq
          exfalso
          have hstart_le_one : start ≤ (1 : unitInterval) := le_top
          have hdisj : Disjoint (Set.Icc start 1) (pathHitTimes γ (segment ℝ a b)) := by
            rw [Set.disjoint_left]
            intro t ht ht'
            obtain ⟨B, hBin, _, _⟩ := hcover' t ht' ht.1
            cases hBin
          exact (subpath_avoids_of_Icc_disjoint_hitTimes γ (segment ℝ a b) start 1 hstart_le_one hdisj) q hq
      | cons A rest ih =>
          simp only [MixedAttachmentsRetainedAvoid]
          have hle : start ≤ A.left := hstart_le_all A (List.Mem.head rest)
          refine ⟨hle, ?_, ?_⟩
          · apply subpath_avoids_of_Icc_disjoint_hitTimes γ (segment ℝ a b) start A.left hle
            rw [Set.disjoint_left]
            intro t ht ht'
            obtain ⟨B, hBmem, hBleft, _⟩ := hcover' t ht' ht.1
            rcases List.mem_cons.mp hBmem with hBeq | hBinrest
            · rw [hBeq] at hBleft; exact not_le.mpr hBleft ht.2
            · have hord : A.right ≤ B.left := by
                have hpw := hbord
                rw [MixedAttachmentsOrdered] at hpw
                exact List.pairwise_cons.1 hpw |>.1 B hBinrest
              have hAleAri : A.left ≤ A.right := A.left_le_right
              have htle : (t : ℝ) ≤ A.left := ht.2
              have hAri : (A.left : ℝ) ≤ A.right := hAleAri
              have hOrd : (A.right : ℝ) ≤ B.left := hord
              have hBlt : (B.left : ℝ) < t := hBleft
              linarith
          · exact ih A.right
              (List.pairwise_cons.1 hbord |>.2)
              (fun t ht htge => by
                specialize hcover' t ht (le_trans hle (le_trans A.left_le_right htge))
                obtain ⟨B, hBmem, hBleft, hBright⟩ := hcover'
                rcases List.mem_cons.mp hBmem with hBeq | hBinrest
                · rw [hBeq] at hBright
                  have : (t : ℝ) < A.right := hBright
                  have : (A.right : ℝ) ≤ t := htge
                  linarith
                · exact ⟨B, hBinrest, hBleft, hBright⟩)
              (fun B hB => by
                have hpw := hbord
                rw [MixedAttachmentsOrdered] at hpw
                exact List.pairwise_cons.1 hpw |>.1 B hB)
    exact hgen 0 blocks hordered (fun t ht _ => hcover t ht) (fun B _ => B.left.2.1)
  exact mixedSchedule_of_blocks 0 blocks hsafe

/-- The zero-crossing branch of mixed finite selection. -/
lemma exists_finite_ordered_mixed_cover_of_no_hits
    {x y : ℂ} (γ : Path x y) (a b : ℂ) (oldTail : Set ℂ)
    (hno : pathHitTimes γ (segment ℝ a b) = ∅) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ blocks : List (MixedDetourAttachment γ a b oldTail ε),
        MixedAttachmentsOrdered blocks ∧
        MixedAttachmentsCoverHitTimes blocks := by
  refine ⟨1, by norm_num, [], ?_, ?_⟩
  · exact List.Pairwise.nil
  · intro t ht
    rw [hno] at ht
    exact False.elim (Set.notMem_empty t ht)

/-- **Positive-crossing geometric selector.**  Proved by the corridor
construction of `SAWUmlaufCorridorSelect`: a single corridor block covers every
crossing at once, because the corridor overhangs the free endpoint `a` and so
`corridor \ edge` is path connected.  This removes the parity obstruction that
blocked the earlier same-side selection.

The adjacent-overlap case is handled honestly: no clearance ball around `a` is
asserted.  Instead the corridor is built around the initial piece
`[a, a + s₀ (b-a)]` reaching the deepest crossing, which is tail free because
the tail meets `[a,b]` in a convex set containing `b`. -/
lemma exists_finite_ordered_mixed_cover_of_nonempty
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    {x y : ℂ} (γ : Path x y)
    (hγtail : ∀ q, γ q ∈ (chainCarrier (b :: L))ᶜ)
    (hx : x ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hy : y ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hhit : (pathHitTimes γ (segment ℝ a b)).Nonempty) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ blocks : List (MixedDetourAttachment γ a b
          (chainCarrier (b :: L)) ε),
        MixedAttachmentsOrdered blocks ∧
        MixedAttachmentsCoverHitTimes blocks := by
  obtain ⟨A, hA⟩ :=
    exists_corridorAttachment_covering a b L hsimple γ hγtail hx hy hhit
  refine ⟨1, one_pos, [MixedDetourAttachment.corridor A], List.pairwise_singleton _ _, ?_⟩
  intro t ht
  exact ⟨MixedDetourAttachment.corridor A, List.mem_singleton_self _, hA t ht⟩

/-- **Remaining geometric selector.**  The compact crossing set admits a finite
left-to-right cover by ordinary same-side packets and endpoint-escape packets.
All consumers of this statement are proved.  The old-tail avoidance assumption
is essential for adjacent collinear overlap: only the genuinely new portion of
`[a,b]` can be hit. -/
lemma exists_finite_ordered_mixed_cover
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    {x y : ℂ} (γ : Path x y)
    (hγtail : ∀ q, γ q ∈ (chainCarrier (b :: L))ᶜ)
    (hx : x ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hy : y ∈ (chainCarrier (a :: b :: L))ᶜ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ blocks : List (MixedDetourAttachment γ a b
          (chainCarrier (b :: L)) ε),
        MixedAttachmentsOrdered blocks ∧
        MixedAttachmentsCoverHitTimes blocks := by
  by_cases hno : pathHitTimes γ (segment ℝ a b) = ∅
  · exact exists_finite_ordered_mixed_cover_of_no_hits γ a b
      (chainCarrier (b :: L)) hno
  · exact exists_finite_ordered_mixed_cover_of_nonempty a b L hsimple γ
      hγtail hx hy (Set.nonempty_iff_ne_empty.mpr hno)

end HexArea
