/-
# Constancy of `ptWind` along an edge-avoiding chain of vertices

This file adds the small, generic winding-number bricks that turn the
project's *walk invariance* `HexArea.ptWind_eq_of_walk`
(`RequestProject.SAWUmlaufPtWindMove`) into a statement about a whole **list** of
points: if all consecutive segments of a list `ys` avoid every closed-cycle edge
of the polygon `P`, then `ptWind · P` takes the same value at every member of
`ys`.

## Why (NOT a dead branch)

This is the reduction step for the point-in-polygon residue
`chord_ear_other_ptWind_zero` of `RequestProject.SAWUmlaufPolygon`.  Cutting a
simple polygon `W` along a chord into the two pieces `P` and `Q`, the vertices of
`W` that do **not** lie on `P` are exactly the interior vertices of `Q`'s arc,
and consecutive such vertices are joined by `W`-edges that are disjoint from
*every* edge of `P` (they share no endpoint with them, and the chord is avoided
by the diagonal hypothesis).  Hence `ptWind · P` is **constant** on that whole
set, and the Jordan-content residue shrinks from "the winding of `P` around every
vertex of the other piece vanishes" to "**one** such vertex has winding `0`" —
for instance any vertex lying outside `convexHull P`.

The consumers are in `RequestProject.SAWUmlaufPolygon`
(`chordPiece_other_arc_chain`, `chord_ear_other_ptWind_zero_of_witness`).
-/

import Mathlib
import RequestProject.SAWUmlaufPtWind
import RequestProject.SAWUmlaufPtWindMove

open Real Complex

noncomputable section

namespace HexArea

/-- Strengthening a chain relation using membership of the two endpoints in the
list.  (`List.IsChain.imp` only offers the relation, not membership, which is
what the chord-piece application needs.) -/
lemma isChain_of_forall_mem {α : Type*} (R S : α → α → Prop) :
    ∀ (l : List α), List.IsChain R l →
      (∀ a ∈ l, ∀ b ∈ l, R a b → S a b) → List.IsChain S l := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x t ih =>
      cases t with
      | nil => intro _ _; simp
      | cons y t' =>
          intro h hm
          rw [List.isChain_cons_cons] at h ⊢
          refine ⟨hm x (by simp) y (by simp) h.1, ih h.2 ?_⟩
          intro a ha b hb hab
          exact hm a (by simp [ha]) b (by simp [hb]) hab

/-- The avoidance relation used for `ptWind`-invariance: the segment `[a,b]` is
disjoint from every closed-cycle edge of `P`. -/
def SegAvoids (P : List ℂ) (a b : ℂ) : Prop :=
  ∀ e ∈ cycleEdges P, Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)

/-- Along an edge-avoiding chain, every member has the same winding as the head. -/
lemma ptWind_eq_head_of_isChain (P : List ℂ) :
    ∀ (ys : List ℂ) (y0 : ℂ), List.IsChain (SegAvoids P) (y0 :: ys) →
      ∀ y ∈ (y0 :: ys), ptWind y P = ptWind y0 P := by
  intro ys
  induction ys with
  | nil => intro y0 _ y hy; simp only [List.mem_singleton] at hy; rw [hy]
  | cons a t ih =>
      intro y0 hchain y hy
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hrest⟩ := hchain
      have hhead : ptWind y0 P = ptWind a P :=
        ptWind_eq_of_segment_avoids P y0 a hstep
      rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · rw [ih a hrest y hy', hhead]

/-- **`ptWind` is constant along an edge-avoiding chain of points.** -/
lemma ptWind_const_of_isChain (P : List ℂ) (ys : List ℂ)
    (hchain : List.IsChain (SegAvoids P) ys) :
    ∀ y ∈ ys, ∀ z ∈ ys, ptWind y P = ptWind z P := by
  cases ys with
  | nil => intro y hy; simp at hy
  | cons y0 t =>
      intro y hy z hz
      rw [ptWind_eq_head_of_isChain P t y0 hchain y hy,
        ptWind_eq_head_of_isChain P t y0 hchain z hz]

/-- **One exterior witness suffices.**  If some member of an edge-avoiding chain
has vanishing winding around `P`, then every member does. -/
lemma ptWind_zero_of_isChain_witness (P : List ℂ) (ys : List ℂ)
    (hchain : List.IsChain (SegAvoids P) ys)
    (y0 : ℂ) (hy0 : y0 ∈ ys) (hzero : ptWind y0 P = 0) :
    ∀ y ∈ ys, ptWind y P = 0 := by
  intro y hy
  rw [ptWind_const_of_isChain P ys hchain y hy y0 hy0]
  exact hzero

/-- A member of the chain lying outside `convexHull P` is such a witness. -/
lemma ptWind_zero_of_isChain_hull_witness (P : List ℂ) (ys : List ℂ)
    (hchain : List.IsChain (SegAvoids P) ys)
    (y0 : ℂ) (hy0 : y0 ∈ ys) (hhull : y0 ∉ convexHull ℝ (P.toFinset : Set ℂ)) :
    ∀ y ∈ ys, ptWind y P = 0 :=
  ptWind_zero_of_isChain_witness P ys hchain y0 hy0
    (ptWind_zero_of_not_mem_convexHull y0 P hhull)

end HexArea
