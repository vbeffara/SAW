import Mathlib
import RequestProject.SAWUmlaufHullExterior

/-!
# Finite polygonal arcs: combinatorial foundations

This file is part of the live ear-clipping/Umlaufsatz branch.  It separates the
finite-list facts about an open polygonal chain from the planar non-separation
theorem in `SAWUmlaufArcInduction`.  The resulting theorem is consumed by
`SAWUmlaufArcEscape`, then by the boundary-vertex escape construction in
`SAWUmlaufPolygon`; it is therefore preparation for the main theorem rather
than a dead branch.
-/

open Real Complex

noncomputable section

namespace HexArea

/-- Consecutive directed edges of an open vertex chain. -/
def chainEdges (L : List ℂ) : List (ℂ × ℂ) := L.zip L.tail

/-- A polygonal arc has distinct vertices and nonincident edges are disjoint.
Adjacent edges may share their prescribed common endpoint. -/
def PlaneArcSimple (L : List ℂ) : Prop :=
  L.Nodup ∧
  ∀ e₁ ∈ chainEdges L, ∀ e₂ ∈ chainEdges L,
    e₁.1 ≠ e₂.1 → e₁.1 ≠ e₂.2 → e₁.2 ≠ e₂.1 → e₁.2 ≠ e₂.2 →
      Disjoint (segment ℝ e₁.1 e₁.2) (segment ℝ e₂.1 e₂.2)

/-- The geometric carrier of an open polygonal chain. -/
def chainCarrier (L : List ℂ) : Set ℂ :=
  ⋃ e ∈ chainEdges L, segment ℝ e.1 e.2

@[simp] lemma chainEdges_nil : chainEdges ([] : List ℂ) = [] := rfl
@[simp] lemma chainEdges_singleton (a : ℂ) : chainEdges [a] = [] := rfl
@[simp] lemma chainEdges_cons_cons (a b : ℂ) (L : List ℂ) :
    chainEdges (a :: b :: L) = (a, b) :: chainEdges (b :: L) := by
  simp [chainEdges]

@[simp] lemma chainCarrier_nil : chainCarrier ([] : List ℂ) = ∅ := by
  simp [chainCarrier]

@[simp] lemma chainCarrier_singleton (a : ℂ) : chainCarrier [a] = ∅ := by
  simp [chainCarrier]

lemma chainCarrier_cons_cons (a b : ℂ) (L : List ℂ) :
    chainCarrier (a :: b :: L) = segment ℝ a b ∪ chainCarrier (b :: L) := by
  simp [chainCarrier]

/-
Removing the initial vertex of a simple open chain leaves a simple chain.
-/
lemma PlaneArcSimple.tail {L : List ℂ} (h : PlaneArcSimple L) :
    PlaneArcSimple L.tail := by
  rcases L with ( _ | ⟨ x, _ | ⟨ y, L ⟩ ⟩ ) <;> simp_all +decide [ PlaneArcSimple ]

/-
Every edge of the tail is an edge of the original chain.
-/
lemma chainEdges_tail_subset (L : List ℂ) :
    ∀ e ∈ chainEdges L.tail, e ∈ chainEdges L := by
  rcases L with ( _ | ⟨ a, _ | ⟨ b, L ⟩ ⟩ ) <;> simp_all +decide [ chainEdges ]

/-- The finite union of segments carried by an open chain is closed. -/
lemma isClosed_chainCarrier (L : List ℂ) : IsClosed (chainCarrier L) := by
  simpa [chainCarrier] using
    (HexArea.isOpen_compl_iUnion_segments (chainEdges L)).isClosed_compl

/-- Compatibility form of `isClosed_chainCarrier` using the explicit union. -/
lemma isClosed_iUnion_chainEdges (L : List ℂ) :
    IsClosed (⋃ e ∈ chainEdges L, segment ℝ e.1 e.2) := by
  simpa [chainCarrier] using isClosed_chainCarrier L

end HexArea