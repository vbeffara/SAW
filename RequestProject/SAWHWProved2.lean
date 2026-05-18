/-
# Hammersley-Welsh Decomposition: Helper Lemmas
-/

import Mathlib
import RequestProject.SAWPaperChain

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Diagonal coordinate -/

def diagCoord (v : HexVertex) : ℤ := v.1 + v.2.1

lemma diagCoord_adj_le {v w : HexVertex} (h : hexGraph.Adj v w) :
    diagCoord w - diagCoord v ≤ 1 := by
  unfold diagCoord; unfold hexGraph at h
  rcases h with ⟨_, _, h | h | h⟩ | ⟨_, _, h | h | h⟩ <;> obtain ⟨h1, h2⟩ := h <;> omega

lemma diagCoord_adj_ge {v w : HexVertex} (h : hexGraph.Adj v w) :
    -(1 : ℤ) ≤ diagCoord w - diagCoord v := by
  unfold diagCoord; unfold hexGraph at h
  rcases h with ⟨_, _, h | h | h⟩ | ⟨_, _, h | h | h⟩ <;> obtain ⟨h1, h2⟩ := h <;> omega

lemma walk_diagCoord_bound {v w : HexVertex} (p : hexGraph.Walk v w) :
    diagCoord w - diagCoord v ≤ p.length ∧
    diagCoord v - diagCoord w ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp [SimpleGraph.Walk.length_cons]
    constructor <;> linarith [diagCoord_adj_le h, diagCoord_adj_ge h, ih.1, ih.2]

lemma walk_support_diagCoord_bound {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    diagCoord u - diagCoord v ≤ p.length ∧
    diagCoord v - diagCoord u ≤ p.length := by
  have h := walk_diagCoord_bound (p.takeUntil u hu)
  have hlen : (p.takeUntil u hu).length ≤ p.length := p.length_takeUntil_le hu
  constructor <;> linarith [h.1, h.2]

lemma Finset.sum_powerset_prod_eq_prod_add_one
    (N : ℕ) (a : ℕ → ℝ) :
    ∑ S ∈ (Finset.range N).powerset, ∏ i ∈ S, a i =
    ∏ i ∈ Finset.range N, (1 + a i) := by
  simp [add_comm, Finset.prod_add]

end
