/-
# Discrete Stokes: summing the vertex relation over a finite vertex set

This file contains the *combinatorial* half of Step 2 of the proof of Lemma 2
(the strip identity) in Duminil-Copin & Smirnov 2012: summing the local vertex
relation over all vertices of a finite domain `V`, the mid-edges with **both**
endpoints in `V` cancel pairwise, and only the mid-edges with exactly one
endpoint in `V` survive.

The content here is purely formal: it works for an arbitrary finite set `V` of
hex vertices and only uses

* antisymmetry of the direction vector `midDir v w = -midDir w v`;
* symmetry of the observable combination `freshSym v w = freshSym w v`.

## Main results

* `freshVertexSum_eq_nbr_sum` — the vertex sum is a sum over the neighbour set
* `stokes_interior_cancel` — the "both endpoints inside" part vanishes
* `stokes_boundary_sum` — `∑_{v ∈ V} freshVertexSum v` equals the boundary sum

These are combined with the vertex relation in `SAWStripBoundarySum.lean`.
-/

import Mathlib
import RequestProject.SAWPathVertexRelation

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Neighbour finsets -/

/-- The (three-element) finset of neighbours of a hex vertex. -/
def nbrFinset (v : HexVertex) : Finset HexVertex :=
  Finset.image (hexNeighbors3 v) Finset.univ

lemma mem_nbrFinset_iff (v w : HexVertex) :
    w ∈ nbrFinset v ↔ hexGraph.Adj v w := by
  constructor
  · intro h
    simp only [nbrFinset, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨i, hi⟩ := h
    exact hi ▸ hexNeighbors3_adj v i
  · intro h
    simp only [nbrFinset, Finset.mem_image, Finset.mem_univ, true_and]
    rcases hexNeighbors3_complete v w h with h0 | h1 | h2
    · exact ⟨0, h0.symm⟩
    · exact ⟨1, h1.symm⟩
    · exact ⟨2, h2.symm⟩

lemma mem_nbrFinset_symm {v w : HexVertex} (h : w ∈ nbrFinset v) :
    v ∈ nbrFinset w :=
  (mem_nbrFinset_iff w v).2 ((mem_nbrFinset_iff v w).1 h).symm

/-- Summing a function over the three neighbours is the same as summing over
`Fin 3` composed with `hexNeighbors3`. -/
lemma sum_nbrFinset (v : HexVertex) (f : HexVertex → ℂ) :
    ∑ w ∈ nbrFinset v, f w = ∑ i : Fin 3, f (hexNeighbors3 v i) := by
  rw [nbrFinset, Finset.sum_image]
  intro a _ b _ hab
  exact hexNeighbors3_injective v hab

/-! ## The Stokes term -/

/-- The direction vector of the mid-edge from `v` to `w`. -/
def midDir (v w : HexVertex) : ℂ := correctHexEmbed w - correctHexEmbed v

lemma midDir_antisymm (v w : HexVertex) : midDir w v = -midDir v w := by
  simp [midDir]

lemma midDir_eq_midEdgeDir (v : HexVertex) (i : Fin 3) :
    midDir v (hexNeighbors3 v i) = midEdgeDir v i := rfl

/-- The symmetric combination of the observable on the two orientations of the
mid-edge `{v, w}`. -/
def freshSym (T L : ℕ) (v w : HexVertex) : ℂ :=
  freshObs T L v w + freshObs T L w v

lemma freshSym_comm (T L : ℕ) (v w : HexVertex) :
    freshSym T L w v = freshSym T L v w := by
  simp [freshSym]; ring

/-- The contribution of the *oriented* mid-edge `(v, w)` to the vertex sum. -/
def stokesTerm (T L : ℕ) (v w : HexVertex) : ℂ :=
  midDir v w * freshSym T L v w

lemma stokesTerm_antisymm (T L : ℕ) (v w : HexVertex) :
    stokesTerm T L w v = -stokesTerm T L v w := by
  simp [stokesTerm, midDir_antisymm v w, freshSym_comm]

/-- The fresh vertex sum, rewritten as a sum over the neighbour finset. -/
lemma freshVertexSum_eq_nbr_sum (T L : ℕ) (v : HexVertex) :
    freshVertexSum T L v = ∑ w ∈ nbrFinset v, stokesTerm T L v w := by
  rw [sum_nbrFinset]
  simp only [freshVertexSum, stokesTerm, freshSym, midDir_eq_midEdgeDir]

/-! ## The interior cancellation

Every mid-edge with both endpoints in `V` occurs exactly twice in
`∑_{v ∈ V} ∑_{w ∈ nbrFinset v ∩ V}`, once as `(v, w)` and once as `(w, v)`,
and `stokesTerm` is antisymmetric.  So the whole sum vanishes. -/

/-- The finset of oriented mid-edges with both endpoints in `V`. -/
def innerPairs (V : Finset HexVertex) : Finset (HexVertex × HexVertex) :=
  (V ×ˢ V).filter (fun p => p.2 ∈ nbrFinset p.1)

lemma mem_innerPairs {V : Finset HexVertex} {p : HexVertex × HexVertex} :
    p ∈ innerPairs V ↔ p.1 ∈ V ∧ p.2 ∈ V ∧ p.2 ∈ nbrFinset p.1 := by
  simp [innerPairs, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- Interior mid-edges cancel: the sum of `stokesTerm` over all oriented pairs
with both endpoints inside `V` is zero. -/
lemma stokes_innerPairs_zero (T L : ℕ) (V : Finset HexVertex) :
    ∑ p ∈ innerPairs V, stokesTerm T L p.1 p.2 = 0 := by
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p _
    simp only [stokesTerm_antisymm T L p.1 p.2, add_neg_cancel]
  · intro p hp _ h
    -- `(p.2, p.1) = p` would force `p.1 = p.2`, impossible since they are adjacent
    have h1 : p.2 = p.1 := congrArg Prod.fst h
    have hadj : hexGraph.Adj p.1 p.2 :=
      (mem_nbrFinset_iff _ _).1 (mem_innerPairs.1 hp).2.2
    exact hadj.ne h1.symm
  · intro p hp
    rw [mem_innerPairs] at hp ⊢
    exact ⟨hp.2.1, hp.1, mem_nbrFinset_symm hp.2.2⟩
  · intro p _
    rfl

/-- `∑_{v ∈ V} ∑_{w ∈ nbrFinset v ∩ V}` is exactly the sum over `innerPairs V`. -/
lemma sum_innerPairs_eq (T L : ℕ) (V : Finset HexVertex) :
    ∑ p ∈ innerPairs V, stokesTerm T L p.1 p.2
      = ∑ v ∈ V, ∑ w ∈ nbrFinset v ∩ V, stokesTerm T L v w := by
  rw [innerPairs, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext a
  simp only [Finset.mem_filter, Finset.mem_inter]
  tauto

/-- **Discrete Stokes.**  Summing the fresh vertex sum over a finite set `V` of
vertices leaves only the mid-edges leaving `V`. -/
theorem stokes_boundary_sum (T L : ℕ) (V : Finset HexVertex) :
    ∑ v ∈ V, freshVertexSum T L v
      = ∑ v ∈ V, ∑ w ∈ nbrFinset v \ V, stokesTerm T L v w := by
  have hsplit : ∀ v : HexVertex,
      ∑ w ∈ nbrFinset v, stokesTerm T L v w
        = ∑ w ∈ nbrFinset v ∩ V, stokesTerm T L v w
          + ∑ w ∈ nbrFinset v \ V, stokesTerm T L v w := by
    intro v
    rw [← Finset.sum_inter_add_sum_diff (nbrFinset v) V]
  calc ∑ v ∈ V, freshVertexSum T L v
      = ∑ v ∈ V, ∑ w ∈ nbrFinset v, stokesTerm T L v w := by
        exact Finset.sum_congr rfl fun v _ => freshVertexSum_eq_nbr_sum T L v
    _ = ∑ v ∈ V, (∑ w ∈ nbrFinset v ∩ V, stokesTerm T L v w
          + ∑ w ∈ nbrFinset v \ V, stokesTerm T L v w) :=
        Finset.sum_congr rfl fun v _ => hsplit v
    _ = (∑ v ∈ V, ∑ w ∈ nbrFinset v ∩ V, stokesTerm T L v w)
          + ∑ v ∈ V, ∑ w ∈ nbrFinset v \ V, stokesTerm T L v w := Finset.sum_add_distrib
    _ = ∑ v ∈ V, ∑ w ∈ nbrFinset v \ V, stokesTerm T L v w := by
        rw [← sum_innerPairs_eq, stokes_innerPairs_zero, zero_add]

end
