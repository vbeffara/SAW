/-
# Hammersley-Welsh Bridge Decomposition: Structural Lemmas

Key structural lemmas for the Hammersley-Welsh bridge decomposition.

The main result: on any walk on the hexagonal lattice, the maximum
diagCoord (v.1 + v.2.1) is always achieved by a TRUE-sublattice vertex.
This is the foundation for the bridge decomposition, since it ensures
that the walk can always be split at a TRUE vertex, producing bridges
that are compatible with the PaperBridge definition.

## Reference

J.M. Hammersley and D.J.A. Welsh,
"Further results on the rate of convergence to the connective constant
 of the hypercubical lattice", 1962.

H. Duminil-Copin and S. Smirnov,
"The connective constant of the hexagonal lattice equals √(2+√2)",
Annals of Mathematics 175(3), 2012, Section 3.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWWalkPartition

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Max diagCoord is always TRUE

For any walk on the hexagonal lattice, the maximum diagCoord (v.1 + v.2.1)
is always achieved by a TRUE vertex. This is because:
- FALSE(x,y) at dc D = x+y has TRUE neighbor (x,y,true) at the SAME dc D
- In any walk, a FALSE vertex must be adjacent to a TRUE vertex
  (hexGraph is bipartite), and all TRUE neighbors of FALSE(x,y) have dc ≥ x+y
-/

/-- FALSE vertex at (x,y) has TRUE neighbor at same diagCoord in same cell -/
lemma false_same_cell_neighbor' (x y : ℤ) :
    hexGraph.Adj (x, y, false) (x, y, true) := by
  left; exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- In any non-trivial hex walk, a FALSE vertex has a TRUE vertex at dc ≥ its dc.
    This is because hexGraph is bipartite (FALSE only adjacent to TRUE),
    and every TRUE neighbor of FALSE(x,y) has dc ≥ x+y:
    - TRUE(x,y) at dc x+y
    - TRUE(x+1,y) at dc x+y+1
    - TRUE(x,y+1) at dc x+y+1 -/
lemma false_has_true_ge_dc' {v w : HexVertex} (p : hexGraph.Walk v w)
    (hp : 1 ≤ p.length)
    (u : HexVertex) (hu : u ∈ p.support) (hu_false : u.2.2 = false) :
    ∃ t ∈ p.support, t.2.2 = true ∧ u.1 + u.2.1 ≤ t.1 + t.2.1 := by
  induction' p with h p ih generalizing u <;> simp_all +decide [ SimpleGraph.Walk.cons ];
  cases hu <;> simp_all +decide [ hexGraph ];
  · grind +suggestions;
  · cases ‹hexGraph.Walk ih _› ; aesop;
    cases ‹hexGraph.Adj ih _› <;> aesop

/-- In any non-trivial hex path, max diagCoord is achieved by a TRUE vertex.
    This is the key structural lemma for the Hammersley-Welsh decomposition:
    it ensures that when we split a SAW at its max-diagCoord vertex, that
    vertex is always TRUE, which is compatible with the PaperBridge definition
    (PaperBridges start at paperStart, a TRUE vertex). -/
lemma max_dc_is_true' {v w : HexVertex} (p : hexGraph.Walk v w)
    (hp : p.IsPath) (hp_ne : p.support.length ≥ 2)
    (u : HexVertex) (hu : u ∈ p.support)
    (hu_max : ∀ z ∈ p.support, z.1 + z.2.1 ≤ u.1 + u.2.1) :
    ∃ t ∈ p.support, t.2.2 = true ∧ u.1 + u.2.1 ≤ t.1 + t.2.1 := by
  by_cases hu_false : u.2.2 = false;
  · apply false_has_true_ge_dc' p (by grind) u hu hu_false;
  · exact ⟨ u, hu, by simpa using hu_false, le_rfl ⟩

end
