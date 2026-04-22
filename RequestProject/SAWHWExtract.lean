/-
# Half-Plane Bridge Extraction (Hammersley-Welsh)

Infrastructure for the bridge decomposition from Section 3 of
Duminil-Copin & Smirnov (2012).
-/

import Mathlib
import RequestProject.SAWHWDecompNew

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-! ## diagCoord adjacency bounds -/

/-- Adjacent vertices have diagCoord differing by at most 1. -/
lemma diagCoord_adj_diff' {v w : HexVertex} (h : hexGraph.Adj v w) :
    diagCoord w - diagCoord v ∈ ({-1, 0, 1} : Set ℤ) := by
  simp only [diagCoord, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases h with ⟨h1, h2, h3 | h3 | h3⟩ | ⟨h1, h2, h3 | h3 | h3⟩ <;>
    simp_all <;> omega

end
