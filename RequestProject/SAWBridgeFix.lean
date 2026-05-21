/-
# Corrected bridge partition and connection to SAW counts

The original `bridge_partition` sums over ALL bridges (including translates),
making the tsum always 0 for T ≥ 1. We define corrected versions:
- `OriginBridge T`: bridges starting from hexOrigin
- `origin_bridge_partition`: the corrected bridge partition function

Note: the diagonal coordinate bridges (`PaperBridge`, `paper_bridge_partition`)
from SAWStripIdentityCorrect.lean and SAWDiagProof.lean supersede these
for the main proof. This file provides the infrastructure they build on.
-/

import RequestProject.SAWBridge

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Construction of bridges of width 1 -/

/-- Adjacency: (0, y, false) is adjacent to (1, y, true) in hexGraph. -/
private lemma width1_adj (y : ℤ) : hexGraph.Adj (0, y, false) (1, y, true) := by
  left; exact ⟨rfl, rfl, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩

/-- The single-edge walk from (0,y,false) to (1,y,true). -/
private def width1_walk (y : ℤ) : hexGraph.Walk (0, y, false) (1, y, true) :=
  SimpleGraph.Walk.cons (width1_adj y) SimpleGraph.Walk.nil

private lemma width1_walk_isPath (y : ℤ) : (width1_walk y).IsPath := by
  refine ⟨⟨?_⟩, ?_⟩ <;> simp [width1_walk]

private def width1_path (y : ℤ) : hexGraph.Path (0, y, false) (1, y, true) :=
  ⟨width1_walk y, width1_walk_isPath y⟩

/-- A bridge of width 1 for each y ∈ ℤ. -/
def bridge_width1 (y : ℤ) : Bridge 1 where
  start_v := (0, y, false)
  end_v := (1, y, true)
  walk := width1_path y
  start_left := rfl
  end_right := rfl
  in_strip := by
    intro v hv
    simp [width1_path, width1_walk, SimpleGraph.Walk.support] at hv
    rcases hv with rfl | rfl <;> omega

/-! ## Corrected bridge partition (from hexOrigin) -/

/-- A bridge of width T starting from hexOrigin. -/
def OriginBridge (T : ℕ) := {b : Bridge T // b.start_v = hexOrigin}

/-- The corrected bridge partition function: sum over bridges from hexOrigin. -/
def origin_bridge_partition (T : ℕ) (x : ℝ) : ℝ :=
  ∑' (b : OriginBridge T), x ^ b.1.walk.1.length

end
