/-
# Hammersley-Welsh Bridge Decomposition for Diagonal Bridges

Helper lemmas for the HW decomposition counting inequality.
-/

import Mathlib
import RequestProject.SAWDecompHelpers

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## SAW diagCoord bounds -/

/-- Each SAW from paperStart of length n has max diagCoord at most n. -/
lemma saw_maxDiag_le' {n : ℕ} (s : SAW paperStart n)
    (u : HexVertex) (hu : u ∈ s.p.1.support) :
    u.1 + u.2.1 ≤ n := by
  have h := hexGraph_walk_sum_bound_pos (s.p.1.takeUntil u hu)
  have hlen := s.p.1.length_takeUntil_le hu
  simp [paperStart] at h
  linarith [s.l]

/-- Each SAW from paperStart of length n has min diagCoord at least -n. -/
lemma saw_minDiag_ge' {n : ℕ} (s : SAW paperStart n)
    (u : HexVertex) (hu : u ∈ s.p.1.support) :
    -(n : ℤ) ≤ u.1 + u.2.1 := by
  have h := hexGraph_walk_sum_bound_neg (s.p.1.takeUntil u hu)
  have hlen := s.p.1.length_takeUntil_le hu
  simp [paperStart] at h
  linarith [s.l]

/-- paperStart has diagCoord 0. -/
@[simp] lemma paperStart_diagCoord : paperStart.1 + paperStart.2.1 = 0 := by
  simp [paperStart]

/-- A SAW from paperStart stays in a strip of width at most 2n around 0.
    Specifically, every vertex has |diagCoord| ≤ n. -/
lemma saw_diagCoord_abs_le {n : ℕ} (s : SAW paperStart n)
    (u : HexVertex) (hu : u ∈ s.p.1.support) :
    |u.1 + u.2.1| ≤ n := by
  rw [abs_le]
  exact ⟨by linarith [saw_minDiag_ge' s u hu], by exact_mod_cast saw_maxDiag_le' s u hu⟩

end
