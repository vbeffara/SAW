/-
# Diagonal-strip bridges for the Hammersley-Welsh argument

The paper's strip identity uses strips defined by x+y coordinates.
This file defines diagonal bridges matching the paper and proves
key properties for the Hammersley-Welsh bound.
-/

import Mathlib
import RequestProject.SAWBridgeFix
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Change in x+y per hex step -/

/-- Each step in hexGraph changes x+y by at most 1. -/
lemma hexGraph_adj_sum_bound {v w : HexVertex} (h : hexGraph.Adj v w) :
    w.1 + w.2.1 - (v.1 + v.2.1) ≤ 1 ∧ v.1 + v.2.1 - (w.1 + w.2.1) ≤ 1 := by
  rcases h with ⟨h1, h2, h3 | h3 | h3⟩ | ⟨h1, h2, h3 | h3 | h3⟩ <;>
    constructor <;> simp_all <;> omega

/-- Walk bound for x+y: change bounded by walk length. -/
lemma hexGraph_walk_sum_bound_pos {v w : HexVertex} (p : hexGraph.Walk v w) :
    w.1 + w.2.1 - (v.1 + v.2.1) ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp [SimpleGraph.Walk.length_cons]
    linarith [(hexGraph_adj_sum_bound h).1]

lemma hexGraph_walk_sum_bound_neg {v w : HexVertex} (p : hexGraph.Walk v w) :
    v.1 + v.2.1 - (w.1 + w.2.1) ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp [SimpleGraph.Walk.length_cons]
    linarith [(hexGraph_adj_sum_bound h).2]

/-! ## Diagonal bridges -/

/-- A diagonal bridge of width T: walk from x+y=0 to x+y=T in strip. -/
structure DiagBridge (T : ℕ) where
  start_v : HexVertex
  end_v : HexVertex
  walk : hexGraph.Path start_v end_v
  start_left : start_v.1 + start_v.2.1 = 0
  end_right : end_v.1 + end_v.2.1 = (T : ℤ)
  in_strip : ∀ v ∈ walk.1.support, 0 ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ T

/-- Diagonal bridge starting from paperStart. -/
def DiagOriginBridge (T : ℕ) := {b : DiagBridge T // b.start_v = paperStart}

/-- Diagonal bridge partition function. -/
def diag_bridge_partition (T : ℕ) (x : ℝ) : ℝ :=
  ∑' (b : DiagOriginBridge T), x ^ b.1.walk.1.length

/-! ## Bridge length ≥ width -/

/-- A diagonal bridge of width T has length ≥ T. -/
theorem diag_bridge_length_ge_width (T : ℕ) (b : DiagBridge T) :
    T ≤ b.walk.1.length := by
  have h := hexGraph_walk_sum_bound_pos b.walk.1
  have h_start := b.start_left
  have h_end := b.end_right
  omega

/-! ## SAW x+y coordinate bound -/

/-- In a SAW from hexOrigin, each vertex has x+y ≤ length. -/
lemma saw_sum_le_length {n : ℕ} (s : SAW hexOrigin n) (v : HexVertex)
    (hv : v ∈ s.p.1.support) : v.1 + v.2.1 ≤ n := by
  have h := hexGraph_walk_sum_bound_pos (s.p.1.takeUntil v hv)
  have h_len := s.p.1.length_takeUntil_le hv
  simp [hexOrigin] at h
  linarith [s.l]

/-- In a SAW from hexOrigin, each vertex has x+y ≥ -length. -/
lemma saw_sum_ge_neg_length {n : ℕ} (s : SAW hexOrigin n) (v : HexVertex)
    (hv : v ∈ s.p.1.support) : -(n : ℤ) ≤ v.1 + v.2.1 := by
  have h := hexGraph_walk_sum_bound_neg (s.p.1.takeUntil v hv)
  have h_len := s.p.1.length_takeUntil_le hv
  simp [hexOrigin] at h
  linarith [s.l]

/-! ## hexOrigin properties -/

@[simp] lemma hexOrigin_sum : hexOrigin.1 + hexOrigin.2.1 = 0 := by
  simp [hexOrigin]

end
