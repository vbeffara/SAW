/-
# Diagonal bridge proof infrastructure

This file provides infrastructure connecting diagonal bridges
to the strip identity and saw_count.

The fundamental sorry remains `B_paper_le_one_direct` from
SAWStripIdentityCorrect.lean (the core strip identity).
-/

import Mathlib
import RequestProject.SAWDiagConnection

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-! ## Paper-compatible bridges (matching PaperInfStrip exactly)

These bridges use the tighter PaperInfStrip constraints:
- TRUE: -(T-1) ≤ x+y ≤ 0
- FALSE: -T ≤ x+y ≤ -1

This ensures the endpoint (FALSE, x+y=-T) matches PaperSAW_B. -/

/-- A paper-compatible bridge of width T from paperStart. -/
structure PaperBridge (T : ℕ) where
  end_v : HexVertex
  walk : hexGraph.Path paperStart end_v
  end_right : end_v.1 + end_v.2.1 = -(T : ℤ) ∧ end_v.2.2 = false
  in_strip : ∀ v ∈ walk.1.support, PaperInfStrip T v

/-- Paper bridge partition function (edge-count convention). -/
def paper_bridge_partition (T : ℕ) (x : ℝ) : ℝ :=
  ∑' (b : PaperBridge T), x ^ b.walk.1.length

/-- Paper bridge length ≥ T (diagonal coordinate changes by T). -/
lemma paper_bridge_length_ge (T : ℕ) (b : PaperBridge T) :
    T ≤ b.walk.1.length := by
  have h := hexGraph_walk_sum_bound_neg b.walk.1
  have h_start : paperStart.1 + paperStart.2.1 = 0 := by simp [paperStart]
  have h_end := b.end_right.1
  rw [h_start] at h
  omega

/-- Each paper bridge fits in PaperFinStrip for large enough L. -/
lemma paper_bridge_in_fin_strip (T : ℕ) (b : PaperBridge T) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ v ∈ b.walk.1.support, PaperFinStrip T L v := by
  use b.walk.1.length + 1
  refine ⟨by omega, fun v hv => ?_⟩
  constructor
  · exact b.in_strip v hv
  · have hbnd := hexGraph_walk_bound (b.walk.1.takeUntil v hv)
    obtain ⟨hb1, hb2, _, _⟩ := hbnd
    have hlen := b.walk.1.length_takeUntil_le hv
    simp [paperStart] at hb1 hb2
    cases v.2.2 <;> simp <;> omega

/-- Finite partial sums of paper bridge weights are ≤ 1/xc.
    From B_paper(T,L,xc) = Σ xc^{n+1} ≤ 1, we get Σ xc^n ≤ 1/xc.
    This uses B_paper_le_one (which depends on B_paper_le_one_direct). -/
lemma paper_bridge_partial_sum_le (T : ℕ) (hT : 1 ≤ T)
    (F : Finset (PaperBridge T)) :
    ∑ b ∈ F, xc ^ b.walk.1.length ≤ 1 / xc := by
  sorry

/-- paper_bridge_partition T xc ≤ 1/xc. -/
theorem paper_bridge_upper_bound (T : ℕ) (hT : 1 ≤ T) :
    paper_bridge_partition T xc ≤ 1 / xc := by
  exact Real.tsum_le_of_sum_le (fun b => pow_nonneg xc_pos.le _)
    (fun F => paper_bridge_partial_sum_le T hT F)

end
