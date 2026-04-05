/-
# The Vertex Relation and Strip Identity (Lemma 1 & 2 of the paper)

Decomposition of the proof of B_paper ≤ 1 into smaller lemmas.
-/

import Mathlib
import RequestProject.SAWObservableProof
import RequestProject.SAWDiagBridge

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-
Each PaperSAW_B walk has length ≥ T.
-/
lemma paperSAW_B_length_ge (T L : ℕ) (s : PaperSAW_B T L) :
    T ≤ s.len := by
  have := @hexGraph_walk_sum_bound_neg ( paperStart ) s.saw.w s.saw.p.1;
  have := s.end_right.1; have := s.end_right.2; norm_num [ paperStart ] at *; linarith [ s.saw.l ] ;

/-- B_paper as a finite sum. -/
lemma B_paper_fintype_sum (T L : ℕ) (inst : Fintype (PaperSAW_B T L)) :
    B_paper T L xc = ∑ s : PaperSAW_B T L, xc ^ (s.len + 1) := by
  unfold B_paper; exact tsum_fintype _

/-- B_paper ≤ 1 from a bound on all partial sums. -/
theorem B_paper_le_one_from_partial_bound (T L : ℕ) (_hT : 1 ≤ T) (_hL : 1 ≤ L)
    (h_bound : ∀ (S : Finset (PaperSAW_B T L)),
      ∑ s ∈ S, xc ^ (s.len + 1) ≤ 1) :
    B_paper T L xc ≤ 1 := by
  haveI inst : Fintype (PaperSAW_B T L) := Fintype.ofFinite _
  rw [B_paper_fintype_sum T L inst]
  exact h_bound _

end