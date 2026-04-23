/-
# Finite strip monotonicity infrastructure

Proves that PaperFinStrip is monotone in L and that B_paper
is bounded above by the bridge partition function.
-/

import Mathlib
import RequestProject.SAWRecurrenceProof
import RequestProject.SAWParafermionicProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## PaperFinStrip monotonicity in L -/

/-- PaperFinStrip T L ⊆ PaperFinStrip T (L+1). -/
lemma PaperFinStrip_mono_L {T L : ℕ} {v : HexVertex}
    (hv : PaperFinStrip T L v) : PaperFinStrip T (L + 1) v := by
  unfold PaperFinStrip at *
  constructor
  · exact hv.1
  · rcases v with ⟨x, y, b⟩; cases b <;> simp_all <;> omega

/-! ## B_paper upper bound from bridge partition -/

/-- B_paper is bounded above by xc · paper_bridge_partition (proved elsewhere). -/
lemma B_paper_le_bridge' (T L : ℕ) (hT : 1 ≤ T) :
    B_paper T L xc ≤ xc * paper_bridge_partition T xc :=
  B_paper_le_xc_bridge' T L hT

end
