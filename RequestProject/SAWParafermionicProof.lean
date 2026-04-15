/-
# Infrastructure for the three remaining critical-path sorries

Helper lemmas working toward the three remaining sorries.
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Diagonal coordinate properties for walks -/

/-- Each hex edge changes the diagonal coordinate v.1 + v.2.1 by at most 1. -/
lemma hex_adj_diag_bound {v w : HexVertex} (h : hexGraph.Adj v w) :
    (v.1 + v.2.1) - 1 ≤ w.1 + w.2.1 ∧ w.1 + w.2.1 ≤ (v.1 + v.2.1) + 1 := by
  rcases h with ⟨_, _, h3 | h3 | h3⟩ | ⟨_, _, h3 | h3 | h3⟩ <;>
    simp_all <;> constructor <;> omega

/-- For a walk from paperStart, every vertex in the support has
    diagonal ≥ -(walk length). -/
lemma walk_from_paperStart_diag_ge {w : HexVertex}
    (p : hexGraph.Walk paperStart w) (u : HexVertex)
    (hu : u ∈ p.support) :
    -(p.length : ℤ) ≤ u.1 + u.2.1 := by
  have h := hexGraph_walk_sum_bound_neg (p.takeUntil u hu)
  have hlen := p.length_takeUntil_le hu
  simp [paperStart] at h
  linarith

/-- PaperFinStrip monotonicity: wider strips contain more vertices. -/
lemma paper_fin_strip_mono (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v) : PaperFinStrip T (L + 1) v := by
  constructor
  · exact hv.1
  · have h2 := hv.2
    dsimp [PaperFinStrip] at h2 ⊢
    split <;> simp_all <;> omega

/-! ## Weight comparison helpers -/

/-- xc is between 0 and 1. -/
lemma xc_in_unit : 0 < xc ∧ xc < 1 := ⟨xc_pos, xc_lt_one'⟩

/-- For 0 < x < xc, x < 1. -/
lemma lt_one_of_lt_xc {x : ℝ} (hxc : x < xc) : x < 1 :=
  lt_trans hxc xc_lt_one'

/-- Each bridge weight is at most x^T for 0 < x ≤ 1. -/
lemma bridge_weight_le_pow_T {T : ℕ} (b : PaperBridge T)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    x ^ b.walk.1.length ≤ x ^ T :=
  pow_le_pow_of_le_one hx.le hx1 (paper_bridge_length_ge T b)

end
