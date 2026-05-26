/-
# Hammersley-Welsh Bridge Decomposition: Final Proof
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary
import RequestProject.SAWHWBound
import RequestProject.SAWHWSawBound

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-- The Hammersley-Welsh bridge decomposition inequality.
    For 0 < x < xc (hence x < 1):
    ∑_{n≤N} c_n x^n ≤ 8 · (∏_{T=1}^N (1 + 6·B_T(x)))² -/
theorem hw_injection_bound {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    8 * (∏ T ∈ Finset.range N, (1 + 6 * paper_bridge_partition (T + 1) x)) ^ 2 :=
  hw_injection_bound_correct hx (lt_trans hxc xc_lt_one) N

end
