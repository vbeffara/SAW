/-
# Hammersley-Welsh Bridge Decomposition: Final Proof

The key inequality for the upper bound μ ≤ √(2+√2).
Uses the half-plane walk machinery from SAWHWHalfPlane.lean.

The constant 8 (vs 2 in the paper) comes from the vertex formulation.
The downstream proof only needs finiteness, so the constant doesn't matter.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary
import RequestProject.SAWHWBound
import RequestProject.SAWHWHalfPlane

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-- The Hammersley-Welsh bridge decomposition inequality.
    For 0 < x < 1:
    ∑_{n≤N} c_n x^n ≤ 8 · (∏_{T=1}^N (1 + B_T(x)))² -/
theorem hw_injection_bound {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    8 * (∏ T ∈ Finset.range N, (1 + paper_bridge_partition (T + 1) x)) ^ 2 :=
  hw_injection_bound_correct hx hx1 N

/-- Powerset form of the bridge decomposition bound. -/
theorem hw_bridge_decomp_proved {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    8 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  have h1 : x < 1 := lt_trans hxc xc_lt_one
  have h2 := hw_injection_bound hx h1 N
  simp only [Finset.prod_one_add] at h2
  exact h2

end
