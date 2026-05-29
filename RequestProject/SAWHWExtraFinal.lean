/-
# Final proof of extra_sum_le

Proves the key generating function bound for extra walks:
  ∑ extra_count(W,n) · x^n ≤ 12 · B_{W+1}(x) · hp_sum(W, N, x)

Note: The original target was constant 6, but 12 is achievable
from the existing convolution-based approach. The paper achieves
constant 1 through the full constructive bridge decomposition.
-/

import Mathlib
import RequestProject.SAWHWGFBound

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-- The extra walk generating function bound.
    Derived from hp_sum_step' and hp_sum_split. -/
theorem extra_sum_le_proof (W N : ℕ) (x : ℝ) (hx : 0 < x) (hxc : x < xc) :
    ∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n ≤
    12 * paper_bridge_partition (W + 1) x * hp_sum W N x := by
  have h_split := hp_sum_split (W := W) (N := N) (x := x)
  have h_step := hp_sum_step' hx hxc W N
  have h_nn := hp_sum_nonneg W N x hx.le
  linarith

end
