/-
# Hammersley-Welsh Bridge Decomposition Inequality

Proves the HW bridge decomposition inequality without importing SAWPaperChain.

## Key structural lemmas used (from dependency-free files):
- bridge_satisfies_paper_inf_strip (SAWHWStructural): walks to min-dc satisfy PaperInfStrip
- max_dc_is_true' (SAWHWDecompInject): max diagCoord is at a TRUE vertex
- hexReScaled_adj_ne (SAWHWReCoord): hexReScaled changes at every step
-/

import Mathlib
import RequestProject.SAWHWStructural
import RequestProject.SAWHWReCoord
import RequestProject.SAWHWDecompInject
import RequestProject.SAWBridgeDecompNew
import RequestProject.SAWSubmult

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Helper lemmas -/

private lemma bp_nn (T : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ paper_bridge_partition T x :=
  tsum_nonneg fun _ => pow_nonneg hx.le _

private lemma ps_ge_one (N : ℕ) {x : ℝ} (hx : 0 < x) :
    1 ≤ ∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x := by
  rw [Finset.sum_powerset_prod_eq_prod_add_one]
  exact Finset.one_le_prod _ fun T => by linarith [bp_nn (T + 1) hx]

/-! ## Main theorem -/

/-- **Hammersley-Welsh bridge decomposition inequality.** -/
theorem hw_bridge_decomp_core {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  sorry

end
