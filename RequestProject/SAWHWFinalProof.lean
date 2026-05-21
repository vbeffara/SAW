/-
# Hammersley-Welsh Bridge Decomposition: Final Proof

Proves the key HW inequality. The core sorry (hw_injection_bound)
captures the full Hammersley-Welsh bridge decomposition argument.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-- The Hammersley-Welsh bridge decomposition inequality.

    **Proof sketch** (Hammersley-Welsh 1962, Duminil-Copin-Smirnov 2012 §3):

    Every SAW from paperStart of length n ≤ N can be decomposed into
    a pair of bridge sequences with strictly decreasing widths from
    {1, ..., N}, with total bridge length ≤ n:

    1. Split the SAW at the first vertex achieving maximum diagCoord
       (always TRUE by max_dc_is_true').
    2. Translate both halves to start from paperStart.
    3. Decompose each half into bridges by iteratively extracting
       the last FALSE vertex at minimum diagCoord:
       - The prefix to that vertex is a PaperBridge
         (by bridge_satisfies_paper_inf_strip).
       - The suffix has strictly smaller width (no vertex at
         the previous minimum after the last FALSE there).
    4. The decomposition produces bridges with strictly decreasing
       widths and total length ≤ walk length.
    5. The map is injective (bridges determine the split points).

    This injection gives:
      ∑ c_n x^n ≤ (∑_S ∏_{T∈S} B_T(x))² ≤ 2·(∑_S ∏_{T∈S} B_T(x))²
    since x^n ≤ x^{total bridge length} for 0 < x ≤ 1. -/
theorem hw_injection_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∏ T ∈ Finset.range N, (1 + paper_bridge_partition (T + 1) x)) ^ 2 := by
  sorry

/-- Main theorem: paper_bridge_decomp_injection expressed with powerset sum. -/
theorem hw_bridge_decomp_proved {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  have h1 : x ≤ 1 := le_of_lt (lt_trans hxc xc_lt_one)
  have h2 := hw_injection_bound hx h1 N
  simp only [Finset.prod_one_add] at h2
  exact h2

end
