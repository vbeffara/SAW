/-
# Hammersley-Welsh Bridge Decomposition: Integration

This file connects hw_bridge_decomp_core (from SAWHWBridgeDecomp.lean)
to paper_bridge_decomp_injection (in SAWPaperChain.lean).

Once hw_bridge_decomp_core is proved, uncomment the import and proof below
to close the sorry in paper_bridge_decomp_injection.
-/

-- import RequestProject.SAWHWBridgeDecomp
-- import RequestProject.SAWPaperChain

-- Once hw_bridge_decomp_core is proved:
-- theorem paper_bridge_decomp_injection_from_hw {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
--     ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
--     2 * (∑ S ∈ (Finset.range N).powerset,
--       ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 :=
--   hw_bridge_decomp_core hx hxc N
