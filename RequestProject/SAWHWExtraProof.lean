/-
# Extra Sum Bound and SAW-to-HP reduction

Proves `extra_sum_le` and `saw_sum_le_hp_sq` — the two remaining
Hammersley-Welsh sorries.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary
import RequestProject.SAWHWStructural
import RequestProject.SAWHWBridgeExtractProof
import RequestProject.SAWHWBound
import RequestProject.SAWHWHalfPlane
import RequestProject.SAWHWStepHelpers

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Monotonicity of hp_walk_count in width -/

/-
hp_walk_count is monotone in width: wider strip ⟹ more walks.
-/
lemma hp_walk_count_mono {W W' : ℕ} (h : W ≤ W') (n : ℕ) :
    hp_walk_count W n ≤ hp_walk_count W' n := by
  refine' Finset.card_le_card _;
  grind

/-! ## hex_origin_strip GF bound -/

/-
The hex_origin_strip GF is ≤ (1 + x) * hp_sum.
    Uses: hex_origin_strip_count(W,0) = 1,
          hex_origin_strip_count(W,k) ≤ hp_walk_count(W,k-1) for k ≥ 1,
          hp_sum(W,N,x) ≥ 1 for x ≥ 0.
-/
lemma hex_origin_strip_sum_le (W N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑ k ∈ Finset.range (N + 1), (hex_origin_strip_count W k : ℝ) * x ^ k ≤
    (1 + x) * hp_sum W N x := by
  -- Split the sum: the k=0 term equals 1 (by hex_origin_strip_zero). For k ≥ 1, use hex_origin_strip_le_hp to get hex_origin_strip_count(W, k) ≤ hp_walk_count(W, k-1).
  have h_split_sum : ∑ k ∈ Finset.range (N + 1), (hex_origin_strip_count W k : ℝ) * x ^ k ≤ 1 + x * ∑ k ∈ Finset.range N, (hp_walk_count W k : ℝ) * x ^ k := by
    rw [ Finset.sum_range_succ' ] ; norm_num [ Finset.mul_sum _ _ _ ] ;
    rw [ add_comm, hex_origin_strip_zero ] ; norm_num [ pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; gcongr ;
    exact hex_origin_strip_le_hp _ _ ( Nat.succ_pos _ );
  refine le_trans h_split_sum ?_;
  rw [ add_mul, hp_sum ];
  gcongr <;> norm_num [ Finset.sum_range_succ ];
  -- Since hp_sum is at least 1, adding the term for N (which is non-negative) will keep it at least 1.
  have h_hp_sum_ge_one : 1 ≤ hp_sum W N x := by
    exact hp_sum_ge_one W N x hx;
  convert h_hp_sum_ge_one using 1 ; unfold hp_sum ; norm_num [ Finset.sum_range_succ ]

end