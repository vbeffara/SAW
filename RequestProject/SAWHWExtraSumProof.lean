/-
# Infrastructure for extra_sum_le proof
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary
import RequestProject.SAWHWStructural
import RequestProject.SAWHWBridgeExtractProof
import RequestProject.SAWHWBound
import RequestProject.SAWHWHalfPlane
import RequestProject.SAWHWLastVertex
import RequestProject.SAWHWStepHelpers

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-
Extra walks need length > W since dc can only change by ≤ 1 per step.
-/
lemma extra_count_zero_small (W n : ℕ) (hn : n ≤ W) : extra_count W n = 0 := by
  rw [ extra_count ];
  rw [ Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem ];
  intro s hs
  obtain ⟨hs_bounds, hs_exists⟩ := Finset.mem_filter.mp hs;
  obtain ⟨ v, hv₁, hv₂ ⟩ := hs_exists.2;
  obtain ⟨ k, hk₁, hk₂ ⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv₁;
  have := walk_getVert_dc_ge s.p.1 k hk₂; simp_all +decide ;
  norm_num [ paperStart ] at this ; linarith [ show ( s.p.1.length : ℤ ) = n from mod_cast s.l ]

/-
1 + 2x*(1+x)*hp_sum(W, N, x) ≤ 6 * hp_sum(W, N, x) for 0 < x < 1.
-/
lemma suffix_gf_bound (W N : ℕ) (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    1 + 2 * x * ((1 + x) * hp_sum W N x) ≤ 6 * hp_sum W N x := by
  nlinarith [ mul_pos hx hx, mul_le_mul_of_nonneg_left hx1.le ( show ( 0 : ℝ ) ≤ hp_sum W N x by exact hp_sum_nonneg W N x ( by positivity ) ), hp_sum_ge_one W N x ( by positivity ) ] ;

end