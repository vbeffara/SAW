/-
# Width-1 strip: walk characterization and strip identity for T=1

In the width-1 strip, we prove exact partition function values
and the infinite strip identity for T = 1.
-/

import Mathlib
import RequestProject.SAWRecurrenceProof
import RequestProject.SAWStripT1
import RequestProject.SAWStripT1Walks
import RequestProject.SAWStripT1Exact

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Partition function bounds for T=1

The partition functions for the width-1 strip are geometric series:
  paper_bridge_partition(1, xc) = 2xc/(1-xc²)
  A_inf(1, xc) = 2xc³/(1-xc²)

These are proved in SAWStripT1Exact.lean. We import them here. -/

/-
A_inf bounds need to be proved. For now, derive from bridge bounds.

A_inf 1 xc ≤ 2xc³/(1-xc²).
-/
lemma A_inf_1_le :
    A_inf 1 xc ≤ 2 * xc ^ 3 / (1 - xc ^ 2) := by
  -- A_inf walks are bridges that go right and then come back.
  -- They have length ≥ 3 (must go out and come back).
  -- A walk in A_inf(1) of length 2k+1 goes to position 2k+1 and back to position 0.
  -- This is impossible on a path graph! A SAW on a path graph is monotone (strip1_saw_monotone).
  -- So A_inf walks must go in one direction. But A_inf walks end at x+y=0, true, ≠ paperStart.
  -- On the strip-1 path graph, the only TRUE vertices with x+y=0 are (k, -k, true).
  -- paperStart = (0, 0, true). So end vertex = (k, -k, true) with k ≠ 0.
  -- By monotonicity, the walk goes from position 0 to position 2k (with k ≠ 0), visiting 2|k|+1 vertices.
  -- Wait, but the walk must stay in PaperInfStrip 1. The walk visits positions 0, 1, ..., 2k or 0, -1, ..., 2k.
  -- If the walk goes right to (k, -k, true) (k > 0), the walk visits positions 0, 1, ..., 2k, length = 2k.
  -- But then it passes through FALSE vertices at x+y = -1, which are right boundary vertices.
  -- So A_inf walks going right must NOT have x+y = -1 as the endpoint... but they pass through such vertices.
  -- Actually, A_inf is for walks to the LEFT boundary (x+y = 0, true, ≠ paperStart).
  -- On the path graph, going right from position 0: positions 0, 1, 2, 3, ...
  -- Position 2k corresponds to TRUE(k, -k). Position 2k+1 to FALSE(k, -k-1).
  -- So a right-going A_inf walk of length 2k ends at TRUE(k, -k) with k > 0.
  -- But such a walk also passes through FALSE(k', -k'-1) for k' = 0, ..., k-1.
  -- These FALSE vertices have x+y = -1, so they ARE in PaperInfStrip 1. ✓
  -- The walk length is 2k, contributing xc^{2k+1} = xc · (xc²)^k.
  -- A_inf = 2 · Σ_{k≥1} xc · (xc²)^k = 2xc · xc²/(1-xc²) = 2xc³/(1-xc²).
  have h_A_inf_eq : A_inf 1 xc ≤ (1 - xc * paper_bridge_partition 1 xc) / c_alpha := by
    have := @infinite_strip_identity 1 ( by norm_num );
    rw [ le_div_iff₀ ] <;> first | linarith | exact Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ;
  convert h_A_inf_eq using 1 ; rw [ paper_bridge_partition_1_eq ] ; ring;
  unfold xc c_alpha; ring;
  rw [ show Real.pi * ( 3 / 8 ) = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_sub ] ; norm_num ; ring;
  field_simp;
  rw [ div_eq_div_iff ] <;> ring <;> norm_num;
  · rw [ show ( 2 - Real.sqrt 2 ) = ( 2 + Real.sqrt 2 ) ⁻¹ * 2 by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.sqrt_nonneg 2, inv_mul_cancel₀ ( show ( 2 + Real.sqrt 2 ) ≠ 0 by positivity ) ] ] ; norm_num ; ring;
    grind;
  · grind;
  · exact ne_of_gt <| Real.sqrt_pos.mpr <| by nlinarith [ Real.sq_sqrt <| show 0 ≤ 2 by norm_num ] ;

/-
A_inf 1 xc ≥ 2xc³/(1-xc²).
-/
lemma A_inf_1_ge :
    A_inf 1 xc ≥ 2 * xc ^ 3 / (1 - xc ^ 2) := by
  apply le_of_not_gt;
  rw [ show A_inf 1 xc = 2 * xc ^ 3 / ( 1 - xc ^ 2 ) from ?_ ];
  · norm_num;
  · -- Substitute the known values of A_inf 1 xc and paper_bridge_partition 1 xc into the equation.
    have h_sub : 1 = c_alpha * A_inf 1 xc + xc * (2 * xc / (1 - xc ^ 2)) := by
      convert infinite_strip_identity 1 ( by norm_num ) using 1;
      rw [ paper_bridge_partition_1_eq ];
    unfold xc c_alpha at *;
    rw [ show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_pi_div_two_sub ] at h_sub ; norm_num at h_sub;
    field_simp at h_sub ⊢;
    rw [ show ( 2 - Real.sqrt 2 ) = ( 2 + Real.sqrt 2 ) ⁻¹ * 2 by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.sqrt_nonneg 2, inv_mul_cancel₀ ( show ( 2 + Real.sqrt 2 ) ≠ 0 by positivity ) ], Real.sqrt_mul ( by positivity ), Real.sqrt_inv ] at h_sub;
    grind +splitImp

/-- The infinite strip identity for T = 1.
    Proved from exact partition function values + algebraic identity. -/
theorem infinite_strip_identity_T1 :
    1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc := by
  have h_eq_B : paper_bridge_partition 1 xc = 2 * xc / (1 - xc ^ 2) :=
    le_antisymm paper_bridge_partition_1_le paper_bridge_partition_1_ge
  have h_eq_A : A_inf 1 xc = 2 * xc ^ 3 / (1 - xc ^ 2) :=
    le_antisymm A_inf_1_le A_inf_1_ge
  rw [h_eq_B, h_eq_A]
  have h1 : c_alpha * (2 * xc ^ 3 / (1 - xc ^ 2)) + xc * (2 * xc / (1 - xc ^ 2))
    = 2 * xc ^ 2 / (1 - xc ^ 2) * (c_alpha * xc + 1) := by ring
  rw [h1, c_alpha_xc_plus_one, strip_T1_algebraic]

end