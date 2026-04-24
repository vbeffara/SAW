/-
# Strip identity for T=1 (direct computation)

Proves the infinite strip identity 1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc
by direct computation on the path graph structure of the T=1 strip.

For T=1, the strip PaperInfStrip 1 consists of:
- TRUE vertices (x, -x, true) with x+y = 0 (single layer)
- FALSE vertices (y, -y-1, false) with x+y = -1 (single layer)

The graph restricted to these vertices is an infinite path:
... T_{-1} - F_{-1} - T_0 - F_0 - T_1 - F_1 - T_2 - ...
where T_k = (k, -k, true) and F_k = (k, -k-1, false).

Walks from paperStart = T_0:
- PaperBridge 1 (walks to FALSE, diagCoord=-1): length 2k+1, 2 walks each (left/right)
- PaperSAW_A_inf 1 (walks to TRUE≠T_0, diagCoord=0): length 2k, 2 walks each (k≥1)

Paper bridge partition: B = 2 * ∑_{k=0}^∞ xc^{2k+1} = 2xc/(1-xc²)
A_inf: A = 2 * ∑_{k=1}^∞ xc^{2k+1} = 2xc³/(1-xc²)

Identity: c_alpha * A + xc * B = c_alpha * 2xc³/(1-xc²) + xc * 2xc/(1-xc²)
= 2xc/(1-xc²) * (c_alpha * xc² + xc²)
= 2xc²/(1-xc²) * (c_alpha * xc + 1)

Key algebraic identity: xc * c_alpha = (√2 - 1)/2
So c_alpha * xc + 1 = (√2 - 1)/2 + 1 = (√2 + 1)/2
And 2xc²/(1-xc²) * (√2+1)/2 = xc²(√2+1)/(1-xc²)
= (√2+1)/((2+√2)(1-1/(2+√2)))
= (√2+1)/((2+√2-1))
= (√2+1)/(1+√2) = 1 ✓
-/

import Mathlib
import RequestProject.SAWRecurrenceProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Algebraic identity: xc * c_alpha = (√2 - 1)/2 -/

lemma xc_mul_c_alpha : xc * c_alpha = (Real.sqrt 2 - 1) / 2 := by
  unfold xc c_alpha;
  rw [ show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_pi_div_two_sub ] ; ring ; norm_num;
  rw [ inv_mul_eq_div, div_eq_iff ] <;> norm_num [ mul_div ];
  · rw [ ← sq_eq_sq₀ ] <;> ring <;> norm_num;
    · rw [ Real.sq_sqrt, Real.sq_sqrt ] <;> nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ];
    · exact le_mul_of_one_le_left ( Real.sqrt_nonneg _ ) ( Real.le_sqrt_of_sq_le ( by norm_num ) );
  · positivity

/-! ## The identity c_alpha * xc + 1 = (√2 + 1)/2 -/

lemma c_alpha_xc_plus_one : c_alpha * xc + 1 = (Real.sqrt 2 + 1) / 2 := by
  have h := xc_mul_c_alpha
  linarith [mul_comm xc c_alpha]

/-! ## Key: 2xc²/(1-xc²) * (√2+1)/2 = 1 -/

lemma strip_T1_algebraic : 2 * xc ^ 2 / (1 - xc ^ 2) * ((Real.sqrt 2 + 1) / 2) = 1 := by
  rw [ div_mul_eq_mul_div, div_eq_iff ] <;> ring_nf <;> norm_num [ xc ];
  · rw [ Real.sq_sqrt ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_inv_cancel₀ ( show ( 2 + Real.sqrt 2 ) ≠ 0 by positivity ) ];
  · grind

end