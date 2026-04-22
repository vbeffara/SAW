/-
# Strip identity for T = 1 (explicit computation)

For the infinite strip of width T = 1, we can compute the bridge
partition function and A_inf exactly, verifying the identity
  1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc
by algebraic manipulation.

The strip S_1 has:
- TRUE vertices at diagCoord 0: TRUE(x, -x) for all x ∈ ℤ
- FALSE vertices at diagCoord -1: FALSE(x, -x-1) for all x ∈ ℤ

The strip graph is a doubly-infinite path:
  ... - TRUE(-1,1) - FALSE(-1,0) - TRUE(0,0) - FALSE(0,-1) - TRUE(1,-1) - ...

PaperBridges of width 1:
- Going right: paperStart → FALSE(0,-1) → TRUE(1,-1) → FALSE(1,-2) → ...
  Length 2k+1 for k = 0, 1, 2, ...
- Going left: paperStart → FALSE(-1,0) → TRUE(-1,1) → FALSE(-2,1) → ...
  Length 2k+1 for k = 0, 1, 2, ...

So paper_bridge_partition 1 xc = 2 * ∑_{k≥0} xc^{2k+1} = 2xc/(1-xc²).

Similarly, A_inf 1 xc = 2 * ∑_{k≥0} xc^{2k+3} = 2xc³/(1-xc²).

The identity becomes:
  1 = c_alpha * 2xc³/(1-xc²) + xc * 2xc/(1-xc²)
    = 2xc/(1-xc²) * (c_alpha * xc² + xc)
    = 2xc²/(1-xc²) * (c_alpha * xc + 1)

Using c_alpha = cos(3π/8) = sin(π/8) and xc = 1/(2cos(π/8)):
  c_alpha * xc = sin(π/8)/(2cos(π/8)) = tan(π/8)/2 = (√2-1)/2
  c_alpha * xc + 1 = (√2+1)/2
  2xc² * (√2+1)/2 = xc² * (√2+1) = (√2+1)/(2+√2) = 1/√2 = √2/2
  1 - xc² = (1+√2)/(2+√2) = 1/√2 = √2/2 ✓
-/

import Mathlib
import RequestProject.SAWCuttingProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Key algebraic identities for xc and c_alpha -/

/-
c_alpha * xc = (√2 - 1) / 2, which equals tan(π/8)/2.
-/
lemma c_alpha_mul_xc : c_alpha * xc = (Real.sqrt 2 - 1) / 2 := by
  unfold c_alpha xc;
  rw [ show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_pi_div_two_sub ] ; norm_num;
  field_simp;
  rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg ( 2 + Real.sqrt 2 ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ 2 + Real.sqrt 2 by positivity ) ]

/-
2 * xc² * (c_alpha * xc + 1) = 1 - xc².
-/
lemma strip_T1_algebraic : 2 * xc ^ 2 * (c_alpha * xc + 1) = 1 - xc ^ 2 := by
  unfold c_alpha;
  rw [ show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_pi_div_two_sub ] ; ring ; norm_num [ mul_div ] ; ring;
  unfold xc;
  field_simp;
  rw [ show ( 2 - Real.sqrt 2 ) = ( 2 + Real.sqrt 2 ) ⁻¹ * 2 by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.sqrt_nonneg 2, inv_mul_cancel₀ ( show ( 2 + Real.sqrt 2 ) ≠ 0 by positivity ) ], Real.sqrt_mul ( by positivity ), Real.sqrt_inv ] ; ring;
  grind

/-- The strip identity for T = 1 in algebraic form:
    If paper_bridge_partition 1 xc = 2xc/(1-xc²) and
    A_inf 1 xc = 2xc³/(1-xc²), then
    1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc. -/
lemma strip_identity_T1_from_formulas
    (hB : paper_bridge_partition 1 xc = 2 * xc / (1 - xc ^ 2))
    (hA : A_inf 1 xc = 2 * xc ^ 3 / (1 - xc ^ 2)) :
    1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc := by
  rw [hA, hB]
  have h1xc : 1 - xc ^ 2 ≠ 0 := by
    have hlt : xc < 1 := xc_lt_one'
    have hpos : 0 < xc := xc_pos
    have : xc ^ 2 < 1 := by nlinarith
    linarith
  field_simp
  have := strip_T1_algebraic
  nlinarith

end