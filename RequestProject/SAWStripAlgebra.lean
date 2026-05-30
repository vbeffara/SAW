/-
# Algebraic identities for the strip identity

Key algebraic identities used in the proof of the infinite strip identity
(Lemma 2 of Duminil-Copin & Smirnov 2012).

These identities relate xc = 1/√(2+√2) and c_alpha = cos(3π/8)
via the triple angle formula cos(3θ) = 4cos³(θ) - 3cos(θ).

## Main results

* `strip_algebraic_identity` — 2·c_α·xc³ + 3·xc² = 1
* `xc_eq_inv_two_cos` — xc = 1/(2·cos(π/8))
* `c_alpha_eq_cos` — c_α = cos(3π/8)
* `cos_pi_eight_pos` — cos(π/8) > 0
-/

import Mathlib
import RequestProject.SAWStripT1Exact

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Basic identities -/

/-- cos(π/8) is positive. -/
lemma cos_pi_eight_pos : 0 < Real.cos (Real.pi / 8) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- xc = 1/(2·cos(π/8)). -/
lemma xc_eq_inv_two_cos : xc = 1 / (2 * Real.cos (Real.pi / 8)) := by
  unfold xc; rw [sqrt_two_add_sqrt_two_eq]

/-- c_α = cos(3π/8). -/
lemma c_alpha_eq_cos : c_alpha = Real.cos (3 * Real.pi / 8) := by
  unfold c_alpha; ring_nf

/-- The triple angle formula at π/8. -/
lemma cos_triple_pi_eight :
    4 * Real.cos (Real.pi / 8) ^ 3 =
    Real.cos (3 * Real.pi / 8) + 3 * Real.cos (Real.pi / 8) := by
  have h := Real.cos_three_mul (Real.pi / 8)
  rw [show 3 * (Real.pi / 8) = 3 * Real.pi / 8 by ring] at h
  linarith

/-! ## The key algebraic identity -/

/-
**2·c_α·xc³ + 3·xc² = 1** — the algebraic identity underlying the strip identity.

    Proof: Substitute xc = 1/(2cos(π/8)) and c_α = cos(3π/8), then
    apply the triple angle formula cos(3θ) = 4cos³(θ) - 3cos(θ).
-/
theorem strip_algebraic_identity :
    2 * c_alpha * xc ^ 3 + 3 * xc ^ 2 = 1 := by
  unfold c_alpha xc; ring;
  field_simp;
  rw [ show Real.pi * 3 / 8 = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_sub ] ; norm_num ; ring;
  rw [ show ( Real.sqrt ( 2 + Real.sqrt 2 ) ) ^ 3 = ( Real.sqrt ( 2 + Real.sqrt 2 ) ^ 2 ) * Real.sqrt ( 2 + Real.sqrt 2 ) by ring, Real.sq_sqrt <| by positivity ] ; ring_nf;
  rw [ ← sq_eq_sq₀ ] <;> ring <;> norm_num;
  · rw [ ← Real.sqrt_mul <| by nlinarith [ Real.sq_sqrt <| show 0 ≤ 2 by norm_num ] ] ; ring ; norm_num;
    rw [ Real.sq_sqrt, Real.sq_sqrt ] <;> nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ];
  · positivity;
  · positivity

/-
Equivalent form: c_α·xc = (1 - 3·xc²)/(2·xc²).
-/
lemma c_alpha_xc_relation :
    c_alpha * xc = (1 - 3 * xc ^ 2) / (2 * xc ^ 2) := by
  rw [ eq_div_iff ];
  · linarith [ strip_algebraic_identity ];
  · norm_num [ xc_pos.ne' ]

/-
xc² + c_α·xc < 1
-/
lemma xc_sq_plus_ca_xc_lt_one : xc ^ 2 + c_alpha * xc < 1 := by
  rw [ ← strip_algebraic_identity ];
  rw [ show c_alpha = Real.cos ( 3 * Real.pi / 8 ) by exact? ];
  rw [ show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_pi_div_two_sub ] ; norm_num [ xc ] ; ring_nf ; norm_num;
  field_simp;
  rw [ ← Real.sqrt_mul <| by positivity ] ; ring_nf ; norm_num;
  nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg ( 2 + Real.sqrt 2 ), Real.sqrt_nonneg ( 2 - Real.sqrt 2 ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ 2 + Real.sqrt 2 by positivity ), Real.mul_self_sqrt ( show 0 ≤ 2 - Real.sqrt 2 by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ) ] ) ]

/-- The T=1 case of infinite_strip_identity follows from the
    exact computations of A_inf(1) and B(1) plus the algebraic identity. -/
theorem strip_identity_T1_algebraic
    (hA : A_inf 1 xc = 2 * xc ^ 3 / (1 - xc ^ 2))
    (hB : paper_bridge_partition 1 xc = 2 * xc / (1 - xc ^ 2)) :
    1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc := by
  rw [hA, hB]
  have hxc2 : xc ^ 2 < 1 := xc_sq_lt_one
  have hxc_pos := xc_pos
  have hne : (1 - xc ^ 2) ≠ 0 := by linarith
  field_simp
  nlinarith [strip_algebraic_identity]

/-- The T=1 case using the known exact value of B(1). -/
theorem strip_identity_T1_from_A
    (hA : A_inf 1 xc = 2 * xc ^ 3 / (1 - xc ^ 2)) :
    1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc :=
  strip_identity_T1_algebraic hA paper_bridge_partition_1_eq

end