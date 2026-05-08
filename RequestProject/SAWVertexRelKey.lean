/-
# Key algebraic identities for the vertex relation

This file proves algebraic identities that are essential for the
parafermionic observable and the vertex relation (Lemma 1 of
Duminil-Copin & Smirnov 2012).

## Main results

1. `two_xc_cos_pi_eight_eq_one`: 2·xc·cos(π/8) = 1
   This is the fundamental identity connecting xc to cos(π/8).
   It captures the vertex relation at the starting vertex (triplet).

2. `xc_inv_eq_two_cos_pi_eight`: xc⁻¹ = 2·cos(π/8)
   Equivalent formulation of the above.

3. `starting_vertex_relation`: The triplet cancellation at paperStart:
   -1 + 2·xc·cos(π/8) = 0.
-/

import Mathlib
import RequestProject.SAW

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## The identity 2·xc·cos(π/8) = 1 -/

/-- The fundamental identity: 2·xc·cos(π/8) = 1.
    This connects the critical fugacity xc = 1/√(2+√2) to cos(π/8) = √(2+√2)/2.
    It is the key algebraic content of the starting vertex relation. -/
theorem two_xc_cos_pi_eight_eq_one : 2 * xc * Real.cos (Real.pi / 8) = 1 := by
  unfold xc
  rw [Real.cos_pi_div_eight]
  rw [show 2 * (1 / Real.sqrt (2 + Real.sqrt 2)) * (Real.sqrt (2 + Real.sqrt 2) / 2) =
      (Real.sqrt (2 + Real.sqrt 2) / Real.sqrt (2 + Real.sqrt 2)) from by ring]
  rw [div_self (Real.sqrt_ne_zero'.mpr two_add_sqrt_two_pos)]

/-- Equivalent: xc⁻¹ = 2·cos(π/8). -/
theorem xc_inv_eq_two_cos_pi_eight : xc⁻¹ = 2 * Real.cos (Real.pi / 8) := by
  have h := two_xc_cos_pi_eight_eq_one
  have hxc : xc ≠ 0 := ne_of_gt xc_pos
  rw [eq_comm, inv_eq_of_mul_eq_one_left]
  linarith

/-- The starting vertex triplet relation: -1 + 2·xc·cos(π/8) = 0. -/
theorem starting_vertex_relation : -1 + 2 * xc * Real.cos (Real.pi / 8) = 0 := by
  linarith [two_xc_cos_pi_eight_eq_one]

/-- cos(3π/8) = sin(π/8) = √(2-√2)/2. -/
lemma cos_three_pi_eight_eq : Real.cos (3 * Real.pi / 8) = Real.sin (Real.pi / 8) := by
  rw [show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 from by ring]
  exact Real.cos_pi_div_two_sub _

/-- c_alpha = cos(3π/8) > 0. -/
lemma c_alpha_eq_cos : c_alpha = Real.cos (3 * Real.pi / 8) := rfl

/-- c_alpha = sin(π/8). -/
lemma c_alpha_eq_sin : c_alpha = Real.sin (Real.pi / 8) := by
  rw [c_alpha_eq_cos, cos_three_pi_eight_eq]

/-- c_eps = cos(π/4) = √2/2. -/
lemma c_eps_eq_cos : c_eps = Real.cos (Real.pi / 4) := rfl

/-! ## Phase computation for boundary mid-edges

These lemmas compute the phase factors that appear in the
boundary evaluation of the discrete Stokes sum. -/

/-- Right boundary phase: winding = 0, so the phase is 1.
    Right boundary mid-edges connect FALSE at diagCoord -T to TRUE at diagCoord -T.
    The walk from a to a right boundary mid-edge follows horizontal edges,
    accumulating zero net winding. -/
lemma right_boundary_phase : Real.cos (sigma * 0) = 1 := by
  simp [sigma]

/-- Left boundary phase factor: cos(σπ) = cos(5π/8) = -cos(3π/8) = -c_alpha.
    Left boundary mid-edges have winding ±π from the starting mid-edge. -/
lemma left_boundary_phase : Real.cos (sigma * Real.pi) = -c_alpha := by
  unfold sigma c_alpha
  rw [show 5 / 8 * Real.pi = Real.pi - 3 * Real.pi / 8 from by ring]
  exact Real.cos_pi_sub _

/-- The boundary sum structure:
    0 = -1 + (right boundary: coeff 1) · B + (left boundary: coeff c_α) · A + ...
    This is the real part of the discrete Stokes identity. -/
lemma boundary_sum_structure (A B : ℝ) (hA : 0 ≤ A)
    (h : 0 = -1 + B + c_alpha * A) : B ≤ 1 := by
  have := c_alpha_pos
  nlinarith

end
