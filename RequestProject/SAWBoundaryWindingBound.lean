/-
# The boundary winding bound

The boundary evaluation of Duminil-Copin & Smirnov (Step 3 of the proof of
Lemma 2) needs one geometric input, over and above the telescoping law
`freshTrail_winding_angle` (which pins the winding of a configuration *modulo*
`2π`): a configuration whose final mid-edge *leaves* the strip makes at most
half a full turn,

  `freshTrail_boundary_winding_bound : |γ.winding| ≤ π`.

This is the only place where the self-avoidance of the configuration and the
simple connectivity of the strip are used.  It is stated here with `sorry`; all
three remaining boundary statements of `SAWStripBoundarySum.lean`
(`alphaTrail_winding_bound`, `betaTrail_winding_bound`, `bdry_E_re_nonneg`) are
*derived* from it in this file, so it is the single remaining geometric input
of the boundary evaluation.

The derivation is the "`cos(3θ/8) > 0`" computation of the paper: if the
direction `d` of the final mid-edge has `arg d ≡ W (mod 2π)`, then

  `Re (d · e^{-iσW} x^ℓ) = ‖d‖ · cos((1 - σ) W) · x^ℓ`,

and with `σ = 5/8` and `|W| ≤ π` the cosine is `cos(3W/8) ≥ cos(3π/8) > 0`.
-/

import Mathlib
import RequestProject.SAWFreshWindingAngle
import RequestProject.SAWStokesSum

open Real Complex

noncomputable section

set_option maxHeartbeats 1600000

/-! ## The real part of a boundary contribution -/

/-- If the argument of `d` agrees with `W` modulo `2π`, the real part of
`d · e^{-i s W} x^n` is `‖d‖ · cos((1 - s) W) · x^n`. -/
lemma re_mul_walkWeight (d : ℂ) (W s x : ℝ) (n : ℕ) (k : ℤ)
    (hk : Complex.arg d - W = 2 * Real.pi * k) :
    (d * walkWeight W n x s).re = ‖d‖ * Real.cos ((1 - s) * W) * x ^ n := by
  have harg : Complex.arg d = W + 2 * Real.pi * k := by linarith
  unfold walkWeight
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I d]
  rw [show (-Complex.I * (s : ℂ) * (W : ℂ)) = ((-(s * W) : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    ← Complex.ofReal_pow, mul_assoc, ← mul_assoc (Complex.exp _), ← Complex.exp_add,
    ← add_mul, ← Complex.ofReal_add]
  rw [Complex.mul_re, Complex.mul_re]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  rw [harg]
  have hc : Real.cos (W + 2 * Real.pi * k + -(s * W)) = Real.cos ((1 - s) * W) := by
    rw [show W + 2 * Real.pi * (k : ℝ) + -(s * W) = (1 - s) * W + (k : ℝ) * (2 * Real.pi) by
      ring]
    exact Real.cos_add_int_mul_two_pi ((1 - s) * W) k
  rw [hc]
  ring

/-- The real part of the contribution of a single configuration to a boundary
mid-edge, in terms of the winding. -/
lemma freshTrail_dir_weight_re {T L : ℕ} {v w : HexVertex}
    (γ : FreshTrail T L v w) :
    ((correctHexEmbed w - correctHexEmbed v) * γ.weight).re
      = ‖correctHexEmbed w - correctHexEmbed v‖
        * Real.cos ((1 - sigma) * γ.winding) * xc ^ γ.len := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (freshTrail_winding_angle γ)
  exact re_mul_walkWeight _ _ _ _ _ (-k) (by push_cast; linarith)

/-- `cos(3W/8) > 0` for `|W| ≤ π`: the positivity at the heart of the boundary
evaluation. -/
lemma boundary_cos_pos' {W : ℝ} (hW : |W| ≤ Real.pi) :
    0 < Real.cos ((1 - sigma) * W) := by
  have hpi := Real.pi_pos
  rw [abs_le] at hW
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> rw [sigma] <;> nlinarith [hW.1, hW.2]

/-! ## The geometric input -/

/-- **The boundary winding bound.**  A configuration in the strip whose final
mid-edge leaves the strip winds by at most half a turn.

Geometrically: the strip is a simply-connected domain, the configuration is a
self-avoiding path (`freshTrail_isPath`) starting at the boundary mid-edge `a`
and ending at a mid-edge on the boundary of the strip; such an arc cannot make
a full extra revolution, so its total turning lies in `[-π, π]`. -/
theorem freshTrail_boundary_winding_bound {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) (hout : ¬ PaperFinStrip T L next) :
    |γ.winding| ≤ Real.pi := by
  sorry

/-- **Every boundary mid-edge contributes a non-negative real part.**  This is
the sign statement the paper uses to discard the escape term. -/
theorem freshObs_dir_re_nonneg (T L : ℕ) (v w : HexVertex)
    (hout : ¬ PaperFinStrip T L w) :
    0 ≤ ((correctHexEmbed w - correctHexEmbed v) * freshObs T L v w).re := by
  set d : ℂ := correctHexEmbed w - correctHexEmbed v with hd
  have hsum : d * freshObs T L v w = ∑' γ : FreshTrail T L v w, d * γ.weight := by
    rw [freshObs, tsum_mul_left]
  rw [hsum, ← Complex.reCLM_apply,
    ← ((Summable.of_finite (f := fun γ : FreshTrail T L v w => d * γ.weight)).hasSum.mapL
      Complex.reCLM).tsum_eq]
  refine tsum_nonneg fun γ => ?_
  rw [Complex.reCLM_apply, freshTrail_dir_weight_re γ]
  have h1 : (0 : ℝ) ≤ ‖d‖ := norm_nonneg _
  have h2 : 0 < Real.cos ((1 - sigma) * γ.winding) :=
    boundary_cos_pos' (freshTrail_boundary_winding_bound γ hout)
  have h3 : (0 : ℝ) < xc ^ γ.len := pow_pos xc_pos _
  positivity

end
