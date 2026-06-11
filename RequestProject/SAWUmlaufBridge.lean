/-
# Bridge between hex turning angles and the signed-area cross product

This file connects the *local* turning data of a honeycomb trail
(`hex_turn_value`: every turn is `±π/3`) with the *signed-area* cross product
`HexArea.cross` developed in `RequestProject.SAWSignedArea`.

The single result `hex_turn_cross` shows that at every (non-backtracking) turn of
a hex trail the cross product of the incoming and outgoing edge vectors is
`±√3/2`, with the **sign equal to the sign of the turn**: a left turn
(`arg = +π/3`) gives `+√3/2`, a right turn (`arg = -π/3`) gives `-√3/2`.

This is the local half of the signed-area route to the discrete Umlaufsatz
`umlaufsatz_pm_one`: it converts the sequence of turning signs into a sequence
of signed triangle areas, which (together with the algebraic `shoelace2_ear`
ear-step and the still-open topological fact that a simple polygon has nonzero
signed area) yields the turning number `±1`.

This file is imported from `RequestProject.SAWFinal`; it is **preparation** for
the Umlaufsatz and is not yet consumed by another declaration.
-/

import Mathlib
import RequestProject.SAWTurningNumber
import RequestProject.SAWSignedArea

open Real Complex ComplexConjugate

noncomputable section

/-- The cross product of two unit complex numbers equals the imaginary part of
    their ratio scaled by the modulus: `cross z w = ‖z‖² · Im (w / z)`.  For
    unit `z` this is just `Im (w / z)`. -/
lemma cross_eq_normSq_mul_im_div (z w : ℂ) (hz : z ≠ 0) :
    HexArea.cross z w = Complex.normSq z * (w / z).im := by
  have hd : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.normSq_pos.mpr hz).ne'
  rw [HexArea.cross, Complex.div_im, Complex.normSq_apply]
  field_simp [hd]

/-
At every non-backtracking turn of a hex trail, the cross product of the
    incoming and outgoing unit edge vectors is `±√3/2`, with sign equal to the
    sign of the turning angle: a left turn (`arg (d₂/d₁) = +π/3`) gives `+√3/2`,
    a right turn (`arg (d₂/d₁) = -π/3`) gives `-√3/2`.
-/
lemma hex_turn_cross (v₀ v₁ v₂ : HexVertex)
    (h₁ : hexGraph.Adj v₀ v₁) (h₂ : hexGraph.Adj v₁ v₂)
    (h_ne : s(v₀, v₁) ≠ s(v₁, v₂)) :
    HexArea.cross (correctHexEmbed v₁ - correctHexEmbed v₀)
                  (correctHexEmbed v₂ - correctHexEmbed v₁) = Real.sqrt 3 / 2 ∨
    HexArea.cross (correctHexEmbed v₁ - correctHexEmbed v₀)
                  (correctHexEmbed v₂ - correctHexEmbed v₁) = -(Real.sqrt 3 / 2) := by
  have hd₁ : correctHexEmbed v₁ - correctHexEmbed v₀ ≠ 0 := hex_embed_sub_ne_zero' v₀ v₁ h₁
  obtain h | h := hex_turn_value v₀ v₁ v₂ h₁ h₂ h_ne
  · rw [cross_eq_normSq_mul_im_div _ _ hd₁,
      ← Complex.norm_mul_exp_arg_mul_I
        ((correctHexEmbed v₂ - correctHexEmbed v₁) / (correctHexEmbed v₁ - correctHexEmbed v₀)), h]
    norm_num [Complex.exp_re, Complex.exp_im, Complex.normSq_eq_norm_sq]
    rw [hex_edge_norm_one' v₀ v₁ h₁, hex_edge_norm_one' v₁ v₂ h₂]; norm_num
  · rw [cross_eq_normSq_mul_im_div _ _ hd₁,
      ← Complex.norm_mul_exp_arg_mul_I
        ((correctHexEmbed v₂ - correctHexEmbed v₁) / (correctHexEmbed v₁ - correctHexEmbed v₀)), h]
    norm_num [Complex.exp_re, Complex.exp_im, Complex.normSq_eq_norm_sq]
    rw [hex_edge_norm_one' v₀ v₁ h₁, hex_edge_norm_one' v₁ v₂ h₂]; norm_num

end