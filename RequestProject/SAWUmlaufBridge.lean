/-
# Bridge between hex turning angles and the signed-area cross product

This file connects the *local* turning data of a honeycomb trail
(`hex_turn_value`: every turn is `±π/3`) with the *signed-area* cross product
`HexArea.cross` developed in `RequestProject.SAWSignedArea`.

The results here form the *local* half of the signed-area route to the discrete
Umlaufsatz `umlaufsatz_pm_one`:

* `hex_turn_cross` shows that at every (non-backtracking) turn of a hex trail the
  cross product of the incoming and outgoing edge vectors is `±√3/2`, with the
  **sign equal to the sign of the turn**: a left turn (`arg = +π/3`) gives
  `+√3/2`, a right turn (`arg = -π/3`) gives `-√3/2`.
* `hex_turn_cross_ne_zero` records the non-degeneracy consequence: every turn
  has nonzero cross product (no three consecutive polygon vertices are
  collinear), which the signed-area argument needs.
* `hexTurnSign_eq_cross_sign` is the **linchpin**: the combinatorial turn sign
  `hexTurnSign` (used to define `hexSignedTurnCount`) equals the sign of the
  geometric cross product `HexArea.cross` of the two edge vectors.  This is the
  exact bridge that converts the integer signed-turn count into the sign of the
  shoelace signed area `HexArea.shoelace2`.

Together with the algebraic `shoelace2_ear` ear-step and the still-open
topological fact that a simple polygon has nonzero signed area, this yields the
turning number `±1`.

This file is imported from `RequestProject.SAWFinal`; it is **preparation** for
the Umlaufsatz (`hex_total_signed_turn_pm_six` / `umlaufsatz_pm_one` in
`RequestProject.SAWTurningNumber`) and is not yet consumed by another
declaration.
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

/-- At every non-backtracking hex turn the cross product of the incoming and
    outgoing edge vectors is nonzero (it is `±√3/2`).  This is the
    non-degeneracy fact (no three consecutive polygon vertices are collinear)
    needed by the signed-area route to the Umlaufsatz. -/
lemma hex_turn_cross_ne_zero (v₀ v₁ v₂ : HexVertex)
    (h₁ : hexGraph.Adj v₀ v₁) (h₂ : hexGraph.Adj v₁ v₂)
    (h_ne : s(v₀, v₁) ≠ s(v₁, v₂)) :
    HexArea.cross (correctHexEmbed v₁ - correctHexEmbed v₀)
                  (correctHexEmbed v₂ - correctHexEmbed v₁) ≠ 0 := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := by
    have : (0 : ℝ) < (3 : ℝ) := by norm_num
    exact Real.sqrt_pos.mpr this
  rcases hex_turn_cross v₀ v₁ v₂ h₁ h₂ h_ne with h | h <;> rw [h] <;>
    · intro hc; nlinarith

/-- **Linchpin of the signed-area route.**  The combinatorial turn sign
    `hexTurnSign` equals the sign of the geometric cross product of the two
    edge vectors.  This is exactly the bridge that turns the integer signed-turn
    count `hexSignedTurnCount` into the sign of the shoelace signed area
    `HexArea.shoelace2`, linking the combinatorial and geometric pictures.
    Only adjacency of the *first* edge is needed (it guarantees the denominator
    edge is nonzero). -/
lemma hexTurnSign_eq_cross_sign (v₀ v₁ v₂ : HexVertex)
    (h₁ : hexGraph.Adj v₀ v₁) :
    (hexTurnSign v₀ v₁ v₂ : ℤ) =
      (if 0 < HexArea.cross (correctHexEmbed v₁ - correctHexEmbed v₀)
                            (correctHexEmbed v₂ - correctHexEmbed v₁) then 1 else -1) := by
  set e₁ : ℂ := correctHexEmbed v₁ - correctHexEmbed v₀ with he₁
  set e₂ : ℂ := correctHexEmbed v₂ - correctHexEmbed v₁ with he₂
  have hd : e₁ ≠ 0 := hex_embed_sub_ne_zero' v₀ v₁ h₁
  have hcr : HexArea.cross e₁ e₂ = Complex.normSq e₁ * (e₂ / e₁).im :=
    cross_eq_normSq_mul_im_div e₁ e₂ hd
  have hpos : 0 < Complex.normSq e₁ := Complex.normSq_pos.mpr hd
  have hiff : 0 < HexArea.cross e₁ e₂ ↔ 0 < (e₂ / e₁).im := by
    rw [hcr]; exact mul_pos_iff_of_pos_left hpos
  unfold hexTurnSign
  by_cases hsign : 0 < (e₂ / e₁).im
  · rw [if_pos hsign, if_pos (hiff.mpr hsign)]
  · rw [if_neg hsign, if_neg (fun h => hsign (hiff.mp h))]

end