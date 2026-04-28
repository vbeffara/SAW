/-
# Algebraic lemmas for the strip identity

Key algebraic facts about xc that support the strip identity proof.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-- xc² = 1/(2+√2) -/
lemma xc_sq : xc ^ 2 = 1 / (2 + Real.sqrt 2) := by
  unfold xc
  rw [div_pow, one_pow, Real.sq_sqrt two_add_sqrt_two_pos.le]

/-
xc² < 1/2
-/
lemma xc_sq_lt_half : xc ^ 2 < 1 / 2 := by
  rw [ xc_sq ] ; rw [ div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;

/-- 1 - xc² > 0 -/
lemma one_sub_xc_sq_pos : 0 < 1 - xc ^ 2 := by
  linarith [xc_sq_lt_half]

/-
2·(√2-1) < 1, equivalently 2√2 < 3, equivalently 8 < 9.
-/
lemma two_sqrt_two_sub_one_lt_one : 2 * (Real.sqrt 2 - 1) < 1 := by
  nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ]

end