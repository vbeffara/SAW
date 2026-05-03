/-
# Strip identity for T=1, L=1: computational verification

For the smallest non-trivial strip PaperFinStrip 1 1, we verify
B_paper 1 1 xc ≤ 1 by explicit enumeration of walks.

PaperFinStrip 1 1 vertices:
- TRUE: (0,0,true) [paperStart], (1,-1,true)  [x+y=0, 0 ≤ x ≤ 1]
- FALSE: (-1,0,false), (0,-1,false)  [x+y=-1, -1 ≤ x ≤ 0]

PaperSAW_B 1 1 walks (from paperStart to FALSE with x+y=-1):
1. paperStart → (-1,0,false), length 1
2. paperStart → (0,-1,false), length 1

So B_paper(1,1,xc) = 2·xc² = 2/(2+√2) = 2-√2 ≈ 0.586 < 1.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-
3·xc² < 1, equivalently xc² < 1/3. Since xc = 1/√(2+√2) and 2+√2 > 3.
-/
lemma three_xc_sq_lt_one : 3 * xc ^ 2 < 1 := by
  unfold xc;
  rw [ div_pow, Real.sq_sqrt <| by positivity, mul_div, div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

/-- 2·xc² < 1: the key bound for T=1. -/
lemma two_xc_sq_lt_one : 2 * xc ^ 2 < 1 := by
  linarith [three_xc_sq_lt_one]

end