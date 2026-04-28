/-
# Direction factor lemmas for the vertex relation

The vertex relation at vertex v uses the direction factors (w-v)
from v to its three neighbors. These are related by multiplication by j = exp(2iπ/3).
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect
import RequestProject.SAWObservableProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Direction factors from FALSE vertices

For FALSE(x,y), the three neighbors are TRUE(x,y), TRUE(x+1,y), TRUE(x,y+1).
The direction vectors are:
  d₁ = embed(TRUE(x,y)) - embed(FALSE(x,y)) = 1  (horizontal right)
  d₂ = embed(TRUE(x+1,y)) - embed(FALSE(x,y)) = (-1/2, √3/2)
  d₃ = embed(TRUE(x,y+1)) - embed(FALSE(x,y)) = (-1/2, -√3/2)

These satisfy d₂ = j·d₁ and d₃ = conj(j)·d₁ where j = exp(2iπ/3). -/

/-- Direction from FALSE to same-cell TRUE is 1. -/
lemma dir_false_true_same (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 :=
  false_to_true_dir x y

/-- The three directions from FALSE(x,y) sum to zero. -/
lemma false_dir_sum (x y : ℤ) :
    (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) +
    (correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false)) +
    (correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false)) = 0 :=
  false_vertex_dir_sum x y

/-- The three directions from TRUE(x,y) sum to zero. -/
lemma true_dir_sum (x y : ℤ) :
    (correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)) +
    (correctHexEmbed (x - 1, y, false) - correctHexEmbed (x, y, true)) +
    (correctHexEmbed (x, y - 1, false) - correctHexEmbed (x, y, true)) = 0 :=
  true_vertex_dir_sum x y

/-! ## Second direction is j times the first -/

/-
For FALSE vertex: d₂ = j · d₁ where d₁ = F→T(same), d₂ = F→T(x+1).
-/
lemma false_dir2_eq_j_dir1 (x y : ℤ) :
    correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false) =
    j * (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) := by
      unfold correctHexEmbed j; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring;
      norm_num [ ( by ring : Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 ) ];
      grobner

/-
For FALSE vertex: d₃ = conj(j) · d₁ where d₁ = F→T(same), d₃ = F→T(y+1).
-/
lemma false_dir3_eq_conjj_dir1 (x y : ℤ) :
    correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false) =
    conj j * (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) := by
      unfold j correctHexEmbed;
      norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring ] ; ring;
      norm_num

/-
For TRUE vertex: d₂ = j · d₁ where d₁ = T→F(same), d₂ = T→F(x-1).
-/
lemma true_dir2_eq_j_dir1 (x y : ℤ) :
    correctHexEmbed (x - 1, y, false) - correctHexEmbed (x, y, true) =
    j * (correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)) := by
      unfold correctHexEmbed j; ring; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring;
      rw [ show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub ] ; norm_num ; ring

/-
For TRUE vertex: d₃ = conj(j) · d₁ where d₁ = T→F(same), d₃ = T→F(y-1).
-/
lemma true_dir3_eq_conjj_dir1 (x y : ℤ) :
    correctHexEmbed (x, y - 1, false) - correctHexEmbed (x, y, true) =
    conj j * (correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)) := by
      unfold correctHexEmbed j;
      norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring ];
      constructor <;> ring

end