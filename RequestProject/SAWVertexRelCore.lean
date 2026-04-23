/-
# Vertex Relation Core — Direction factors at hex vertices

Proves that the direction vectors from a hex vertex to its three
neighbors are {1, j, conj(j)} (up to sign depending on sublattice).

These are needed for the vertex relation (Lemma 1).
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Direction from FALSE to TRUE(x+1,y) = j -/

lemma false_to_plus1_dir (x y : ℤ) :
    correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false) = j := by
  unfold correctHexEmbed;
  unfold j; rw [ Complex.ext_iff ] ; norm_num ; ring;
  norm_num [ Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring

/-! ## Direction from FALSE to TRUE(x,y+1) = conj(j) -/

lemma false_to_yplus1_dir (x y : ℤ) :
    correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false) = starRingEnd ℂ j := by
  unfold correctHexEmbed j; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring;
  rw [ show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; norm_num ; ring;

/-! ## Direction from TRUE to FALSE(x-1,y) = -j -/

lemma true_to_minus1_dir (x y : ℤ) :
    correctHexEmbed (x - 1, y, false) - correctHexEmbed (x, y, true) = -j := by
  unfold correctHexEmbed;
  unfold j; norm_num [ Complex.ext_iff ];
  norm_num [ Complex.exp_re, Complex.exp_im, Real.cos_two_mul, Real.sin_two_mul, mul_div_assoc ] ; ring ; norm_num

/-! ## Direction from TRUE to FALSE(x,y-1) = -conj(j) -/

lemma true_to_yminus1_dir (x y : ℤ) :
    correctHexEmbed (x, y - 1, false) - correctHexEmbed (x, y, true) = -(starRingEnd ℂ j) := by
  unfold correctHexEmbed j; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring;
  rw [ show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; norm_num ; ring;

end