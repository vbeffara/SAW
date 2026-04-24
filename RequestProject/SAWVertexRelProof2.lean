/-
# Vertex relation proof helpers

Additional algebraic identities for the parafermionic observable.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Direction ratios on the hex lattice

The direction vectors from a FALSE vertex to its three TRUE neighbors
are related by multiplication by j = exp(i2π/3) (120° rotation). -/

/-
The direction vector from FALSE(x,y) to TRUE(x+1,y) divided by the
    direction vector from FALSE(x,y) to TRUE(x,y) equals j.
-/
lemma dir_ratio_j (x y : ℤ) :
    (correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false)) =
    j * (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) := by
  unfold correctHexEmbed j; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring;
  norm_num [ ( by ring : Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 ) ] ; ring;

/-
The direction vector from FALSE(x,y) to TRUE(x,y+1) divided by the
    direction vector from FALSE(x,y) to TRUE(x,y) equals j².
-/
lemma dir_ratio_j_sq (x y : ℤ) :
    (correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false)) =
    j ^ 2 * (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) := by
  unfold correctHexEmbed j;
  norm_num [ Complex.ext_iff, sq, Complex.exp_re, Complex.exp_im ];
  norm_num [ mul_div_assoc, Real.cos_two_mul, Real.sin_two_mul ] ; ring ; norm_num

end