/-
# Infrastructure toward proving the strip identity

Helper lemmas for the parafermionic observable proof
of B_paper(T,L,xc) ≤ 1 (Lemma 2 of Duminil-Copin & Smirnov 2012).

These compute the boundary exit directions in ℂ for each boundary type
of the strip domain PaperFinStrip T L.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-- Left boundary exit direction is -1 in ℂ.
    A left boundary mid-edge connects TRUE(x,-x) (inside) to FALSE(x,-x) (outside).
    The direction from TRUE to FALSE is -1 (going left). -/
lemma left_boundary_dir_is_neg_one' (x : ℤ) :
    correctHexEmbed (x, -x, false) - correctHexEmbed (x, -x, true) = -1 := by
  unfold correctHexEmbed; apply Complex.ext <;> simp

/-- Right boundary exit direction is +1 in ℂ.
    A right boundary mid-edge connects FALSE(x,y) (inside, x+y=-T) to
    TRUE(x,y) (outside). The direction from FALSE to TRUE is +1. -/
lemma right_boundary_dir_is_one' (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 := by
  unfold correctHexEmbed; apply Complex.ext <;> simp

/-- cos(3θ/8) > 0 for hex angles (already proved as boundary_cos_pos). -/
lemma escape_boundary_phase_nonneg' (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    0 ≤ Real.cos (3 * θ / 8) :=
  le_of_lt (boundary_cos_pos θ hθ)

end
