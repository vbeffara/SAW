/-
# Infrastructure toward proving B_paper ≤ 1

Helper lemmas for the parafermionic observable proof
of B_paper(T,L,xc) ≤ 1 (Lemma 2 of Duminil-Copin & Smirnov 2012).
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-- Left boundary exit direction is -1 in ℂ. -/
lemma left_boundary_dir_is_neg_one' (x : ℤ) :
    correctHexEmbed (x, -x, false) - correctHexEmbed (x, -x, true) = -1 := by
  unfold correctHexEmbed
  apply Complex.ext <;> simp <;> push_cast <;> ring

/-- Right boundary exit direction is +1 in ℂ. -/
lemma right_boundary_dir_is_one' (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 := by
  unfold correctHexEmbed
  apply Complex.ext <;> simp <;> push_cast <;> ring

/-- cos(3θ/8) > 0 for hex angles. -/
lemma escape_boundary_phase_nonneg' (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    0 ≤ Real.cos (3 * θ / 8) :=
  le_of_lt (boundary_cos_pos θ hθ)

end
