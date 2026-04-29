/-
# Core proof infrastructure for the strip identity

Direction rotation lemmas, direction sum identities, and geometric
forms of pair/triplet cancellation for the vertex relation (Lemma 1).
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect
import RequestProject.SAWVertexCore
import RequestProject.SAWVertexPartition

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Direction rotation around hex vertices -/

lemma hex_direction_false_01 (x y : ℤ) :
    correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false) =
    conj j * (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) := by
  unfold correctHexEmbed j
  norm_num [Complex.ext_iff, Complex.exp_re, Complex.exp_im,
    show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]; ring; norm_num

lemma hex_direction_false_02 (x y : ℤ) :
    correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false) =
    j * (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) := by
  unfold correctHexEmbed j; ring
  norm_num [Complex.ext_iff, Complex.exp_re, Complex.exp_im,
    show Real.pi * (2 / 3) = Real.pi - Real.pi / 3 by ring]; ring; norm_num

lemma hex_direction_true_01 (x y : ℤ) :
    correctHexEmbed (x - 1, y, false) - correctHexEmbed (x, y, true) =
    j * (correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)) := by
  unfold j correctHexEmbed
  norm_num [Complex.ext_iff, Complex.exp_re, Complex.exp_im,
    Real.sin_two_mul, Real.cos_two_mul, mul_div_assoc]; ring; norm_num

lemma hex_direction_true_02 (x y : ℤ) :
    correctHexEmbed (x, y - 1, false) - correctHexEmbed (x, y, true) =
    conj j * (correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)) := by
  unfold correctHexEmbed j
  norm_num [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]; norm_num; ring; norm_num

/-! ## Three-direction sum identities -/

lemma hex_direction_sum_false (x y : ℤ) :
    (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) +
    (correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false)) +
    (correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false)) = 0 := by
  unfold correctHexEmbed; norm_num [Complex.ext_iff]; ring; norm_num

lemma hex_direction_sum_true (x y : ℤ) :
    (correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)) +
    (correctHexEmbed (x - 1, y, false) - correctHexEmbed (x, y, true)) +
    (correctHexEmbed (x, y - 1, false) - correctHexEmbed (x, y, true)) = 0 := by
  convert true_vertex_dir_sum x y using 1

/-! ## Triplet cancellation in geometric form -/

lemma triplet_cancel_geometric_dir (d₀ : ℂ) :
    d₀ + (xc : ℂ) * conj lam * (j * d₀) + (xc : ℂ) * lam * (conj j * d₀) = 0 := by
  have h := triplet_cancellation; linear_combination h * d₀

/-! ## Pair cancellation in geometric form -/

lemma pair_cancel_geometric_dir (d₀ : ℂ) :
    conj lam ^ 4 * (j * d₀) + lam ^ 4 * (conj j * d₀) = 0 := by
  have h_pair_cancellation : j * (starRingEnd ℂ) lam ^ 4 + starRingEnd ℂ j * lam ^ 4 = 0 := by
    exact pair_cancellation;
  linear_combination' h_pair_cancellation * d₀

/-! ## Boundary direction computation -/

lemma hex_same_cell_direction (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 := by
  exact false_to_true_dir x y

lemma hex_same_cell_direction_true (x y : ℤ) :
    correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true) = -1 := by
  convert congr_arg Neg.neg ( hex_same_cell_direction x y ) using 1 ; ring

end