/-
# Triplet infrastructure for the vertex relation

This file provides combinatorial infrastructure for the TRIPLET part
of the vertex relation (Lemma 1 of Duminil-Copin & Smirnov 2012).

A triplet consists of three walks γ₁, γ₂, γ₃ where:
- γ₁ ends at a neighbor w_i of vertex v, NOT visiting v
- γ₂ = γ₁ extended by w_i → v, then exits toward w_j
- γ₃ = γ₁ extended by w_i → v, then exits toward w_k

The triplet cancellation identity (already proved in SAW.lean):
  1 + xc · j · conj(λ) + xc · conj(j) · λ = 0
ensures the contributions sum to zero.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Hex adjacency helpers -/

lemma hex_adj_ft (x y : ℤ) : hexGraph.Adj (x, y, false) (x, y, true) := by
  left; exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

lemma hex_adj_ft_xp1 (x y : ℤ) : hexGraph.Adj (x, y, false) (x + 1, y, true) := by
  left; exact ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

lemma hex_adj_ft_yp1 (x y : ℤ) : hexGraph.Adj (x, y, false) (x, y + 1, true) := by
  left; exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

lemma hex_adj_tf (x y : ℤ) : hexGraph.Adj (x, y, true) (x, y, false) := by
  right; exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

lemma hex_adj_tf_xm1 (x y : ℤ) : hexGraph.Adj (x, y, true) (x - 1, y, false) := by
  right; exact ⟨rfl, rfl, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩

lemma hex_adj_tf_ym1 (x y : ℤ) : hexGraph.Adj (x, y, true) (x, y - 1, false) := by
  unfold hexGraph; simp

/-! ## Direction vectors

The direction vectors from a vertex v to its neighbors are the (w-v) terms
in the vertex relation. On the hex lattice, these are related to cube
roots of unity. -/

/-- Direction from FALSE(x,y) to TRUE(x,y) is 1. -/
lemma dir_ft_same (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 := by
  unfold correctHexEmbed; simp [Complex.ext_iff]

/-
Direction from FALSE(x,y) to TRUE(x+1,y) is j.
-/
lemma dir_ft_xp1 (x y : ℤ) :
    correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false) = j := by
  unfold correctHexEmbed j; ring;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring;
  lia

/-
Direction from FALSE(x,y) to TRUE(x,y+1) is conj(j).
-/
lemma dir_ft_yp1 (x y : ℤ) :
    correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false) = conj j := by
  unfold j;
  unfold correctHexEmbed; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Real.cos_two_mul, Real.sin_two_mul, mul_div_assoc ] ; ring;
  grind +revert

/-- Direction from TRUE(x,y) to FALSE(x,y) is -1. -/
lemma dir_tf_same (x y : ℤ) :
    correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true) = -1 := by
  unfold correctHexEmbed; simp [Complex.ext_iff]

/-
Direction from TRUE(x,y) to FALSE(x-1,y) is -j.
-/
lemma dir_tf_xm1 (x y : ℤ) :
    correctHexEmbed (x - 1, y, false) - correctHexEmbed (x, y, true) = -j := by
  unfold correctHexEmbed j; ring;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring;
  norm_num

/-
Direction from TRUE(x,y) to FALSE(x,y-1) is -conj(j).
-/
lemma dir_tf_ym1 (x y : ℤ) :
    correctHexEmbed (x, y - 1, false) - correctHexEmbed (x, y, true) = -conj j := by
  unfold correctHexEmbed j; norm_num [ Complex.ext_iff ] ; ring;
  norm_num [ Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring

end