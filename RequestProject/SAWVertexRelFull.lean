/-
# Walk extension infrastructure for the vertex relation
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Walk extension: append one step -/

/-- Extend a walk by one step. -/
def walkCons' {v w u : HexVertex} (p : hexGraph.Walk v w)
    (hadj : hexGraph.Adj w u) : hexGraph.Walk v u :=
  p.append (.cons hadj .nil)

@[simp] lemma walkCons'_length {v w u : HexVertex} (p : hexGraph.Walk v w)
    (hadj : hexGraph.Adj w u) :
    (walkCons' p hadj).length = p.length + 1 := by
  simp [walkCons', SimpleGraph.Walk.length_append]

lemma walkCons'_support {v w u : HexVertex} (p : hexGraph.Walk v w)
    (hadj : hexGraph.Adj w u) :
    (walkCons' p hadj).support = p.support ++ [u] := by
  simp [walkCons', SimpleGraph.Walk.support_append]

/-- Extending a path by one step to a vertex not in its support gives a path. -/
lemma walkCons'_isPath {v w u : HexVertex} (p : hexGraph.Walk v w)
    (hp : p.IsPath) (hadj : hexGraph.Adj w u) (hnotin : u ∉ p.support) :
    (walkCons' p hadj).IsPath := by
  unfold walkCons'
  simp_all +decide [SimpleGraph.Walk.isPath_def]
  simp_all +decide [SimpleGraph.Walk.support_append]
  grind

/-! ## Adjacency lemmas for hexGraph -/

lemma adj_false_true_same (x y : ℤ) :
    hexGraph.Adj (x, y, false) (x, y, true) := by
  left; exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

lemma adj_false_true_xp1 (x y : ℤ) :
    hexGraph.Adj (x, y, false) (x + 1, y, true) := by
  left; exact ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

lemma adj_false_true_yp1 (x y : ℤ) :
    hexGraph.Adj (x, y, false) (x, y + 1, true) := by
  left; exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

lemma adj_true_false_same (x y : ℤ) :
    hexGraph.Adj (x, y, true) (x, y, false) := by
  right; exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

lemma adj_true_false_xm1 (x y : ℤ) :
    hexGraph.Adj (x, y, true) (x - 1, y, false) := by
  exact Or.inr ⟨rfl, rfl, by simp +decide⟩

lemma adj_true_false_ym1 (x y : ℤ) :
    hexGraph.Adj (x, y, true) (x, y - 1, false) := by
  unfold hexGraph; aesop

/-! ## Direction vectors from vertices to their neighbors -/

/-- The direction from FALSE(x,y) to TRUE(x+1,y) is j. -/
lemma false_to_true_xp1_dir (x y : ℤ) :
    correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false) = j := by
  unfold correctHexEmbed j; ring; norm_num [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
  ring
  rw [show Real.pi * (2 / 3) = Real.pi - Real.pi / 3 by ring]
  norm_num [Real.cos_pi_sub, Real.sin_pi_sub]; ring

/-- The direction from FALSE(x,y) to TRUE(x,y+1) is conj(j). -/
lemma false_to_true_yp1_dir (x y : ℤ) :
    correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false) = conj j := by
  unfold correctHexEmbed j; norm_num [Complex.ext_iff]; ring
  norm_num [Complex.exp_re, Complex.exp_im,
    show Real.pi * (2 / 3) = Real.pi - Real.pi / 3 by ring]; ring

/-! ## Direction sum at vertices -/

/-- At FALSE(x,y), the three direction vectors sum to zero. -/
lemma false_dir_sum_zero (x y : ℤ) :
    (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) +
    (correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false)) +
    (correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false)) = 0 :=
  false_vertex_dir_sum x y

/-
1 + j + conj(j) = 0 (cube roots of unity sum to zero).
-/
lemma one_add_j_add_conj_j : (1 : ℂ) + j + conj j = 0 := by
  unfold j; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ;
  norm_num [ mul_div_assoc, Real.cos_two_mul ]

/-- The direction vectors from a FALSE vertex are 1, j, conj(j). -/
lemma false_dir_eq_cube_roots (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 ∧
    correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false) = j ∧
    correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false) = conj j :=
  ⟨false_to_true_dir x y, false_to_true_xp1_dir x y, false_to_true_yp1_dir x y⟩

end