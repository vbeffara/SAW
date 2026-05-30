/-
# Cancellation Identity (Lemma 1) — Walk Partition and Observable

Formalizes the cancellation identity from Section 2 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.
-/

import Mathlib
import RequestProject.SAWObservableDef

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Key properties of j -/

/-- j is nonzero. -/
lemma j_ne_zero : j ≠ 0 := by
  rw [j_eq_complex]
  intro h
  have hre := congr_arg Complex.re h
  simp at hre

/-- conj(j) is nonzero. -/
lemma conj_j_ne_zero : conj j ≠ 0 := by
  rw [conj_j_eq_complex]
  intro h
  have hre := congr_arg Complex.re h
  simp at hre

/-- |j|² = 1. -/
lemma j_normSq_eq_one : Complex.normSq j = 1 := by
  rw [j_eq_complex, Complex.normSq_mk]
  ring_nf
  rw [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  ring

/-
j³ = 1.
-/
lemma j_cube_eq_one' : j ^ 3 = 1 := by
  rw [ pow_succ' ];
  rw [ sq ] ; rw [ j_eq_complex ] ; norm_num [ Complex.ext_iff, pow_three ] ;
  grind

/-
1 + j + j² = 0.
-/
lemma j_sum_zero' : (1 : ℂ) + j + j ^ 2 = 0 := by
  norm_num [ Complex.ext_iff, sq ];
  norm_num [ j_eq_complex ] ; ring ; norm_num;

/-
j² = conj(j).
-/
lemma j_sq_eq_conj' : j ^ 2 = conj j := by
  unfold j; norm_num [ pow_two, Complex.ext_iff ] ;
  norm_num [ Complex.exp_re, Complex.exp_im, ( by ring : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 ) ] ; ring ; norm_num;

/-! ## Direction vector properties -/

/-- The direction from any hex vertex to its 0-th neighbor is nonzero. -/
lemma midEdgeDir_zero_ne_zero (v : HexVertex) : midEdgeDir v 0 ≠ 0 := by
  rcases v with ⟨x, y, b⟩
  unfold midEdgeDir hexNeighbors3
  cases b
  · -- FALSE vertex: direction to TRUE(x,y) is 1
    simp only [ite_false]
    show correctHexEmbed (falseNeighbors x y 0) - correctHexEmbed (x, y, false) ≠ 0
    simp only [falseNeighbors]
    rw [false_to_true_dir]; exact one_ne_zero
  · -- TRUE vertex: direction to FALSE(x,y) is -1
    simp only [ite_true]
    show correctHexEmbed (trueNeighbors x y 0) - correctHexEmbed (x, y, true) ≠ 0
    simp only [trueNeighbors]
    rw [true_dir1]; exact neg_ne_zero.mpr one_ne_zero

/-! ## Hex vertex neighbor completeness -/

/-
Every neighbor of a hex vertex is one of the three listed neighbors.
-/
lemma hexNeighbors3_complete (v w : HexVertex) (h : hexGraph.Adj v w) :
    w = hexNeighbors3 v 0 ∨ w = hexNeighbors3 v 1 ∨ w = hexNeighbors3 v 2 := by
  rcases v with ⟨ x, y, b ⟩ ; rcases w with ⟨ x', y', b' ⟩ ; simp_all +decide [ hexNeighbors3 ] ;
  cases b <;> cases b' <;> simp_all +decide [ hexGraph ];
  · unfold falseNeighbors; aesop;
  · unfold trueNeighbors; aesop;

/-
The three neighbors are distinct.
-/
lemma hexNeighbors3_injective (v : HexVertex) :
    Function.Injective (hexNeighbors3 v) := by
  unfold hexNeighbors3;
  split_ifs <;> simp +decide [ Function.Injective, * ];
  · simp +decide [ Fin.forall_fin_succ, trueNeighbors ];
    omega;
  · simp +decide [ Fin.forall_fin_succ, falseNeighbors ]

/-! ## Reduced form of the cancellation identity -/

/-- The reduced cancellation identity: F₀ + j·F₁ + j̄·F₂ = 0
    implies the full vertex relation. -/
theorem vertex_relation_from_reduced (v : HexVertex) (F₀ F₁ F₂ : ℂ)
    (h : F₀ + j * F₁ + conj j * F₂ = 0) :
    midEdgeDir v 0 * F₀ + midEdgeDir v 1 * F₁ + midEdgeDir v 2 * F₂ = 0 := by
  have hj := midEdgeDir_j_relation v
  rw [hj.1, hj.2]
  have : midEdgeDir v 0 * F₀ + j * midEdgeDir v 0 * F₁ +
    conj j * midEdgeDir v 0 * F₂ =
    midEdgeDir v 0 * (F₀ + j * F₁ + conj j * F₂) := by ring
  rw [this, h, mul_zero]

/-- Conversely, the full vertex relation implies the reduced form. -/
theorem reduced_from_vertex_relation (v : HexVertex) (F₀ F₁ F₂ : ℂ)
    (h : midEdgeDir v 0 * F₀ + midEdgeDir v 1 * F₁ + midEdgeDir v 2 * F₂ = 0) :
    F₀ + j * F₁ + conj j * F₂ = 0 := by
  have hj := midEdgeDir_j_relation v
  rw [hj.1, hj.2] at h
  have h' : midEdgeDir v 0 * (F₀ + j * F₁ + conj j * F₂) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h').resolve_left (midEdgeDir_zero_ne_zero v)

/-! ## Vertex contribution -/

/-- The contribution of a walk to the vertex relation sum at v. -/
def vertexContrib (v : HexVertex) (midEdgeIdx : Fin 3) (winding : ℝ) (len : ℕ) : ℂ :=
  midEdgeDir v midEdgeIdx * walkWeight winding len xc sigma

/-- Triplet contribution is zero. -/
theorem vertexContrib_triplet_zero (v : HexVertex) (W : ℝ) (ℓ : ℕ) :
    vertexContrib v 0 W ℓ +
    vertexContrib v 1 (W - Real.pi / 3) (ℓ + 1) +
    vertexContrib v 2 (W + Real.pi / 3) (ℓ + 1) = 0 := by
  unfold vertexContrib
  have hj := midEdgeDir_j_relation v
  rw [hj.1, hj.2]
  convert triplet_contribution_zero (midEdgeDir v 0) W ℓ using 1
  ring

/-- Pair contribution is zero. -/
theorem vertexContrib_pair_zero (v : HexVertex) (W : ℝ) (ℓ : ℕ) :
    vertexContrib v 1 (W - 4 * Real.pi / 3) ℓ +
    vertexContrib v 2 (W + 4 * Real.pi / 3) ℓ = 0 := by
  unfold vertexContrib
  have hj := midEdgeDir_j_relation v
  rw [hj.1, hj.2]
  convert pair_contribution_zero (midEdgeDir v 0) W ℓ using 1
  ring

/-! ## Abstract partition cancellation -/

/-- If a finite sum can be partitioned into groups, each summing to zero,
    then the total sum is zero. -/
theorem sum_zero_of_partition_cancel {α β : Type*} [DecidableEq β]
    [Fintype α] [Fintype β]
    (f : α → ℂ) (group : α → β)
    (h_cancel : ∀ b : β, ∑ a ∈ Finset.univ.filter (fun a => group a = b), f a = 0) :
    ∑ a : α, f a = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (group a)) f]
  exact Finset.sum_eq_zero fun b _ => h_cancel b

/-! ## Interior edge cancellation for discrete Stokes -/

/-- Interior edge cancellation: opposite directions cancel. -/
lemma direction_cancellation (v w : HexVertex) :
    (correctHexEmbed w - correctHexEmbed v) +
    (correctHexEmbed v - correctHexEmbed w) = 0 := by ring

end