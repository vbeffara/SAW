/-
# Vertex Relation for the Parafermionic Observable (Lemma 1)

Formalization of the vertex relation from Section 2 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Main results

* `false_edge_dirs` / `true_edge_dirs` — the three edge directions
* `triplet_cancel_at_vertex` — triplet cancellation at any vertex
* `pair_cancel_at_vertex` — pair cancellation at any vertex
* `left_boundary_contrib_re` — boundary phase = c_alpha
* `interior_midedge_cancels` — discrete Stokes cancellation
* `j_cube_eq_one` / `j_sum_zero` — cube root of unity properties
* `winding_telescopes` — the winding of a walk is a telescoping sum
-/

import Mathlib
import RequestProject.SAWObservable

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Cube root of unity properties

j = exp(i2π/3) is a primitive cube root of unity.
These properties underpin the cancellation identity. -/

/-
j³ = 1: j is a cube root of unity.
-/
lemma j_cube_eq_one : j ^ 3 = 1 := by
  unfold j; norm_num [ Complex.ext_iff, pow_three ] ; ring; norm_num;
  norm_num [ Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring ; norm_num;
  norm_num [ pow_three ] ; ring

/-
|j| = 1: j lies on the unit circle.
-/
lemma j_norm_one : Complex.normSq j = 1 := by
  convert Complex.normSq_eq_norm_sq j ; norm_num [ j ];
  norm_num [ Complex.norm_exp ]

/-
1 + j + j² = 0: the sum of cube roots of unity is zero.
-/
lemma j_sum_zero : (1 : ℂ) + j + j ^ 2 = 0 := by
  norm_num [ sq, Complex.ext_iff, j_eq_complex ];
  ring_nf; norm_num;

/-
j² = conj(j): the square of j is its conjugate.
-/
lemma j_sq_eq_conj : j ^ 2 = conj j := by
  unfold j; norm_num [ Complex.ext_iff, sq ] ;
  norm_num [ Complex.exp_re, Complex.exp_im, ( by ring : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 ) ] ; ring ; norm_num;

/-! ## Edge directions on the hexagonal lattice -/

/-- The complex direction of an edge from v to w. -/
def hexEdgeDir (v w : HexVertex) : ℂ :=
  correctHexEmbed w - correctHexEmbed v

/-- At a FALSE vertex, the three edge directions are 1, j, conj(j). -/
lemma false_edge_dirs (x y : ℤ) :
    hexEdgeDir (x, y, false) (x, y, true) = 1 ∧
    hexEdgeDir (x, y, false) ((x + 1 : ℤ), y, true) = j ∧
    hexEdgeDir (x, y, false) (x, (y + 1 : ℤ), true) = conj j := by
  refine ⟨false_to_true_dir x y, ?_, ?_⟩
  · have h1 := false_to_true_dir x y
    have h2 := false_dir2_eq_j x y
    unfold hexEdgeDir at *; rw [h1, mul_one] at h2; exact h2
  · have h1 := false_to_true_dir x y
    have h3 := false_dir3_eq_conjj x y
    unfold hexEdgeDir at *; rw [h1, mul_one] at h3; exact h3

/-- At a TRUE vertex, the three edge directions are -1, -j, -conj(j). -/
lemma true_edge_dirs (x y : ℤ) :
    hexEdgeDir (x, y, true) (x, y, false) = -1 ∧
    hexEdgeDir (x, y, true) ((x - 1 : ℤ), y, false) = -j ∧
    hexEdgeDir (x, y, true) (x, (y - 1 : ℤ), false) = -(conj j) := by
  refine ⟨true_dir1 x y, ?_, ?_⟩
  · have h1 := true_dir1 x y
    have h2 := true_dir2_eq_j x y
    unfold hexEdgeDir at *; rw [h1] at h2; simp only [mul_neg, mul_one] at h2; exact h2
  · have h1 := true_dir1 x y
    have h3 := true_dir3_eq_conjj x y
    unfold hexEdgeDir at *; rw [h1] at h3; simp only [mul_neg, mul_one] at h3; exact h3

/-! ## Neighbor enumeration -/

/-- The three neighbors of a FALSE vertex. -/
def falseNeighbors (x y : ℤ) : Fin 3 → HexVertex
  | 0 => (x, y, true)
  | 1 => (x + 1, y, true)
  | 2 => (x, y + 1, true)

/-- The three neighbors of a TRUE vertex. -/
def trueNeighbors (x y : ℤ) : Fin 3 → HexVertex
  | 0 => (x, y, false)
  | 1 => (x - 1, y, false)
  | 2 => (x, y - 1, false)

/-- Each false neighbor is adjacent to v. -/
lemma falseNeighbors_adj (x y : ℤ) (i : Fin 3) :
    hexGraph.Adj (x, y, false) (falseNeighbors x y i) := by
  fin_cases i <;> simp [falseNeighbors, hexGraph]

/-- Each true neighbor is adjacent to v. -/
lemma trueNeighbors_adj (x y : ℤ) (i : Fin 3) :
    hexGraph.Adj (x, y, true) (trueNeighbors x y i) := by
  fin_cases i <;> simp [trueNeighbors, hexGraph] <;> omega

/-! ## Triplet cancellation at a vertex

For any walk entering vertex v from neighbor nᵢ with direction dᵢ,
winding W, and edge-length ℓ, the triplet contribution

  dᵢ · wt(W, ℓ) + j·dᵢ · wt(W - π/3, ℓ+1) + j̄·dᵢ · wt(W + π/3, ℓ+1) = 0

follows from `triplet_contribution_zero`. The direction dᵢ is
arbitrary (the triplet cancellation works for any d ∈ ℂ).

This is the ONLY place where x = xc (the critical value) is used. -/

/-- Triplet cancellation at any hex vertex, for any entering direction d ∈ ℂ. -/
theorem triplet_cancel_at_vertex (d : ℂ) (W : ℝ) (ℓ : ℕ) :
    d * walkWeight W ℓ xc sigma +
    (d * j) * walkWeight (W - Real.pi / 3) (ℓ + 1) xc sigma +
    (d * conj j) * walkWeight (W + Real.pi / 3) (ℓ + 1) xc sigma = 0 :=
  triplet_contribution_zero d W ℓ

/-! ## Pair cancellation at a vertex

For walks visiting all 3 mid-edges of v (loop direction reversal),
the pair contribution vanishes. This uses the specific value σ = 5/8. -/

/-- Pair cancellation at any hex vertex, for any direction d ∈ ℂ. -/
theorem pair_cancel_at_vertex (d : ℂ) (W : ℝ) (ℓ : ℕ) :
    (d * j) * walkWeight (W - 4 * Real.pi / 3) ℓ xc sigma +
    (d * conj j) * walkWeight (W + 4 * Real.pi / 3) ℓ xc sigma = 0 :=
  pair_contribution_zero d W ℓ

/-! ## Boundary contribution phases

For the strip identity, boundary walks contribute with specific phases.
The real part of each boundary contribution is determined by the exit
angle of the mid-edge. -/

/-- The phase for right boundary contributions is 1 (winding = 0). -/
lemma right_boundary_phase' :
    Complex.exp (-Complex.I * ↑sigma * (0 : ℂ)) = 1 := by
  simp

/-- The contribution from a left boundary walk with winding π:
    Re((-1) · e^{-iσπ}) = c_alpha = cos(3π/8). -/
lemma left_boundary_contrib_re :
    ((-1 : ℂ) * Complex.exp (-Complex.I * ↑sigma * ↑Real.pi)).re = c_alpha := by
  unfold c_alpha; norm_num [ Complex.exp_re, Complex.exp_im, sigma ] ; ring;
  rw [ ← Real.cos_pi_sub ] ; ring

/-- Same result for winding -π (walks going the other direction). -/
lemma left_boundary_contrib_re_neg :
    ((-1 : ℂ) * Complex.exp (-Complex.I * ↑sigma * ↑(-Real.pi))).re = c_alpha := by
  convert left_boundary_contrib_re using 1 ; ring;
  norm_num [ Complex.exp_re ]

/-! ## Discrete Stokes: interior edge cancellation -/

/-- Interior mid-edges cancel in the discrete Stokes sum:
    the direction from v to w plus the direction from w to v is 0. -/
lemma interior_midedge_cancels (v w : HexVertex) :
    hexEdgeDir v w + hexEdgeDir w v = 0 := by
  unfold hexEdgeDir; ring

/-! ## Winding telescoping

The winding of a walk on the hex lattice (as computed by
`correctWalkWinding`) is a telescoping sum of edge direction angle
differences. For a walk visiting vertices [v₀, v₁, ..., vₙ]:

  correctWalkWinding = Σᵢ (arg(vᵢ₊₂ - vᵢ₊₁) - arg(vᵢ₊₁ - vᵢ))
                     = arg(vₙ - vₙ₋₁) - arg(v₁ - v₀)

Note: this is the winding of the WALK EDGES only; the starting
and ending half-edges at mid-edges a and z are NOT included.
The full winding from mid-edge a to mid-edge z equals:

  W_full = arg(starting half-edge) + correctWalkWinding + arg(ending half-edge)
         = arg(ending half-edge) - arg(starting half-edge) + correctWalkWinding

The telescoping of correctWalkWinding plus the half-edge contributions
gives the full winding as a simple difference of boundary angles. -/

/-- The winding of a 3-vertex walk telescopes to a single angle difference. -/
lemma winding_three_vertices (v₀ v₁ v₂ : HexVertex) :
    correctWalkWinding [v₀, v₁, v₂] =
    Complex.arg (correctHexEmbed v₂ - correctHexEmbed v₁) -
    Complex.arg (correctHexEmbed v₁ - correctHexEmbed v₀) := by
  simp [correctWalkWinding]

/-- The winding of appending one vertex telescopes. -/
lemma winding_append_vertex (v₀ v₁ : HexVertex) (vs : List HexVertex)
    (hvs : vs.length ≥ 1) :
    correctWalkWinding (v₀ :: v₁ :: vs) =
    (Complex.arg (correctHexEmbed vs.head! - correctHexEmbed v₁) -
     Complex.arg (correctHexEmbed v₁ - correctHexEmbed v₀)) +
    correctWalkWinding (v₁ :: vs) := by
  cases vs with
  | nil => simp at hvs
  | cons v₂ rest => simp [correctWalkWinding]

/-! ## Summary of the Cancellation Identity (Lemma 1)

### Status of formalization

**Fully proved:**
1. Algebraic cancellation identities:
   - `triplet_bracket`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
   - `pair_bracket`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
   - `triplet_contribution_zero`: triplet sum = 0 for any d, W, ℓ
   - `pair_contribution_zero`: pair sum = 0 for any d, W, ℓ
2. Direction vector computations:
   - `false_edge_dirs`: directions at FALSE vertices are 1, j, conj(j)
   - `true_edge_dirs`: directions at TRUE vertices are -1, -j, -conj(j)
   - `false_vertex_j_relation` / `true_vertex_j_relation`
3. Vertex relation structure:
   - `triplet_cancel_at_vertex`: triplet cancellation at any vertex
   - `pair_cancel_at_vertex`: pair cancellation at any vertex
   - `vertex_relation_false` / `vertex_relation_true`
4. Boundary phase computations:
   - `left_boundary_contrib_re`: Re((-1)·e^{-iσπ}) = c_alpha
   - `left_boundary_contrib_re_neg`: Re((-1)·e^{iσπ}) = c_alpha
   - `right_boundary_phase'`: phase at right boundary is 1
5. Discrete Stokes key step:
   - `interior_midedge_cancels`: direction(v→w) + direction(w→v) = 0
6. Winding structure:
   - `winding_three_vertices`: winding of 3-vertex walk
   - `winding_append_vertex`: recursive winding decomposition

**Sorry'd (in this file):**
- `j_cube_eq_one`, `j_norm_one`, `j_sum_zero`, `j_sq_eq_conj`:
  properties of j as a cube root of unity

**Remaining gaps (not in this file):**
- The combinatorial walk partition (grouping walks into cancelling
  triplets and pairs). This requires showing every walk belongs to
  exactly one group.
- The discrete Stokes summation over all vertices of the strip.
- The full boundary evaluation connecting the boundary sum to the
  strip partition functions A, B, E.
-/

end