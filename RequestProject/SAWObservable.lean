/-
# Parafermionic Observable and Cancellation Identity (Lemma 1)

Formalization of the parafermionic observable F(z) from Section 2 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Main results

* `triplet_contribution_zero` — algebraic cancellation for walk triplets
* `pair_contribution_zero` — algebraic cancellation for walk pairs
* `false_vertex_j_relation` / `true_vertex_j_relation` — direction vectors
  from a hex vertex to its neighbors are related by cube roots of unity
* `vertex_relation_false` / `vertex_relation_true` — the cancellation identity

## Proof strategy

The cancellation identity (Lemma 1) states that for every interior vertex v:
  (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0

The proof partitions walks ending at v's mid-edges into groups:
- **Triplets**: a walk ending at v (visiting 1 mid-edge) + its 2 extensions
  → cancel by `triplet_cancellation`
- **Pairs**: walks visiting all 3 mid-edges, paired by loop reversal
  → cancel by `pair_cancellation`
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Walk ending at a mid-edge -/

/-- A self-avoiding walk from `start` ending at mid-edge (prev, endpoint).
    The walk consists of a hexGraph.Path from start to prev,
    followed by one more step to endpoint. -/
structure WalkToMidEdge (start prev endpoint : HexVertex) where
  prefix_path : hexGraph.Path start prev
  adj : hexGraph.Adj prev endpoint
  fresh : endpoint ∉ prefix_path.1.support

/-- The length of a WalkToMidEdge. -/
def WalkToMidEdge.length {start prev endpoint : HexVertex}
    (γ : WalkToMidEdge start prev endpoint) : ℕ :=
  γ.prefix_path.1.length + 1

/-- The support of a WalkToMidEdge. -/
def WalkToMidEdge.support {start prev endpoint : HexVertex}
    (γ : WalkToMidEdge start prev endpoint) : List HexVertex :=
  γ.prefix_path.1.support ++ [endpoint]

/-! ## Winding using correctHexEmbed -/

/-- The winding of a walk, computed using correctHexEmbed. -/
def correctWalkWinding : List HexVertex → ℝ
  | [] | [_] | [_, _] => 0
  | v₀ :: v₁ :: v₂ :: rest =>
    (Complex.arg (correctHexEmbed v₂ - correctHexEmbed v₁) -
     Complex.arg (correctHexEmbed v₁ - correctHexEmbed v₀)) +
    correctWalkWinding (v₁ :: v₂ :: rest)

/-! ## Walk weights -/

/-- The weight of a walk: exp(-iσW) · x^ℓ. -/
noncomputable def walkWeight (W : ℝ) (len : ℕ) (x s : ℝ) : ℂ :=
  Complex.exp (-Complex.I * s * W) * (x : ℂ) ^ len

/-- The contribution of a walk to the vertex relation sum:
    (direction) · exp(-iσW) · x^ℓ. -/
noncomputable def walkContrib (direction : ℂ) (W : ℝ) (len : ℕ) (x s : ℝ) : ℂ :=
  direction * walkWeight W len x s

/-! ## Direction vectors on the hexagonal lattice

The three direction vectors from a hex vertex to its neighbors are
related by the cube root of unity j = exp(i2π/3). -/

/-- j as a complex number: (-1/2, √3/2). -/
lemma j_eq_complex : j = ⟨-1/2, Real.sqrt 3 / 2⟩ := by
  unfold j
  rw [show Complex.I * (2 * (↑Real.pi : ℂ) / 3) = ↑(2 * Real.pi / 3) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_mul_I]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
               Complex.cos_ofReal_re, Complex.sin_ofReal_im]
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub]
    simp [Real.cos_pi_div_three]; ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
               Complex.sin_ofReal_re, Complex.cos_ofReal_im]
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
        Real.sin_pi_div_three]
    ring

/-- conj(j) as a complex number: (-1/2, -√3/2). -/
lemma conj_j_eq_complex : conj j = ⟨-1/2, -(Real.sqrt 3 / 2)⟩ := by
  rw [j_eq_complex]; apply Complex.ext <;> simp

/-- Direction from FALSE(x,y) to TRUE(x,y) is 1. -/
lemma false_dir1 (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 :=
  false_to_true_dir x y

/-- Direction from FALSE(x,y) to TRUE(x+1,y) is j. -/
lemma false_dir2_eq_j (x y : ℤ) :
    correctHexEmbed (↑(x + 1), y, true) - correctHexEmbed (x, y, false) =
    j * (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) := by
  rw [false_dir1, j_eq_complex]
  unfold correctHexEmbed
  apply Complex.ext <;> simp <;> (try push_cast) <;> ring

/-- Direction from FALSE(x,y) to TRUE(x,y+1) is conj(j). -/
lemma false_dir3_eq_conjj (x y : ℤ) :
    correctHexEmbed (x, ↑(y + 1), true) - correctHexEmbed (x, y, false) =
    conj j * (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) := by
  rw [false_dir1, conj_j_eq_complex]
  unfold correctHexEmbed
  apply Complex.ext <;> simp <;> (try push_cast) <;> ring

/-- Direction from TRUE(x,y) to FALSE(x,y) is -1. -/
lemma true_dir1 (x y : ℤ) :
    correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true) = -1 := by
  unfold correctHexEmbed; apply Complex.ext <;> simp

/-- Direction from TRUE(x,y) to FALSE(x-1,y) is j * (-1). -/
lemma true_dir2_eq_j (x y : ℤ) :
    correctHexEmbed (↑(x - 1), y, false) - correctHexEmbed (x, y, true) =
    j * (correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)) := by
  rw [true_dir1, j_eq_complex]
  unfold correctHexEmbed
  apply Complex.ext <;> simp <;> (try push_cast) <;> ring

/-- Direction from TRUE(x,y) to FALSE(x,y-1) is conj(j) * (-1). -/
lemma true_dir3_eq_conjj (x y : ℤ) :
    correctHexEmbed (x, ↑(y - 1), false) - correctHexEmbed (x, y, true) =
    conj j * (correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)) := by
  rw [true_dir1, conj_j_eq_complex]
  unfold correctHexEmbed
  apply Complex.ext <;> simp <;> (try push_cast) <;> ring

/-- At a FALSE vertex, the three direction vectors satisfy the j-relation. -/
theorem false_vertex_j_relation (x y : ℤ) :
    let d₁ := correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)
    let d₂ := correctHexEmbed (↑(x + 1), y, true) - correctHexEmbed (x, y, false)
    let d₃ := correctHexEmbed (x, ↑(y + 1), true) - correctHexEmbed (x, y, false)
    d₂ = j * d₁ ∧ d₃ = conj j * d₁ :=
  ⟨false_dir2_eq_j x y, false_dir3_eq_conjj x y⟩

/-- At a TRUE vertex, the three direction vectors satisfy the j-relation. -/
theorem true_vertex_j_relation (x y : ℤ) :
    let d₁ := correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)
    let d₂ := correctHexEmbed (↑(x - 1), y, false) - correctHexEmbed (x, y, true)
    let d₃ := correctHexEmbed (x, ↑(y - 1), false) - correctHexEmbed (x, y, true)
    d₂ = j * d₁ ∧ d₃ = conj j * d₁ :=
  ⟨true_dir2_eq_j x y, true_dir3_eq_conjj x y⟩

/-! ## Phase factors for the triplet

At the critical spin σ = 5/8, the winding change of ±π/3 produces
phase factors conj(λ) and λ respectively. -/

/-- exp(-iσ(W - π/3)) = exp(-iσW) · exp(iσπ/3). -/
lemma exp_winding_minus (W : ℝ) :
    Complex.exp (-Complex.I * sigma * (W - Real.pi / 3)) =
    Complex.exp (-Complex.I * sigma * W) *
    Complex.exp (Complex.I * ↑(sigma * (Real.pi / 3))) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- exp(-iσ(W + π/3)) = exp(-iσW) · exp(-iσπ/3). -/
lemma exp_winding_plus (W : ℝ) :
    Complex.exp (-Complex.I * sigma * (W + Real.pi / 3)) =
    Complex.exp (-Complex.I * sigma * W) *
    Complex.exp (-Complex.I * ↑(sigma * (Real.pi / 3))) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- exp(iσπ/3) = conj(λ), since σ·π/3 = 5π/24. -/
lemma phase_plus_eq_conj_lam :
    Complex.exp (Complex.I * ↑(sigma * (Real.pi / 3))) = conj lam := by
  unfold sigma lam; rw [← Complex.exp_conj]
  simp only [map_mul, map_neg, conj_I, map_div₀, map_mul, map_ofNat,
             Complex.conj_ofReal]
  congr 1; push_cast; ring

/-- exp(-iσπ/3) = λ. -/
lemma phase_minus_eq_lam :
    Complex.exp (-Complex.I * ↑(sigma * (Real.pi / 3))) = lam := by
  unfold sigma lam; congr 1; push_cast; ring

/-! ## Triplet Cancellation

The triplet contribution is:
  d · e^{-iσW} · xc^ℓ + d·j · e^{-iσ(W-π/3)} · xc^{ℓ+1} + d·j̄ · e^{-iσ(W+π/3)} · xc^{ℓ+1}
= d · e^{-iσW} · xc^ℓ · (1 + xc · j · conj(λ) + xc · conj(j) · λ)
= 0

This is the ONLY place where x = xc (the critical value) is used. -/

/-- The triplet bracket: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0. -/
lemma triplet_bracket :
    (1 : ℂ) + (xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam = 0 :=
  triplet_cancellation

/-
**Triplet cancellation**: the sum of contributions from a triplet of walks
    (one visiting 1 mid-edge, two visiting 2 mid-edges) vanishes.
-/
theorem triplet_contribution_zero (d : ℂ) (W : ℝ) (ℓ : ℕ) :
    d * walkWeight W ℓ xc sigma +
    (d * j) * walkWeight (W - Real.pi / 3) (ℓ + 1) xc sigma +
    (d * conj j) * walkWeight (W + Real.pi / 3) (ℓ + 1) xc sigma = 0 := by
  -- Factor out $d * \exp(-i\sigma W) * xc^\ell$ from the sum.
  have h_factor : d * walkWeight W ℓ xc sigma + d * j * walkWeight (W - Real.pi / 3) (ℓ + 1) xc sigma + d * starRingEnd ℂ j * walkWeight (W + Real.pi / 3) (ℓ + 1) xc sigma =
    d * Complex.exp (-Complex.I * sigma * W) * (xc : ℂ) ^ ℓ * (1 + (xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam) := by
      unfold walkWeight;
      rw [ ← phase_plus_eq_conj_lam, ← phase_minus_eq_lam ] ; ring;
      norm_num [ Complex.exp_add, Complex.exp_neg, Complex.exp_mul_I ] ; ring;
      norm_num [ Complex.exp_add, Complex.exp_neg ] ; ring;
  rw [ h_factor, triplet_bracket, MulZeroClass.mul_zero ]

/-! ## Pair Cancellation

The pair contribution is:
  d·j · e^{-iσ(W-4π/3)} · xc^ℓ + d·j̄ · e^{-iσ(W+4π/3)} · xc^ℓ
= d · e^{-iσW} · xc^ℓ · (j · conj(λ)⁴ + conj(j) · λ⁴)
= 0 -/

/-- The pair bracket: j · conj(λ)⁴ + conj(j) · λ⁴ = 0. -/
lemma pair_bracket :
    j * conj lam ^ 4 + conj j * lam ^ 4 = 0 :=
  pair_cancellation

/-
**Pair cancellation**: the sum of contributions from a pair of walks
    (both visiting all 3 mid-edges, differing by loop direction) vanishes.
-/
theorem pair_contribution_zero (d : ℂ) (W : ℝ) (ℓ : ℕ) :
    (d * j) * walkWeight (W - 4 * Real.pi / 3) ℓ xc sigma +
    (d * conj j) * walkWeight (W + 4 * Real.pi / 3) ℓ xc sigma = 0 := by
  -- Factor out $d * \exp(-i\sigma W) * xc^\ell$ from the sum.
  suffices h_factor : j * Complex.exp (-Complex.I * sigma * (W - 4 * Real.pi / 3)) + starRingEnd ℂ j * Complex.exp (-Complex.I * sigma * (W + 4 * Real.pi / 3)) = 0 by
    convert congr_arg ( fun x : ℂ => d * xc ^ ℓ * x ) h_factor using 1 <;> push_cast [ walkWeight ] <;> ring!;
  unfold sigma j; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, mul_div ] ; ring; norm_num;
  norm_num [ ( by ring : Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 ), ( by ring : Real.pi * ( 5 / 6 ) = Real.pi - Real.pi / 6 ), Real.sin_add, Real.cos_add ] ; ring ; norm_num

/-! ## The Cancellation Identity (Lemma 1)

For every interior vertex v of a simply connected domain Ω, the
parafermionic observable satisfies the vertex relation:

  (p - v) · F(p) + (q - v) · F(q) + (r - v) · F(r) = 0

where p, q, r are the three mid-edges adjacent to v.

The proof partitions walks ending at v's mid-edges into groups:
- **Triplets**: cancel by `triplet_contribution_zero`
- **Pairs**: cancel by `pair_contribution_zero`

Below we state the vertex relation as a consequence of these
cancellations and the walk partition. -/

/-- The vertex relation for a FALSE vertex (x,y,false).

    The three mid-edges are edges to TRUE(x,y), TRUE(x+1,y), TRUE(x,y+1).
    The direction vectors satisfy d₂ = j·d₁, d₃ = conj(j)·d₁.

    The observable values F₁, F₂, F₃ at these three mid-edges satisfy
    d₁·F₁ + d₂·F₂ + d₃·F₃ = 0 when walks can be partitioned into
    cancelling triplets and pairs. -/
theorem vertex_relation_false (x y : ℤ) (F₁ F₂ F₃ : ℂ)
    (h_cancel : let d := correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)
                d * F₁ + (j * d) * F₂ + (conj j * d) * F₃ = 0) :
    let d₁ := correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)
    let d₂ := correctHexEmbed (↑(x + 1), y, true) - correctHexEmbed (x, y, false)
    let d₃ := correctHexEmbed (x, ↑(y + 1), true) - correctHexEmbed (x, y, false)
    d₁ * F₁ + d₂ * F₂ + d₃ * F₃ = 0 := by
  simp only
  rw [false_dir2_eq_j, false_dir3_eq_conjj]
  exact h_cancel

/-- The vertex relation for a TRUE vertex (x,y,true). -/
theorem vertex_relation_true (x y : ℤ) (F₁ F₂ F₃ : ℂ)
    (h_cancel : let d := correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)
                d * F₁ + (j * d) * F₂ + (conj j * d) * F₃ = 0) :
    let d₁ := correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)
    let d₂ := correctHexEmbed (↑(x - 1), y, false) - correctHexEmbed (x, y, true)
    let d₃ := correctHexEmbed (x, ↑(y - 1), false) - correctHexEmbed (x, y, true)
    d₁ * F₁ + d₂ * F₂ + d₃ * F₃ = 0 := by
  simp only
  rw [true_dir2_eq_j, true_dir3_eq_conjj]
  exact h_cancel

/-! ## Walk partition

The key combinatorial ingredient: every walk ending at one of v's
three mid-edges belongs to exactly one cancelling group.

- A walk ending at v (visiting 1 mid-edge) forms a triplet with its
  two one-step extensions (if both other neighbors are unvisited).
- A walk visiting all 3 mid-edges forms a pair with its loop-reversed
  counterpart.

In the vertex-SAW model (each vertex visited at most once), only
triplets arise since at most 2 edges at v can be used.

In the medial-SAW model (self-avoiding on mid-edges, vertex
revisiting allowed), both triplets and pairs arise. -/

/-- The walk partition lemma: the observable values F₁, F₂, F₃ at v's
    three mid-edges satisfy d·F₁ + j·d·F₂ + j̄·d·F₃ = 0.

    This follows from partitioning walks into cancelling triplets and pairs.
    The algebraic cancellation is proved by `triplet_contribution_zero`
    and `pair_contribution_zero`. The combinatorial partition argument
    (showing every walk belongs to exactly one group) is the key step. -/
lemma walk_partition_cancellation (d : ℂ) (F₁ F₂ F₃ : ℂ)
    (h_decomp : d * F₁ + (j * d) * F₂ + (conj j * d) * F₃ =
      -- Each walk's contribution to the sum is captured by the triplet
      -- or pair cancellation. The total sum is zero because:
      -- 1. Every walk is in exactly one group (partition exhaustiveness)
      -- 2. Each group's contribution is zero (algebraic cancellation)
      0) :
    d * F₁ + (j * d) * F₂ + (conj j * d) * F₃ = 0 := h_decomp

/-! ## Summary

The cancellation identity (vertex relation, Lemma 1) has been decomposed into:

### Proved
1. `pair_cancellation` — algebraic identity j·conj(λ)⁴ + conj(j)·λ⁴ = 0
2. `triplet_cancellation` — algebraic identity 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
3. `false_vertex_j_relation` / `true_vertex_j_relation` — direction vectors
   from each hex vertex to its three neighbors are related by j and conj(j)
4. `exp_winding_minus` / `exp_winding_plus` — exponential factoring for winding changes
5. `phase_plus_eq_conj_lam` / `phase_minus_eq_lam` — phase factors are conj(λ) and λ
6. `vertex_relation_false` / `vertex_relation_true` — the vertex relation
   reduces to d·F₁ + j·d·F₂ + j̄·d·F₃ = 0

### Remaining gap
The combinatorial walk partition argument (showing every walk ending at
v's mid-edges belongs to exactly one cancelling group) is not yet
formalized. This is the key step connecting the algebraic cancellation
to the actual observable. Once this is established, the vertex relation
(Lemma 1) follows, and summing over all vertices gives the strip
identity (Lemma 2), from which B_paper ≤ 1.
-/

end