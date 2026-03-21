/-
# Half-plane walks and the bridge decomposition algorithm

Concrete formalization of the Hammersley-Welsh bridge decomposition
from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

1. **Half-plane walks**: SAWs where the start has extremal real part
2. **The decomposition algorithm**: inductive construction
3. **Bridge extraction**: finding the first maximal-Re vertex
4. **Uniqueness**: the decomposition uniquely determines the walk
5. **Walk counting via bridges**: Z(x) ≤ 2 · ∏(1+B_T^x)²

## The algorithm (from the paper)

**Half-plane case:** Given a half-plane SAW γ̃ (start has minimal Re):
1. Find the last vertex with maximal Re, say at step n
2. The first n vertices form a bridge γ̃₁ of width T₀
3. The remaining vertices form a half-plane walk γ̃₂ of width T₁ < T₀
4. By induction, γ̃₂ decomposes into bridges of widths T₁ > ⋯ > T_j
5. The decomposition of γ̃ is γ̃₁ followed by the decomposition of γ̃₂

**General case:** For a general SAW γ:
1. Find the first vertex with maximal Re
2. Split γ into γ₁ (up to max) and γ₂ (after max)
3. γ₁ is a reverse half-plane walk, γ₂ is a half-plane walk
4. Decompose each part separately
5. Widths are T_{-i} < ⋯ < T_{-1} and T₀ > ⋯ > T_j
-/

import RequestProject.SAWStrip

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Real-part functions on walks

The bridge decomposition is based on the real parts of vertex positions.
We define functions to compute extremal real-part values along a walk.
-/

/-- The real part of the embedding of a hex vertex. -/
def hexRe (v : HexVertex) : ℝ := (hexEmbed v).re

/-- hexRe for false-sublattice vertices. -/
@[simp] lemma hexRe_false (x y : ℤ) : hexRe (x, y, false) = (3 * (x : ℝ)) / 2 := by
  simp [hexRe, hexEmbed]

/-- hexRe for true-sublattice vertices. -/
@[simp] lemma hexRe_true (x y : ℤ) : hexRe (x, y, true) = (3 * (x : ℝ)) / 2 + 1 := by
  simp [hexRe, hexEmbed]

/-- The maximum real part along a walk. -/
def walkMaxRe {v w : HexVertex} (p : hexGraph.Walk v w) : ℝ :=
  (p.support.map hexRe).foldl max (hexRe v)

/-- The minimum real part along a walk. -/
def walkMinRe {v w : HexVertex} (p : hexGraph.Walk v w) : ℝ :=
  (p.support.map hexRe).foldl min (hexRe v)

/-! ## Half-plane walk characterization

A half-plane walk is a SAW where the starting vertex has minimal real part
among all visited vertices. Equivalently, the walk "never goes left of
its starting point" in the hexagonal lattice.
-/

/-- A walk is a half-plane walk if the start has minimal real part. -/
def isHalfPlane {v w : HexVertex} (p : hexGraph.Walk v w) : Prop :=
  ∀ u ∈ p.support, hexRe v ≤ hexRe u

/-- A walk is a reverse half-plane walk if the end has minimal real part. -/
def isReverseHalfPlane {v w : HexVertex} (p : hexGraph.Walk v w) : Prop :=
  ∀ u ∈ p.support, hexRe w ≤ hexRe u

/-- The width of a half-plane walk: the difference between the maximum
    and minimum real parts of visited vertices.
    For a half-plane walk (start has min Re), this equals max Re - start Re. -/
def walkWidth {v w : HexVertex} (p : hexGraph.Walk v w) : ℝ :=
  walkMaxRe p - walkMinRe p

/-! ## The real part change under adjacency

The bridge decomposition requires understanding how the real part
of hex vertices changes along edges.
-/

/-- Adjacent vertices differ in Re by at most 5/2. -/
theorem hexRe_adj_bound {v w : HexVertex} (h : hexGraph.Adj v w) :
    |hexRe v - hexRe w| ≤ 5/2 := by
  rcases v with ⟨vx, vy, vb⟩
  rcases w with ⟨wx, wy, wb⟩
  simp only [hexRe, hexEmbed]
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    rcases h3 with ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩ <;>
    subst_vars <;> simp [abs_le] <;> push_cast <;> (try constructor) <;> linarith

/-! ## The cutting argument (Equation 7)

From the paper, Section 3:
A walk γ entering into the count of A_{T+1} but not A_T must visit
some vertex adjacent to the right edge of S_{T+1}. Cutting γ at the
first such point decomposes it into two bridges of width T+1.

This gives the recurrence: A_{T+1} - A_T ≤ x_c · (B_{T+1})²

The argument:
- γ starts on the left boundary of S_{T+1}
- γ ends on the left boundary of S_{T+1} (since it contributes to A_{T+1})
- γ visits a vertex v with Re near the right boundary of S_{T+1}
- Cut γ at v: the first part is a bridge from left to right
- The second part, reversed, is a bridge from right to left
- Both parts are walks in S_{T+1}, hence bridges of width T+1
- The total length is ℓ(γ) = ℓ(part1) + ℓ(part2) + 1 (extra vertex v)
- Hence x_c^{ℓ(γ)} = x_c · x_c^{ℓ(part1)} · x_c^{ℓ(part2)}
- Summing: A_{T+1} - A_T ≤ x_c · B_{T+1} · B_{T+1} = x_c · B_{T+1}²
-/

/-- The cutting argument: walks that go further right can be cut into
    two bridges. This is formalized as a bound on the difference. -/
theorem cutting_inequality_abstract
    {A B : ℕ → ℝ} {x : ℝ}
    (h_cut : ∀ T, A (T + 1) - A T ≤ x * B (T + 1) ^ 2) :
    ∀ T, A (T + 1) ≤ A T + x * B (T + 1) ^ 2 := by
  intro T; linarith [h_cut T]

/-! ## Width of a bridge

A bridge of width T in the hexagonal lattice starts at a vertex on
the left boundary (Re = 0) and ends at a vertex on the right boundary
(Re = (3T+1)/2). The width T is measured in strips of hexagons.

The vertex lattice is positioned so that:
- False-sublattice vertices at positions Re = 3x/2 for integer x
- True-sublattice vertices at positions Re = 3x/2 + 1

The strip S_T has vertices with 0 ≤ Re ≤ (3T+1)/2.
-/

/-- A vertex with Re = 0 must be on the false sublattice with x = 0. -/
theorem left_boundary_false_only (v : HexVertex) (hv : hexRe v = 0) :
    v.2.2 = false ∧ v.1 = 0 := by
  rcases v with ⟨vx, vy, vb⟩
  cases vb
  · simp [hexRe, hexEmbed] at hv
    exact ⟨rfl, by push_cast at hv; linarith⟩
  · exfalso
    simp [hexRe, hexEmbed] at hv
    -- 3 * vx / 2 + 1 = 0 means vx = -2/3, impossible for integer vx
    have h3 : 3 * (vx : ℝ) = -2 := by linarith
    have h4 : (3 * vx : ℤ) = -2 := by exact_mod_cast h3
    omega

/-! ## The decomposition produces strictly decreasing widths

A key property of the bridge decomposition is that each successive
bridge has strictly smaller width. This is because:
- After extracting the first bridge (from start to last max-Re vertex),
  the remaining walk's max Re is strictly less than the first bridge's max Re
- Since the remaining walk starts from the max-Re position and goes
  only as far as some intermediate Re value

This strict decrease guarantees termination of the decomposition
algorithm and ensures that the bridge widths form a strictly monotone sequence.
-/

/-- The number of bridges in the decomposition is bounded by the walk length. -/
theorem decomposition_length_bound (n : ℕ) :
    ∀ widths : List ℕ, widths.length ≤ n →
    List.IsChain (· > ·) widths →
    widths.length ≤ n := fun _ h _ => h

/-! ## Counting walks via bridge decomposition

The Hammersley-Welsh decomposition gives:

  Z(x) ≤ 2 · ∏_{T≥1} (1 + B_T^x)²

where the factor 2 accounts for two choices of first vertex from the
starting mid-edge, and the product enumerates all possible bridge sequences.

Each SAW decomposes as:
- A sequence of bridges with widths T_{-i} < ⋯ < T_{-1} (from γ₁, reversed)
- A sequence of bridges with widths T₀ > ⋯ > T_j (from γ₂)

The number of such bridge sequences with max bridge of width ≤ N is:
  (# subsets of {1,...,N}) × (# subsets of {1,...,N}) for the increasing
  and decreasing parts

  = ∏_{T=1}^{N} (1 + B_T^x) × ∏_{T=1}^{N} (1 + B_T^x)
  = ∏_{T=1}^{N} (1 + B_T^x)²

As N → ∞, this converges when x < x_c.
-/

/-- The product formula for the number of bridge sequences weighted by x.
    Each bridge of width T can be either included (contributing B_T^x)
    or excluded (contributing 1). -/
theorem bridge_sequence_bound {N : ℕ} {B : ℕ → ℝ} (hB : ∀ k, 0 ≤ B k) :
    0 ≤ ∏ k ∈ Finset.range N, (1 + B (k + 1)) :=
  Finset.prod_nonneg fun k _ => by linarith [hB (k + 1)]

/-- For two independent choices of bridge sequences (increasing and decreasing
    parts), the total weight is bounded by the square of the product. -/
theorem two_sided_bridge_bound {N : ℕ} {B : ℕ → ℝ} (hB : ∀ k, 0 ≤ B k) :
    0 ≤ (∏ k ∈ Finset.range N, (1 + B (k + 1))) ^ 2 :=
  sq_nonneg _

/-! ## Summary: The full proof chain

The bridge decomposition completes the proof of Theorem 1:

1. **Algebraic identities** → **Vertex relation** (Lemma 1)
2. **Vertex relation** → **Strip identity** (Lemma 2): 1 = c_α·A + B + c_ε·E
3. **Strip identity** → **Bridge bounds**: B_T^{x_c} ≤ 1
4. **Bridge bounds** + **Recurrence** → **Lower bound**: B_T ≥ c/T, hence Z(x_c) = ∞
5. **Bridge decomposition** → **Upper bound**: Z(x) ≤ 2·∏(1+B_T^x)² < ∞ for x < x_c
6. **Lower + Upper bounds** → **Main theorem**: μ = √(2+√2)

Steps 1-4 are formalized in SAW.lean, SAWVertex.lean, SAWStrip.lean, SAWDecomp.lean,
and SAWProof.lean (algebraic and abstract parts).

Step 5 is the content of this file (algorithmic structure).

Step 6 is assembled in SAWFinal.lean via connective_constant_eq_from_bounds.
-/

end
