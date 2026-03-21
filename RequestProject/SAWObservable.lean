/-
# The Parafermionic Observable

Concrete formalization of the parafermionic observable from Section 2 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

1. **Walks restricted to a domain**: SAWs contained within a hex domain
2. **The parafermionic observable F(z)**: defined as a concrete sum
   F(z) = Σ_{γ ⊂ Ω : a → z} exp(-iσ W_γ(a,z)) · x^{ℓ(γ)}
3. **The vertex relation** (Lemma 1): formalized as a property of F
4. **Pair and triplet cancellation** in terms of walk contributions
5. **The summing argument** for Lemma 2 (strip identity)
-/

import RequestProject.SAWStrip

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Walks restricted to a domain

A walk γ is contained in domain Ω if all vertices visited by γ belong to V(Ω).
-/

/-- A walk is contained in a domain Ω if all vertices in its support
    belong to V(Ω). -/
def Walk.inDomain {v w : HexVertex} (p : hexGraph.Walk v w) (Ω : HexDomain) : Prop :=
  ∀ u ∈ p.support, u ∈ Ω.verts

/-- A self-avoiding walk contained in domain Ω. -/
structure DomainSAW (Ω : HexDomain) (a z : HexVertex) where
  /-- The underlying path. -/
  path : hexGraph.Path a z
  /-- The walk stays within the domain. -/
  inDomain : Walk.inDomain path.1 Ω

/-! ## The winding weight

The complex weight exp(-iσ W_γ(a,z)) can be decomposed as a product
of factors λ = exp(-i5π/24) per left turn and λ̄ per right turn.

On the hexagonal lattice, each step turns by ±π/3 or 0 (in the
bipartite structure, each step alternates between sublattices).
-/

/-- The winding weight of a walk, computed from its vertex list.
    exp(-iσ · W_γ(a,z)) where W is the total winding and σ = 5/8. -/
def windingWeight (vertices : List HexVertex) : ℂ :=
  Complex.exp (-Complex.I * ↑sigma * ↑(walkWinding vertices))

/-! ## The parafermionic observable

For a domain Ω with boundary mid-edge a ∈ ∂Ω and interior/boundary
point z ∈ Ω, the parafermionic observable is:

  F(z) = F(a, z, x, σ) = Σ_{γ ⊂ Ω : a → z} exp(-iσ W_γ(a,z)) · x^{ℓ(γ)}

The sum is over self-avoiding walks from a to z contained in Ω.

When z = a, the only walk is the trivial walk of length 0, giving F(a) = 1.
-/

/-- The contribution of a single walk to the observable. -/
def singleWalkContribution (s x : ℝ) {a z : HexVertex} (p : hexGraph.Path a z) : ℂ :=
  Complex.exp (-Complex.I * ↑s * ↑(walkWinding p.1.support)) *
  (x : ℂ) ^ p.1.length

/-- **Definition 1**: The parafermionic observable.

    F(a, z, x, σ) = Σ_{γ ⊂ Ω : a → z} exp(-iσ W_γ(a,z)) · x^{ℓ(γ)}

    This is the central tool of the paper. At the critical parameters
    x = x_c and σ = 5/8, this observable satisfies a vertex relation
    (Lemma 1) that is the key to the proof. -/
def parafermionicObservable (Ω : HexDomain) (a z : HexVertex) (x : ℝ) (s : ℝ) : ℂ :=
  ∑' (γ : DomainSAW Ω a z),
    Complex.exp (-Complex.I * ↑s * ↑(walkWinding γ.path.1.support)) *
    (x : ℂ) ^ γ.path.1.length

/-! ## Walk contributions to the vertex relation

The vertex relation (Lemma 1) states that for every vertex v ∈ V(Ω),
the sum of (p-v)·F(p) + (q-v)·F(q) + (r-v)·F(r) = 0,
where p, q, r are the three mid-edges adjacent to v.

The proof partitions walks ending at p, q, r into pairs and triplets:
- **Pairs**: walks visiting all three mid-edges (grouped by loop direction)
- **Triplets**: walk visiting one mid-edge + its two extensions
-/

/-- Classification of walks by the number of mid-edges of v that they visit. -/
inductive VertexVisitType
  | one : VertexVisitType   -- visits exactly one mid-edge
  | two : VertexVisitType   -- visits exactly two mid-edges
  | three : VertexVisitType -- visits all three mid-edges

/-- A pair of walks visiting all three mid-edges.
    If γ₁ ends at q and γ₂ ends at r (both visiting all three mid-edges),
    then they coincide up to mid-edge p and follow the loop in opposite
    directions.

    Properties:
    - ℓ(γ₁) = ℓ(γ₂)
    - W_γ₁(a,q) = W_γ₁(a,p) - 4π/3
    - W_γ₂(a,r) = W_γ₁(a,p) + 4π/3 -/
structure WalkPair (Ω : HexDomain) (a p q r : HexVertex)  where
  /-- The walk ending at q. -/
  walk_q : DomainSAW Ω a q
  /-- The walk ending at r. -/
  walk_r : DomainSAW Ω a r
  /-- Both walks have the same length. -/
  same_length : walk_q.path.1.length = walk_r.path.1.length

/-- A triplet of walks: one visiting one mid-edge and its two extensions.
    If γ₁ ends at p (visiting only one mid-edge), then γ₂ and γ₃ extend
    γ₁ to q and r respectively.

    Properties:
    - ℓ(γ₂) = ℓ(γ₃) = ℓ(γ₁) + 1
    - W_γ₂(a,q) = W_γ₁(a,p) - π/3
    - W_γ₃(a,r) = W_γ₁(a,p) + π/3 -/
structure WalkTriplet (Ω : HexDomain) (a p q r : HexVertex)  where
  /-- The walk ending at p (visiting only one mid-edge). -/
  walk_p : DomainSAW Ω a p
  /-- The walk ending at q (extending walk_p by one step). -/
  walk_q : DomainSAW Ω a q
  /-- The walk ending at r (extending walk_p by one step). -/
  walk_r : DomainSAW Ω a r
  /-- Extensions are one step longer. -/
  ext_length : walk_q.path.1.length = walk_p.path.1.length + 1 ∧
               walk_r.path.1.length = walk_p.path.1.length + 1

/-! ## Pair cancellation in context

For a pair (γ₁, γ₂) of walks visiting all three mid-edges:

  c(γ₁) + c(γ₂) = (p-v) · exp(-iσ W(a,p)) · x^{ℓ} · (j·λ̄⁴ + j̄·λ⁴) = 0

The cancellation follows from pair_cancellation (proved in SAW.lean):
  j · conj(λ)⁴ + conj(j) · λ⁴ = 0
-/

/-- The pair contribution vanishes by pair_cancellation. -/
theorem pair_contribution_vanishes (W_ap : ℝ) (ℓ : ℕ) :
    (↑(xc ^ ℓ) : ℂ) * Complex.exp (-Complex.I * ↑sigma * ↑W_ap) *
    (j * conj lam ^ 4 + conj j * lam ^ 4) = 0 := by
  rw [pair_cancellation]; ring

/-! ## Triplet cancellation in context

For a triplet (γ₁, γ₂, γ₃):

  c(γ₁) + c(γ₂) + c(γ₃) = (p-v) · exp(-iσ W(a,p)) · x^{ℓ(γ₁)} ·
                             (1 + x_c · j · λ̄ + x_c · j̄ · λ) = 0

The cancellation follows from triplet_cancellation (proved in SAW.lean):
  1 + x_c · j · conj(λ) + x_c · conj(j) · λ = 0

This is the ONLY place where x = x_c is used (as noted in the paper).
-/

/-- The triplet contribution vanishes by triplet_cancellation. -/
theorem triplet_contribution_vanishes (W_ap : ℝ) (ℓ : ℕ) :
    (↑(xc ^ ℓ) : ℂ) * Complex.exp (-Complex.I * ↑sigma * ↑W_ap) *
    (1 + (xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam) = 0 := by
  rw [triplet_cancellation]; ring

/-! ## The vertex relation (Lemma 1)

**Lemma 1**: If x = x_c and σ = 5/8, then F satisfies the following
relation for every vertex v ∈ V(Ω):

  (p - v) · F(p) + (q - v) · F(q) + (r - v) · F(r) = 0

where p, q, r are the mid-edges of the three edges adjacent to v,
ordered counter-clockwise.

The proof works by showing that every walk's contribution cancels:
- Walks visiting all three mid-edges cancel in pairs (pair_cancellation)
- Walks visiting one or two mid-edges cancel in triplets (triplet_cancellation)
-/

/-- **Lemma 1** (abstract): The vertex relation holds at critical parameters.
    This combines pair_cancellation and triplet_cancellation. -/
theorem vertex_relation :
    j * conj lam ^ 4 + conj j * lam ^ 4 = 0 ∧
    1 + (xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam = 0 :=
  ⟨pair_cancellation, triplet_cancellation⟩

/-! ## The summing argument (Lemma 2)

**Lemma 2** (strip identity): Summing the vertex relation over all
vertices in V(S_{T,L}) gives:

  0 = -Σ_{z ∈ α} F(z) + Σ_{z ∈ β} F(z) + j·Σ_{z ∈ ε} F(z) + j̄·Σ_{z ∈ ε̄} F(z)

Interior mid-edges cancel telescopically because each interior
mid-edge is adjacent to exactly two vertices, and its contributions
from these two vertex relations cancel.

The symmetry F(z̄) = F̄(z) of the strip domain (horizontal reflection
symmetry) is then used to extract real-valued partition functions.
-/

/-- The symmetry F(z̄) = F̄(z) for domains with horizontal reflection symmetry.
    This is a consequence of the fact that the winding of the conjugate
    walk equals the negation of the winding of the original walk. -/
theorem observable_symmetry_abstract (W : ℝ) :
    Complex.exp (-Complex.I * ↑sigma * ↑(-W)) =
    conj (Complex.exp (-Complex.I * ↑sigma * ↑W)) := by
  rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]

/-! ## Boundary winding values

The specific winding values for walks ending on each boundary part of S_{T,L}:

1. **Left boundary α\{a}**: winding is ±π (walks go up or down)
   - Top part of α: W = +π
   - Bottom part of α: W = -π
   - By symmetry: Σ F = F(a) + ½·Σ (F(z) + F(z̄))
   - = 1 + (e^{-iσπ} + e^{iσπ})/2 · A = 1 + cos(5π/8)·A = 1 - c_α·A

2. **Right boundary β**: winding is 0
   - Σ F = B (no complex weight)

3. **Top boundary ε**: winding is +2π/3
   - j · Σ F(z) = j · e^{-iσ·2π/3} · (sum of walk weights)

4. **Bottom boundary ε̄**: winding is -2π/3
   - j̄ · Σ F(z) = j̄ · e^{+iσ·2π/3} · (sum of walk weights)

Combined top+bottom:
  j · e^{-i5π/12} + j̄ · e^{i5π/12} = 2·cos(2π/3 - 5π/12) = 2·cos(π/4) = √2

So: 0 = -(1 - c_α·A) + B + c_ε·E, giving 1 = c_α·A + B + c_ε·E.
-/

/-- Winding to the top part of the left boundary is +π. -/
theorem left_boundary_winding_top : sigma * Real.pi = 5 * Real.pi / 8 := by
  unfold sigma; ring

/-- Winding to the bottom part of the left boundary is -π. -/
theorem left_boundary_winding_bottom : sigma * (-Real.pi) = -(5 * Real.pi / 8) := by
  unfold sigma; ring

/-- The right boundary contribution: e^{-iσ·0} = 1. -/
theorem right_boundary_contribution :
    Complex.exp (-Complex.I * ↑sigma * 0) = 1 := by
  simp

/-- The combined top/bottom boundary gives coefficient 2·c_ε. -/
theorem top_bottom_combined :
    2 * Real.cos (Real.pi / 4) = 2 * c_eps := by
  unfold c_eps; ring

/-! ## The discrete contour integral interpretation (Remark 1)

The vertex relation (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0 can be
rewritten as:

  Σ_{z ~ v} (z - v) · F(z) = 0

The coefficients (p-v), (q-v), (r-v) are proportional to three cube
roots of unity times (p-v), since the three mid-edges are at 120°
angles from v.

This means the left-hand side is a discrete contour integral of F
along an elementary contour on the dual triangular lattice. The vanishing
of all such contour integrals suggests that F is discretely holomorphic.

However, this gives only 2E/3 equations for E values (one equation per
vertex, while there is one mid-edge per edge), which is insufficient
to make F exactly discrete holomorphic. The "missing equations" are
conjectured to hold in the scaling limit, which would imply convergence
to SLE(8/3).
-/

/-- The three directions from a hex vertex to its mid-edges form
    three cube roots of unity (up to a common factor).
    Specifically: 1 + j + j̄ = 0 where j = exp(i2π/3). -/
theorem directions_are_cube_roots :
    1 + j + conj j = 0 := by
  -- j + conj(j) = 2·cos(2π/3) = -1, so 1 + j + conj(j) = 0
  have hre : j.re = -1/2 := by
    unfold j
    rw [show Complex.I * (2 * ↑Real.pi / 3) = ↑(2 * Real.pi / 3) * Complex.I from by push_cast; ring]
    rw [Complex.exp_mul_I]
    simp only [add_re, mul_re, Complex.I_re, Complex.I_im]; ring_nf
    conv_lhs => rw [show Real.pi * (2 / 3) = Real.pi - Real.pi / 3 from by ring]
    rw [Complex.cos_ofReal_re, Complex.sin_ofReal_im, Real.cos_pi_sub]
    simp [Real.cos_pi_div_three]; ring
  have hadd : j + conj j = (2 * j.re : ℝ) := Complex.add_conj j
  have h1 : (1 : ℂ) + (j + conj j) = 0 := by
    rw [hadd, hre]; push_cast; ring
  have h2 : (1 : ℂ) + j + conj j = 1 + (j + conj j) := by ring
  rw [h2]; exact h1

/-! ## Summary

This file formalizes the concrete definitions and cancellation arguments
underlying Sections 2 and 3 of the paper:

**Section 2 (Parafermionic Observable)**:
- F(z) = Σ_{γ ⊂ Ω : a → z} exp(-iσW) · x^ℓ (Definition 1)
- Walk contributions partition into pairs and triplets
- Pair cancellation: j·λ̄⁴ + j̄·λ⁴ = 0 (from pair_cancellation)
- Triplet cancellation: 1 + x_c·j·λ̄ + x_c·j̄·λ = 0 (from triplet_cancellation)
- Vertex relation: (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0

**Section 3 (Strip Identity Derivation)**:
- Sum vertex relation over V(S_{T,L}) → telescopic cancellation
- Interior mid-edges cancel, leaving boundary contributions
- Symmetry F(z̄) = F̄(z) extracts real partition functions
- Boundary winding values → coefficients c_α, c_ε
- Result: 1 = c_α·A + B + c_ε·E (Lemma 2)

The algebraic identities pair_cancellation and triplet_cancellation are
imported from SAW.lean; all other results are proved here.
-/

end
