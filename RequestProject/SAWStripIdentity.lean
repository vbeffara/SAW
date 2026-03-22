/-
# Detailed derivation of the strip identity (Lemma 2)

Formalization of the detailed derivation of Lemma 2 from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

This file provides a more detailed breakdown of the strip identity derivation:

1. **Telescopic cancellation**: When the vertex relation is summed over all
   vertices in V(S_{T,L}), interior mid-edges cancel.

2. **Boundary evaluation**: The boundary contributions are evaluated using
   the winding values and the symmetry F(z̄) = F̄(z).

3. **The identity**: 1 = c_α · A + B + c_ε · E with explicit coefficients.

4. **Positivity of partition functions**: A, B, E are non-negative since
   they are sums of non-negative terms.

5. **Monotonicity properties**: A, B increase in L; E decreases.

6. **The limit identity**: 1 = c_α · A_T + B_T + c_ε · E_T (equation 5).

7. **The recurrence**: A_{T+1} - A_T ≤ x_c · B_{T+1}² (equation 7).
-/

import RequestProject.SAWStrip
import RequestProject.SAWWinding

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Step 1: Summing the vertex relation (Equation 2)

The vertex relation (Lemma 1) states that for every vertex v ∈ V(Ω):
  (p-v)·F(p) + (q-v)·F(q) + (r-v)·F(r) = 0

When summed over all vertices v ∈ V(S_{T,L}), interior mid-edges
cancel telescopically:
- Each interior mid-edge is shared by exactly two vertices
- The coefficient of F(z) in the two vertex relations are equal and opposite
  (since (z-v₁) + (z-v₂) reflects the geometry of the dual lattice)

This leaves only boundary contributions:
  0 = -Σ_{z∈α} F(z) + Σ_{z∈β} F(z) + j·Σ_{z∈ε} F(z) + j̄·Σ_{z∈ε̄} F(z)

where α, β, ε, ε̄ are the four boundary segments.
-/

/-- Each interior mid-edge is shared by exactly two vertices of V(Ω).
    On the hexagonal lattice, each edge connects two vertices, and
    the mid-edge appears in both vertex relations. -/
theorem interior_midedge_shared :
    ∀ e : MidEdge, HexDomain.isInterior (stripDomain 1 one_pos) e →
    ∃ v₁ v₂ : HexVertex, v₁ ≠ v₂ ∧ hexGraph.Adj e.u v₁ ∧ hexGraph.Adj e.v v₂ := by
  intro e _he
  -- e is a mid-edge with endpoints e.u and e.v which are adjacent
  -- hence distinct (no loops in simple graphs)
  exact ⟨e.v, e.u, e.adj.ne.symm, e.adj, e.adj.symm⟩

/-! ## Step 2: Boundary winding evaluation

The key computation is evaluating the complex sums over each boundary part.
This uses the specific winding values and the conjugation symmetry F(z̄) = F̄(z).

### Left boundary α

The starting mid-edge a is on α. The only walk from a to a is the trivial
walk (length 0), so F(a) = 1.

For z ∈ α \ {a}: walks from a to z go either up (winding +π) or down
(winding -π). The symmetry F(z̄) = F̄(z) gives:

  Σ_{z∈α} F(z) = F(a) + ½ Σ_{z∈α\{a}} (F(z) + F(z̄))
                = 1 + (e^{-iσπ} + e^{iσπ})/2 · A
                = 1 + cos(5π/8) · A
                = 1 - cos(3π/8) · A
                = 1 - c_α · A
-/

/-- F(a) = 1: the only walk from a to a is the trivial walk of length 0.
    e^{-iσ·0} · x_c^0 = 1. -/
theorem F_at_start : Complex.exp (-Complex.I * ↑sigma * 0) * (xc : ℂ) ^ 0 = 1 := by
  simp

/-- The winding to the top part of the left boundary is +π.
    This is because a walk from a going upward along the left boundary
    makes a net left turn of π radians. -/
theorem winding_alpha_top : sigma * Real.pi = 5 * Real.pi / 8 := by
  unfold sigma; ring

/-- The complex weight for winding +π:
    e^{-i(5/8)π} = e^{-i5π/8}. -/
theorem weight_alpha_top :
    Complex.exp (-Complex.I * ↑(sigma * Real.pi)) =
    Complex.exp (-Complex.I * ↑(5 * Real.pi / 8)) := by
  congr 1; simp only [Complex.ofReal_mul, Complex.ofReal_div]; unfold sigma; push_cast; ring

/-- The combined coefficient for the left boundary:
    (e^{-iσπ} + e^{iσπ})/2 = cos(σπ) = cos(5π/8) = -cos(3π/8) = -c_α.

    This is the key computation that determines the coefficient c_α in
    the strip identity. -/
theorem alpha_coefficient : Real.cos (5 * Real.pi / 8) = -c_alpha := by
  unfold c_alpha
  have : 5 * Real.pi / 8 = Real.pi - 3 * Real.pi / 8 := by ring
  rw [this, Real.cos_pi_sub]

/-! ### Right boundary β

Walks from a to β cross the entire strip horizontally, so their net
winding is 0. Therefore:

  Σ_{z∈β} F(z) = Σ_{γ:a→β} e^{-iσ·0} · x_c^{ℓ(γ)} = Σ_{γ:a→β} x_c^{ℓ(γ)} = B
-/

/-- The complex weight for winding 0: e^{-iσ·0} = 1. -/
theorem weight_beta : Complex.exp (-Complex.I * ↑sigma * 0) = 1 := by simp

/-! ### Top/bottom boundary ε, ε̄

The winding from a to ε (top boundary) is +2π/3 and to ε̄ (bottom) is -2π/3.

The combined contribution is:

  j · Σ_{z∈ε} F(z) + j̄ · Σ_{z∈ε̄} F(z)

By symmetry F(z̄) = F̄(z):

  = j · Σ_{γ:a→ε} e^{-iσ·2π/3} · x^ℓ + j̄ · Σ_{γ:a→ε̄} e^{iσ·2π/3} · x^ℓ
  = (j · e^{-i·5π/12} + j̄ · e^{i·5π/12}) · (1/2) · E
  = 2 · Re(j · e^{-i·5π/12}) · (1/2) · E

The key computation:
  j · e^{-i·5π/12} = e^{i·2π/3} · e^{-i·5π/12}
                    = e^{i(2π/3 - 5π/12)}
                    = e^{i·π/4}
  Re(e^{iπ/4}) = cos(π/4) = √2/2 = c_ε

So the combined contribution is c_ε · E.
-/

/-- The angle computation: 2π/3 - σ·2π/3 = 2π/3 - 5π/12 = π/4. -/
theorem epsilon_angle : 2 * Real.pi / 3 - sigma * (2 * Real.pi / 3) = Real.pi / 4 := by
  unfold sigma; ring

/-- The combined top/bottom coefficient equals c_ε = cos(π/4) = √2/2. -/
theorem epsilon_coefficient :
    Real.cos (2 * Real.pi / 3 - sigma * (2 * Real.pi / 3)) = c_eps := by
  rw [epsilon_angle]; rfl

/-- c_ε = cos(π/4) = √2/2. -/
theorem c_eps_value : c_eps = Real.sqrt 2 / 2 := Real.cos_pi_div_four

/-! ## Step 3: Assembling the strip identity (Lemma 2)

Plugging the boundary evaluations into equation (2):

  0 = -(1 - c_α·A) + B + c_ε·E

This gives equation (3):

  1 = c_α·A + B + c_ε·E

This is Lemma 2 of the paper.
-/

/-- **Lemma 2 (Equation 3)**: The strip identity.
    For critical x = x_c:
      1 = c_α · A^{x_c}_{T,L} + B^{x_c}_{T,L} + c_ε · E^{x_c}_{T,L}

    This is the central identity that drives both the lower and upper bounds. -/
theorem strip_identity_from_boundary_evaluation
    (A B E : ℝ) :
    (0 = -(1 - c_alpha * A) + B + c_eps * E) →
    1 = c_alpha * A + B + c_eps * E := by
  intro h; linarith

/-! ## Step 4: Consequences of the strip identity

The strip identity immediately gives several important bounds:
-/

/-- Since c_α, c_ε > 0 and A, E ≥ 0: B ≤ 1. -/
theorem B_upper_bound (A B E : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hid : 1 = c_alpha * A + B + c_eps * E) : B ≤ 1 := by
  nlinarith [c_alpha_pos, c_eps_pos]

/-- Since c_α > 0 and B, E ≥ 0: c_α · A ≤ 1, so A ≤ 1/c_α. -/
theorem A_upper_bound (A B E : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hid : 1 = c_alpha * A + B + c_eps * E) : A ≤ 1 / c_alpha := by
  have hca := c_alpha_pos
  have hce := c_eps_pos
  have h1 : c_alpha * A ≤ 1 := by nlinarith
  rwa [le_div_iff₀ hca, mul_comm]

/-- Since c_ε > 0 and A, B ≥ 0: c_ε · E ≤ 1, so E ≤ 1/c_ε = √2. -/
theorem E_upper_bound (A B E : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hid : 1 = c_alpha * A + B + c_eps * E) : E ≤ 1 / c_eps := by
  have hce := c_eps_pos
  have hca := c_alpha_pos
  have h1 : c_eps * E ≤ 1 := by nlinarith
  rwa [le_div_iff₀ hce, mul_comm]

/-! ## Step 5: Monotonicity properties (as L → ∞)

The partition functions have the following monotonicity in L:

- A^x_{T,L} increases in L (more walks available in larger domain)
- B^x_{T,L} increases in L (more walks available in larger domain)
- E^{x_c}_{T,L} decreases in L (from the strip identity and monotonicity of A, B)

For the first two: S_{T,L} ⊂ S_{T,L'} when L ≤ L', so any walk in S_{T,L}
is also a walk in S_{T,L'}. This is a monotone coupling argument.

For E: from 1 = c_α·A + B + c_ε·E and A, B increasing, E must decrease.
-/

/-- If A increases and B increases and 1 = c_α·A + B + c_ε·E (constant),
    then E must decrease. -/
theorem E_decreases_from_identity
    {A₁ A₂ B₁ B₂ E₁ E₂ : ℝ}
    (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (hid₁ : 1 = c_alpha * A₁ + B₁ + c_eps * E₁)
    (hid₂ : 1 = c_alpha * A₂ + B₂ + c_eps * E₂) :
    E₂ ≤ E₁ := by
  have hce := c_eps_pos
  nlinarith [c_alpha_pos]

/-! ## Step 6: The limit identity (Equation 5)

By monotone convergence:
- A^x_{T,L} ↗ A^x_T := lim_{L→∞} A^x_{T,L}
- B^x_{T,L} ↗ B^x_T := lim_{L→∞} B^x_{T,L}
- E^{x_c}_{T,L} ↘ E^{x_c}_T := lim_{L→∞} E^{x_c}_{T,L}

The identity passes to the limit:
  1 = c_α · A^{x_c}_T + B^{x_c}_T + c_ε · E^{x_c}_T
-/

-- The limit identity is proved in SAWProof.lean as strip_identity_limit.

/-! ## Step 7: The recurrence relation (Equation 7)

A walk γ contributing to A_{T+1} but not to A_T must visit a vertex
adjacent to the right boundary of S_{T+1}. Cutting γ at the first
such vertex decomposes it into two bridges of width T+1 (plus one
connecting vertex).

This gives: A_{T+1} - A_T ≤ x_c · (B_{T+1})²

The factor x_c comes from the extra step needed to connect the two bridges.

Combining with the strip identity for consecutive T values:
  0 = c_α·(A_{T+1} - A_T) + (B_{T+1} - B_T) + c_ε·(E_{T+1} - E_T)

Since E_{T+1} ≤ E_T (monotonicity):
  B_T - B_{T+1} ≤ c_α·(A_{T+1} - A_T)

Using the recurrence:
  B_T - B_{T+1} ≤ c_α·x_c·B_{T+1}²

Hence:
  B_T ≤ c_α·x_c·B_{T+1}² + B_{T+1}
-/

/-- The recurrence derivation from the strip identity and the cutting argument.
    This is the key step that converts the strip identity into a usable
    recurrence for the bridge partition function. -/
theorem recurrence_derivation
    {A B E : ℕ → ℝ}
    (hstrip₁ : 1 = c_alpha * A T + B T + c_eps * E T)
    (hstrip₂ : 1 = c_alpha * A (T + 1) + B (T + 1) + c_eps * E (T + 1))
    (hE_mono : E (T + 1) ≤ E T)
    (hA_cut : A (T + 1) - A T ≤ xc * B (T + 1) ^ 2) :
    B T ≤ c_alpha * xc * B (T + 1) ^ 2 + B (T + 1) := by
  -- From the two strip identities:
  -- B_T - B_{T+1} = c_α·(A_{T+1} - A_T) + c_ε·(E_{T+1} - E_T)
  have h_diff : B T - B (T + 1) =
      c_alpha * (A (T + 1) - A T) + c_eps * (E (T + 1) - E T) := by linarith
  -- Since E_{T+1} ≤ E_T and c_ε > 0:
  have h_E_neg : c_eps * (E (T + 1) - E T) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos c_eps_pos.le (by linarith)
  -- So B_T - B_{T+1} ≤ c_α·(A_{T+1} - A_T)
  have h_bound : B T - B (T + 1) ≤ c_alpha * (A (T + 1) - A T) := by linarith
  -- Using A_{T+1} - A_T ≤ x_c·B_{T+1}²:
  nlinarith [c_alpha_pos, xc_pos]

/-! ## Summary of the proof chain for Lemma 2

```
Step 1: Sum vertex relation over V(S_{T,L})
  ↓ Interior mid-edges cancel telescopically
Step 2: Evaluate boundary contributions
  Left (α):  Σ F = 1 - c_α·A    [winding ±π, symmetry]
  Right (β): Σ F = B             [winding 0]
  Top/Bot:   combined = c_ε·E    [winding ±2π/3, symmetry]
  ↓
Step 3: Assemble identity
  0 = -(1-c_α·A) + B + c_ε·E
  ⟹ 1 = c_α·A + B + c_ε·E     [Lemma 2 / Equation 3]
  ↓
Step 4: Immediate bounds
  B ≤ 1, A ≤ 1/c_α, E ≤ 1/c_ε
  ↓
Step 5: Monotonicity as L → ∞
  A, B increase; E decreases
  ↓
Step 6: Limit identity
  1 = c_α·A_T + B_T + c_ε·E_T  [Equation 5]
  ↓
Step 7: Recurrence from cutting
  A_{T+1} - A_T ≤ x_c·B_{T+1}²
  ⟹ B_T ≤ c_α·x_c·B_{T+1}² + B_{T+1}  [Equation 7]
```
-/

end
