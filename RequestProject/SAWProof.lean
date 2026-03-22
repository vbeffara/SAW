/-
# Proof of Theorem 1: The connective constant equals √(2+√2)

Detailed formalization of the proof of Theorem 1 from:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the hexagonal lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

This file contains the abstract proof structure, reducing the main theorem
to explicit combinatorial hypotheses.

## Proof overview

The proof establishes μ = √(2+√2) by showing:

**Lower bound (μ ≥ √(2+√2))**: Z(x_c) = ∞

Proved by case analysis:
- **Case 1**: If E_T^{x_c} > 0 for some T, then E_{T,L} is monotone
  decreasing in L with positive limit, so Z(x_c) ≥ Σ_L E_{T,L} = ∞.
- **Case 2**: If E_T^{x_c} = 0 for all T, then the strip identity
  simplifies to 1 = c_α·A_T + B_T. The recurrence
  B_T ≤ c_α·x_c·B_{T+1}² + B_{T+1} gives B_T ≥ c/T by induction,
  so Z(x_c) ≥ Σ_T B_T ≥ Σ_T c/T = ∞.

**Upper bound (μ ≤ √(2+√2))**: Z(x) < ∞ for x < x_c

The Hammersley-Welsh bridge decomposition gives an injection:
  SAWs → sequences of bridges with monotone widths
Hence Z(x) ≤ 2·∏_{T≥1} (1 + B_T^x)².
Since B_T^{x_c} ≤ 1 and bridges of width T have length ≥ T,
  B_T^x ≤ (x/x_c)^T for x < x_c.
The product converges since x/x_c < 1.
-/

import RequestProject.SAWDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## The lower bound: Z(x_c) = ∞

We formalize the case analysis that proves Z(x_c) = ∞.
-/

/-- **Case 1**: If a positive constant is summed infinitely often, the series diverges. -/
theorem case1_divergence {c : ℝ} (hc : 0 < c) :
    ¬ Summable (fun _ : ℕ => c) := by
  intro h
  have := h.tendsto_atTop_zero
  simp at this
  linarith

/-- **Case 2** of the lower bound: If E_T = 0 for all T, then
    1 = c_α·A_T + B_T for all T (strip identity with E = 0).
    The recurrence A_{T+1} - A_T ≤ x_c·B_{T+1}² combined with
    the simplified strip identity gives:
      B_T ≤ c_α·x_c·B_{T+1}² + B_{T+1}
    By quadratic_recurrence_lower_bound, B_T ≥ min(B_1, 1/(c_α·x_c)) / T.
    Hence Σ B_T = ∞.

    This uses the quadratic_recurrence_lower_bound from SAWDecomp.lean
    and the harmonic series divergence. -/
theorem case2_lower_bound
    {B : ℕ → ℝ}
    (hB_nn : ∀ T, 0 ≤ B T)
    (hB_recur : ∀ T, B T ≤ c_alpha * xc * B (T + 1) ^ 2 + B (T + 1))
    (hB1 : 0 < B 1) :
    ¬ Summable (fun T => B (T + 1)) :=
  case2_divergence hB_nn hB_recur hB1

/-! ## The complete lower bound argument

Combining Cases 1 and 2, we get the full lower bound Z(x_c) = ∞.
-/

/-- The full lower bound argument (Case 2 only, with E = 0 assumed).
    When E_T = 0 for all T, the strip identity simplifies to
    1 = c_α·A_T + B_T. Combined with the recurrence
    A_{T+1} - A_T ≤ x_c · B_{T+1}², we get
    B_T ≤ c_α·x_c·B_{T+1}² + B_{T+1},
    which gives B_T ≥ c/T and hence Σ B_T = ∞. -/
theorem lower_bound_abstract
    {A B E : ℕ → ℝ}
    (hA_nn : ∀ T, 0 ≤ A T) (hB_nn : ∀ T, 0 ≤ B T) (_hE_nn : ∀ T, 0 ≤ E T)
    (hstrip : ∀ T, 1 = c_alpha * A T + B T + c_eps * E T)
    (hrecur : ∀ T, A (T + 1) - A T ≤ xc * B (T + 1) ^ 2)
    (_hE_decr : ∀ T, E (T + 1) ≤ E T)
    (hB1 : 0 < B 1)
    (hE_all_zero : ∀ T, E T = 0) :
    ¬ Summable (fun T => B (T + 1)) := by
  -- In Case 2, E_T = 0 for all T.
  -- The strip identity simplifies to 1 = c_α·A_T + B_T.
  have hstrip' : ∀ T, 1 = c_alpha * A T + B T := by
    intro T; have := hstrip T; simp [hE_all_zero T] at this ⊢; linarith
  -- B_T ≤ 1 since A_T ≥ 0 and c_α > 0
  have hB_le : ∀ T, B T ≤ 1 := by
    intro T; nlinarith [hstrip' T, c_alpha_pos, hA_nn T]
  -- The recurrence: B_T ≤ c_α·x_c·B_{T+1}² + B_{T+1}
  have hB_recur : ∀ T, B T ≤ c_alpha * xc * B (T + 1) ^ 2 + B (T + 1) := by
    intro T
    have h1 := hstrip' T
    have h2 := hstrip' (T + 1)
    nlinarith [hrecur T, c_alpha_pos, xc_pos]
  exact case2_divergence hB_nn hB_recur hB1

/-! ## The upper bound: Z(x) < ∞ for x < x_c

The upper bound uses the Hammersley-Welsh bridge decomposition.
We formalize the abstract argument that reduces convergence to
the product ∏(1 + B_T^x)².
-/

/-- From the strip identity: B_T^{x_c} ≤ 1.
    Since 1 = c_α·A + B + c_ε·E with A, E ≥ 0 and c_α, c_ε > 0,
    we have B ≤ 1. -/
theorem bridge_upper_bound_from_identity {A B E : ℝ}
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hid : 1 = c_alpha * A + B + c_eps * E) :
    B ≤ 1 := bridge_bound_of_strip_identity hA hE hid

/-! ## Equation (3): The strip identity in detail

The strip identity (Lemma 2, Equation (3)):
  1 = c_α · A^{x_c}_{T,L} + B^{x_c}_{T,L} + c_ε · E^{x_c}_{T,L}

is derived by summing the vertex relation over V(S_{T,L}).

The proof involves three key steps:

### Step 1: Sum the vertex relation
  0 = Σ_v [(p_v - v)F(p_v) + (q_v - v)F(q_v) + (r_v - v)F(r_v)]

### Step 2: Interior cancellation
  Interior mid-edges cancel telescopically (each appears in two vertex
  relations with opposite signs), leaving only boundary contributions:
  0 = -Σ_{z∈α} F(z) + Σ_{z∈β} F(z) + j·Σ_{z∈ε} F(z) + j̄·Σ_{z∈ε̄} F(z)

### Step 3: Evaluate boundary sums using winding values
  - Σ_{z∈α} F(z) = 1 - c_α · A (using F(a) = 1 and winding ±π)
  - Σ_{z∈β} F(z) = B (winding 0)
  - j·Σ_{z∈ε} F(z) + j̄·Σ_{z∈ε̄} F(z) = c_ε · E (winding ±2π/3)

Plugging into Step 2: 0 = -(1 - c_α·A) + B + c_ε·E, giving 1 = c_α·A + B + c_ε·E.
-/

/-- The left boundary evaluation (from the paper):
    Σ_{z∈α} F(z) = F(a) + Σ_{z∈α\{a}} F(z)
                  = 1 + cos(σπ) · A
                  = 1 - c_α · A

    The winding to the top part of α is +π and to the bottom is -π.
    Since σ = 5/8: exp(-i·5π/8) + exp(i·5π/8) = 2cos(5π/8) = -2cos(3π/8) = -2c_α.
    The average over the pair (z, z̄) gives factor cos(5π/8) = -c_α.
    F(a) = 1 since the only walk from a to a is trivial (length 0). -/
theorem left_boundary_evaluation :
    Real.cos (sigma * Real.pi) = -c_alpha := left_boundary_coeff

/-- The right boundary evaluation: Σ_{z∈β} F(z) = B.
    The winding from a to any mid-edge in β is 0, so exp(0) = 1.
    The sum is simply the partition function B. -/
theorem right_boundary_evaluation :
    Real.cos (sigma * 0) = 1 := right_boundary_coeff

/-! ## The recurrence relation: A_{T+1} - A_T ≤ x_c · B_{T+1}²

From the paper (Section 3):
"A walk γ entering into the count of A_{T+1} and not into A_T has to
visit some vertex adjacent to the right edge of S_{T+1}. Cutting γ at
the first such point, we uniquely decompose it into two walks crossing
S_{T+1} (bridges), which together are one step longer than γ."

This gives the inequality:
  A_{T+1}^{x_c} - A_T^{x_c} ≤ x_c · (B_{T+1}^{x_c})²

The factor x_c comes from the extra step needed to connect the two bridges.
-/

/-- **Equation (7)**: The recurrence for the A partition function.
    Walks in A_{T+1} but not in A_T must cross through the right boundary
    of S_{T+1}, decomposing into two bridges of width T+1.

    Formally stated as an abstract inequality. -/
theorem recurrence_inequality_abstract
    {A B : ℕ → ℝ} {x : ℝ}
    (_hA_nn : ∀ T, 0 ≤ A T)
    (_hB_nn : ∀ T, 0 ≤ B T)
    (_hx : 0 < x)
    (hdecomp : ∀ T, A (T + 1) - A T ≤ x * B (T + 1) ^ 2) :
    ∀ T, A (T + 1) ≤ A T + x * B (T + 1) ^ 2 := by
  intro T; linarith [hdecomp T]

/-! ## Passage to the infinite strip (Equation (5))

As L → ∞:
- (A^x_{T,L})_{L>0} is increasing in L and bounded → converges to A^x_T
- (B^x_{T,L})_{L>0} is increasing in L and bounded → converges to B^x_T
- (E^{x_c}_{T,L})_{L>0} is decreasing → converges to E^{x_c}_T

Monotonicity of A and B follows from: expanding L gives more walks.
Boundedness follows from: the strip identity 1 = c_α·A + B + c_ε·E
and non-negativity of all terms.

Monotonicity of E (decreasing): the strip identity gives
  c_ε·E_{T,L} = 1 - c_α·A_{T,L} - B_{T,L}
  and A_{T,L}, B_{T,L} are increasing in L, so E_{T,L} is decreasing.
-/

/-
PROBLEM
Monotone convergence for bounded increasing sequences.
    This is used for A^x_{T,L} and B^x_{T,L} as L → ∞.

PROVIDED SOLUTION
Use Real.tendsto_of_bddAbove_monotone (or tendsto_of_monotone_of_bddAbove, whatever the name is in current Mathlib). The sequence a is monotone and bounded above by M. So it converges to L = iSup a (or sSup of the range). The bound L ≤ M follows from ciSup_le (since a n ≤ M for all n).
-/
theorem monotone_bounded_converges {a : ℕ → ℝ} {M : ℝ}
    (ha_mono : Monotone a) (ha_bound : ∀ n, a n ≤ M) :
    ∃ L : ℝ, Filter.Tendsto a Filter.atTop (nhds L) ∧ L ≤ M := by
      exact ⟨ _, tendsto_atTop_ciSup ha_mono <| show BddAbove ( Set.range a ) from ⟨ M, by rintro x ⟨ n, rfl ⟩ ; exact ha_bound n ⟩, by exact ciSup_le ha_bound ⟩

/-
PROBLEM
Monotone convergence for bounded decreasing sequences.
    This is used for E^{x_c}_{T,L} as L → ∞.

PROVIDED SOLUTION
Use the antitone version: tendsto_of_antitone combined with BddBelow. The sequence a is antitone and bounded below by m, so it converges to L = iInf a. The bound m ≤ L follows from le_ciInf since m ≤ a n for all n.
-/
theorem antitone_bounded_converges {a : ℕ → ℝ} {m : ℝ}
    (ha_anti : Antitone a) (ha_bound : ∀ n, m ≤ a n) :
    ∃ L : ℝ, Filter.Tendsto a Filter.atTop (nhds L) ∧ m ≤ L := by
      -- Since $a$ is antitone and bounded below, it converges to its infimum.
      have h_conv : Filter.Tendsto a Filter.atTop (nhds (sInf {a n | n : ℕ})) := by
        exact tendsto_atTop_ciInf ha_anti ⟨ m, Set.forall_mem_range.mpr ha_bound ⟩
      generalize_proofs at *; (
      exact ⟨ _, h_conv, le_csInf ⟨ _, ⟨ 0, rfl ⟩ ⟩ fun x hx => by rcases hx with ⟨ n, rfl ⟩ ; exact ha_bound n ⟩)

/-! ## The strip identity persists in the limit

Since A_L → A, B_L → B, E_L → E (all monotone/antitone and bounded),
the identity 1 = c_α·A_L + B_L + c_ε·E_L passes to the limit:
  1 = c_α·A + B + c_ε·E
-/

/-
PROBLEM
The strip identity passes to the limit by continuity of addition
    and multiplication.

PROVIDED SOLUTION
The constant sequence 1 = c_alpha * A n + B n + c_eps * E n converges to both 1 (since it's constant) and c_alpha * a + b + c_eps * e (by the sum/product of limits). Use tendsto_nhds_unique to conclude 1 = c_alpha * a + b + c_eps * e.

The limit of c_alpha * A n + B n + c_eps * E n is c_alpha * a + b + c_eps * e by:
- Tendsto.const_mul or Tendsto.mul_left for c_alpha * A n → c_alpha * a
- Tendsto.add for the sum
- Similarly for c_eps * E n → c_eps * e

Then the constant function n ↦ 1 converges to 1. By hid, these are the same function, so 1 = c_alpha * a + b + c_eps * e by tendsto_nhds_unique.
-/
theorem strip_identity_limit
    {A B E : ℕ → ℝ} {a b e : ℝ}
    (hA_lim : Filter.Tendsto A Filter.atTop (nhds a))
    (hB_lim : Filter.Tendsto B Filter.atTop (nhds b))
    (hE_lim : Filter.Tendsto E Filter.atTop (nhds e))
    (hid : ∀ n, 1 = c_alpha * A n + B n + c_eps * E n) :
    1 = c_alpha * a + b + c_eps * e := by
      exact tendsto_nhds_unique ( tendsto_const_nhds.congr fun n => by rw [hid n] ) ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.mul hA_lim ) hB_lim ) ( tendsto_const_nhds.mul hE_lim ) )

/-! ## Summary of the proof chain

The complete proof of Theorem 1 (μ = √(2+√2)) follows this chain:

```
Algebraic identities (SAW.lean):
  pair_cancellation: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
  triplet_cancellation: 1 + x_c·j·conj(λ) + x_c·conj(j)·λ = 0
        ↓
Vertex relation (SAWVertex.lean):
  (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0 at x = x_c, σ = 5/8
        ↓
Strip identity (SAWStrip.lean):
  1 = c_α·A_{T,L} + B_{T,L} + c_ε·E_{T,L}
        ↓ (monotone convergence as L → ∞)
Infinite strip identity:
  1 = c_α·A_T + B_T + c_ε·E_T
        ↓
Bridge bounds:
  B_T^{x_c} ≤ 1 (upper, from strip identity + non-negativity)
  B_T^{x_c} ≥ c/T (lower, from quadratic recurrence, SAWDecomp.lean)
        ↓
Lower bound (SAWProof.lean):
  Z(x_c) = ∞ (either via E > 0 or B_T ≥ c/T)
  → μ ≥ 1/x_c = √(2+√2)
        ↓
Upper bound (SAWBridge.lean):
  Hammersley-Welsh: Z(x) ≤ 2·∏(1+B_T^x)²
  Bridge scaling: B_T^x ≤ (x/x_c)^T for x < x_c
  → Z(x) < ∞ for x < x_c
  → μ ≤ 1/x_c = √(2+√2)
        ↓
Main theorem (SAWBridge.lean):
  connective_constant_eq_from_bounds
  → μ = √(2+√2)
```

The remaining gaps are the combinatorial infrastructure:
1. Bridge decomposition injection (SAWs → bridge sequences)
2. Bridge-to-partition connection (bridges contribute to Z)
3. SAWs restricted to strip domains (formal definitions)

These require formalizing the full graph-theoretic machinery of
walks restricted to domains, which is a substantial project.
-/

end
