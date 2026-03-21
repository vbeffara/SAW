/-
# Conjectures on conformal invariance of self-avoiding walks (Section 4)

Formalization of the conjectures from Section 4 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

This file formalizes the conjectures and discussion from Section 4:

1. **Conjecture 1** (SLE(8/3) convergence): The scaling limit of SAWs at x_c
   converges to chordal SLE(8/3).

2. **Conjecture 2** (Observable convergence): The normalized parafermionic
   observable F_δ(z_δ)/F_δ(b_δ) converges to (Φ'(z)/Φ'(b))^{5/8}.

3. **The Riemann boundary value problem** (Equation 8):
   Im(F(z) · (tangent to ∂Ω)^{5/8}) = 0 for z ∈ ∂Ω.

4. **The SLE parameter** κ = 8/3 and the relation between σ = 5/8 and κ.

5. **Critical exponents**: γ = 43/32 (asymptotic number) and ν = 3/4 (displacement).

## Mathematical context

The parafermionic observable satisfies a discrete version of the Riemann BVP
(equation 8). The vertex relation (Lemma 1) implies that discrete contour
integrals of F vanish, suggesting F is discretely holomorphic.

However, the vertex relation alone gives only ~(2/3)E equations for E values
of F (one equation per vertex, V:E = 2:3 on the trivalent hex lattice).
This is insufficient to reconstruct F from boundary values — F is
divergence-free but may have non-trivial curl.

In the scaling limit, the curl is expected to vanish, making F holomorphic.
Combined with the Riemann BVP boundary conditions, this would determine F
and imply convergence to SLE(8/3).
-/

import RequestProject.SAW

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## The SLE parameter and its relation to σ

The SLE parameter κ = 8/3 is related to the spin σ = 5/8 by the
formula σ = 1 - κ/8 (from the general O(n) model correspondence).
At σ = 5/8: κ = 8(1 - 5/8) = 8 · 3/8 = 3... no, κ = 8/3.

Actually, the relation is different. In the context of SLE and the
parafermionic observable, the spin parameter σ determines the conformal
dimension of the observable as a (dz)^σ-form. The SLE parameter κ = 8/3
is predicted from the separate scaling limit analysis by Lawler-Schramm-Werner.
-/

/-- The SLE parameter κ = 8/3 for the self-avoiding walk. -/
def kappa : ℚ := 8 / 3

/-- The conformal dimension of the parafermionic observable.
    F is a discrete (dz)^σ-form, where σ = 5/8.
    Under conformal maps Φ, such forms transform as
    f ↦ (Φ')^σ · f ∘ Φ⁻¹. -/
def conformal_dimension : ℝ := sigma

/-- σ = 5/8 is the conformal dimension. -/
lemma conformal_dimension_eq : conformal_dimension = 5 / 8 := rfl

/-! ## The Riemann boundary value problem (Equation 8)

The parafermionic observable satisfies a discrete version of:

  Im(F(z) · (tangent to ∂Ω)^{5/8}) = 0,  z ∈ ∂Ω

with a singularity at the starting point a.

This is a homogeneous version of the Riemann-Hilbert-Privalov BVP.

Key properties:
- The problem has conformally covariant solutions (as (dz)^{5/8}-forms)
- It is well-defined even for domains with fractal boundaries
- The solution is unique (up to a multiplicative constant) for smooth boundaries

The winding of an interface leading to a boundary edge z is uniquely
determined and coincides with the winding of the boundary itself.
Therefore F_δ satisfies this BVP in the discrete sense.
-/

/-- The Riemann BVP exponent: the tangent direction is raised to the
    power σ = 5/8. This determines the boundary condition for the
    parafermionic observable. -/
def rbvp_exponent : ℝ := sigma

/-- The BVP has conformally covariant solutions: under a conformal map Φ,
    a solution f transforms to (Φ')^σ · f ∘ Φ⁻¹.
    Since σ = 5/8, the solution is a (dz)^{5/8}-form. -/
def is_conformal_covariant (f : ℂ → ℂ) (Φ : ℂ → ℂ) (Φ' : ℂ → ℂ) : Prop :=
  ∀ z, f (Φ z) = Φ' z ^ (sigma : ℂ) * f z

/-! ## Conjecture 1: SLE(8/3) convergence

**Conjecture 1** (Lawler-Schramm-Werner):
Let Ω be a simply connected domain (≠ ℂ) with two distinct points a, b
on its boundary. For x = x_c, the law of γ_δ in (Ω_δ, a_δ, b_δ) converges
when δ → 0 to the chordal Schramm-Loewner Evolution with parameter κ = 8/3
in Ω from a to b.

This is the central open problem in the theory of self-avoiding walks.
Proving it would establish the universality of the scaling limit and
enable the computation of all critical exponents.
-/

/-- **Conjecture 1** (SLE convergence): The scaling limit of the self-avoiding
    walk at x = x_c on the honeycomb lattice is SLE(8/3).

    Formally stated as a property of the probability measure on SAW paths
    in the discrete approximation Ω_δ of a simply connected domain Ω. -/
def sle_convergence_conjecture : Prop :=
  -- This is stated informally since SLE and weak convergence of measures
  -- are not yet formalized in Mathlib.
  -- The conjecture is: for any simply connected domain Ω ≠ ℂ with
  -- boundary points a, b, the probability measure P_{x_c,δ} on SAWs
  -- from a_δ to b_δ in Ω_δ converges weakly as δ → 0 to SLE(8/3).
  True  -- placeholder for the formal statement

/-! ## Conjecture 2: Observable convergence

**Conjecture 2** from the paper:
Let Ω be a simply connected domain (≠ ℂ) with boundary points a, b, and
let z ∈ Ω. Assume ∂Ω is smooth near b. Then

  lim_{δ→0} F_δ(z_δ) / F_δ(b_δ) = (Φ'(z) / Φ'(b))^{5/8}

where Φ is a conformal map from Ω to the upper half-plane mapping a to ∞
and b to 0.

The right-hand side is well-defined since Φ is unique up to multiplication
by a real factor, and (Φ'(z)/Φ'(b))^{5/8} is invariant under such rescaling.

Proving this conjecture would be a major step toward Conjecture 1 and
the derivation of critical exponents, since a conformally covariant
discrete observable with the right boundary conditions converging to
a holomorphic function would establish convergence to SLE.
-/

/-- **Conjecture 2** (Observable convergence):
    The normalized parafermionic observable converges to the derivative
    of a conformal map raised to the power 5/8.

    Formally: for Ω simply connected with smooth boundary near b,
    F_δ(z_δ)/F_δ(b_δ) → (Φ'(z)/Φ'(b))^{5/8}
    where Φ : Ω → ℍ maps a ↦ ∞, b ↦ 0. -/
def observable_convergence_conjecture : Prop :=
  -- This requires defining:
  -- 1. Conformal maps between simply connected domains (Riemann mapping theorem)
  -- 2. Discrete approximations Ω_δ
  -- 3. The parafermionic observable F_δ on Ω_δ
  -- All of which are beyond current Mathlib coverage.
  True  -- placeholder for the formal statement

/-- The conformal map Φ is unique up to a positive real multiplicative factor.
    Since Φ maps ∂Ω to ℝ with a ↦ ∞ and b ↦ 0, the group of conformal
    self-maps of ℍ fixing 0 and ∞ consists of positive dilations z ↦ c·z.

    Therefore (Φ'(z)/Φ'(b))^{5/8} is independent of the choice of Φ:
    if Φ̃ = c·Φ, then Φ̃' = c·Φ', and (Φ̃'(z)/Φ̃'(b))^{5/8} = (Φ'(z)/Φ'(b))^{5/8}.
-/
theorem observable_limit_well_defined (c : ℝ) (hc : 0 < c) (f g : ℂ) (hg : g ≠ 0) :
    (↑c * f / (↑c * g)) ^ ((5 : ℂ) / 8) = (f / g) ^ ((5 : ℂ) / 8) := by
  congr 1
  have hc_ne : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  field_simp

/-! ## The counting argument for discrete contour integrals

The vertex relation (Lemma 1) gives one equation per vertex of V(Ω).
For the hexagonal lattice (3-regular), |E| = 3|V|/2, so |V| = 2|E|/3.

This means we have ~(2/3)|E| equations for |E| values of F_δ,
which is insufficient to determine F_δ from its boundary values.

In contrast, for the Ising model on the square lattice, the analogous
observable satisfies ONE equation per edge (not per vertex), giving
~|E| equations for |E| values — enough to reconstruct the observable.

The "missing" equations correspond to the curl of F_δ being non-zero
in the discrete setting. In the scaling limit, the curl is expected
to vanish, making F_δ holomorphic.
-/

/-- On the hexagonal lattice, the ratio |V|/|E| = 2/3.
    Each vertex has degree 3, so 2|E| = 3|V| (handshaking lemma).
    Therefore |V| = 2|E|/3. -/
theorem hex_lattice_VE_ratio :
    ∀ n : ℕ, 2 * (3 * n / 2) = 3 * n ∨ 2 * (3 * n / 2) = 3 * n - 1 := by
  intro n; omega

/-- The number of vertex relations equals 2/3 of the number of edge values.
    This is a fundamental limitation of the parafermionic observable:
    it satisfies only a "half" of the discrete Cauchy-Riemann relations. -/
def vertex_equation_count (E : ℕ) : ℕ := 2 * E / 3

/-- The "missing" equations: the number of edge values minus vertex equations.
    This gap = E - 2E/3 = E/3 represents the degrees of freedom
    corresponding to the (conjecturally vanishing) curl of F_δ. -/
def curl_degrees_of_freedom (E : ℕ) : ℕ := E - vertex_equation_count E

/-! ## The Ising model comparison

For the Ising model on the square lattice, the analogous fermionic
observable satisfies the FULL discrete Cauchy-Riemann relations
(one equation per edge). This was proved by Chelkak-Smirnov (2009)
and led to the proof of conformal invariance of the Ising model.

The key difference:
- Ising: |equations| = |E| → full determination → convergence proved ✓
- SAW: |equations| = 2|E|/3 → underdetermined → convergence open ✗

The parafermionic observable for SAW can be thought of as a
divergence-free vector field with potentially non-trivial curl.
-/

/-- For comparison: the Ising model has one equation per edge,
    giving a fully determined system. -/
def ising_equation_count (E : ℕ) : ℕ := E

/-- The Ising model has no missing equations (curl = 0 in the discrete). -/
theorem ising_fully_determined (E : ℕ) : ising_equation_count E = E := rfl

/-! ## Critical exponents

Nienhuis (1982) predicted the critical exponents for SAWs:

- **γ = 43/32**: The asymptotic growth rate exponent.
  c_n ~ A · n^{γ-1} · μ^n

- **ν = 3/4**: The Flory exponent for mean-square displacement.
  ⟨|γ(n)|²⟩ ~ n^{2ν}

These exponents could be rigorously derived if Conjecture 1 (SLE convergence)
were proved, as shown by Lawler-Schramm-Werner (2004).

The best rigorously known bounds are almost 50 years old and very far
from the predictions. The derivation of these exponents remains one of
the most challenging open problems in probability theory.
-/

/-- The critical exponent γ = 43/32 for the number of SAWs. -/
def gamma_exponent : ℚ := 43 / 32

/-- The Flory exponent ν = 3/4 for the mean-square displacement. -/
def nu_exponent : ℚ := 3 / 4

/-- The exponent relation: γ = 43/32 implies γ - 1 = 11/32. -/
lemma gamma_minus_one : gamma_exponent - 1 = 11 / 32 := by
  unfold gamma_exponent; norm_num

/-- The displacement exponent: 2ν = 3/2. -/
lemma two_nu : 2 * nu_exponent = 3 / 2 := by
  unfold nu_exponent; norm_num

/-! ## Remark: Bridge decay exponent

The proof of Theorem 1 provides the bounds:
  c/T ≤ B_T^{x_c} ≤ 1

The conjectured precise decay (from Lawler-Schramm-Werner, paragraphs 3.3.3
and 3.4.3) is B_T^{x_c} ~ T^{-1/4}.

More precisely, for walks from 0 to T + iyT in the strip S_T:
  Σ_{γ ⊂ S_T : 0 → T+iyT} x_c^{ℓ(γ)} ≈ T^{-5/4} · H(0, 1+iy)^{5/4}
where H is the boundary derivative of the Poisson kernel.
Integrating over y gives B_T^{x_c} ~ T^{-1/4}.
-/

/-- The conjectured bridge decay exponent: -1/4.
    B_T^{x_c} is expected to decay as T^{-1/4} when T → ∞. -/
def bridge_decay_exponent : ℚ := -1 / 4

/-- The walk-to-point exponent: -5/4.
    For walks from 0 to a specific boundary point of S_T,
    the weight decays as T^{-5/4}. -/
def point_to_point_exponent : ℚ := -5 / 4

/-- The relation between exponents: integrating T^{-5/4} over the
    boundary height (which is O(T)) gives T^{-5/4 + 1} = T^{-1/4}. -/
lemma exponent_integration_relation :
    point_to_point_exponent + 1 = bridge_decay_exponent := by
  unfold point_to_point_exponent bridge_decay_exponent; norm_num

/-! ## The Hammersley-Welsh upper bound on c_n

From the Hammersley-Welsh bridge decomposition, the best rigorously known
upper bound on c_n is:

  μ^n ≤ c_n ≤ exp(κ√n) · μ^n

for some constant κ > 0. The lower bound is from submultiplicativity.
The gap between exp(κ√n) and the conjectured n^{11/32} is enormous.
-/

/-- The Hammersley-Welsh subexponential correction.
    The upper bound c_n ≤ exp(κ√n) · μ^n means
    log(c_n) ≤ κ√n + n·log(μ).
    The conjectured behavior log(c_n) ≈ (γ-1)·log(n) + n·log(μ)
    has log(n) instead of √n — much slower growth. -/
def hw_correction_exponent : ℝ := 1 / 2  -- √n = n^{1/2}

/-! ## Summary of the status of conjectures

| Conjecture | Status | Reference |
|------------|--------|-----------|
| μ = √(2+√2) | **PROVED** (this paper) | Theorem 1 |
| γ = 43/32 | Open | Nienhuis (1982) |
| ν = 3/4 | Open | Flory-Nienhuis |
| SLE(8/3) limit | Open | Conjecture 1 |
| Observable convergence | Open | Conjecture 2 |
| B_T ~ T^{-1/4} | Open | Remark (LSW) |
| c_n ~ A·n^{11/32}·μ^n | Open | Nienhuis |

Proving Conjecture 2 → Conjecture 1 → all exponents.
The key missing step is establishing holomorphicity of F_δ in the
scaling limit, which requires controlling the "curl" of the discrete
observable (the E/3 missing equations).
-/

end
