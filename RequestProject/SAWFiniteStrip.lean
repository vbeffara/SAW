/-
# The finite strip domain S_{T,L}

Formalization of the finite strip domain and its boundary decomposition,
from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the hexagonal lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Overview

The paper defines the strip domain S_{T,L} as follows. Position a hexagonal
lattice H of mesh size 1 in ℂ so that there exists a horizontal edge e
with mid-edge a being 0. Then:

  V(S_T) = {z ∈ V(H) : 0 ≤ Re(z) ≤ (3T+1)/2}
  V(S_{T,L}) = {z ∈ V(S_T) : |√3·Im(z) - Re(z)| ≤ 3L}

The boundary of S_{T,L} decomposes into four parts:
  α = left boundary (Re = 0)
  β = right boundary (Re = (3T+1)/2)
  ε = top boundary (√3·Im - Re = 3L)
  ε̄ = bottom boundary (√3·Im - Re = -3L)

The angled cuts at ±π/3 are needed to ensure the telescoping of the
vertex relation (Lemma 1) at the boundary.

## Content

1. The infinite strip S_T
2. The finite strip S_{T,L}
3. Boundary classification: α, β, ε, ε̄
4. Partition functions A_{T,L}, B_{T,L}, E_{T,L}
5. Monotonicity properties (A,B increasing in L; E decreasing)
-/

import RequestProject.SAWBridgeFix

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Strip domain using integer coordinates

We work with the integer coordinates (x, y, b) where x is the column
index and y is the row index. The embedding into ℂ maps:
  (x, y, false) ↦ (3x/2, √3·y)        [approximately]
  (x, y, true)  ↦ (3x/2 + 1, √3·y)    [approximately]

For the strip of width T:
  V(S_T) = {(x, y, b) : 0 ≤ x ≤ T}

For the finite strip S_{T,L} with the angled cuts, the condition
|√3·Im(z) - Re(z)| ≤ 3L translates to conditions on (x, y).
-/

/-- The infinite strip of width T in integer coordinates.
    A vertex (x, y, b) is in S_T iff 0 ≤ x ≤ T. -/
def InfiniteStrip (T : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T

/-- The finite strip S_{T,L} in integer coordinates.
    In addition to the strip condition 0 ≤ x ≤ T,
    vertices must satisfy the angled boundary condition.

    The paper's condition |√3·Im(z) - Re(z)| ≤ 3L in the embedding
    coordinates translates approximately to |2y - x| ≤ 2L for the
    integer coordinates (since √3·(√3·y) - 3x/2 = 3y - 3x/2).

    We use the simplified integer condition for the formalization. -/
def FiniteStrip (T L : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T ∧
  |2 * v.2.1 - v.1| ≤ 2 * (L : ℤ)

instance (T L : ℕ) (v : HexVertex) : Decidable (FiniteStrip T L v) :=
  inferInstanceAs (Decidable (0 ≤ v.1 ∧ v.1 ≤ T ∧ |2 * v.2.1 - v.1| ≤ 2 * (L : ℤ)))

/-! ## Boundary classification

The boundary of S_{T,L} decomposes into four parts:
- α (left): vertices with x = 0
- β (right): vertices with x = T
- ε (top): vertices on the upper angled cut
- ε̄ (bottom): vertices on the lower angled cut
-/

/-- Left boundary α: vertices in S_{T,L} with x = 0. -/
def LeftBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  FiniteStrip T L v ∧ v.1 = 0

/-- Right boundary β: vertices in S_{T,L} with x = T. -/
def RightBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  FiniteStrip T L v ∧ v.1 = T

/-- Top boundary ε: vertices on the upper angled cut.
    These are vertices in S_T that are on the boundary of S_{T,L}
    from the top, i.e., 2y - x = 2L (approximately). -/
def TopBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T ∧ 2 * v.2.1 - v.1 = 2 * (L : ℤ)

/-- Bottom boundary ε̄: vertices on the lower angled cut. -/
def BottomBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T ∧ 2 * v.2.1 - v.1 = -(2 * (L : ℤ))

/-! ## Partition functions on the finite strip

The partition functions A_{T,L}, B_{T,L}, E_{T,L} count SAWs
from the starting mid-edge a to the respective boundary parts.
-/

/-- A SAW from hexOrigin within the finite strip S_{T,L} ending on the left boundary.
    This contributes to A_{T,L}^x. -/
structure StripSAW_A (T L : ℕ) where
  len : ℕ
  saw : SAW hexOrigin len
  /-- Endpoint is on left boundary, excluding the starting point a -/
  end_left : saw.w.1 = 0 ∧ saw.w ≠ hexOrigin
  /-- Walk stays within the finite strip -/
  in_strip : ∀ v ∈ saw.p.1.support, FiniteStrip T L v

/-- A SAW from hexOrigin within the finite strip S_{T,L} ending on the right boundary.
    This contributes to B_{T,L}^x. -/
structure StripSAW_B (T L : ℕ) where
  len : ℕ
  saw : SAW hexOrigin len
  /-- Endpoint is on right boundary -/
  end_right : saw.w.1 = T
  /-- Walk stays within the finite strip -/
  in_strip : ∀ v ∈ saw.p.1.support, FiniteStrip T L v

/-- A SAW from hexOrigin within the finite strip S_{T,L} ending on the
    top or bottom boundary. This contributes to E_{T,L}^x. -/
structure StripSAW_E (T L : ℕ) where
  len : ℕ
  saw : SAW hexOrigin len
  /-- Endpoint is on top or bottom boundary -/
  end_escape : |2 * saw.w.2.1 - saw.w.1| = 2 * (L : ℤ)
  /-- Walk stays within the finite strip -/
  in_strip : ∀ v ∈ saw.p.1.support, FiniteStrip T L v

/-! ## Partition functions as sums

The partition functions weight each walk by x^{length}:
  A_{T,L}^x = Σ_{γ} x^{ℓ(γ)}
  B_{T,L}^x = Σ_{γ} x^{ℓ(γ)}
  E_{T,L}^x = Σ_{γ} x^{ℓ(γ)}

Since the finite strip is bounded, these sums are finite.
-/

/-- The A partition function (left boundary, excluding origin). -/
def A_TL (T L : ℕ) (x : ℝ) : ℝ :=
  ∑' (s : StripSAW_A T L), x ^ s.len

/-- The B partition function (right boundary). -/
def B_TL (T L : ℕ) (x : ℝ) : ℝ :=
  ∑' (s : StripSAW_B T L), x ^ s.len

/-- The E partition function (top/bottom escape boundary). -/
def E_TL (T L : ℕ) (x : ℝ) : ℝ :=
  ∑' (s : StripSAW_E T L), x ^ s.len

/-! ## Monotonicity properties

From the paper: "sequences (A^x_{T,L})_{L>0} and (B^x_{T,L})_{L>0}
are increasing in L and bounded for x ≤ x_c thanks to (3) and their
monotonicity in x."

This follows because increasing L gives more walks (a walk in S_{T,L}
is also in S_{T,L'} for L' ≥ L), so the partition functions can only increase.
-/

/-- Every walk in S_{T,L} is also in S_{T,L'} for L' ≥ L.
    This is because the finite strip S_{T,L} ⊆ S_{T,L'}. -/
lemma finite_strip_monotone {T L L' : ℕ} (hLL : L ≤ L') (v : HexVertex)
    (hv : FiniteStrip T L v) : FiniteStrip T L' v := by
  obtain ⟨h1, h2, h3⟩ := hv
  exact ⟨h1, h2, le_trans h3 (by omega)⟩

/-! ## The strip identity (Lemma 2)

At x = x_c, the following identity holds for every T, L:

  1 = c_α · A_{T,L}^{x_c} + B_{T,L}^{x_c} + c_ε · E_{T,L}^{x_c}

This is derived by summing the vertex relation (Lemma 1) over all
vertices in V(S_{T,L}). Interior contributions cancel telescopically,
leaving only boundary terms.

The boundary evaluation uses:
- Left boundary α: winding to top part is π, to bottom is -π
  → Σ F(z) = 1 - c_α · A (since F(a) = 1)
- Right boundary β: winding is 0 → Σ F(z) = B
- Top/bottom ε, ε̄: winding is ±2π/3
  → j·Σ_ε F + j̄·Σ_{ε̄} F = c_ε · E

The strip identity has been proved abstractly in SAWStripIdentity.lean.
The connection to the concrete partition functions A_TL, B_TL, E_TL
defined here requires showing that the abstract identity holds for
these concrete definitions.
-/

/-- **Lemma 2** (Strip identity, abstract form):
    The strip identity holds for the concrete partition functions.
    This is the key hypothesis for the main proof. -/
theorem strip_identity_concrete (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    1 = c_alpha * A_TL T L xc + B_TL T L xc + c_eps * E_TL T L xc := by
  sorry

/-! ## Passage to the infinite strip

As L → ∞:
- A_{T,L} ↑ A_T (increasing, bounded by 1/c_α)
- B_{T,L} ↑ B_T (increasing, bounded by 1)
- E_{T,L} ↓ E_T (decreasing, bounded below by 0)

In the limit: 1 = c_α · A_T + B_T + c_ε · E_T
-/

/-- The infinite strip A partition function (limit as L → ∞). -/
def A_T_inf (T : ℕ) (x : ℝ) : ℝ :=
  ⨆ L : ℕ, A_TL T L x

/-- The infinite strip B partition function (limit as L → ∞).
    This equals the origin_bridge_partition for the strip of width T. -/
def B_T_inf (T : ℕ) (x : ℝ) : ℝ :=
  ⨆ L : ℕ, B_TL T L x

/-! ## Connection to origin_bridge_partition

The infinite strip B partition function B_T_inf agrees with
origin_bridge_partition T from SAWBridgeFix.lean. Both count
SAWs from hexOrigin to the right boundary of S_T, staying in S_T.
-/

/-- B_T_inf equals origin_bridge_partition when x > 0.
    Both count the same set of walks: SAWs from hexOrigin staying
    in the strip S_T and ending with x-coordinate T. -/
theorem B_T_inf_eq_origin_bridge (T : ℕ) (x : ℝ) (hx : 0 < x) :
    B_T_inf T x = origin_bridge_partition T x := by
  sorry

/-! ## Non-negativity of partition functions -/

lemma A_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ A_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

lemma B_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ B_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

lemma E_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ E_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

/-! ## Consequences of the strip identity

From 1 = c_α · A + B + c_ε · E with all terms ≥ 0 and c_α, c_ε > 0:
- A ≤ 1/c_α
- B ≤ 1
- E ≤ 1/c_ε
-/

/-- From the strip identity: B_{T,L} ≤ 1 for all T, L at x = x_c. -/
theorem B_TL_le_one (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_TL T L xc ≤ 1 := by
  have hid := strip_identity_concrete T L hT hL
  have hA := A_TL_nonneg T L xc xc_pos.le
  have hE := E_TL_nonneg T L xc xc_pos.le
  nlinarith [c_alpha_pos, c_eps_pos]

end
