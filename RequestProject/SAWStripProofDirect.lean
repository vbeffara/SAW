/-
# Direct proof of the strip identity (Lemma 2)

Reduces `strip_identity_genuine` to the vertex relation and
discrete Stokes identity.

## Strategy

The parafermionic observable F(z) at each mid-edge z satisfies
the vertex relation at each vertex v:
  (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0

Summing over all vertices in PaperFinStrip T L:
- Interior mid-edges cancel (each appears twice with opposite signs)
- Only boundary mid-edges survive
- Boundary evaluation gives: 1 = c_α·A + B + c_ε·E

## Reference
  Duminil-Copin, H. and Smirnov, S.,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012, Section 2-3.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Directed boundary edges

A "directed boundary edge" is a pair (v, w) where v is in the strip
and w is outside the strip, with v ~ w in hexGraph. -/

/-- A directed boundary edge of PaperFinStrip T L. -/
structure DirBdryEdge (T L : ℕ) where
  inside : HexVertex
  outside : HexVertex
  inside_in : PaperFinStrip T L inside
  outside_out : ¬ PaperFinStrip T L outside
  adj : hexGraph.Adj inside outside

/-! ## Boundary classification

Each boundary edge is classified as:
- Starting: the unique edge from hexOrigin to paperStart
- Left (α): exit through d = 0 boundary (TRUE side)
- Right (β): exit through d = -T boundary (FALSE side)
- Escape (ε/ε̄): exit through the ±L boundaries -/

/-- Classification of boundary edges. -/
inductive BdryType
  | starting  -- the starting mid-edge a (hexOrigin → paperStart)
  | left      -- left boundary α (d = 0)
  | right     -- right boundary β (d = -T)
  | escape    -- escape boundary ε ∪ ε̄
  deriving DecidableEq

/-! ## Winding angle from the starting mid-edge

For each SAW from paperStart ending at a vertex v adjacent to the
strip boundary, the "exit winding" is the total direction change
from the starting mid-edge a = (hexOrigin, paperStart) to the
exit mid-edge (v, w). -/

/-- The exit angle for a boundary edge, used in the winding computation.
    - Right boundary (β): exit angle = 0
    - Left boundary (α): exit angle = π or -π
    - Escape boundary (ε): exit angle = ±π/3 or ±2π/3 -/
def bdryExitAngle (e : DirBdryEdge T L) : ℝ :=
  hexEdgeAngle e.inside e.outside

/-! ## The key bound: B_paper ≤ 1

We prove B_paper T L xc ≤ 1 from the parafermionic observable.

The approach is to define a real-valued "boundary contribution" for each
SAW and show that the total boundary contribution is zero. The right
boundary (β) contribution equals B_paper, while all other contributions
are non-negative. Therefore B_paper ≤ 1.

Formally, for each SAW γ from paperStart ending at a boundary vertex v
with exit edge (v, w):

  contribution(γ) = Re[ (embed(w) - embed(v)) · exp(-iσ·W(γ)) ] · xc^{ℓ(γ)+1}

where W(γ) is the extended winding angle.

The discrete Stokes identity says: Σ contribution(γ) = 0 over all
boundary SAWs γ.

The right boundary contribution gives B_paper (with coefficient 1).
The starting mid-edge contribution gives -1.
All other contributions are non-negative.
Therefore: 0 = -1 + B_paper + (non-negative) → B_paper ≤ 1. -/

/-! ## Proof of B_paper ≤ 1 from the boundary sum identity

Assume the boundary sum identity (which follows from the vertex relation
+ discrete Stokes). Then B_paper ≤ 1 follows by real-part analysis. -/

/-- The boundary sum identity implies B_paper ≤ 1.
    The identity says: the total boundary contribution is zero.
    The right boundary contributes B_paper (positive).
    The starting mid-edge contributes -1 (negative).
    All other boundary contributions have non-negative real part.
    Therefore B_paper ≤ 1.

    Proof: from 0 = -1 + B_paper + (non-negative), we get B_paper ≤ 1. -/
theorem B_paper_le_one_from_boundary_sum (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (h_boundary : ∃ (R : ℝ), 0 ≤ R ∧ 0 = -1 + B_paper T L xc + R) :
    B_paper T L xc ≤ 1 := by
  obtain ⟨R, hR, hid⟩ := h_boundary
  linarith

/-- strip_identity_genuine from B_paper ≤ 1. -/
theorem strip_identity_from_B_bound (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (hB : B_paper T L xc ≤ 1) :
    ∃ (A_m E_m : ℝ), 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m := by
  exact ⟨(1 - B_paper T L xc) / c_alpha, 0,
    div_nonneg (sub_nonneg.mpr hB) c_alpha_pos.le,
    le_refl _,
    by simp [mul_div_cancel₀ _ (ne_of_gt c_alpha_pos)]⟩

/-! ## The boundary sum identity

This is the core result: the total boundary contribution is zero.
It follows from the vertex relation (Lemma 1) and the discrete
Stokes argument (interior mid-edge cancellation).

The boundary sum identity states:
  0 = -1 + B_paper T L xc + R
where R ≥ 0 is the sum of left boundary + escape boundary contributions.

**Status: sorry.** This encapsulates the entire parafermionic observable
argument. The algebraic ingredients (pair_cancellation, triplet_cancellation)
are proved. The combinatorial infrastructure (walk pairing/tripling,
discrete Stokes summation) remains to be formalized. -/

theorem boundary_sum_identity (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ (R : ℝ), 0 ≤ R ∧ 0 = -1 + B_paper T L xc + R := by
  -- The proof requires the full parafermionic observable argument.
  -- See SAW.tex Section 2-3 for the mathematical argument.
  sorry

/-! ## Proving strip_identity_genuine from boundary_sum_identity -/

/-- strip_identity_genuine follows from the boundary sum identity. -/
theorem strip_identity_genuine_from_boundary (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ (A_m E_m : ℝ), 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m :=
  strip_identity_from_B_bound T L hT hL
    (B_paper_le_one_from_boundary_sum T L hT hL (boundary_sum_identity T L hT hL))

end