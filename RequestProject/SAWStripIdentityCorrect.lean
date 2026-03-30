/-
# Corrected Strip Identity (Lemma 2)

Formalization of the strip identity from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Key corrections over SAWFiniteStrip.lean

The original `strip_identity_concrete` in SAWFiniteStrip.lean has three issues:

1. **Boundary overlap**: `StripSAW_A`, `StripSAW_B`, `StripSAW_E` use
   vertex-based classification that is non-disjoint.

2. **Starting point**: Walks start from `hexOrigin = (0,0,false)`, but
   in the paper's geometry, the starting mid-edge `a` connects
   `(0,0,false)` (outside) to `(0,0,true)` (inside the strip).
   Walks in the paper start from `(0,0,true)`, the interior endpoint
   of the starting mid-edge.

3. **Domain mismatch**: The `FiniteStrip` domain uses `0 ≤ v.1 ≤ T`,
   which does not match the paper's strip `V(S_T)` defined by
   `0 ≤ Re(z) ≤ (3T+1)/2`.

This file defines the paper-compatible strip domain and states the
corrected strip identity using walks from `(0,0,true)`.

## Paper-compatible domain

In the correct honeycomb embedding, the Re coordinate is:
  - `FALSE(x,y)` at `Re = -(3(x+y)+1)/2`
  - `TRUE(x,y)` at `Re = -(3(x+y)-1)/2`

The paper's `V(S_T) = {z : 0 ≤ Re(z) ≤ (3T+1)/2}` translates to:
  - `FALSE(x,y)`: `x + y ∈ {-T, ..., -1}` (i.e. `-T ≤ x+y` and `x+y ≤ -1`)
  - `TRUE(x,y)`: `x + y ∈ {-T, ..., 0}` (i.e. `-T ≤ x+y` and `x+y ≤ 0`)

The finite strip `S_{T,L}` additionally constrains:
  - `FALSE(x,y)`: `x ∈ {-L, ..., L-1}`
  - `TRUE(x,y)`: `x ∈ {-L+1, ..., L}`

In the paper, `hexOrigin = (0,0,false)` is OUTSIDE the strip (since
`x+y = 0` but FALSE requires `x+y ≤ -1`). The walk starts from
`(0,0,true)` which IS inside (since `x+y = 0 ≤ 0`).
-/

import Mathlib
import RequestProject.SAWBridgeFix

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Paper-compatible strip domain -/

/-- The paper's infinite strip S_T: vertex (x, y, b) is in the paper strip iff
    FALSE vertices satisfy -T ≤ x+y ≤ -1, and
    TRUE vertices satisfy -T ≤ x+y ≤ 0. -/
def PaperInfStrip (T : ℕ) (v : HexVertex) : Prop :=
  if v.2.2 then
    -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0
  else
    -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ -1

/-- The paper's finite strip S_{T,L}: additionally constrains x. -/
def PaperFinStrip (T L : ℕ) (v : HexVertex) : Prop :=
  PaperInfStrip T v ∧
  if v.2.2 then
    -(L : ℤ) + 1 ≤ v.1 ∧ v.1 ≤ L
  else
    -(L : ℤ) ≤ v.1 ∧ v.1 ≤ L - 1

instance decidablePaperInfStrip (T : ℕ) (v : HexVertex) :
    Decidable (PaperInfStrip T v) := by
  unfold PaperInfStrip; split <;> exact inferInstance

instance decidablePaperFinStrip (T L : ℕ) (v : HexVertex) :
    Decidable (PaperFinStrip T L v) := by
  unfold PaperFinStrip; exact inferInstance

/-! ## Starting vertex

The paper's walks start from the interior endpoint of the starting
mid-edge a. In the paper's geometry, a = (hexOrigin, TRUE(0,0)),
and the interior endpoint is TRUE(0,0) = (0, 0, true). -/

/-- The starting vertex for paper-compatible walks. -/
def paperStart : HexVertex := (0, 0, true)

/-- paperStart is in PaperInfStrip T for T ≥ 1. -/
lemma paperStart_in_strip (T : ℕ) (_hT : 1 ≤ T) : PaperInfStrip T paperStart := by
  unfold PaperInfStrip paperStart; simp

/-- paperStart is in PaperFinStrip T L for T ≥ 1 and L ≥ 1. -/
lemma paperStart_in_fin_strip (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    PaperFinStrip T L paperStart := by
  constructor
  · exact paperStart_in_strip T hT
  · unfold paperStart; simp; omega

/-! ## hexOrigin is OUTSIDE the paper strip -/

/-- hexOrigin is not in PaperInfStrip for any T. -/
lemma hexOrigin_not_in_strip (T : ℕ) : ¬ PaperInfStrip T hexOrigin := by
  unfold PaperInfStrip hexOrigin; simp

/-! ## Boundary classification

In the paper's strip domain:
- **Left boundary (α)**: mid-edges connecting `FALSE(x,-x)` (outside, x+y=0)
  to `TRUE(x,-x)` (inside, x+y=0). These are horizontal edges at Re = 0.
  The starting mid-edge `a` is the one at `x = 0`.
- **Right boundary (β)**: vertices with x+y = -T (the rightmost slice).
- **Escape boundaries (ε, ε̄)**: mid-edges on the top/bottom cuts.
-/

/-! ## Partition functions using paper-compatible domain -/

/-- SAW from paperStart ending at a left boundary vertex (TRUE with x+y=0, not paperStart). -/
structure PaperSAW_A (T L : ℕ) where
  len : ℕ
  saw : SAW paperStart len
  end_left : saw.w.1 + saw.w.2.1 = 0 ∧ saw.w.2.2 = true ∧ saw.w ≠ paperStart
  in_strip : ∀ v ∈ saw.p.1.support, PaperFinStrip T L v

/-- SAW from paperStart ending at a right boundary vertex. -/
structure PaperSAW_B (T L : ℕ) where
  len : ℕ
  saw : SAW paperStart len
  end_right : saw.w.1 + saw.w.2.1 = -(T : ℤ)
  in_strip : ∀ v ∈ saw.p.1.support, PaperFinStrip T L v

/-- SAW from paperStart ending at an escape boundary vertex
    (on the top/bottom boundary, not on left or right). -/
structure PaperSAW_E (T L : ℕ) where
  len : ℕ
  saw : SAW paperStart len
  not_left : saw.w.1 + saw.w.2.1 ≠ 0 ∨ saw.w.2.2 = false
  not_right : saw.w.1 + saw.w.2.1 ≠ -(T : ℤ)
  on_boundary : ∃ w : HexVertex, hexGraph.Adj saw.w w ∧ ¬ PaperFinStrip T L w
  in_strip : ∀ v ∈ saw.p.1.support, PaperFinStrip T L v

/-- Paper-compatible partition functions. -/
def A_paper (T L : ℕ) (x : ℝ) : ℝ := ∑' (s : PaperSAW_A T L), x ^ s.len
def B_paper (T L : ℕ) (x : ℝ) : ℝ := ∑' (s : PaperSAW_B T L), x ^ s.len
def E_paper (T L : ℕ) (x : ℝ) : ℝ := ∑' (s : PaperSAW_E T L), x ^ s.len

/-! ## The corrected strip identity -/

/-- **Lemma 2 (corrected)**: The strip identity for the paper-compatible domain.

    For critical `x = x_c`, the following identity holds:
    `1 = c_α · A_paper + B_paper + c_ε · E_paper`

    **Proof sketch** (from the paper):
    1. The parafermionic observable F satisfies the vertex relation
       at every vertex v ∈ V(S_{T,L}): `(p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0`.
       This holds by pair cancellation (`j·conj(λ)⁴ + conj(j)·λ⁴ = 0`)
       and triplet cancellation (`1 + x_c·j·conj(λ) + x_c·conj(j)·λ = 0`).
    2. Summing over all vertices: interior mid-edges cancel telescopically
       (each interior mid-edge appears in exactly two vertex relations
       with opposite signs, since the mid-edge is the midpoint of its edge).
    3. Boundary mid-edges remain. `F(a) = 1` (trivial walk) contributes the
       "1" on the left side.
    4. Symmetry `F(z̄) = F̄(z)` extracts real-valued partition functions.
    5. Boundary winding values give the coefficients `c_α` and `c_ε`. -/
theorem paper_strip_identity (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    1 = c_alpha * A_paper T L xc + B_paper T L xc + c_eps * E_paper T L xc := by
  sorry

/-! ## Non-negativity -/

lemma A_paper_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ A_paper T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

lemma B_paper_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ B_paper T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

lemma E_paper_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ E_paper T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

/-! ## Consequences of the strip identity -/

/-- B_paper ≤ 1 at x = x_c: direct consequence of the strip identity. -/
theorem B_paper_le_one (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 := by
  have hid := paper_strip_identity T L hT hL
  have hA := A_paper_nonneg T L xc xc_pos.le
  have hE := E_paper_nonneg T L xc xc_pos.le
  nlinarith [c_alpha_pos, c_eps_pos]

end
