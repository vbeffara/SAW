/-
# Corrected Strip Identity (Lemma 2)

Formalization of the strip identity from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Key corrections

### Issue 1: Strip domain boundary alignment

The paper's strip S_T is defined by V(S_T) = {z ∈ V(H) : 0 ≤ Re(z) ≤ (3T+1)/2}.
In the correct honeycomb embedding:
  - FALSE(x,y) at Re = -(3(x+y)+1)/2
  - TRUE(x,y) at Re = -(3(x+y)-1)/2

The paper's right boundary β consists of **horizontal** mid-edges connecting
FALSE(x,y) at x+y = -T (inside, Re = (3T-1)/2) to TRUE(x,y) at x+y = -T
(at Re = (3T+1)/2). The walk exits horizontally, so winding from a to β is 0.

For the boundary mid-edges to be horizontal, TRUE at x+y = -T must be
**outside** the strip. This means the strict inequality Re < (3T+1)/2 should
be used for the right boundary, giving:
  - TRUE(x,y) in strip: -(T-1) ≤ x+y ≤ 0  (NOT -T ≤ x+y ≤ 0)
  - FALSE(x,y) in strip: -T ≤ x+y ≤ -1     (unchanged)

### Issue 2: Weight convention

The paper defines ℓ(γ) = number of vertices visited. For an n-edge SAW from
paperStart, ℓ = n+1. The paper's partition functions use x^ℓ = x^{n+1}.
The Lean SAW has len = n (edges), so the weight should be x^{len+1}.

### Issue 3: Boundary classification for the finite strip

For the finite strip S_{T,L}, the escape boundary has non-uniform winding
for small L. The identity 1 = c_α·A + B + c_ε·E holds with the paper's
specific boundary classification by mid-edge type, which accounts for
the winding at each boundary mid-edge individually.

In this file, we state the corrected identity using the corrected strip
domain and vertex-weight convention. The proof is left as sorry pending
full formalization of the parafermionic observable and boundary evaluation.
-/

import Mathlib
import RequestProject.SAWBridgeFix

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Corrected paper-compatible strip domain

The key change from the previous version: TRUE vertices with x+y = -T
are **excluded** from the strip. This ensures right boundary mid-edges
are horizontal (connecting FALSE inside to TRUE outside at x+y = -T),
giving winding 0 from the starting mid-edge a. -/

/-- The corrected infinite strip S_T.
    TRUE(x,y) in strip: -(T-1) ≤ x+y ≤ 0  (excludes x+y = -T)
    FALSE(x,y) in strip: -T ≤ x+y ≤ -1

    This ensures the right boundary consists of horizontal mid-edges
    connecting FALSE at x+y = -T (inside) to TRUE at x+y = -T (outside). -/
def PaperInfStrip (T : ℕ) (v : HexVertex) : Prop :=
  if v.2.2 then
    -((T : ℤ) - 1) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0
  else
    -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ -1

/-- The corrected finite strip S_{T,L}. -/
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

/-! ## Starting vertex -/

/-- The starting vertex for paper-compatible walks. -/
def paperStart : HexVertex := (0, 0, true)

/-- paperStart is in PaperInfStrip T for T ≥ 1. -/
lemma paperStart_in_strip (T : ℕ) (_hT : 1 ≤ T) : PaperInfStrip T paperStart := by
  unfold PaperInfStrip paperStart; simp; omega

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

/-! ## Partition functions using vertex-weight convention

The paper's partition functions use x^ℓ where ℓ = number of vertices visited.
For an n-edge SAW, ℓ = n+1. So the weight is x^{n+1} = x · x^n. -/

/-- SAW from paperStart ending at a left boundary vertex.
    Left boundary: TRUE with x+y = 0, excluding paperStart.
    These connect to FALSE at x+y = 0 outside the strip. -/
structure PaperSAW_A (T L : ℕ) where
  len : ℕ
  saw : SAW paperStart len
  end_left : saw.w.1 + saw.w.2.1 = 0 ∧ saw.w.2.2 = true ∧ saw.w ≠ paperStart
  in_strip : ∀ v ∈ saw.p.1.support, PaperFinStrip T L v

/-- SAW from paperStart ending at a right boundary vertex.
    Right boundary: FALSE with x+y = -T.
    These connect to TRUE at x+y = -T outside the strip (horizontal mid-edges). -/
structure PaperSAW_B (T L : ℕ) where
  len : ℕ
  saw : SAW paperStart len
  end_right : saw.w.1 + saw.w.2.1 = -(T : ℤ) ∧ saw.w.2.2 = false
  in_strip : ∀ v ∈ saw.p.1.support, PaperFinStrip T L v

/-- SAW from paperStart ending at an escape boundary vertex. -/
structure PaperSAW_E (T L : ℕ) where
  len : ℕ
  saw : SAW paperStart len
  not_left : ¬(saw.w.1 + saw.w.2.1 = 0 ∧ saw.w.2.2 = true)
  not_right : ¬(saw.w.1 + saw.w.2.1 = -(T : ℤ) ∧ saw.w.2.2 = false)
  on_boundary : ∃ w : HexVertex, hexGraph.Adj saw.w w ∧ ¬ PaperFinStrip T L w
  in_strip : ∀ v ∈ saw.p.1.support, PaperFinStrip T L v

/-- Paper-compatible partition functions using vertex-weight x^{n+1}. -/
def A_paper (T L : ℕ) (x : ℝ) : ℝ := ∑' (s : PaperSAW_A T L), x ^ (s.len + 1)
def B_paper (T L : ℕ) (x : ℝ) : ℝ := ∑' (s : PaperSAW_B T L), x ^ (s.len + 1)
def E_paper (T L : ℕ) (x : ℝ) : ℝ := ∑' (s : PaperSAW_E T L), x ^ (s.len + 1)

/-! ## The corrected strip identity -/

/-- **Lemma 2 (corrected)**: The strip identity for the paper-compatible domain.

    For critical x = x_c, the following identity holds:
    1 = c_α · A_paper + B_paper + c_ε · E_paper

    Key changes from the previous version:
    1. Strip domain excludes TRUE at x+y = -T (right boundary is horizontal)
    2. Weight is x^{len+1} (vertex count convention)
    3. Right boundary classification uses FALSE at x+y = -T (not all vertices)

    The proof follows the paper:
    1. At each vertex v in the strip, the vertex relation holds:
       the complex sum of walk contributions at v's three mid-edges vanishes
       (by pair_cancellation and triplet_cancellation).
    2. Summing over all vertices: interior mid-edges cancel telescopically.
    3. Boundary mid-edges survive. The starting mid-edge contributes 1.
    4. Left boundary: winding ±π gives coefficient cos(5π/8) = -c_α.
       Right boundary: winding 0 gives coefficient 1.
       Escape boundary: combined coefficient c_ε.
    5. Assembly gives 1 = c_α·A + B + c_ε·E. -/
theorem paper_strip_identity (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    1 = c_alpha * A_paper T L xc + B_paper T L xc + c_eps * E_paper T L xc := by
  sorry

/-! ## Non-negativity -/

lemma A_paper_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ A_paper T L x :=
  tsum_nonneg fun s => pow_nonneg hx (s.len + 1)

lemma B_paper_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ B_paper T L x :=
  tsum_nonneg fun s => pow_nonneg hx (s.len + 1)

lemma E_paper_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ E_paper T L x :=
  tsum_nonneg fun s => pow_nonneg hx (s.len + 1)

/-! ## Consequences of the strip identity -/

/-- B_paper ≤ 1 at x = x_c: direct consequence of the strip identity. -/
theorem B_paper_le_one (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 := by
  have hid := paper_strip_identity T L hT hL
  have hA := A_paper_nonneg T L xc xc_pos.le
  have hE := E_paper_nonneg T L xc xc_pos.le
  nlinarith [c_alpha_pos, c_eps_pos]

end
