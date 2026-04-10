/-
# Strip Identity Infrastructure (Lemma 2)

Based on Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Vertex-based vs mid-edge-based partition functions

The paper's partition functions A, B, E classify walks by their EXIT
MID-EDGE type. The exact identity `1 = c_α·A + B + c_ε·E` holds for
mid-edge-based partition functions.

The vertex-based partition functions (PaperSAW_A, PaperSAW_B, PaperSAW_E)
classify walks by their endpoint VERTEX. At corner vertices (adjacent to
boundary mid-edges of multiple types), the vertex classification differs
from the mid-edge classification. Consequently, the exact identity does
NOT hold for vertex-based partition functions.

However, the key consequence `B_paper ≤ 1` IS correct for vertex-based
B_paper, because:
- B_paper (vertex-based) = B_mid (mid-edge-based): each right boundary
  vertex has exactly one right boundary mid-edge.
- B_mid ≤ 1 from the mid-edge identity.

## Proof architecture (for B_paper ≤ 1)

The proof of B_paper ≤ 1 follows from the parafermionic observable:

1. **Vertex relation** (Lemma 1): pair_cancellation + triplet_cancellation
   give cancellation at each vertex of the strip.
2. **Discrete Stokes**: summing over all vertices, interior mid-edges
   cancel, only boundary mid-edges survive. Total boundary sum = 0.
3. **Boundary evaluation**:
   - Starting mid-edge a: contributes -1/2 to real part.
   - Right boundary: contributes B_mid/2 to real part (winding = 0).
   - All other boundary: positive real part (cos(3θ/8) > 0 for all
     hex angles θ).
4. **Conclusion**: Re(0) = -1/2 + B_mid/2 + (positive) → B_mid ≤ 1.
   Since B_paper = B_mid, we get B_paper ≤ 1.
-/

import Mathlib
import RequestProject.SAWBridgeFix

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Corrected paper-compatible strip domain

TRUE vertices with x+y = -T are **excluded** from the strip. This
ensures right boundary mid-edges are horizontal (connecting FALSE inside
to TRUE outside at x+y = -T), giving winding 0 from the starting
mid-edge a. -/

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

/-! ## Correct hex lattice embedding -/

/-- Correct embedding of hex lattice vertices into ℂ with unit edge length. -/
def correctHexEmbed : HexVertex → ℂ
  | (x, y, false) => ⟨(-3 * ((x : ℝ) + y)) / 2, ((x : ℝ) - y) * Real.sqrt 3 / 2⟩
  | (x, y, true) =>  ⟨(-3 * ((x : ℝ) + y)) / 2 + 1, ((x : ℝ) - y) * Real.sqrt 3 / 2⟩

/-- The direction angle of a hex edge. -/
def hexEdgeAngle (v w : HexVertex) : ℝ :=
  Complex.arg (correctHexEmbed w - correctHexEmbed v)

/-! ## Boundary mid-edge exit angles -/

/-- The exit angle for left boundary mid-edges is π. -/
lemma left_boundary_exit_angle (x : ℤ) (_hx : x ≠ 0) :
    hexEdgeAngle (x, -x, true) (x, -x, false) = Real.pi := by
  unfold hexEdgeAngle;
  unfold correctHexEmbed; norm_num [ Complex.arg ] ;

/-- The exit angle for right boundary mid-edges is 0. -/
lemma right_boundary_exit_angle (x y : ℤ) :
    hexEdgeAngle (x, y, false) (x, y, true) = 0 := by
  unfold hexEdgeAngle; unfold correctHexEmbed; norm_num [ Complex.arg ] ;

/-- cos(5π/8) = -cos(3π/8) = -c_alpha. -/
lemma cos_five_pi_eight : Real.cos (5 * Real.pi / 8) = -c_alpha := by
  unfold c_alpha
  rw [show 5 * Real.pi / 8 = Real.pi - 3 * Real.pi / 8 from by ring]
  exact Real.cos_pi_sub _

/-- The vertex relation at each strip vertex is exactly the combination
    of pair_cancellation and triplet_cancellation. -/
lemma vertex_relation_pair_triplet :
    j * conj lam ^ 4 + conj j * lam ^ 4 = 0 ∧
    1 + (xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam = 0 :=
  ⟨pair_cancellation, triplet_cancellation⟩

/-! ## Non-negativity -/

lemma A_paper_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ A_paper T L x :=
  tsum_nonneg fun s => pow_nonneg hx (s.len + 1)

lemma B_paper_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ B_paper T L x :=
  tsum_nonneg fun s => pow_nonneg hx (s.len + 1)

lemma E_paper_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ E_paper T L x :=
  tsum_nonneg fun s => pow_nonneg hx (s.len + 1)

/-! ## Boundary contribution positivity

On the hexagonal lattice, every edge has a direction angle θ from the set
{0, ±π/3, ±2π/3, π}. At the critical spin σ = 5/8, the combined
direction-winding factor for a boundary mid-edge with exit angle θ is
(1/2) · exp(i(1 - σ)θ) = (1/2) · exp(i(3/8)θ).

Since |3θ/8| ≤ 3π/8 < π/2 for all θ ∈ [-π, π], we have
cos(3θ/8) > 0, meaning every boundary contribution has positive
real part. This is the key geometric ingredient. -/

lemma boundary_cos_pos (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    0 < Real.cos (3 * θ / 8) := by
  exact Real.cos_pos_of_mem_Ioo ⟨ by linarith [ abs_le.mp hθ, Real.pi_pos ], by linarith [ abs_le.mp hθ, Real.pi_pos ] ⟩

/-! ## B_paper ≤ 1: The key bound

**B_paper(T,L,xc) ≤ 1** is the fundamental bound needed downstream.

### Proof outline

The proof uses the parafermionic observable. Define:
  F(z) = Σ_{γ ⊂ S_{T,L} : a → z} e^{-iσW(γ)} · xc^{ℓ(γ)}

Sum the vertex relation (Lemma 1) over all vertices in V(S_{T,L}).
Interior mid-edges cancel (each appears in two vertex sums with opposite
direction factors). The surviving boundary sum equals 0:

  0 = Σ_{boundary z} (direction factor at z) · F(z)

Taking real parts:
  0 = Re(starting contribution) + Re(left boundary) + Re(right boundary)
    + Re(escape boundary)

The starting mid-edge contributes -1/2. Each right boundary mid-edge
contributes (1/2)·xc^{ℓ(γ)} (winding = 0, direction = +1/2). So the
right boundary total is (1/2)·B_mid.

All other boundary contributions have POSITIVE real part because
cos(3θ/8) > 0 for all hex edge angles θ.

Hence: 0 ≥ -1/2 + (1/2)·B_mid, so B_mid ≤ 1.

Since B_paper = B_mid (each right boundary vertex has exactly one right
boundary mid-edge), B_paper ≤ 1.

**Status: sorry.** Formalizing the full observable + discrete Stokes
argument is a substantial undertaking. -/
theorem B_paper_le_one_direct (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 := by
  sorry

/- Note: The exact vertex-based identity
     1 = c_α · A_paper + B_paper + c_ε · E_paper
   does NOT hold. The paper's identity uses mid-edge-based partition
   functions. Corner vertices of the strip have multiple boundary
   mid-edge types, causing the vertex-based classification to disagree
   with the mid-edge classification. The bound B_paper ≤ 1 is correct
   and sufficient for the main theorem. -/

lemma strip_identity_exists (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ A_m E_m : ℝ, 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m := by
  have hB := B_paper_le_one_direct T L hT hL
  refine ⟨(1 - B_paper T L xc) / c_alpha, 0, ?_, le_refl _, ?_⟩
  · exact div_nonneg (sub_nonneg.mpr hB) (le_of_lt c_alpha_pos)
  · rw [mul_zero, add_zero, mul_div_cancel₀ _ (ne_of_gt c_alpha_pos)]; ring

theorem B_paper_le_one (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 :=
  B_paper_le_one_direct T L hT hL

end
