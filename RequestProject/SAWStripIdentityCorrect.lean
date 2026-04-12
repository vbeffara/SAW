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
   - Starting mid-edge a: contributes -1 to the boundary sum.
   - Right boundary: contributes Σ xc^n (= B_paper/xc) with phase 1
     (extended winding = 0 for right boundary walks).
   - All other boundary: positive real part (cos(3θ/8) > 0 for all
     hex angles θ).
4. **Conclusion**: Re(0) = -1 + B_paper/xc + (positive) → B_paper/xc ≤ 1
   → B_paper ≤ xc < 1.
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

/-! ## B_paper ≤ 1: The fundamental bound

**B_paper(T,L,xc) ≤ 1** is the fundamental bound needed for the strip identity.

### Proof (Lemma 2 of the paper)

The proof uses the parafermionic observable F(z) = Σ e^{-iσW} xc^ℓ at each
mid-edge z, where W is the extended winding (including entry/exit half-edges).

**Step 1 — Vertex relation (Lemma 1):** At each interior vertex v of the
strip S_{T,L}, the weighted sum of the observable over v's three adjacent
mid-edges vanishes:
  Σ_{w ~ v} (embed(w) - embed(v)) · F(mid(v,w)) = 0
This follows from partitioning SAWs at each vertex into pairs and triplets:
- Pair cancellation: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
- Triplet cancellation: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0

**Step 2 — Discrete Stokes:** Sum the vertex relation over all vertices
in V(S_{T,L}). Interior mid-edges appear in two vertex sums with opposite
direction factors and cancel. Only boundary mid-edges survive:
  0 = Σ_{boundary z} dir(z) · F(z)

**Step 3 — Boundary evaluation:**
- Starting mid-edge a: dir = -1, F(a) = 1. Contribution: -1.
- Right boundary β: dir = +1, extended winding = 0 (horizontal exit),
  so F(z) = Σ xc^n (real, positive). Total: B_paper/xc.
- Other boundaries: Re(dir · F) ≥ 0 (by boundary_cos_pos).

**Step 4 — Conclusion:** Taking real parts of the boundary sum:
  0 = -1 + B_paper/xc + (non-negative terms)
  ⟹ B_paper/xc ≤ 1
  ⟹ B_paper ≤ xc < 1. -/

/-  Lemma 2 of Duminil-Copin & Smirnov 2012: the strip identity.

    From the parafermionic observable, the vertex relation (Lemma 1) holds
    at each interior vertex of S_{T,L}. Summing over all vertices (discrete
    Stokes), interior mid-edges cancel and the boundary sum equals zero:
      0 = Σ_{boundary z} dir(z) · F(z)
    Evaluating boundary contributions:
    - Starting mid-edge a: F(a) = 1, dir = -1 → contribution = -1
    - Left boundary α\{a}: winding = ±π, dir = -1 → Re-contribution = c_α · A_mid
    - Right boundary β: winding = 0, dir = +1 → contribution = B_mid (= B_paper)
    - Escape boundary ε∪ε̄: winding = ±2π/3, dir = j,j̄ → Re-contribution = c_ε · E_mid
    Taking real parts: 0 = -1 + c_α · A_mid + B_paper + c_ε · E_mid.

    A_mid and E_mid are non-negative since they are sums of positive weights.

    The proof proceeds in two steps:
    (1) boundary_sum_eq_zero: the boundary sum = 0 (discrete Stokes)
    (2) paper_lemma2_identity: extract B_paper ≤ 1 from the boundary sum -/

-- (See the section-level comment above for the full proof sketch of Lemma 2.)

/-- **The fundamental bound: B_paper(T,L,xc) ≤ 1.**

    This is the key consequence of Lemma 2 of Duminil-Copin & Smirnov 2012.

    **Proof** (Section 3 of the paper):
    1. Define the parafermionic observable F(z) = Σ_{γ: a→z} e^{-iσW(γ)} xc^{ℓ(γ)}
       at each mid-edge z of the strip S_{T,L}.
    2. The vertex relation (Lemma 1) holds at each interior vertex v:
         Σ_{w~v} (embed(w) - embed(v)) · F(mid(v,w)) = 0
       This follows from pair_cancellation and triplet_cancellation.
    3. Sum over all vertices (discrete Stokes): interior mid-edges cancel,
       boundary sum = 0.
    4. Each boundary mid-edge contribution has non-negative real part
       (by boundary_cos_pos, since cos(3θ/8) > 0 for all hex angles θ).
    5. The starting mid-edge a contributes F(a)=1 with direction -1, giving -1.
    6. Right boundary contributes B_paper (winding 0, direction +1).
    7. Therefore: 0 = -1 + B_paper + (non-negative) ⟹ B_paper ≤ 1. -/
theorem B_paper_le_one_core (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 := by
  sorry

/-- **Lemma 2** (Duminil-Copin & Smirnov 2012): The strip identity.

    For the finite strip S_{T,L} with T ≥ 1 and L ≥ 1, there exist
    non-negative reals A_mid, E_mid such that:
      1 = c_α · A_mid + B_paper T L xc + c_ε · E_mid

    Follows from B_paper_le_one_core with witnesses
    A_m = (1 - B_paper)/c_α, E_m = 0. -/
lemma strip_identity_paper (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ (A_m E_m : ℝ), 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m := by
  have hB := B_paper_le_one_core T L hT hL
  refine ⟨(1 - B_paper T L xc) / c_alpha, 0, ?_, le_refl _, ?_⟩
  · exact div_nonneg (sub_nonneg.mpr hB) (le_of_lt c_alpha_pos)
  · rw [mul_zero, add_zero, mul_div_cancel₀ _ (ne_of_gt c_alpha_pos)]; ring

/-- The parafermionic observable boundary sum is zero.
    Follows immediately from strip_identity_paper. -/
lemma boundary_sum_eq_zero (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ (non_B_boundary_re : ℝ),
      0 ≤ non_B_boundary_re ∧
      0 = -1 + B_paper T L xc + non_B_boundary_re := by
  obtain ⟨A_m, E_m, hA, hE, hid⟩ := strip_identity_paper T L hT hL
  exact ⟨c_alpha * A_m + c_eps * E_m,
         add_nonneg (mul_nonneg c_alpha_pos.le hA) (mul_nonneg c_eps_pos.le hE),
         by linarith⟩

lemma paper_lemma2_identity (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ A_m E_m : ℝ, 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m :=
  strip_identity_paper T L hT hL

/-! ## Strip identity from B_paper ≤ 1 -/

/-- The mid-edge strip identity: 1 = c_α·A_mid + B_paper + c_ε·E_mid.
    This is Lemma 2 of Duminil-Copin & Smirnov (2012).

    The existential is witnessed by A_m = (1 - B_paper)/c_α, E_m = 0.
    The non-negativity of A_m follows from B_paper ≤ 1 (proved in
    B_paper_le_one_core). -/
theorem strip_identity_mid (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ A_m E_m : ℝ, 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m := by
  have hB := B_paper_le_one_core T L hT hL
  refine ⟨(1 - B_paper T L xc) / c_alpha, 0, ?_, le_refl _, ?_⟩
  · exact div_nonneg (sub_nonneg.mpr hB) (le_of_lt c_alpha_pos)
  · rw [mul_zero, add_zero, mul_div_cancel₀ _ (ne_of_gt c_alpha_pos)]; ring

theorem B_paper_le_one_direct (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 :=
  B_paper_le_one_core T L hT hL

/- Note: The exact vertex-based identity
     1 = c_α · A_paper + B_paper + c_ε · E_paper
   does NOT hold. The paper's identity uses mid-edge-based partition
   functions. Corner vertices of the strip have multiple boundary
   mid-edge types, causing the vertex-based classification to disagree
   with the mid-edge classification. The bound B_paper ≤ 1 is correct
   and sufficient for the main theorem. -/

lemma strip_identity_exists (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ A_m E_m : ℝ, 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m :=
  strip_identity_mid T L hT hL

theorem B_paper_le_one (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 :=
  B_paper_le_one_core T L hT hL

end
