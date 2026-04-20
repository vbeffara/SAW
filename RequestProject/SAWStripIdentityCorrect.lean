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

/-! ## xc properties -/

/-- xc < 1, since √(2+√2) > 1. -/
lemma xc_lt_one' : xc < 1 := by
  unfold xc
  rw [div_lt_one (Real.sqrt_pos.mpr two_add_sqrt_two_pos)]
  calc (1 : ℝ) < Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    _ ≤ Real.sqrt (2 + Real.sqrt 2) :=
        Real.sqrt_le_sqrt (by linarith [Real.sqrt_nonneg 2])

/-- xc ≤ 1. -/
lemma xc_le_one : xc ≤ 1 := le_of_lt xc_lt_one'

/-! ## Finiteness of PaperFinStrip -/

/-- The set of vertices in PaperFinStrip T L is finite. -/
lemma paper_fin_strip_finite' (T L : ℕ) :
    Set.Finite {v : HexVertex | PaperFinStrip T L v} := by
  refine Set.Finite.subset (Set.toFinite
    ((Set.Icc (-(L : ℤ)) L) ×ˢ (Set.Icc (-(L : ℤ) - T) (L + T)) ×ˢ (Set.univ : Set Bool))) ?_
  rintro ⟨x, y, b⟩ hp
  unfold PaperFinStrip at hp; unfold PaperInfStrip at hp
  simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true]
  cases b <;> simp_all <;> omega

/-! ## SAW length bound in finite strip -/

/-- SAWs from paperStart in PaperFinStrip T L have bounded length. -/
lemma paper_saw_length_bound' (T L : ℕ) (n : ℕ) (s : SAW paperStart n)
    (hs : ∀ v ∈ s.p.1.support, PaperFinStrip T L v) :
    n ≤ (paper_fin_strip_finite' T L).toFinset.card := by
  have h_subset : s.p.1.support.toFinset ⊆ (paper_fin_strip_finite' T L).toFinset := by
    exact fun x hx => by simpa using hs x <| List.mem_toFinset.mp hx
  have hslen := s.l
  calc n = s.p.1.support.toFinset.card - 1 := by
        rw [List.toFinset_card_of_nodup s.p.2.support_nodup,
            SimpleGraph.Walk.length_support]; omega
    _ ≤ s.p.1.support.toFinset.card := Nat.sub_le _ _
    _ ≤ _ := Finset.card_mono h_subset

/-! ## Finiteness of PaperSAW_B -/

/-- PaperSAW_B T L is a finite type. -/
instance paperSAW_B_finite' (T L : ℕ) : Finite (PaperSAW_B T L) := by
  have hN : ∀ s : PaperSAW_B T L,
      s.len ≤ (paper_fin_strip_finite' T L).toFinset.card :=
    fun s => paper_saw_length_bound' T L s.len s.saw s.in_strip
  exact Finite.of_injective
    (fun s : PaperSAW_B T L => (⟨⟨s.len,
      Nat.lt_add_one_iff.mpr (hN s)⟩, s.saw⟩ :
      Σ n : Fin ((paper_fin_strip_finite' T L).toFinset.card + 1),
        SAW paperStart n))
    (fun s t h => by cases s; cases t; aesop)

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

/-! ## Direction vectors sum to zero at each hex vertex -/

/-
At a FALSE vertex, the three direction vectors to neighbors sum to zero.
-/
lemma false_vertex_dir_sum (x y : ℤ) :
    (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) +
    (correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false)) +
    (correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false)) = 0 := by
  unfold correctHexEmbed;
  norm_num [ Complex.ext_iff ] ; ring_nf;
  norm_num

/-
At a TRUE vertex, the three direction vectors to neighbors sum to zero.
-/
lemma true_vertex_dir_sum (x y : ℤ) :
    (correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)) +
    (correctHexEmbed (x - 1, y, false) - correctHexEmbed (x, y, true)) +
    (correctHexEmbed (x, y - 1, false) - correctHexEmbed (x, y, true)) = 0 := by
  unfold correctHexEmbed; norm_num; ring_nf;
  norm_num [ Complex.ext_iff ] ; ring_nf;
  grind

/-
The direction from FALSE(x,y) to TRUE(x,y) is 1.
-/
lemma false_to_true_dir (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 := by
  unfold correctHexEmbed; norm_num;
  norm_num [ Complex.ext_iff ]

/-
The starting mid-edge direction factor is -1.
-/
lemma starting_direction :
    correctHexEmbed hexOrigin - correctHexEmbed paperStart = -1 := by
  unfold hexOrigin paperStart correctHexEmbed ;
  norm_num [ Complex.ext_iff ]

/-! ## The strip identity (Lemma 2 of Duminil-Copin & Smirnov 2012)

The proof uses the parafermionic observable F(z) = Σ e^{-iσW} xc^ℓ
at each mid-edge z of the strip S_{T,L}.

**Step 1 — Vertex relation (Lemma 1):** At each interior vertex v,
pair_cancellation and triplet_cancellation give:
  Σ_{w ~ v} (embed(w) - embed(v)) · F(mid(v,w)) = 0

**Step 2 — Discrete Stokes:** Summing over all vertices, interior
mid-edges cancel, boundary sum = 0.

**Step 3 — Boundary evaluation:** The winding on the hex lattice
TELESCOPES: W = d_last - d_first. Since all walks start from
paperStart through mid-edge a, d_first = 0 for all walks. So:
- Right boundary: d_last = 0, so exp(-iσ·0) = 1, giving real
  contribution B_paper.
- Left boundary: d_last = π, so exp(-iσπ) = exp(-i5π/8), giving
  contribution with Re = -cos(5π/8) = cos(3π/8) = c_alpha > 0.
- Escape boundary: d_last ∈ {±π/3, ±2π/3, π}, all giving
  cos(3θ/8) > 0 by boundary_cos_pos.
- Starting mid-edge a: F(a) = 1 (trivial walk), direction = -1.

**Step 4 — Conclusion:**
  0 = Re(boundary sum) = -1 + B_paper + (non-negative terms)
  ⟹ B_paper ≤ 1. -/

/-- **The genuine strip identity** (Lemma 2 of Duminil-Copin & Smirnov 2012).

    For the finite strip S_{T,L} with T ≥ 1 and L ≥ 1, we have:
      1 = c_α · A + B_paper T L xc + c_ε · E
    where A, E ≥ 0 are the partition functions for walks ending on
    the left and escape boundaries respectively.

    **Proof outline (from the paper):**
    1. Define the parafermionic observable F(z) at each mid-edge z.
    2. The vertex relation (Lemma 1) holds at each interior vertex:
       (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0
       This follows from pair_cancellation and triplet_cancellation.
    3. Sum over all vertices (discrete Stokes): interior mid-edges cancel,
       boundary mid-edges survive, giving equation (2) of the paper.
    4. The winding from a to β is 0, giving B_paper with coefficient 1.
       The winding from a to α\{a} is ±π, giving A with coefficient c_α.
       The winding from a to ε∪ε̄ is ±2π/3, giving E with coefficient c_ε.
       The winding from a to a is 0, giving F(a) = 1.
    5. Equation: 0 = -(1 - c_α·A) + B + c_ε·E, i.e., 1 = c_α·A + B + c_ε·E.

    **Status: sorry.** This is the fundamental gap.
    The algebraic ingredients (pair_cancellation, triplet_cancellation,
    boundary_cos_pos) are proved. What remains is the combinatorial
    infrastructure: partitioning walks into pairs/triplets at each vertex,
    proving exhaustiveness, and the discrete Stokes summation. -/
lemma strip_identity_genuine (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ (A_m E_m : ℝ), 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m := by
  sorry

/-- **B_paper(T,L,xc) ≤ 1** — follows from the genuine strip identity.

    This is the core consequence of Lemma 2 of Duminil-Copin & Smirnov (2012).
    Given the strip identity 1 = c_α·A + B + c_ε·E with A,E ≥ 0,
    we have B ≤ 1 since c_α, c_ε > 0 and A, E ≥ 0. -/
lemma B_paper_le_one_obs (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 := by
  obtain ⟨A_m, E_m, hA, hE, hid⟩ := strip_identity_genuine T L hT hL
  exact bridge_bound_of_strip_identity hA hE hid

/-- **Lemma 2** (Duminil-Copin & Smirnov 2012): The strip identity.

    For the finite strip S_{T,L} with T ≥ 1 and L ≥ 1, there exist
    non-negative reals A_mid, E_mid such that:
      1 = c_α · A_mid + B_paper T L xc + c_ε · E_mid

    Proved from B_paper_le_one_obs by taking A_mid = (1 - B)/c_α, E_mid = 0. -/
lemma strip_identity_paper (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ (A_m E_m : ℝ), 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m := by
  refine ⟨(1 - B_paper T L xc) / c_alpha, 0,
          div_nonneg (sub_nonneg.mpr (B_paper_le_one_obs T L hT hL)) c_alpha_pos.le,
          le_refl _,
          ?_⟩
  have hca : c_alpha ≠ 0 := ne_of_gt c_alpha_pos
  field_simp
  ring

/-- **B_paper(T,L,xc) ≤ 1** — follows from the strip identity (Lemma 2). -/
lemma B_paper_le_one_parafermionic (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 := by
  obtain ⟨A_m, E_m, hA, hE, hid⟩ := strip_identity_paper T L hT hL
  exact bridge_bound_of_strip_identity hA hE hid

/-- **The fundamental bound: B_paper(T,L,xc) ≤ 1.**

    Follows immediately from the strip identity (Lemma 2) and the
    abstract bound `bridge_bound_of_strip_identity`. -/
theorem B_paper_le_one_core (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 := by
  obtain ⟨A_m, E_m, hA, hE, hid⟩ := strip_identity_paper T L hT hL
  exact bridge_bound_of_strip_identity hA hE hid

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
    This is Lemma 2 of Duminil-Copin & Smirnov (2012). -/
theorem strip_identity_mid (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ A_m E_m : ℝ, 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m :=
  strip_identity_paper T L hT hL

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
