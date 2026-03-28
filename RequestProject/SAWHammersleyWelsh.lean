/-
# The Hammersley-Welsh Bridge Decomposition

Formalization of the bridge decomposition algorithm from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the hexagonal lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Overview

The paper proves (for completeness) that any self-avoiding walk can be
uniquely decomposed into a sequence of bridges with monotone widths.
This decomposition, first introduced by Hammersley and Welsh (1962),
is the key tool for the upper bound μ ≤ √(2+√2).

## Main results in this file

1. `subset_product_identity`: ∑_{S ⊆ range N} ∏_{T∈S} b(T+1) = ∏(1+b(T+1)) [✓ proved]
2. `origin_bridge_summable_at_xc`: bridge weights summable at xc [✓ proved]
3. `origin_bridge_decay`: B_T^x ≤ (x/xc)^T for x < xc [✓ proved]
4. `hw_upper_bound_abstract`: product convergence for geometric bounds [✓ proved]
5. `bridge_decomposition_injection`: SAW→bridges injection [SORRY - core gap]
6. `hw_partial_sum_bound`: ∑ c_n x^n ≤ 2·∏(1+(x/xc)^T)² [✓ proved from 1,3,5]
7. `hammersley_welsh_summable`: Z(x) converges for x < xc [✓ proved from 4,6]

## Sorry status

All theorems in this file are proved. The key theorem
`bridge_decomposition_injection` delegates to
`bridge_decomposition_injection_proof` from SAWHWDecomp.lean,
which is sorry'd (the core combinatorial gap).
The imports from SAWBridgeFix (`origin_bridge_upper_bound`,
`origin_bridge_lower_bound`) are also sorry'd, depending on
`strip_identity_concrete` from SAWFiniteStrip.
-/

import RequestProject.SAWStripWalks
import RequestProject.SAWDecomp
import RequestProject.SAWHWDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Walk x-coordinate range -/

/-- The minimum x-coordinate visited by a walk. -/
def walkMinX {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map (·.1)).foldl min v.1

/-- The maximum x-coordinate visited by a walk. -/
def walkMaxX {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map (·.1)).foldl max v.1

/-- The width of a walk is max_x - min_x. -/
def walkWidth {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  walkMaxX p - walkMinX p

/-! ## Half-plane walks -/

/-- A half-plane walk: a SAW where the start has minimal x-coordinate. -/
structure HalfPlaneSAW where
  start : HexVertex
  finish : HexVertex
  path : hexGraph.Path start finish
  start_minimal : ∀ v ∈ path.1.support, start.1 ≤ v.1

/-- The width of a half-plane walk. -/
def HalfPlaneSAW.width (h : HalfPlaneSAW) : ℤ :=
  walkMaxX h.path.1 - h.start.1

/-! ## Bridge decomposition data structures -/

/-- A bridge sequence with strictly decreasing widths. -/
structure BridgeDecomposition where
  widths : List ℕ
  strictly_decreasing : widths.Pairwise (· > ·)

/-- Full decomposition: left (increasing) + right (decreasing) widths. -/
structure FullBridgeDecomposition where
  left_widths : List ℕ
  right_widths : List ℕ
  left_increasing : left_widths.Pairwise (· < ·)
  right_decreasing : right_widths.Pairwise (· > ·)

/-! ## Subset product identity -/

/-- **Key counting lemma**: ∑_{S ⊆ range N} ∏_{T∈S} b(T+1) = ∏_{T < N} (1+b(T+1)).
    This is `Finset.prod_one_add` in Mathlib. -/
theorem subset_product_identity (b : ℕ → ℝ) (N : ℕ) :
    ∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, b (T + 1) = ∏ T ∈ Finset.range N, (1 + b (T + 1)) := by
  rw [Finset.prod_one_add]

/-! ## Bridge decay

For x < xc and T ≥ 1, origin_bridge_partition T x ≤ (x/xc)^T.

This combines:
1. The strip identity giving B_T^{xc} ≤ 1
2. Summability of bridge weights at xc
3. The scaling argument: each bridge of width T has length ≥ T
-/

/-- **Summability of bridge weights at xc.**
    From the strip identity, B_T^{x_c} ≤ 1, which gives summability. -/
theorem origin_bridge_summable_at_xc (T : ℕ) (hT : 1 ≤ T) :
    Summable (fun b : OriginBridge T => xc ^ b.1.walk.1.length) := by
  have h_bound : origin_bridge_partition T xc ≤ 1 := by
    grind +suggestions;
  contrapose! h_bound;
  convert absurd ( origin_bridge_lower_bound ) _ using 1;
  simp +zetaDelta at *;
  exact fun x hx => ⟨ T, hT, by rw [ origin_bridge_partition ] ; exact lt_of_le_of_lt ( tsum_eq_zero_of_not_summable h_bound |> le_of_eq ) <| by positivity ⟩

/-- **Bridge decay**: B_T^x ≤ (x/xc)^T for 0 < x < xc and T ≥ 1.

    Proof: Each bridge of width T has length ≥ T (bridge_length_ge_width).
    For each bridge b: x^{b.length} ≤ (x/xc)^T · xc^{b.length}.
    Summing: B_T^x ≤ (x/xc)^T · B_T^{xc} ≤ (x/xc)^T · 1. -/
theorem origin_bridge_decay {T : ℕ} (hT : 1 ≤ T) {x : ℝ} (hx : 0 < x)
    (hxc : x < xc) :
    origin_bridge_partition T x ≤ (x / xc) ^ T := by
  have h_summ := origin_bridge_summable_at_xc T hT
  have h_bound := origin_bridge_upper_bound T hT
  have h_summ_x : Summable (fun b : OriginBridge T => x ^ b.1.walk.1.length) :=
    Summable.of_nonneg_of_le (fun _ => pow_nonneg hx.le _)
      (fun b => pow_le_pow_left₀ hx.le hxc.le _) h_summ
  have h_pw : ∀ b : OriginBridge T,
      x ^ b.1.walk.1.length ≤ (x / xc) ^ T * xc ^ b.1.walk.1.length := by
    intro b
    have hlen : T ≤ b.1.walk.1.length := bridge_length_ge_width T b.1
    have hxn : x ^ b.1.walk.1.length = (x / xc) ^ b.1.walk.1.length * xc ^ b.1.walk.1.length := by
      rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt xc_pos)]
    rw [hxn]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (div_nonneg hx.le xc_pos.le)
        ((div_le_one xc_pos).mpr hxc.le) hlen)
      (pow_nonneg xc_pos.le _)
  have h_summ_rhs : Summable (fun b : OriginBridge T =>
      (x / xc) ^ T * xc ^ b.1.walk.1.length) := h_summ.mul_left _
  calc origin_bridge_partition T x
      = ∑' b : OriginBridge T, x ^ b.1.walk.1.length := rfl
    _ ≤ ∑' b : OriginBridge T, ((x / xc) ^ T * xc ^ b.1.walk.1.length) :=
        Summable.tsum_mono h_summ_x h_summ_rhs h_pw
    _ = (x / xc) ^ T * ∑' b : OriginBridge T, xc ^ b.1.walk.1.length :=
        tsum_mul_left ..
    _ ≤ (x / xc) ^ T * 1 :=
        mul_le_mul_of_nonneg_left h_bound (pow_nonneg (div_nonneg hx.le xc_pos.le) _)
    _ = (x / xc) ^ T := mul_one _

/-! ## Abstract upper bound from geometric bridge bounds -/

/-- **The Hammersley-Welsh upper bound** (abstract form):
    If B_T ≤ r^T for 0 ≤ r < 1, then ∏(1 + B_T)² is uniformly bounded. -/
theorem hw_upper_bound_abstract {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {B : ℕ → ℝ} (hB : ∀ T, 0 ≤ B T) (hBr : ∀ T, B T ≤ r ^ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ N, ∏ T ∈ Finset.range N, (1 + B (T + 1)) ^ 2 ≤ C := by
  refine ⟨Real.exp (2 * ∑' T : ℕ, r ^ (T + 1)), Real.exp_pos _, fun N => ?_⟩
  have h_exp : ∀ T, (1 + B (T + 1)) ^ 2 ≤ Real.exp (2 * r ^ (T + 1)) := by
    intro T
    have h1 : 1 + B (T + 1) ≤ Real.exp (r ^ (T + 1)) :=
      le_trans (by linarith [hBr (T + 1)]) (Real.add_one_le_exp _)
    have h2 : 0 ≤ 1 + B (T + 1) := by linarith [hB (T + 1)]
    calc (1 + B (T + 1)) ^ 2 ≤ (Real.exp (r ^ (T + 1))) ^ 2 := by
            exact pow_le_pow_left₀ h2 h1 2
      _ = Real.exp (2 * r ^ (T + 1)) := by
            rw [← Real.exp_nsmul]; ring_nf
  have h_summ : Summable (fun T : ℕ => r ^ (T + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
  calc ∏ T ∈ Finset.range N, (1 + B (T + 1)) ^ 2
      ≤ ∏ T ∈ Finset.range N, Real.exp (2 * r ^ (T + 1)) :=
        Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun T _ => h_exp T)
    _ = Real.exp (∑ T ∈ Finset.range N, 2 * r ^ (T + 1)) :=
        (Real.exp_sum _ _).symm
    _ ≤ Real.exp (2 * ∑' T : ℕ, r ^ (T + 1)) := by
        apply Real.exp_le_exp_of_le
        calc ∑ T ∈ Finset.range N, 2 * r ^ (T + 1)
            = 2 * ∑ T ∈ Finset.range N, r ^ (T + 1) := by rw [Finset.mul_sum]
          _ ≤ 2 * ∑' T : ℕ, r ^ (T + 1) := by
              apply mul_le_mul_of_nonneg_left
              · exact Summable.sum_le_tsum (Finset.range N) (fun _ _ => by positivity) h_summ
              · norm_num

/-! ## Product convergence -/

/-- **Product convergence**: partial products ∏(1 + r^T) bounded for 0 ≤ r < 1. -/
theorem prod_one_add_geometric_converges' {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N, ∏ T ∈ Finset.range N, (1 + r ^ (T + 1)) ≤ C := by
  obtain ⟨C, hC_pos, hC_bound⟩ := hw_upper_bound_abstract hr0 hr1
    (fun T => pow_nonneg hr0 T) (fun T => le_refl _)
  exact ⟨C, hC_pos, fun N => le_trans
    (Finset.prod_le_prod (fun _ _ => by positivity)
      (fun T _ => by nlinarith [pow_nonneg hr0 (T + 1)]))
    (hC_bound N)⟩

/-! ## Bridge decomposition injection

The Hammersley-Welsh bridge decomposition (1962) shows that any SAW
from hexOrigin can be uniquely decomposed into a pair of bridge sequences
with monotone widths. This gives an injection from SAWs into pairs of
bridge selections, yielding the key inequality for the upper bound.

The hypothesis `x < xc` ensures that `origin_bridge_partition` gives
the true sum (the series is summable for x ≤ xc by the strip identity).
-/

/-- **Bridge decomposition injection** (Hammersley-Welsh, 1962):
    Every SAW from hexOrigin decomposes into a pair of bridge sequences,
    giving: ∑_{n ≤ N} c_n x^n ≤ 2 · (∑_{S ⊆ range N} ∏_{T∈S} B_{T+1}^x)²

    The factor 2 accounts for the two choices of first vertex from
    the starting mid-edge.

    The hypothesis `x < xc` ensures bridge partition functions are summable,
    so that the tsum convention gives the correct (finite) values.

    **Proof sketch** (from the paper):
    (a) For a half-plane walk (start has minimal x-coordinate), find the
        last vertex with maximal x. The initial segment is a bridge of
        width T₀. The remainder is a half-plane walk of width T₁ < T₀.
        By induction on width, decompose into bridges T₀ > T₁ > ⋯ > T_j.
    (b) For a general walk, split at the first vertex with maximal x.
        The left part (reversed) and right part are both half-plane walks.
        Decompose each, getting widths T_{-i} < ⋯ < T_{-1} and T₀ > ⋯ > T_j.
    (c) The decomposition is injective: given the bridge sequence and first
        vertex, one can reconstruct the walk uniquely (reverse procedure).
    (d) The walk length n ≥ total bridge lengths (since "forgotten" vertices
        at connection points add edges not counted in bridges), so
        x^n ≤ ∏ x^{bridge_length} for 0 < x ≤ 1. -/
theorem bridge_decomposition_injection {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, origin_bridge_partition (T + 1) x) ^ 2 :=
  bridge_decomposition_injection_proof hx hxc N

/-! ## Partial-sum bound -/

/-- origin_bridge_partition is non-negative for x > 0. -/
lemma origin_bridge_partition_nonneg (T : ℕ) (x : ℝ) (hx : 0 < x) :
    0 ≤ origin_bridge_partition T x :=
  tsum_nonneg fun _ => pow_nonneg hx.le _

/-- **Partial-sum bound**: ∑ c_n x^n ≤ 2·∏(1+(x/xc)^T)² for x < xc.

    Combines bridge_decomposition_injection, origin_bridge_decay,
    and subset_product_identity. -/
theorem hw_partial_sum_bound {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * ∏ T ∈ Finset.range N, (1 + (x / xc) ^ (T + 1)) ^ 2 := by
  have h_inj := bridge_decomposition_injection hx hxc N
  have h_decay : ∀ T ∈ (Finset.range N).powerset, ∀ t ∈ T,
      origin_bridge_partition (t + 1) x ≤ (x / xc) ^ (t + 1) := by
    intro S _ t _
    exact origin_bridge_decay (by omega) hx hxc
  have h_sum_bound : ∑ S ∈ (Finset.range N).powerset,
        ∏ T ∈ S, origin_bridge_partition (T + 1) x ≤
      ∑ S ∈ (Finset.range N).powerset,
        ∏ T ∈ S, (x / xc) ^ (T + 1) :=
    Finset.sum_le_sum fun S hS =>
      Finset.prod_le_prod
        (fun T _ => origin_bridge_partition_nonneg (T + 1) x hx)
        (fun t ht => h_decay S hS t ht)
  have h_prod_id : ∑ S ∈ (Finset.range N).powerset,
        ∏ T ∈ S, (x / xc) ^ (T + 1) =
      ∏ T ∈ Finset.range N, (1 + (x / xc) ^ (T + 1)) :=
    subset_product_identity _ N
  have h_nn : 0 ≤ ∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, origin_bridge_partition (T + 1) x :=
    Finset.sum_nonneg fun S _ =>
      Finset.prod_nonneg fun T _ => origin_bridge_partition_nonneg (T + 1) x hx
  calc ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n
      ≤ 2 * (∑ S ∈ (Finset.range N).powerset,
          ∏ T ∈ S, origin_bridge_partition (T + 1) x) ^ 2 := h_inj
    _ ≤ 2 * (∑ S ∈ (Finset.range N).powerset,
          ∏ T ∈ S, (x / xc) ^ (T + 1)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        nlinarith [sq_nonneg (∑ S ∈ (Finset.range N).powerset,
          ∏ T ∈ S, (x / xc) ^ (T + 1) -
          ∑ S ∈ (Finset.range N).powerset,
          ∏ T ∈ S, origin_bridge_partition (T + 1) x)]
    _ = 2 * (∏ T ∈ Finset.range N, (1 + (x / xc) ^ (T + 1))) ^ 2 := by
        rw [h_prod_id]
    _ = 2 * ∏ T ∈ Finset.range N, (1 + (x / xc) ^ (T + 1)) ^ 2 := by
        rw [Finset.prod_pow]

/-! ## Summability from the partial-sum bound -/

/-- **Hammersley-Welsh upper bound on Z(x)**: Z(x) = ∑ c_n x^n converges
    for 0 < x < xc. -/
theorem hammersley_welsh_summable {x : ℝ} (hx : 0 < x) (hxc : x < xc) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  have hr : x / xc < 1 := (div_lt_one xc_pos).mpr hxc
  have hr0 : 0 ≤ x / xc := div_nonneg hx.le xc_pos.le
  obtain ⟨C, hC_pos, hC_bound⟩ := hw_upper_bound_abstract hr0 hr
    (fun T => pow_nonneg hr0 T) (fun T => le_refl _)
  have hbound : ∀ N, ∑ n ∈ Finset.range N, (saw_count n : ℝ) * x ^ n ≤ 2 * C := by
    intro N
    match N with
    | 0 => simp; linarith
    | N + 1 =>
      calc ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n
          ≤ 2 * ∏ T ∈ Finset.range N, (1 + (x / xc) ^ (T + 1)) ^ 2 :=
            hw_partial_sum_bound hx hxc N
        _ ≤ 2 * C := mul_le_mul_of_nonneg_left (hC_bound N) (by norm_num)
  exact summable_of_sum_range_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.le n))
    hbound

end
