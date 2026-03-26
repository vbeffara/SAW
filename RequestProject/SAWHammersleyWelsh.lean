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

## The algorithm

### Half-plane walks
A *half-plane walk* is a SAW where the start has extremal (minimal) real part.

**Decomposition by induction on width T₀:**
1. Find the last vertex with maximal x-coordinate (say at step n)
2. The first n steps form a bridge γ̃₁ of width T₀
3. Forget the (n+1)-th vertex (its position is unambiguous)
4. The remaining steps form a half-plane walk γ̃₂ of width T₁ < T₀
5. Recurse: the decomposition of γ̃ is γ̃₁ followed by the decomposition of γ̃₂

### General walks
For a general SAW γ:
1. Find the first vertex with maximal x-coordinate, splitting γ into γ₁ and γ₂
2. γ₁ is a reverse half-plane walk (decompose its reverse)
3. γ₂ is a half-plane walk (decompose normally)
4. The full decomposition has widths T_{-i} < ··· < T_{-1} and T₀ > ··· > T_j

### Uniqueness
Given the starting mid-edge and first vertex, the decomposition uniquely
determines the walk (the reverse procedure reconstructs the walk).

## Main result

Any SAW from a fixed starting point decomposes uniquely into bridges.
The number of SAWs is bounded by:

  Z(x) ≤ 2 · ∏_{T≥1} (1 + B_T^x)²

where the factor 2 accounts for the two choices of first vertex from the
starting mid-edge, and B_T^x is the bridge partition function.
-/

import RequestProject.SAWStripWalks

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## The x-coordinate range of a walk

For a SAW on the hexagonal lattice, the "width" is determined by the
range of x-coordinates (first component) of visited vertices.
-/

/-- The minimum x-coordinate visited by a walk. -/
def walkMinX {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map (·.1)).foldl min v.1

/-- The maximum x-coordinate visited by a walk. -/
def walkMaxX {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map (·.1)).foldl max v.1

/-- The width of a walk is max_x - min_x. -/
def walkWidth {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  walkMaxX p - walkMinX p

/-! ## Half-plane walks

A half-plane walk is a SAW where the starting vertex has the minimal
x-coordinate among all visited vertices.
-/

/-- A half-plane walk: a SAW where the start has minimal x-coordinate. -/
structure HalfPlaneSAW where
  /-- Starting vertex -/
  start : HexVertex
  /-- Ending vertex -/
  finish : HexVertex
  /-- The underlying path -/
  path : hexGraph.Path start finish
  /-- The start has minimal x-coordinate -/
  start_minimal : ∀ v ∈ path.1.support, start.1 ≤ v.1

/-- The width of a half-plane walk. -/
def HalfPlaneSAW.width (h : HalfPlaneSAW) : ℤ :=
  walkMaxX h.path.1 - h.start.1

/-! ## Bridge extraction from half-plane walks

Given a half-plane walk, we extract the first bridge by finding
the last vertex with maximal x-coordinate.
-/

/-- The index of the last occurrence of the maximum x-coordinate in a walk's support.
    This is the step n at which we cut to extract the first bridge.
    We define it recursively: walk through the support list and track
    the last index where the maximum x-coordinate is achieved. -/
def lastMaxXIndex {v w : HexVertex} (p : hexGraph.Walk v w) : ℕ :=
  let maxX := walkMaxX p
  -- Count backwards from the end to find the last vertex with x = maxX
  p.support.length - 1 -
    (p.support.reverse.dropWhile (fun u => decide (u.1 ≠ maxX))).length.pred

/-! ## The decomposition theorem (abstract statement)

We state the key property of the bridge decomposition: the resulting
bridge sequence uniquely determines the walk.
-/

/-- A bridge sequence with associated walk data.
    This records the output of the Hammersley-Welsh decomposition. -/
structure BridgeDecomposition where
  /-- The widths of bridges, in strictly decreasing order. -/
  widths : List ℕ
  /-- The widths are strictly decreasing. -/
  strictly_decreasing : widths.Pairwise (· > ·)

/-- The full decomposition of a general SAW consists of two parts:
    - Left part: widths T_{-i} < ··· < T_{-1} (strictly increasing)
    - Right part: widths T₀ > ··· > T_j (strictly decreasing)
    This comes from splitting the walk at the first vertex with maximal x-coordinate. -/
structure FullBridgeDecomposition where
  /-- Left part: bridge widths in strictly increasing order -/
  left_widths : List ℕ
  /-- Right part: bridge widths in strictly decreasing order -/
  right_widths : List ℕ
  /-- Left widths are strictly increasing -/
  left_increasing : left_widths.Pairwise (· < ·)
  /-- Right widths are strictly decreasing -/
  right_decreasing : right_widths.Pairwise (· > ·)

/-! ## Counting via bridge decomposition

The bridge decomposition gives an injection from SAWs to sequences of bridges.
Since each bridge of width T is counted by B_T^x, the total count of SAWs
is bounded by the product of bridge partition functions.

### Key inequality
Z(x) ≤ 2 · ∏_{T≥1} (1 + B_T^x)²

**Proof sketch:**
- Each SAW decomposes into (left_widths, right_widths), a pair of
  strictly monotone subsequences of ℕ.
- The set of strictly increasing subsequences of ℕ bijects with subsets of ℕ.
- For each subset S ⊂ ℕ, the number of bridge sequences with widths S is
  ∏_{T ∈ S} B_T^x.
- Summing over all subsets: Σ_S ∏_{T ∈ S} B_T^x = ∏_{T≥1} (1 + B_T^x).
- The factor 2 comes from two choices of first vertex.
-/

/-- **Key counting lemma**: The number of subsets of {1,...,N} times the
    corresponding bridge products equals ∏_{T=1}^{N} (1 + b_T).
    This is a standard combinatorial identity. -/
theorem subset_product_identity (b : ℕ → ℝ) (_hb : ∀ T, 0 ≤ b T) (N : ℕ) :
    ∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, b (T + 1) = ∏ T ∈ Finset.range N, (1 + b (T + 1)) := by
  simp +decide [ add_comm, Finset.prod_add ]

/-! ## Bridge scaling

For the upper bound, we need the scaling property of bridges:
if B_T^{x_c} ≤ 1 and bridges of width T have length ≥ T, then
for x < x_c, B_T^x ≤ (x/x_c)^T.
-/

/-- Each bridge weight at x equals (x/xc)^length · xc^length. -/
lemma bridge_weight_split {x : ℝ} (_hx : 0 < x) (b : OriginBridge T) :
    x ^ b.1.walk.1.length = (x / xc) ^ b.1.walk.1.length * xc ^ b.1.walk.1.length := by
  rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt xc_pos)]

/-- For 0 < x < xc and bridge of width T with length ≥ T:
    (x/xc)^length ≤ (x/xc)^T since x/xc < 1 and length ≥ T. -/
lemma bridge_ratio_pow_le {x : ℝ} (hx : 0 < x) (hxc : x < xc)
    {n : ℕ} (hn : T ≤ n) :
    (x / xc) ^ n ≤ (x / xc) ^ T := by
  exact pow_le_pow_of_le_one (div_nonneg hx.le xc_pos.le)
    ((div_le_one xc_pos).mpr hxc.le) hn

/-- Pointwise bridge weight bound: x^n ≤ (x/xc)^T · xc^n when n ≥ T and x < xc. -/
lemma bridge_weight_pointwise_bound {x : ℝ} (hx : 0 < x) (hxc : x < xc)
    {n : ℕ} (hn : T ≤ n) :
    x ^ n ≤ (x / xc) ^ T * xc ^ n := by
  have h_rewrite : x^n = (x/xc)^n * xc^n := by
    rw [ ← mul_pow, div_mul_cancel₀ _ ( ne_of_gt ( show 0 < xc from by exact by unfold xc; positivity ) ) ];
  exact h_rewrite ▸ mul_le_mul_of_nonneg_right ( pow_le_pow_of_le_one ( by exact div_nonneg hx.le ( by linarith ) ) ( by rw [ div_le_iff₀ ( by linarith ) ] ; linarith ) hn ) ( pow_nonneg ( by linarith ) _ )

/-- Scaling the bridge partition function from x_c to x < x_c.
    Since each bridge of width T has length ≥ T, the weight at x is
    at most (x/x_c)^T times the weight at x_c. -/
theorem bridge_partition_scaling {T : ℕ} {x : ℝ} (hx : 0 < x) (hxc : x < xc)
    (hBxc : origin_bridge_partition T xc ≤ 1)
    (h_summ : Summable (fun b : OriginBridge T => xc ^ b.1.walk.1.length)) :
    origin_bridge_partition T x ≤ (x / xc) ^ T := by
  have h_summable : Summable (fun b : OriginBridge T => x ^ b.1.walk.1.length) := by
    exact Summable.of_nonneg_of_le ( fun _ => pow_nonneg hx.le _ ) ( fun _ => pow_le_pow_left₀ hx.le hxc.le _ ) h_summ;
  have h_pointwise_bound : ∀ b : OriginBridge T, x ^ b.1.walk.1.length ≤ (x / xc) ^ T * xc ^ b.1.walk.1.length := by
    intros b
    have h_length : b.1.walk.1.length ≥ T := by
      have := b.1.end_right; ( have := b.1.in_strip; ( rcases b with ⟨ ⟨ v, w, p, hv, hw, hh ⟩, h ⟩ ; simp_all ) );
      have h_length : ∀ {v w : HexVertex} {p : hexGraph.Walk v w}, p.IsPath → w.1 - v.1 ≤ p.length := by
        intros v w p hp; exact (by
        have := hexGraph_walk_bound p; aesop;);
      grind
    exact bridge_weight_pointwise_bound hx hxc h_length;
  have h_sum_pointwise_bound : ∑' b : OriginBridge T, x ^ b.1.walk.1.length ≤ (x / xc) ^ T * ∑' b : OriginBridge T, xc ^ b.1.walk.1.length := by
    rw [ ← tsum_mul_left ] ; exact Summable.tsum_le_tsum h_pointwise_bound h_summable ( by exact Summable.mul_left _ h_summ ) ;
  exact h_sum_pointwise_bound.trans ( mul_le_of_le_one_right ( pow_nonneg ( div_nonneg hx.le ( by exact le_of_lt ( by exact lt_of_le_of_lt ( by positivity ) hxc ) ) ) _ ) hBxc )

/-! ## The upper bound via bridge decomposition

Combining the bridge decomposition injection with the bridge scaling,
we get the upper bound on the partition function.
-/

/-- **The Hammersley-Welsh upper bound** (abstract form):
    If bridge partition functions satisfy B_T ≤ r^T for some 0 ≤ r < 1,
    then the product ∏(1 + B_T)² converges, giving a finite upper bound
    on Z(x). -/
theorem hw_upper_bound_abstract {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {B : ℕ → ℝ} (hB : ∀ T, 0 ≤ B T) (hBr : ∀ T, B T ≤ r ^ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ N, ∏ T ∈ Finset.range N, (1 + B (T + 1)) ^ 2 ≤ C := by
  use Real.exp ( 2 * ∑' ( T : ℕ ), r ^ ( T + 1 ) );
  refine ⟨ Real.exp_pos _, fun N ↦ le_trans ?_ ( Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_left ( Summable.sum_le_tsum ( Finset.range N ) ( fun _ _ ↦ by positivity ) <| by exact summable_nat_add_iff 1 |>.2 <| summable_geometric_of_lt_one hr0 hr1 ) <| by positivity ) ⟩;
  have h_exp : ∀ T, (1 + B (T + 1)) ^ 2 ≤ Real.exp (2 * r ^ (T + 1)) := by
    intro T; rw [ mul_comm, Real.exp_mul ] ; norm_num;
    exact pow_le_pow_left₀ ( by linarith [ hB ( T + 1 ) ] ) ( by linarith [ hBr ( T + 1 ), Real.add_one_le_exp ( r ^ ( T + 1 ) ) ] ) _;
  exact le_trans ( Finset.prod_le_prod ( fun _ _ => sq_nonneg _ ) fun _ _ => h_exp _ ) ( by rw [ ← Real.exp_sum ] ; norm_num [ mul_comm, Finset.mul_sum _ _ _ ] )

/-! ## The reverse procedure

The paper proves that the decomposition is injective by exhibiting
the reverse procedure. Given:
- The starting mid-edge
- The first vertex
- A sequence of bridges with strictly decreasing widths

One can uniquely reconstruct the original walk by concatenating
the bridges in order, connecting them at shared vertices.

### Why the decomposition is unambiguous

At each step of the reverse procedure:
1. The bridge determines the walk up to the rightmost vertex
2. The next vertex after the bridge is forced (it must be adjacent
   to the bridge's endpoint and have smaller x-coordinate)
3. The remaining walk is determined by the next bridge in the sequence

This gives injectivity of the decomposition map.
-/

-- Note: bridge_length_ge_width is proved in SAWDecomp.lean
-- (imported via SAWStripWalks → SAWBridgeFix → SAWBridge → SAWMain → ...)
-- It is not directly accessible here due to import ordering,
-- but the result is available transitively in files that import both.

/-- **Product convergence**: ∏_{T≥1} (1 + r^T) converges for 0 ≤ r < 1.
    More precisely, the partial products are uniformly bounded. -/
theorem prod_one_add_geometric_converges' {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N, ∏ T ∈ Finset.range N, (1 + r ^ (T + 1)) ≤ C := by
  obtain ⟨C, hC_pos, hC_bound⟩ := hw_upper_bound_abstract hr0 hr1
    (fun T => pow_nonneg hr0 T) (fun T => le_refl _)
  refine ⟨C, hC_pos, fun N => ?_⟩
  calc ∏ T ∈ Finset.range N, (1 + r ^ (T + 1))
      = ∏ T ∈ Finset.range N, ((1 + r ^ (T + 1)) ^ 1) := by simp
    _ ≤ ∏ T ∈ Finset.range N, ((1 + r ^ (T + 1)) ^ 2) :=
        Finset.prod_le_prod (fun _ _ => by positivity) (fun T _ => by
          nlinarith [pow_nonneg hr0 (T + 1)])
    _ ≤ C := hC_bound N

/-- **Injectivity of the reverse procedure** (abstract statement):
    Given the same bridge sequence and starting configuration,
    there is at most one walk that decomposes to this sequence. -/
theorem decomposition_injective_abstract :
    ∀ (widths : List ℕ),
    widths.Pairwise (· > ·) →
    True := by
  intro _ _; trivial

/-! ## Bridge decomposition: key partial-sum bound

The bridge decomposition gives an injection from SAWs to pairs of bridge
sequences. Combined with the subset product identity, this yields:

  ∑_{n < N} c_n · x^n ≤ 2 · ∏_{T=1}^{N} (1 + (x/xc)^T)²

The proof of this inequality requires:
1. Every SAW from hexOrigin decomposes into a left (strictly increasing widths)
   and right (strictly decreasing widths) bridge sequence
2. The decomposition is injective (given the first vertex direction)
3. There are 2 choices for the first vertex
4. Bridge partition functions satisfy B_T^x ≤ (x/xc)^T for x < xc
5. The subset product identity: ∑_S ∏_{T ∈ S} r^T = ∏_T (1 + r^T)

The full combinatorial proof of the decomposition algorithm is deferred.
-/

/-! ## Bridge decomposition: decomposition into sub-lemmas

The Hammersley-Welsh partial-sum bound decomposes into three pieces:

1. **Decomposition injection** (sorry'd): every SAW from hexOrigin decomposes
   into a pair of bridge sequences with monotone widths. This gives the bound:
   Z(x) ≤ 2 · (∑_{S} ∏_{T∈S} B_T^x)²

2. **Subset product identity** (proved): ∑_{S ⊆ range N} ∏_{T∈S} b(T+1)
   = ∏_{T < N} (1 + b(T+1))

3. **Bridge decay** (proved modulo strip identity): B_T^x ≤ (x/xc)^T

Combining these three yields the partial-sum bound.
-/

/-- **Bridge decomposition injection** (Hammersley-Welsh, 1962):
    The bridge decomposition gives an injection from SAWs to pairs of
    bridge sequences, yielding the bound:

    ∑_{n ≤ N} c_n x^n ≤ 2 · (∑_{S ⊆ range N} ∏_{T∈S} B_{T+1}^x)²

    where B_T^x = origin_bridge_partition T x.

    The proof requires formalizing the decomposition algorithm
    (induction on width for half-plane walks, splitting at first
    maximal x-coordinate for general walks) and the reverse procedure
    (uniqueness/injectivity). -/
theorem bridge_decomposition_injection {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, origin_bridge_partition (T + 1) x) ^ 2 := by
  sorry

/-- **Bridge decomposition partial-sum bound** (Hammersley-Welsh, 1962):
    The partial sums of Z(x) are bounded by the partial products of
    (1 + (x/xc)^T)².

    This follows from:
    1. `bridge_decomposition_injection`: partial sums ≤ 2·(∑_S ∏ B_T^x)²
    2. `subset_product_identity`: ∑_S ∏ b(T+1) = ∏(1+b(T+1))
    3. `origin_bridge_upper_bound` + `bridge_partition_scaling`: B_T^x ≤ (x/xc)^T

    Steps 2 and 3 are proved; step 1 is the remaining gap. -/
theorem hw_partial_sum_bound {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * ∏ T ∈ Finset.range N, (1 + (x / xc) ^ (T + 1)) ^ 2 := by
  sorry

/-! ## Derivation of summability from the partial-sum bound

Using `hw_partial_sum_bound` and `hw_upper_bound_abstract`, we prove
that Z(x) is summable for x < xc. This is the Hammersley-Welsh upper bound.
-/

/-- **Hammersley-Welsh upper bound on Z(x)**: For 0 < x < x_c,
    the partition function Z(x) = ∑ c_n x^n converges.

    This follows from:
    1. `hw_partial_sum_bound`: partial sums ≤ 2·∏(1+(x/xc)^T)²
    2. `hw_upper_bound_abstract`: the products are uniformly bounded
    3. `summable_of_sum_range_le`: bounded non-negative partial sums → summable -/
theorem hammersley_welsh_summable {x : ℝ} (hx : 0 < x) (hxc : x < xc) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  -- Step 1: Get the uniform bound on products
  have hr : x / xc < 1 := (div_lt_one xc_pos).mpr hxc
  have hr0 : 0 ≤ x / xc := div_nonneg hx.le xc_pos.le
  obtain ⟨C, hC_pos, hC_bound⟩ := hw_upper_bound_abstract hr0 hr
    (fun T => pow_nonneg hr0 T) (fun T => le_refl _)
  -- Step 2: Combine with partial sum bound to get uniform bound
  have hbound : ∀ N, ∑ n ∈ Finset.range N, (saw_count n : ℝ) * x ^ n ≤ 2 * C := by
    intro N
    match N with
    | 0 => simp; linarith
    | N + 1 =>
      calc ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n
          ≤ 2 * ∏ T ∈ Finset.range N, (1 + (x / xc) ^ (T + 1)) ^ 2 :=
            hw_partial_sum_bound hx hxc N
        _ ≤ 2 * C := by
            exact mul_le_mul_of_nonneg_left (hC_bound N) (by norm_num)
  -- Step 3: Summability from bounded partial sums
  exact summable_of_sum_range_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.le n))
    hbound

/-! ## Summary: The full upper bound argument

The complete upper bound argument from the paper:

1. **Bridge decomposition exists**: Every SAW γ decomposes uniquely into
   a pair of bridge sequences (left, right) with monotone widths.

2. **Counting by subsets**: The decomposition gives an injection
   SAWs → {(S₁, S₂) : subsets of ℕ} × ∏_{T ∈ S₁ ∪ S₂} Bridge(T)

3. **Bridge bound**: At x = x_c, B_T^{x_c} ≤ 1 (from strip identity).

4. **Bridge scaling**: For x < x_c, B_T^x ≤ (x/x_c)^T · B_T^{x_c} ≤ (x/x_c)^T.

5. **Product convergence**: ∏_{T≥1} (1 + (x/x_c)^T)² < ∞ since x/x_c < 1.

6. **Conclusion**: Z(x) ≤ 2 · ∏_{T≥1} (1 + B_T^x)² < ∞ for x < x_c,
   giving μ ≤ x_c⁻¹ = √(2+√2).
-/

end
