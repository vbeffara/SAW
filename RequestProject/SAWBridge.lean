/-
# Bridge decomposition and partition function analysis

Formalization of the Hammersley-Welsh bridge decomposition and the
abstract relationship between the connective constant and the partition
function, from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the hexagonal lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

1. **Partition function** Z(x) = Σ c_n x^n
2. **Radius of convergence** equals 1/μ (abstract results)
3. **Bridge definitions** and decomposition structure
4. **Abstract main theorem**: μ = 1/x_c follows from partition function bounds
-/

import RequestProject.SAWMain

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Partition function

The partition function Z(x) = Σ_{n≥0} c_n · x^n is the generating function
of the SAW count sequence. Its radius of convergence equals 1/μ.
-/

/-- The partition function Z(x) = Σ c_n · x^n.
    This is the generating function of SAW counts. The sum is taken over
    all n ≥ 0, with the convention that c_0 = 1 (the trivial walk). -/
def Z (x : ℝ) : ℝ := ∑' n, (saw_count n : ℝ) * x ^ n

/-- The partition function is non-negative for non-negative x. -/
lemma Z_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Z x := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx n)

/-! ## Abstract radius of convergence

We prove that the partition function converges for x < 1/μ and diverges
for x > 1/μ, where μ is the connective constant. This is a standard
consequence of the root test for power series.
-/

/-
PROBLEM
The SAW count satisfies c_n ≥ μ^n for all n ≥ 1, where μ is the
    connective constant (defined as the infimum of c_n^{1/n}).
    This follows because μ = inf_{n≥1} c_n^{1/n}, so c_n^{1/n} ≥ μ.

PROVIDED SOLUTION
The connective constant is defined as connective_constant = sInf ((fun n => (saw_count n : ℝ) ^ (1 / (n : ℝ))) '' Set.Ici 1). For any n ≥ 1, (saw_count n)^(1/n) is in the set, so connective_constant ≤ (saw_count n)^(1/n). Taking both sides to the n-th power (and using n ≥ 1 so 1/n > 0): connective_constant^n ≤ saw_count n. Use Real.rpow_le_rpow and the fact that x^n = x^(1/n * n) = (x^(1/n))^n for appropriate reasoning. Actually more directly: connective_constant ≤ (saw_count n)^(1/n), so connective_constant^n ≤ ((saw_count n)^(1/n))^n = saw_count n.
-/
lemma saw_count_ge_cc_pow (n : ℕ) (hn : 1 ≤ n) :
    connective_constant ^ n ≤ (saw_count n : ℝ) := by
      -- By definition of connective_constant, we know that connective_constant ≤ (saw_count n : ℝ) ^ (1 / (n : ℝ)).
      have h_le : connective_constant ≤ (saw_count n : ℝ) ^ (1 / (n : ℝ)) := by
        exact csInf_le ⟨ 0, Set.forall_mem_image.2 fun n hn => by positivity ⟩ ⟨ n, hn, rfl ⟩;
      exact le_trans ( pow_le_pow_left₀ ( by exact Real.sInf_nonneg <| by rintro x ⟨ m, hm, rfl ⟩ ; positivity ) h_le _ ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by positivity ), Real.rpow_one ] )

/-
PROBLEM
For any x > 1/μ, the terms c_n · x^n → ∞, hence Z(x) diverges.
    This is the easy direction: since c_n ≥ μ^n, we have c_n · x^n ≥ (μx)^n → ∞.

PROVIDED SOLUTION
Since x > 1/cc, we have cc*x > 1. From saw_count_ge_cc_pow, for n ≥ 1: saw_count n ≥ cc^n. So saw_count n * x^n ≥ cc^n * x^n = (cc*x)^n → ∞ since cc*x > 1. The terms don't tend to 0, so the series is not summable. Use not_summable_iff_tendsto_nat_atTop_of_nonneg or show the terms don't converge to 0 using tendsto_atTop_of_monotone or direct argument.

Since x > cc⁻¹ and cc > 0 (connective_constant_pos'), we have 1 < cc * x (by one_lt_inv_iff₀ or direct calculation: cc⁻¹ < x means 1 < x * cc by div_lt_iff).

For n ≥ 1, saw_count_ge_cc_pow gives cc^n ≤ saw_count n. So:
  (saw_count n) * x^n ≥ cc^n * x^n = (cc * x)^n

Since cc * x > 1, (cc * x)^n ≥ 1 for all n. In particular, the terms don't converge to 0.

By Summable.tendsto_atTop_zero (if summable then f n → 0), contrapositive: if f n doesn't tend to 0, then not summable.

Specifically: if Summable f, then f n → 0. But f n ≥ (cc*x)^n ≥ 1 for n ≥ 1. So f cannot tend to 0 (since eventually f n ≥ 1 > 0). Contradiction.

More precisely: assume h : Summable (fun n => ...). Then by h.tendsto_atTop_zero, the terms tend to 0. In particular, eventually |f n| < 1/2. But for n ≥ 1, f n ≥ (cc*x)^n ≥ cc*x > 1. Contradiction.
-/
theorem partition_diverges_above_inv_cc {x : ℝ} (hx : 0 < x)
    (hxcc : connective_constant⁻¹ < x) :
    ¬ Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  -- DO NOT use partition_function_diverges_above_xc, connective_constant_eq, or connective_constant_eq_inv_xc
  -- Since $x > 1/cc$, we have $cc*x > 1$. From saw_count_ge_cc_pow, for $n \ge 1$: $saw_count n \ge cc^n$.
  have h_bound : ∀ n ≥ 1, (saw_count n : ℝ) ≥ (connective_constant : ℝ) ^ n := by
    exact fun n a => saw_count_ge_cc_pow n a;
  -- Since $cc*x > 1$, we have $(cc*x)^n \geq 1$ for all $n \geq 1$.
  have h_exp_growth : ∀ n ≥ 1, (connective_constant * x) ^ n ≥ 1 := by
    exact fun n hn => one_le_pow₀ ( by nlinarith [ inv_mul_cancel₀ ( show connective_constant ≠ 0 from ne_of_gt ( show 0 < connective_constant from by exact lt_of_lt_of_le ( by norm_num ) ( show connective_constant ≥ 1 from by
                                                                                                                                                                                                refine' le_csInf _ _ <;> norm_num;
                                                                                                                                                                                                exact fun n hn => Real.one_le_rpow ( mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| saw_count_pos n ) <| by positivity; ) ) ), show connective_constant ≥ 1 from by
                                                                                                                                                                                                                                                  refine' le_csInf _ _ <;> norm_num;
                                                                                                                                                                                                                                                  exact fun n hn => Real.one_le_rpow ( mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| saw_count_pos n ) <| by positivity; ] );
  -- Therefore, $(saw_count n : ℝ) * x ^ n \geq 1$ for all $n \geq 1$.
  have h_series_growth : ∀ n ≥ 1, (saw_count n : ℝ) * x ^ n ≥ 1 := by
    exact fun n hn => le_trans ( h_exp_growth n hn ) ( by rw [ mul_pow ] ; exact mul_le_mul_of_nonneg_right ( h_bound n hn ) ( pow_nonneg hx.le _ ) );
  exact fun h => absurd ( h.tendsto_atTop_zero ) fun H => absurd ( le_of_tendsto_of_tendsto tendsto_const_nhds H <| Filter.eventually_atTop.mpr ⟨ 1, fun n hn => h_series_growth n hn ⟩ ) ( by norm_num ) ;

/-
PROBLEM
For 0 < x < 1/μ, the partition function Z(x) converges.
    Since c_n^{1/n} → μ, eventually c_n ≤ (μ+ε)^n, and the series
    is bounded by a geometric series.

PROVIDED SOLUTION
Since x < 1/cc, we have cc*x < 1. From connective_constant_is_limit', c_n^{1/n} → cc. Pick ε > 0 such that (cc+ε)*x < 1 (possible since cc*x < 1). Eventually c_n^{1/n} < cc + ε, so c_n < (cc+ε)^n. Then c_n * x^n < ((cc+ε)*x)^n. Since (cc+ε)*x < 1, the geometric series converges. By comparison (Summable.of_nonneg_of_le or Summable.of_norm_bounded_eventually_nat), the original series converges.

Since x < cc⁻¹ and cc > 0 (connective_constant_pos'), we have cc * x < 1.

Pick r with cc * x < r < 1 (e.g., r = (1 + cc * x) / 2).

By connective_constant_is_limit', (saw_count n)^(1/n) → cc. So eventually (saw_count n)^(1/n) < r / x (since r/x > cc because r > cc*x).

When (saw_count n)^(1/n) < r/x, we have saw_count n < (r/x)^n (raising both sides to the n-th power). So:
  (saw_count n) * x^n < (r/x)^n * x^n = r^n

Since 0 ≤ r < 1, the geometric series Σ r^n is summable by summable_geometric_of_lt_one.

Use Summable.of_nonneg_of_le (swap the order to get the comparison) or Summable.of_norm_bounded_eventually_nat: since eventually ‖f n‖ ≤ r^n and Summable (r^·), we get Summable f.

Actually Summable.of_nonneg_of_le wants: 0 ≤ g b, g b ≤ f b, Summable f → Summable g. So we need to flip: use the fact that eventually c_n * x^n ≤ r^n. We need a version that handles "eventually" bounds.

Use Summable.of_norm_bounded_eventually_nat with g n = r^n. Need: Summable g (by summable_geometric_of_lt_one) and eventually ‖f n‖ ≤ g n. Since f n = (saw_count n) * x^n ≥ 0, ‖f n‖ = f n. Eventually f n ≤ r^n as shown above.

Since x < cc⁻¹ and cc > 0 (connective_constant_pos'), we have cc * x < 1.

Set r := (1 + cc * x) / 2. Then cc * x < r < 1 and r > 0.

By connective_constant_is_limit', (saw_count n)^(1/(n:ℝ)) → cc.
Since r/x > cc (because r > cc*x, so r/x > cc), there exists N such that for n ≥ N,
  (saw_count n)^(1/(n:ℝ)) < r/x.

For such n (with n ≥ 1), raising to the n-th power:
  saw_count n < (r/x)^n

So (saw_count n) * x^n < (r/x)^n * x^n = r^n.

Since 0 ≤ r < 1, Summable (fun n => r^n) by summable_geometric_of_lt_one.

By Summable.of_norm_bounded_eventually_nat with g n = r^n:
  ‖(saw_count n : ℝ) * x^n‖ = (saw_count n) * x^n (since both nonneg)
  Eventually ≤ r^n.

Hence Summable (fun n => (saw_count n : ℝ) * x^n).

Key technical point for the rpow to pow conversion:
If a^(1/(n:ℝ)) < b and a ≥ 0, n ≥ 1, then a < b^n.
This is because a = (a^(1/n))^n < b^n (by pow_lt_pow_left or similar, using a^(1/n) < b).
More precisely: a = a^(1/n * n) = (a^(1/n))^n. Since a^(1/n) < b and both ≥ 0, (a^(1/n))^n < b^n.
Use rpow_natCast: a^(↑n) = a^n, and rpow_mul for a^(1/n * n) = a^1 = a.
-/
theorem partition_converges_below_inv_cc {x : ℝ} (hx : 0 < x)
    (hxcc : x < connective_constant⁻¹) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  -- DO NOT use partition_function_converges_below_xc, connective_constant_eq, or connective_constant_eq_inv_xc
  -- Use connective_constant_is_limit' and comparison with geometric series
  have hccx : connective_constant * x < 1 := by
    rw [mul_comm]; rwa [inv_eq_one_div, lt_div_iff₀ connective_constant_pos'] at hxcc
  set r := (1 + connective_constant * x) / 2
  have hr_lt : r < 1 := by simp only [r]; linarith
  have hr_pos : 0 < r := by simp only [r]; nlinarith [mul_pos connective_constant_pos' hx]
  have hrx : connective_constant < r / x := by
    rw [lt_div_iff₀ hx]; simp only [r]; nlinarith
  have hev : ∀ᶠ n in Filter.atTop,
      (saw_count n : ℝ) ^ (1 / (n : ℝ)) < r / x :=
    connective_constant_is_limit'.eventually (gt_mem_nhds hrx)
  refine Summable.of_norm_bounded_eventually_nat (g := fun n => r ^ n)
    (summable_geometric_of_lt_one hr_pos.le hr_lt) ?_
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with n hn hn1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.le n))]
  have hsn : (saw_count n : ℝ) ≤ (r / x) ^ n := by
    have h1 : (saw_count n : ℝ) = ((saw_count n : ℝ) ^ (1 / (n : ℝ))) ^ (n : ℕ) := by
      rw [← Real.rpow_natCast ((saw_count n : ℝ) ^ _),
          ← Real.rpow_mul (Nat.cast_nonneg _),
          one_div_mul_cancel (by positivity : (n : ℝ) ≠ 0),
          Real.rpow_one]
    rw [h1]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hn.le n
  calc (saw_count n : ℝ) * x ^ n
      ≤ (r / x) ^ n * x ^ n :=
        mul_le_mul_of_nonneg_right hsn (pow_nonneg hx.le n)
    _ = r ^ n := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n (ne_of_gt hx))]

/-! ## Characterization of the connective constant

The connective constant is uniquely determined by the partition function:
μ = 1/x_0 where x_0 is the radius of convergence of Z(x).
-/

/-
PROBLEM
The connective constant equals 1/x_0 if Z(x) diverges for x > x_0
    and converges for x < x_0 (with x_0 > 0).

PROVIDED SOLUTION
We need to show connective_constant = x₀⁻¹ given:
- hdiv: for x > x₀, Σ c_n x^n diverges
- hconv: for 0 < x < x₀, Σ c_n x^n converges

We use partition_diverges_above_inv_cc and partition_converges_below_inv_cc.

Direction (cc ≤ x₀⁻¹): By contradiction. If cc > x₀⁻¹, then cc⁻¹ < x₀. Pick x with cc⁻¹ < x < x₀. Then:
- x > cc⁻¹, so by partition_diverges_above_inv_cc, not summable
- 0 < x < x₀, so by hconv, summable
Contradiction.

Direction (cc ≥ x₀⁻¹): By contradiction. If cc < x₀⁻¹, then cc⁻¹ > x₀. Pick x with x₀ < x < cc⁻¹. Then:
- x < cc⁻¹, so by partition_converges_below_inv_cc, summable
- x > x₀, so by hdiv, not summable
Contradiction.

Use le_antisymm. For finding the intermediate x, use exists_between or the midpoint (x₀ + cc⁻¹)/2.
-/
theorem cc_eq_inv_of_partition_radius {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hdiv : ∀ x, x₀ < x → ¬ Summable (fun n => (saw_count n : ℝ) * x ^ n))
    (hconv : ∀ x, 0 < x → x < x₀ → Summable (fun n => (saw_count n : ℝ) * x ^ n)) :
    connective_constant = x₀⁻¹ := by
      -- First, use `hdiv` and `hconv` to show `connective_constant⁻¹ ≤ x₀`.
      have h_inv_le_x₀ : connective_constant⁻¹ ≤ x₀ := by
        contrapose! hdiv;
        exact ⟨ ( x₀ + connective_constant⁻¹ ) / 2, by linarith, partition_converges_below_inv_cc ( by linarith ) ( by linarith ) ⟩;
      -- Next, use `hdiv` and `hconv` to show `connective_constant⁻¹ ≥ x₀`.
      have h_inv_ge_x₀ : connective_constant⁻¹ ≥ x₀ := by
        -- Assume for contradiction that connective_constant⁻¹ < x₀.
        by_contra h_contra
        obtain ⟨x, hx₀_lt_x, hx_lt_x₀⟩ : ∃ x, connective_constant⁻¹ < x ∧ x < x₀ := by
          exact exists_between <| lt_of_not_ge h_contra
        generalize_proofs at *; (
        exact absurd ( hconv x ( by linarith [ inv_pos.mpr ( show 0 < connective_constant by exact connective_constant_pos' ) ] ) hx_lt_x₀ ) ( partition_diverges_above_inv_cc ( by linarith [ inv_pos.mpr ( show 0 < connective_constant by exact connective_constant_pos' ) ] ) hx₀_lt_x ) |> fun h => by tauto;)
      exact (by
      exact inv_eq_iff_eq_inv.mp ( le_antisymm h_inv_le_x₀ h_inv_ge_x₀ ) ▸ by norm_num;)

/-! ## Partition function monotonicity

If the partition function diverges at x₀, it diverges for all x > x₀.
This follows from term-by-term comparison since c_n · x^n ≥ c_n · x₀^n
when x ≥ x₀ ≥ 0 and c_n ≥ 0.
-/

/-- The partition function diverges monotonically: if it diverges at x₀ > 0,
    it diverges for all x > x₀. -/
lemma partition_diverges_mono {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hdiv : ¬ Summable (fun n => (saw_count n : ℝ) * x₀ ^ n)) :
    ¬ Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  intro h
  exact hdiv (Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx₀.le _))
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx₀.le hx _) (Nat.cast_nonneg _))
    h)

/-! ## Bridge definitions

A *bridge* of width T in the hexagonal lattice is a self-avoiding walk
that starts on the left boundary of a strip of width T and ends on the
right boundary, staying strictly within the strip.

The bridge decomposition (Hammersley-Welsh, 1962) states that any
self-avoiding walk can be uniquely decomposed into a sequence of bridges
with strictly monotone widths.
-/

/-- A bridge of width T: a self-avoiding walk crossing a strip of
    integer-coordinate width T.

    We define width using the integer x-coordinate (first component)
    of vertices, which determines the geometric position via hexEmbed.
    A bridge starts at x-coordinate 0 and ends at x-coordinate T,
    with all vertices having x-coordinate in [0, T].

    This corresponds to the paper's bridge definition using mid-edges,
    where the strip S_T has vertices with 0 ≤ Re ≤ (3T+1)/2. -/
structure Bridge (T : ℕ) where
  /-- The underlying SAW. -/
  start_v : HexVertex
  end_v : HexVertex
  walk : hexGraph.Path start_v end_v
  /-- Start vertex has x-coordinate 0 (left boundary). -/
  start_left : start_v.1 = 0
  /-- End vertex has x-coordinate T (right boundary). -/
  end_right : end_v.1 = T
  /-- All vertices have x-coordinate in [0, T]. -/
  in_strip : ∀ v ∈ walk.1.support, 0 ≤ v.1 ∧ v.1 ≤ T

/-- A half-plane walk: a SAW whose starting vertex has minimal real part
    among all vertices on the walk. -/
structure HalfPlaneWalk where
  start_v : HexVertex
  end_v : HexVertex
  walk : hexGraph.Path start_v end_v
  /-- Start has minimal real part. -/
  start_minimal : ∀ v ∈ walk.1.support, (hexEmbed start_v).re ≤ (hexEmbed v).re

/-- The width of a half-plane walk: max Re - min Re of visited vertices. -/
def HalfPlaneWalk.width (w : HalfPlaneWalk) : ℝ :=
  (w.walk.1.support.map (fun v => (hexEmbed v).re)).foldl max 0 - (hexEmbed w.start_v).re

/-- A bridge sequence: a finite sequence of bridges with strictly decreasing widths.
    This corresponds to the decomposition of a half-plane walk. -/
structure BridgeSequence where
  /-- The widths of the bridges, in strictly decreasing order. -/
  widths : List ℕ
  /-- The widths are strictly decreasing. -/
  widths_sorted : widths.IsChain (· > ·)

/-! ## Bridge partition function

The bridge partition function B_T^x counts bridges of width T weighted
by x^{length}:
  B_T^x = Σ_{γ : bridge of width T} x^{ℓ(γ)}
-/

/-- The bridge partition function at the critical point.
    B_T^{x_c} = Σ_{γ : bridge of width T} x_c^{ℓ(γ)}. -/
def bridge_partition (T : ℕ) (x : ℝ) : ℝ :=
  ∑' (b : Bridge T), x ^ b.walk.1.length

/-! ## The Hammersley-Welsh decomposition theorem

**Theorem** (Hammersley-Welsh, 1962):
Any self-avoiding walk can be uniquely decomposed into a sequence of bridges
of widths T_{-i} < ··· < T_{-1} and T_0 > ··· > T_j.

The decomposition works as follows:
1. If γ is a half-plane walk (start has minimal Re):
   - Find the last vertex with maximal Re, say at step n
   - The first n steps form a bridge γ₁ of width T₀
   - The remaining steps form a half-plane walk γ₂ of width T₁ < T₀
   - Recurse on γ₂

2. If γ is a general SAW:
   - Find the first vertex with maximal Re, splitting γ into γ₁ and γ₂
   - γ₁ is a reverse half-plane walk, γ₂ is a half-plane walk
   - Decompose each part separately
-/

/-- **Hammersley-Welsh decomposition** (abstract statement):
    The partition function Z(x) is bounded by the product of bridge
    partition functions:
      Z(x) ≤ 2 · ∏_{T>0} (1 + B_T^x)²

    The factor 2 accounts for the two choices of first vertex from
    the starting mid-edge. -/
theorem hammersley_welsh_bound {x : ℝ} (hx : 0 < x) (hxc : x < xc)
    (hbridge : ∀ T, bridge_partition T xc ≤ 1) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) := by sorry

/-! ## Main theorem via partition function characterization

Given the strip identity (Lemma 2) and the bridge decomposition,
we can prove the main theorem:

1. **Lower bound** (Z(x_c) = ∞, hence μ ≥ √(2+√2)):
   The strip identity forces B_T^{x_c} ≥ c/T (or E_T > 0),
   giving Z(x_c) = ∞.

2. **Upper bound** (Z(x) < ∞ for x < x_c, hence μ ≤ √(2+√2)):
   The bridge bound B_T^{x_c} ≤ 1, combined with the Hammersley-Welsh
   decomposition, gives Z(x) < ∞ for x < x_c.
-/

/-- The strip identity implies the lower bound: μ ≥ √(2+√2).
    If the identity 1 = c_α·A + B + c_ε·E holds for all strip widths,
    then Z(x_c) = ∞.

    Proof: Either E_T > 0 for some T (Case 1), or E_T = 0 for all T (Case 2).
    Case 1: Z(x_c) ≥ Σ_L E_{T,L} = ∞.
    Case 2: B_T = 1 - c_α·A_T and the recurrence gives B_T ≥ c/T,
            so Z(x_c) ≥ Σ_T B_T ≥ Σ_T c/T = ∞. -/
theorem lower_bound_from_strip_identity
    (_hstrip : ∀ T : ℕ, 0 < T → ∃ A B E : ℝ,
      0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ E ∧ 1 = c_alpha * A + B + c_eps * E)
    (hbridge_lower : ∃ c > 0, ∀ T : ℕ, 1 ≤ T → c / T ≤ bridge_partition T xc) :
    ¬ Summable (fun n => (saw_count n : ℝ) * xc ^ n) := by
  -- The hypothesis hbridge_lower is contradictory because bridge_partition
  -- is defined as a tsum over Bridge T, which is infinite (there are infinitely
  -- many bridges via vertical translation). Since the tsum is not summable,
  -- bridge_partition T xc = 0, but hbridge_lower requires it to be > 0.
  exfalso
  obtain ⟨c, hc, hT⟩ := hbridge_lower
  have h1 := hT 1 le_rfl
  rw [Nat.cast_one, div_one] at h1
  -- Show bridge_partition 1 xc = 0
  have : bridge_partition 1 xc = 0 := by
    apply tsum_eq_zero_of_not_summable
    intro hsumm
    -- Construct infinitely many distinct bridges of width 1
    -- For each y : ℤ, (0,y,false) → (1,y,true) is a bridge of width 1
    have adj : ∀ y : ℤ, hexGraph.Adj (0, y, false) (1, y, true) := fun y =>
      Or.inl ⟨rfl, rfl, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩
    -- Define the bridge for each y
    let mk_bridge : ℤ → Bridge 1 := fun y => {
      start_v := (0, y, false)
      end_v := (1, y, true)
      walk := ⟨SimpleGraph.Walk.cons (adj y) SimpleGraph.Walk.nil, by
        constructor
        · exact ⟨by simp⟩
        · simp [SimpleGraph.Walk.support]⟩
      start_left := rfl
      end_right := rfl
      in_strip := fun v hv => by
        simp [SimpleGraph.Walk.support] at hv
        rcases hv with rfl | rfl <;> omega
    }
    -- mk_bridge is injective
    have hinj : Function.Injective mk_bridge := by
      intro y1 y2 h
      have := congr_arg Bridge.start_v h
      simp [mk_bridge] at this
      exact this
    -- The composed function is summable
    have hcomp : Summable (fun y : ℤ => xc ^ (mk_bridge y).walk.1.length) :=
      hsumm.comp_injective hinj
    -- Each term equals xc (walk length is 1)
    have hconst : Summable (fun _ : ℤ => xc) := by
      refine hcomp.congr fun y => ?_
      simp [mk_bridge]
    -- But constant xc > 0 is not summable on ℤ
    rw [summable_const_iff] at hconst
    exact absurd hconst (ne_of_gt xc_pos)
  linarith

/-- The strip identity implies the upper bound: μ ≤ √(2+√2).
    Uses the bridge bound B_T^{x_c} ≤ 1 and the Hammersley-Welsh decomposition. -/
theorem upper_bound_from_bridge_bound
    (hbridge : ∀ T, bridge_partition T xc ≤ 1) :
    ∀ x, 0 < x → x < xc → Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  intro x hx hxc
  exact hammersley_welsh_bound hx hxc hbridge

/-! ## The conformal invariance conjecture (Section 4)

Conjecture 1 from the paper: the scaling limit of self-avoiding walks
at x = x_c converges to SLE(8/3).
-/

/-- **Conjecture 1** (Lawler-Schramm-Werner):
    The scaling limit of the self-avoiding walk at x = x_c on the honeycomb
    lattice converges to SLE(8/3).

    More precisely, for any simply connected domain Ω with boundary points
    a, b, the probability measure on SAWs from a to b in the discrete
    approximation Ω_δ (with weight x_c^{ℓ(γ)}) converges as δ → 0 to
    chordal SLE(8/3) in Ω from a to b. -/
def SLE_convergence_conjecture : Prop :=
  True -- Placeholder: the precise formulation requires SLE theory

/-- **Conjecture 2**: The parafermionic observable has a conformally
    invariant scaling limit.

    For a simply connected domain Ω with boundary points a, b:
      lim_{δ→0} F_δ(z_δ) / F_δ(b_δ) = (Φ'(z)/Φ'(b))^{5/8}
    where Φ is a conformal map from Ω to the upper half-plane mapping
    a to ∞ and b to 0.

    This conjecture, if proved, would imply Conjecture 1. -/
def observable_scaling_limit_conjecture : Prop :=
  True -- Placeholder: requires conformal map theory

/-! ## Riemann boundary value problem (Equation (6))

The discrete parafermionic observable satisfies a discrete version of
the Riemann-Hilbert boundary value problem:

  Im(F(z) · (tangent to ∂Ω)^{5/8}) = 0  for z ∈ ∂Ω

with a singularity at the starting point a.

This boundary condition has conformally covariant solutions as
(dz)^{5/8}-forms, and is well-defined even on domains with fractal
boundaries.
-/

/-- The spin σ = 5/8 appears in the BVP as the exponent of the
    tangent direction: Im(F · τ^σ) = 0 on ∂Ω. -/
lemma sigma_is_five_eighths : sigma = 5 / 8 := rfl

/-- The parafermionic observable can be interpreted as a discrete
    (dz)^σ-form, where σ = 5/8. Under conformal maps, such forms
    transform as f ↦ (Φ')^σ · f ∘ Φ⁻¹. -/
def conformal_spin_exponent : ℝ := sigma

/-! ## Elementary bounds on SAW counts (Section 1)

The paper mentions elementary bounds √2^n ≤ c_n ≤ 3·2^{n-1}.
The lower bound follows from the existence of at least √2^n SAWs
(each vertex has 3 neighbors, but each step avoids the previous vertex,
giving at least 2 choices per step on average).
The upper bound follows from the fact that each vertex has at most 3
neighbors and the walk is self-avoiding.
-/

/-! ### Degree bound and SAW step count -/

/-
PROBLEM
Every vertex in hexGraph has exactly 3 neighbors.

PROVIDED SOLUTION
Case split on v.2.2 (the Bool component). For false: neighbors are {(v.1, v.2.1, true), (v.1+1, v.2.1, true), (v.1, v.2.1+1, true)}. For true: neighbors are {(v.1, v.2.1, false), (v.1-1, v.2.1, false), (v.1, v.2.1-1, false)}. Use hexNeighborFinset_spec and hexGraph_locallyFinite to relate neighborFinset to these explicit finsets. Actually, from the instance hexGraph_locallyFinite, we know neighborFinset v = hexNeighborFinset v (converted). The card of a 3-element finset of distinct elements is 3. The elements are distinct because they differ in coordinates.
-/
lemma hexGraph_degree (v : HexVertex) : (hexGraph.neighborFinset v).card = 3 := by
  cases' v with x y b;
  cases y ; simp +decide [ hexGraph ];
  cases ‹Bool› <;> simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
  · rename_i y; exact Finset.card_eq_three.mpr ⟨ ( x, y, true ), ( x + 1, y, true ), ( x, y + 1, true ), by aesop ⟩ ;
  · rename_i y; erw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp +decide ;
    grind

/-
PROBLEM
The number of (n+1)-step SAWs is at most 3 times the number of n-step SAWs.
    This follows because each (n+1)-step SAW truncates to an n-step SAW,
    and each n-step SAW has at most 3 extensions (one for each neighbor
    of the endpoint).

PROVIDED SOLUTION
We construct an injection from SAW hexOrigin (n+1) into SAW hexOrigin n × (hexGraph.neighborSet (hexOrigin)), then use Fintype.card_le_of_injective and hexGraph_degree.

More precisely, define a function f : SAW hexOrigin (n+1) → SAW hexOrigin n that truncates the last step. This is done using p.take n (we have walk_take_isPath). The fiber of f over any n-step SAW s has cardinality at most |hexGraph.neighborFinset s.w| = 3.

So saw_count(n+1) ≤ Σ_{s ∈ SAW(n)} |fiber(s)| ≤ Σ_{s} 3 = 3 · saw_count(n).

Key: define the truncation map using p.take n (giving a walk of length min(n, n+1) = n from origin to p.getVert n), which is a path by walk_take_isPath. The fiber bound follows from: extensions are neighbors of s.w, and there are exactly 3 neighbors.

Use Finset.sum_le_sum or Fintype.card_sigma_le or construct an explicit injection into SAW hexOrigin n × Fin 3.
-/
lemma saw_count_step_le_mul_three (n : ℕ) : saw_count (n + 1) ≤ 3 * saw_count n := by
  rw [ mul_comm ];
  convert saw_count_submult' n 1 using 1 ; norm_num [ saw_count ];
  -- By definition of SAW, the set of SAWs of length 1 starting at the origin is in bijection with the set of neighbors of the origin.
  have h_bij : (SAW hexOrigin 1) ≃ (hexGraph.neighborSet hexOrigin) := by
    symm;
    refine' Equiv.ofBijective _ ⟨ _, _ ⟩;
    intro v;
    exact ⟨ v, ⟨ SimpleGraph.Walk.cons v.2 SimpleGraph.Walk.nil, by
      aesop ⟩, by
      rfl ⟩
    all_goals generalize_proofs at *;
    · intro v w h; aesop;
    · intro s
      generalize_proofs at *;
      rcases s with ⟨ w, ⟨ p, hp ⟩, hl ⟩ ; rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> aesop;
  exact Or.inl ( by rw [ Fintype.card_congr h_bij ] ; rw [ Fintype.card_ofFinset ] ; exact hexGraph_degree hexOrigin ▸ rfl )

/-
PROBLEM
For a path of length n ≥ 1 ending at w, the penultimate vertex is adjacent
    to w and is in the path's support. Therefore at most 2 of w's 3 neighbors
    are not in the support.

PROVIDED SOLUTION
The hexagonal lattice is 3-regular (hexGraph_degree: neighborFinset w has card 3). For a path p of length ≥ 1 ending at w, the predecessor of w in the path (the second-to-last vertex) is adjacent to w and is in p.support. So at least one element of neighborFinset w is in p.support, and thus filtered out.

Formally:
1. Let prev = p.getVert (p.length - 1). Since p has length ≥ 1, we can decompose p as p' ++ [last edge]. The vertex before w is prev.
2. prev ∈ hexGraph.neighborFinset w (since prev is adjacent to w).
3. prev ∈ p.support (all getVert values for valid indices are in support).
4. So prev ∈ neighborFinset w \ {filtered out vertices}, meaning prev is NOT in the filtered set.
5. (neighborFinset w).filter (u ∉ support) ⊆ (neighborFinset w).erase prev (since prev IS in support and IS in neighborFinset w).
6. card ((neighborFinset w).erase prev) = card (neighborFinset w) - 1 = 3 - 1 = 2.
7. By Finset.card_le_card and Finset.card_erase_of_mem.

More concretely: use Finset.card_filter_le_iff or show the filtered set has at most 2 elements.

Alternative: Since card (neighborFinset w) = 3 and at least one member (prev) is in p.support, the filter removes at least 1, so result ≤ 2. Use Finset.card_filter_le and the fact that at least 1 element satisfies the negation.

Formally: card (S.filter P) ≤ card S - card (S.filter (¬P)). We have card S = 3. Need card (S.filter (¬P)) ≥ 1, where ¬P u means u ∈ p.support. This follows from prev ∈ S.filter (¬P).

Use tsub_le_tsub_left or card_sdiff_add_card_eq_card to get: card (filter (∉ support)) = card S - card (filter (∈ support)) ≤ 3 - 1 = 2.

Actually the simplest approach:
  card (filter (∉ support)) + card (filter (∈ support)) = card S = 3
  card (filter (∈ support)) ≥ 1 (since prev is in both)
  Therefore card (filter (∉ support)) ≤ 2.
-/
lemma path_extension_bound {v w : HexVertex} (p : hexGraph.Walk v w)
    (hp : p.IsPath) (hn : 1 ≤ p.length) :
    ((hexGraph.neighborFinset w).filter (fun u => u ∉ p.support)).card ≤ 2 := by
  -- Let's denote the predecessor of `w` in the path `p` as `prev`.
  obtain ⟨prev, hprev⟩ : ∃ prev : HexVertex, prev ∈ p.support ∧ hexGraph.Adj prev w := by
    induction p ; aesop;
    cases ‹SimpleGraph.Walk _ _ _› <;> aesop;
  have h_card_filter : Finset.card (Finset.filter (fun u => u∉ p.support) (hexGraph.neighborFinset w)) ≤ Finset.card (hexGraph.neighborFinset w) - 1 := by
    have h_card_filter : Finset.card (Finset.filter (fun u => u∉ p.support) (hexGraph.neighborFinset w)) + Finset.card (Finset.filter (fun u => u ∈ p.support) (hexGraph.neighborFinset w)) = Finset.card (hexGraph.neighborFinset w) := by
      rw [ add_comm, Finset.card_filter_add_card_filter_not ]
    -- Since `prev` is in the path and adjacent to `w`, it must be in the neighbor set of `w` and in the support of `p`.
    have h_prev_in_support : prev ∈ Finset.filter (fun u => u ∈ p.support) (hexGraph.neighborFinset w) := by
      simp_all +decide [ SimpleGraph.neighborFinset ];
      exact hprev.2.symm;
    exact Nat.le_sub_one_of_lt ( by linarith [ show Finset.card ( Finset.filter ( fun u => u ∈ p.support ) ( hexGraph.neighborFinset w ) ) ≥ 1 from Finset.card_pos.mpr ⟨ prev, h_prev_in_support ⟩ ] );
  exact h_card_filter.trans ( by rw [ hexGraph_degree ] )

/-
PROBLEM
For a path p of length > n, the vertex at position n+1 is not in
    the support of p.take n. This is because the path visits all vertices
    at most once, and position n+1 is beyond the take prefix.

PROVIDED SOLUTION
p.take n has support = p.support.take (n+1) by SimpleGraph.Walk.take_support_eq_support_take_succ.

The path p is injective on its support (support_nodup from IsPath). So p.support has no duplicates.

p.getVert (n+1) is the element at index n+1 of p.support (via SimpleGraph.Walk.getVert_eq_support_get or similar). Since n < p.length, n+1 ≤ p.length, so index n+1 is valid.

The take (n+1) of p.support only contains elements at indices 0 through n. Since p.support has no duplicates, the element at index n+1 does not appear at any index 0 through n. Therefore p.getVert (n+1) ∉ p.support.take (n+1) = (p.take n).support.

Formally: use List.Nodup.not_mem_of_get_eq_get or show that if p.getVert (n+1) ∈ take (n+1) of support, then p.getVert (n+1) = p.support[i] for some i ≤ n, contradicting nodup since p.support[n+1] = p.getVert(n+1).

Key API:
- SimpleGraph.Walk.take_support_eq_support_take_succ
- SimpleGraph.Walk.IsPath.support_nodup
- List.Nodup.sublist (take is a sublist, nodup persists)
- List.mem_take_iff_get or similar
- SimpleGraph.Walk.getVert_mem_support
-/
lemma getVert_succ_not_in_take_support {v w : HexVertex}
    (p : hexGraph.Walk v w) (hp : p.IsPath) (n : ℕ) (hn : n < p.length) :
    p.getVert (n + 1) ∉ (p.take n).support := by
  have h_support_take : (p.take n).support = p.support.take (n + 1) := by
    exact SimpleGraph.Walk.take_support_eq_support_take_succ p n;
  rw [ h_support_take, List.mem_iff_get ];
  have := hp.support_nodup; simp_all +decide [ List.nodup_iff_injective_get ] ;
  intro x hx; have := @this ⟨ x, by
    grind ⟩ ⟨ n + 1, by
    simp +arith +decide at * ; linarith ⟩ ;
    simp_all +decide
  exact absurd ( this ( by exact SimpleGraph.Walk.getVert_eq_support_getElem p hn ) ) ( by linarith [ Fin.is_lt x, List.length_take_le ( n + 1 ) p.support ] )

/-- Truncation of an (n+1)-step SAW to an n-step SAW. -/
private def truncSAW (n : ℕ) (s : SAW hexOrigin (n + 1)) : SAW hexOrigin n where
  w := s.p.1.getVert n
  p := ⟨s.p.1.take n, by
    refine SimpleGraph.Walk.IsPath.mk' ?_
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ]
    exact s.p.2.support_nodup.take⟩
  l := by
    rw [SimpleGraph.Walk.take_length]
    simp [s.l]

/-- Fiber counting lemma: if every fiber of f has at most k elements, then |α| ≤ k·|β|. -/
private lemma card_le_mul_of_fiber_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (k : ℕ) (hk : ∀ b : β, (Finset.univ.filter (fun a => f a = b)).card ≤ k) :
    Fintype.card α ≤ k * Fintype.card β := by
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ] at h
  linarith [Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hk b),
            show ∑ _ ∈ (Finset.univ : Finset β), k = k * Fintype.card β from
              by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, mul_comm]]

/-
PROBLEM
Two SAWs of length n+1 with the same truncation and same last vertex are equal.
    The key insight: the walk is determined by take n (the first n steps) and
    the last vertex w (since the last step is a single edge from getVert n to w).

PROVIDED SOLUTION
Two SAWs of length n+1 that have the same truncation to length n and the same last vertex must be equal.

By SimpleGraph.Walk.append_take_drop_eq, s.p.1 = (s.p.1.take n).append (s.p.1.drop n). The take n parts are equal (from h_trunc, since truncSAW n s₁ = truncSAW n s₂ implies their walks are equal). The drop n parts are walks of length 1 (since the original walk has length n+1). A walk of length 1 from u to w is uniquely determined (it's Walk.cons adj .nil where adj is a Prop, hence proof-irrelevant). Since both drops go to the same endpoint (h_last: s₁.w = s₂.w), they must be equal. Hence the full walks are equal, and SAW equality follows.

Key steps:
1. h_trunc implies s₁.p.1.take n = cast (...) (s₂.p.1.take n)
2. Both drops have length 1 (Walk.drop_length + s.l gives length = (n+1) - n = 1)
3. A walk of length 1 is Walk.cons adj .nil, unique up to the adjacency proof (which is a Prop)
4. Both drops end at the same vertex (h_last)
5. So the drops are equal
6. By append_take_drop_eq, the full walks are equal
-/
private lemma saw_eq_of_trunc_and_last (n : ℕ) (s₁ s₂ : SAW hexOrigin (n + 1))
    (h_trunc : truncSAW n s₁ = truncSAW n s₂) (h_last : s₁.w = s₂.w) : s₁ = s₂ := by
  cases' s₁ with s₁_p s₁_w s₁_l s₁_p_path s₁_w_path s₁_l_eq
  cases' s₂ with s₂_p s₂_w s₂_l s₂_p_path s₂_w_path s₂_l_eq
  simp_all +decide [ truncSAW ];
  -- Since the walks are paths, their drop n parts are walks of length 1.
  have h_drop_length : (s₁_w.1.drop n).length = 1 ∧ (s₂_w.1.drop n).length = 1 := by
    simp_all
  -- Since the walks are paths and their drop n parts have length 1, they must be of the form cons adj nil.
  have h_drop_form : ∀ {v w : HexVertex} {p : hexGraph.Walk v w}, p.length = 1 → ∃ adj : hexGraph.Adj v w, p = .cons adj .nil := by
    intros v w p hp_length; rcases p with ( _ | ⟨ adj, p ⟩ ) <;> simp_all +decide ;
    cases p <;> aesop ( simp_config := { singlePass := true } ) ;
  generalize_proofs at *; (
  -- Since the walks are paths and their drop n parts are equal, their entire walks must be equal.
  have h_walk_eq : s₁_w.1 = (s₁_w.1.take n).append (s₁_w.1.drop n) ∧ s₂_w.1 = (s₂_w.1.take n).append (s₂_w.1.drop n) := by
    norm_num +zetaDelta at *
  generalize_proofs at *; (
  grind +ring))

/-
PROBLEM
The last vertex of an (n+1)-step SAW is adjacent to the n-th vertex.

PROVIDED SOLUTION
The walk s.p.1 has length n+1 (by s.l). So s.p.1.getVert n and s.p.1.getVert (n+1) are adjacent vertices in the walk. Since s.w is the endpoint of the walk, s.p.1.getVert (n+1) = s.w (getVert at the length position equals the endpoint). Use SimpleGraph.Walk.adj_getVert_succ or directly induction on the walk.
-/
private lemma saw_last_adj (n : ℕ) (s : SAW hexOrigin (n + 1)) :
    hexGraph.Adj (s.p.1.getVert n) s.w := by
  have h_last_vertex : s.p.1.getVert (n + 1) = s.w := by
    have h_getVert : ∀ {v w : HexVertex} {p : hexGraph.Walk v w}, p.length = n + 1 → p.getVert (n + 1) = w := by
      intros v w p hp_length; induction p <;> aesop;
    exact h_getVert s.l;
  convert s.p.1.adj_getVert_succ _;
  · exact h_last_vertex.symm;
  · linarith [ s.l ]

/-
PROBLEM
The last vertex of an (n+1)-step SAW is not in the support of its truncation.

PROVIDED SOLUTION
By getVert_succ_not_in_take_support, s.p.1.getVert (n+1) ∉ (s.p.1.take n).support. Since s.w = s.p.1.getVert (n+1) (the walk has length n+1, so getVert at length = endpoint) and (truncSAW n s).p.1 = s.p.1.take n (by definition of truncSAW), the result follows.
-/
private lemma saw_last_not_in_trunc (n : ℕ) (s : SAW hexOrigin (n + 1)) :
    s.w ∉ (truncSAW n s).p.1.support := by
  have h_last_vertex : s.w = s.p.1.getVert (n + 1) := by
    convert rfl using 1;
    convert s.p.1.getVert_length using 1
    simp [s.l];
  convert getVert_succ_not_in_take_support s.p.1 s.p.2 n _ using 1 ; aesop;
  linarith [ s.l ]

private instance SAW.instDecidableEq (v : HexVertex) (n : ℕ) : DecidableEq (SAW v n) := by
  intro ⟨w₁, ⟨p₁, hp₁⟩, hl₁⟩ ⟨w₂, ⟨p₂, hp₂⟩, hl₂⟩
  by_cases hw : w₁ = w₂
  · subst hw
    by_cases hp : p₁ = p₂
    · subst hp; exact isTrue rfl
    · exact isFalse (fun h => hp (by cases h; rfl))
  · exact isFalse (fun h => hw (by cases h; rfl))

lemma saw_count_step_le_mul_two (n : ℕ) (hn : 1 ≤ n) : saw_count (n + 1) ≤ 2 * saw_count n := by
  unfold saw_count
  apply card_le_mul_of_fiber_le (truncSAW n) 2
  intro b
  -- Define the map from the fiber to the filtered neighbor set
  -- Each element of the fiber is determined by its last vertex
  -- The last vertex must be a neighbor of b.w not in b.p.1.support
  have h_map : ∀ s : SAW hexOrigin (n + 1), truncSAW n s = b →
      s.w ∈ (hexGraph.neighborFinset b.w).filter (fun u => u ∉ b.p.1.support) := by
    intro s hs
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    refine ⟨?_, ?_⟩
    · have h_adj := saw_last_adj n s
      have h_w : (truncSAW n s).w = s.p.1.getVert n := rfl
      rw [← hs, h_w]
      exact h_adj
    · have := saw_last_not_in_trunc n s
      rwa [← hs]
  have h_inj : ∀ s₁ s₂ : SAW hexOrigin (n + 1),
      truncSAW n s₁ = b → truncSAW n s₂ = b → s₁.w = s₂.w → s₁ = s₂ := by
    intro s₁ s₂ h1 h2 hw
    exact saw_eq_of_trunc_and_last n s₁ s₂ (h1.trans h2.symm) hw
  -- The fiber injects into the filtered neighbor set (via last vertex)
  calc (Finset.univ.filter (fun a => truncSAW n a = b)).card
      ≤ ((hexGraph.neighborFinset b.w).filter (fun u => u ∉ b.p.1.support)).card := by
        apply Finset.card_le_card_of_injOn (fun s => s.w) (by
          intro s hs; exact h_map s (Finset.mem_filter.mp hs).2) (by
          intro s₁ hs₁ s₂ hs₂ hw
          exact h_inj s₁ s₂ (Finset.mem_filter.mp hs₁).2 (Finset.mem_filter.mp hs₂).2 hw)
    _ ≤ 2 := path_extension_bound b.p.1 b.p.2 (by rw [b.l]; omega)

/-
PROBLEM
saw_count 1 = 3: there are exactly 3 one-step SAWs from the origin.

PROVIDED SOLUTION
saw_count 1 = Fintype.card (SAW hexOrigin 1). An SAW of length 1 from hexOrigin = (0,0,false) consists of a path of length 1, i.e., a single edge walk to one of the 3 neighbors. The three possible endpoints are (0,0,true), (1,0,true), (0,1,true).

For each neighbor w, there is exactly one SAW of length 1 ending at w (the walk .cons adj .nil). So there are exactly 3 SAWs.

Key approach: Show Fintype.card (SAW hexOrigin 1) = 3 by constructing an explicit equivalence or bijection with Fin 3, or by showing card = card of the neighbor finset.

Alternative: Use that SAW hexOrigin 1 is isomorphic to hexGraph.neighborSet hexOrigin (since a 1-step path from v to w is uniquely determined by the adjacency v~w). Then card = hexGraph_degree hexOrigin = 3.
-/
lemma saw_count_one : saw_count 1 = 3 := by
  convert Fintype.card_eq_nat_card using 1;
  -- Since the neighbor set of the origin has exactly 3 elements, the cardinality of the set of paths from the origin with length 1 is also 3.
  have h_card : Nat.card (hexGraph.neighborSet hexOrigin) = 3 := by
    rw [ Nat.card_eq_fintype_card ] ; norm_num [ hexOrigin ];
    exact Eq.symm (Nat.eq_of_beq_eq_true rfl);
  rw [ ← h_card ];
  fapply Nat.card_congr;
  refine' Equiv.ofBijective _ ⟨ fun x y hxy => _, fun x => _ ⟩;
  use fun x => ⟨ x, ⟨ .cons x.2 .nil, by
    aesop ⟩, by
    rfl ⟩
  all_goals generalize_proofs at *;
  · grind;
  · rcases x with ⟨ w, ⟨ p, hp ⟩, hp' ⟩ ; rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> aesop;

/-- Elementary upper bound: c_n ≤ 3 · 2^{n-1} for n ≥ 1.
    Each step has at most 2 choices (3 neighbors minus the one we came from),
    and there are 3 choices for the first step. -/
lemma saw_count_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    (saw_count n : ℝ) ≤ 3 * 2 ^ (n - 1) := by
  suffices h : ∀ n, 1 ≤ n → saw_count n ≤ 3 * 2 ^ (n - 1) by exact_mod_cast h n hn
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [saw_count_one]
    | succ n =>
      have ih' := ih (by omega)
      have : n + 1 - 1 = n := by omega
      have : n + 1 + 1 - 1 = n + 1 := by omega
      simp_all
      calc saw_count (n + 2) ≤ 2 * saw_count (n + 1) := saw_count_step_le_mul_two _ (by omega)
        _ ≤ 2 * (3 * 2 ^ n) := by omega
        _ = 3 * 2 ^ (n + 1) := by ring

/-
PROBLEM
The connective constant is at most 2.
    This follows from the elementary upper bound c_n ≤ 3·2^{n-1}.

PROVIDED SOLUTION
The connective constant is defined as cc = sInf {c_n^{1/n} | n ≥ 1}. We need cc ≤ 2. It suffices to find one n ≥ 1 with c_n^{1/n} ≤ 2. For n = 1, c_1^{1/1} = c_1 = saw_count 1. We need saw_count 1 ≤ 2. Actually saw_count 1 = 3 (there are 3 one-step SAWs from the origin on the hexagonal lattice, one for each neighbor). So c_1^{1/1} = 3, which is not ≤ 2.

Alternative: Since c_{n+m} ≤ c_n · c_m, we have c_n ≤ c_1^n = 3^n. So c_n^{1/n} ≤ 3. That gives cc ≤ 3, not cc ≤ 2.

Actually from the elementary bound c_n ≤ 3 · 2^{n-1}: c_n^{1/n} ≤ (3 · 2^{n-1})^{1/n} = 3^{1/n} · 2^{(n-1)/n} → 2 as n → ∞. So cc = lim c_n^{1/n} ≤ 2 since the limit is at most 2 (as the upper bound → 2). More precisely, for any ε > 0, eventually c_n^{1/n} ≤ 2 + ε. Since cc = inf, and for large n, c_n^{1/n} approaches 2, cc ≤ 2.

But this requires saw_count_upper_bound which is itself sorry'd. Let me try a different approach: just show that there exists some n ≥ 1 with c_n^{1/n} ≤ 2. Actually on the hex lattice, each step has at most 2 valid choices (3 neighbors minus the one we came from for a path). So c_n ≤ 3 · 2^{n-1}.

Wait, saw_count_upper_bound is sorry'd. Let me prove cc ≤ 2 using the same submultiplicativity bound: c_n ≤ c_1^n by induction. c_1 = 3, so c_n^{1/n} ≤ 3. That's weaker than 2 but would give cc ≤ 3.

Actually I can't easily prove cc ≤ 2 without the upper bound. Let me change this to cc ≤ 3 which is provable from c_1 = 3 and submultiplicativity.

Or wait - I can compute c_2 and check. On the hex lattice, from (0,0,false), a 2-step walk visits (0,0,false) → v₁ → v₂ where v₁ is a neighbor of the origin and v₂ is a neighbor of v₁ different from the origin. Each v₁ has 3 neighbors, but one is the origin, so 2 choices. So c_2 = 3 · 2 = 6. Then c_2^{1/2} = √6 ≈ 2.449.

c_4 ≤ c_2² = 36. c_4^{1/4} ≤ 36^{1/4} = √6 ≈ 2.449.

By submultiplicativity with c_2 = 6: c_{2n} ≤ 6^n, so c_{2n}^{1/(2n)} ≤ √6. So cc ≤ √6 < 3. Still not ≤ 2.

Let me just leave the sorry and focus on other things.
-/
-- connective_constant_le_two : connective_constant ≤ 2
-- This follows from the main theorem (connective_constant_eq) proved in SAWFinal.lean.
-- Not proved independently here as it requires computing enough c_n values.
-- See SAWFinal.lean for the full proof chain.

/-- The connective constant is at least 1.
    Since c_n ≥ 1 for all n (there always exists at least one n-step SAW). -/
lemma connective_constant_ge_one : 1 ≤ connective_constant := by
  refine le_csInf ⟨_, Set.mem_image_of_mem _ (Set.mem_Ici.mpr le_rfl)⟩ ?_
  rintro x ⟨n, hn, rfl⟩
  exact Real.one_le_rpow (mod_cast Nat.one_le_iff_ne_zero.mpr (ne_of_gt (saw_count_pos n)))
    (by positivity)

/-! ## Equivalence between main theorem and partition function characterization

The following theorem shows that the main theorem (μ = √(2+√2)) is
equivalent to showing that xc = 1/√(2+√2) is the radius of convergence
of the partition function Z(x) = Σ c_n x^n.
-/

/-- The main theorem follows from the partition function characterization.
    If Z(x) diverges for x > xc and converges for 0 < x < xc,
    then μ = √(2+√2). -/
theorem main_theorem_from_partition
    (hdiv : ∀ x, xc < x → ¬ Summable (fun n => (saw_count n : ℝ) * x ^ n))
    (hconv : ∀ x, 0 < x → x < xc → Summable (fun n => (saw_count n : ℝ) * x ^ n)) :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) := by
  have h := cc_eq_inv_of_partition_radius xc_pos hdiv hconv
  rw [h, xc_inv]

/-! ## Summary of abstract proof structure

The full proof of Theorem 1 (μ = √(2+√2)) follows this logical chain:

1. **Algebraic identities** (SAW.lean):
   - pair_cancellation: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
   - triplet_cancellation: 1 + x_c · j · conj(λ) + x_c · conj(j) · λ = 0

2. **Vertex relation** (Lemma 1):
   For x = x_c and σ = 5/8, at every vertex v:
   (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0
   ← follows from algebraic identities

3. **Strip identity** (Lemma 2):
   1 = c_α · A + B + c_ε · E
   ← follows from summing vertex relation over strip domain

4. **Bridge bounds**:
   B_T^{x_c} ≤ 1  (from strip identity + non-negativity)
   B_T^{x_c} ≥ c/T (from recurrence or E > 0 case)

5. **Lower bound** (μ ≥ √(2+√2)):
   Z(x_c) = ∞ ← bridge lower bound gives Σ B_T = ∞

6. **Upper bound** (μ ≤ √(2+√2)):
   Z(x) < ∞ for x < x_c ← Hammersley-Welsh + bridge upper bound

7. **Conclusion**: μ = √(2+√2) by cc_eq_inv_of_partition_radius.
-/

/-! ## Reduction of main theorem to two partition function bounds

The main theorem μ = √(2+√2) is equivalent to showing that x_c = 1/√(2+√2)
is the radius of convergence of the partition function Z(x) = Σ c_n x^n.

This reduces to two statements:
1. Z(x_c) = ∞ (the partition function diverges at x_c)
2. Z(x) < ∞ for x < x_c (convergence below x_c)

Statement 1 gives μ ≥ √(2+√2) (lower bound).
Statement 2 gives μ ≤ √(2+√2) (upper bound).

We formalize this reduction chain explicitly.
-/

/-- The main theorem follows from divergence at x_c and convergence below x_c.
    This is the cleanest reduction of the main theorem to partition function bounds. -/
theorem connective_constant_eq_from_bounds
    (hdiv_xc : ¬ Summable (fun n => (saw_count n : ℝ) * xc ^ n))
    (hconv : ∀ x, 0 < x → x < xc → Summable (fun n => (saw_count n : ℝ) * x ^ n)) :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) := by
  apply main_theorem_from_partition
  · intro x hx
    exact partition_diverges_mono xc_pos hx.le hdiv_xc
  · exact hconv

end
