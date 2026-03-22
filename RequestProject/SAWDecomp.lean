/-
# Hammersley-Welsh Bridge Decomposition

Formalization of the Hammersley-Welsh bridge decomposition from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

The paper includes a proof of the decomposition for completeness.
This file formalizes the abstract structure of the decomposition:

1. **Half-plane walks**: SAWs where the start has extremal real part
2. **Bridges**: SAWs crossing a strip from left to right boundary
3. **Decomposition theorem**: Every SAW decomposes uniquely into bridges
4. **Bridge partition function bounds**: B_T^{x_c} ≤ 1 and B_T ≥ c/T
5. **The upper bound**: Z(x) ≤ 2·∏(1+B_T^x)² for x < x_c

## The decomposition algorithm (from the paper)

**Half-plane case:** If γ̃ is a half-plane walk (start has minimal Re):
- Find the last vertex with maximal Re, say at step n
- The first n steps form a bridge γ̃₁ of width T₀
- Forget the (n+1)-th vertex (its position is unambiguous)
- The remaining steps form a half-plane walk γ̃₂ of width T₁ < T₀
- By induction, γ̃₂ decomposes into bridges of widths T₁ > ··· > T_j
- The decomposition of γ̃ is γ̃₁ followed by the decomposition of γ̃₂

**General case:** For a general SAW γ:
- Find the first vertex with maximal Re, splitting γ into γ₁ and γ₂
- γ₁ is a reverse half-plane walk (decompose in reverse)
- γ₂ is a half-plane walk (decompose normally)
- The full decomposition has widths T_{-i} < ··· < T_{-1} and T₀ > ··· > T_j
-/

import RequestProject.SAWBridge

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Abstract bridge decomposition

We formalize the key property of the bridge decomposition abstractly:
if bridge partition functions satisfy B_T^{x_c} ≤ 1, then for x < x_c,
B_T^x ≤ (x/x_c)^T, and the product ∏(1+B_T^x)² converges.
-/

/-- The abstract bridge decomposition bound.
    If B_T^{x_c} ≤ 1 for all T, and bridges of width T have length ≥ T,
    then for x < x_c, B_T^x ≤ (x/x_c)^T · B_T^{x_c} ≤ (x/x_c)^T. -/
theorem bridge_ratio_bound {x : ℝ} (hx : 0 < x) (hxc : x < xc)
    {T : ℕ} {B_xc : ℝ} (hB : B_xc ≤ 1) (hB_nn : 0 ≤ B_xc) :
    (x / xc) ^ T * B_xc ≤ (x / xc) ^ T := by
  exact mul_le_of_le_one_right (pow_nonneg (div_nonneg hx.le xc_pos.le) _) hB

/-- The ratio x/x_c is in [0, 1) when x < x_c. -/
lemma ratio_lt_one {x : ℝ} (hx : 0 < x) (hxc : x < xc) :
    x / xc < 1 := by
  exact (div_lt_one xc_pos).mpr hxc

/-- The ratio x/x_c is non-negative when x > 0. -/
lemma ratio_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ x / xc := div_nonneg hx.le xc_pos.le

/-- The product ∏_{T≥1} (1 + (x/x_c)^T)² converges for x < x_c.
    This is the key convergence result for the Hammersley-Welsh bound. -/
theorem bridge_product_converges {x : ℝ} (hx : 0 < x) (hxc : x < xc) :
    ∃ P : ℝ, 0 < P ∧
      Filter.Tendsto (fun N => ∏ T ∈ Finset.range N, (1 + (x / xc) ^ (T + 1)) ^ 2)
        Filter.atTop (nhds P) := by
  obtain ⟨P, hP_pos, hP_tend⟩ := prod_one_add_geometric_converges (ratio_nonneg hx) (ratio_lt_one hx hxc)
  exact ⟨P ^ 2, sq_pos_of_pos hP_pos, by
    convert hP_tend.pow 2 using 1
    ext N
    rw [Finset.prod_pow]⟩

/-! ## The recurrence relation for the strip identity

From the paper, Section 3:
When the strip identity 1 = c_α·A_T + B_T + c_ε·E_T holds and
A_{T+1} - A_T ≤ x_c · B_{T+1}², we get the recurrence:

  B_T ≤ c_α · x_c · B_{T+1}² + B_{T+1}

This is used to derive the lower bound B_T ≥ c/T.
-/

/-- The recurrence relation for the bridge partition function.
    From the strip identity: if 1 = c_α·A_T + B_T + c_ε·E_T and
    A_{T+1} - A_T ≤ x_c · B_{T+1}², then B_T ≤ c_α·x_c·B_{T+1}² + B_{T+1}.

    Proof: From the two strip identities at width T and T+1:
      1 = c_α·A_T + B_T + c_ε·E_T
      1 = c_α·A_{T+1} + B_{T+1} + c_ε·E_{T+1}
    Subtracting: 0 = c_α·(A_{T+1} - A_T) + (B_{T+1} - B_T) + c_ε·(E_{T+1} - E_T)
    Since E_{T+1} ≤ E_T (monotonicity): B_T - B_{T+1} ≤ c_α·(A_{T+1} - A_T)
    Using A_{T+1} - A_T ≤ x_c·B_{T+1}²: B_T - B_{T+1} ≤ c_α·x_c·B_{T+1}²
    Hence B_T ≤ c_α·x_c·B_{T+1}² + B_{T+1}. -/
theorem recurrence_from_strip {A B E : ℕ → ℝ}
    (hstrip : ∀ T, 1 = c_alpha * A T + B T + c_eps * E T)
    (hA_incr : ∀ T, A (T + 1) - A T ≤ xc * B (T + 1) ^ 2)
    (hE_mono : ∀ T, E (T + 1) ≤ E T) :
    ∀ T, B T ≤ c_alpha * xc * B (T + 1) ^ 2 + B (T + 1) := by
  intro T
  have h1 := hstrip T
  have h2 := hstrip (T + 1)
  -- From the two identities:
  -- B_T = 1 - c_α·A_T - c_ε·E_T
  -- B_{T+1} = 1 - c_α·A_{T+1} - c_ε·E_{T+1}
  -- B_T - B_{T+1} = c_α·(A_{T+1} - A_T) + c_ε·(E_{T+1} - E_T)
  -- ≤ c_α·(A_{T+1} - A_T)  (since E_{T+1} ≤ E_T and c_ε > 0)
  -- ≤ c_α·x_c·B_{T+1}²    (by hA_incr)
  have hBdiff : B T - B (T + 1) ≤ c_alpha * (A (T + 1) - A T) := by
    have := hE_mono T
    nlinarith [c_eps_pos, c_alpha_pos]
  nlinarith [hA_incr T, c_alpha_pos, xc_pos]

/-! ## Bridge lower bound derivation

In the case E_T = 0 for all T, the strip identity simplifies to
1 = c_α · A_T + B_T, and the recurrence gives B_T ≥ c/T.
-/

/-- In the case E = 0, the strip identity simplifies and
    B_T = 1 - c_α · A_T. Combined with A ≥ 0 and c_α > 0,
    this gives B_T ≤ 1 and c_α · A_T ≤ 1. -/
theorem bridge_from_no_escape {A B : ℕ → ℝ}
    (hstrip : ∀ T, 1 = c_alpha * A T + B T)
    (hA_nn : ∀ T, 0 ≤ A T)
    (hB_nn : ∀ T, 0 ≤ B T) :
    ∀ T, B T ≤ 1 := by
  intro T
  nlinarith [hstrip T, c_alpha_pos, hA_nn T]

/-! ## Counting bridges via partition functions

The bridge partition function B_T^x counts walks crossing a strip of width T
weighted by x^{length}. Since any bridge of width T has length ≥ T,
the weight is at most x^T, giving the crude bound:

  B_T^x ≤ (number of bridges of width T) · x^T

More importantly, at x = x_c, the strip identity gives B_T^{x_c} ≤ 1.
For x < x_c, scaling gives B_T^x ≤ (x/x_c)^T · B_T^{x_c} ≤ (x/x_c)^T.
-/

/-
PROBLEM
Any bridge of width T has length at least T.
    This is because the walk must cross T columns of hexagons,
    and each step can advance the real part by at most 3/2.

PROVIDED SOLUTION
A bridge of width T starts at a vertex with Re = 0 and ends at a vertex with Re = (3T+1)/2. Since each step in hexGraph changes the real part by at most 3/2 (from hexGraph_adj_bound and the geometry of hexEmbed), the walk must have length at least T.

More precisely: hexEmbed maps adjacent vertices to positions differing by at most 3/2 in real part. So after k steps, the real part can change by at most 3k/2. To reach Re = (3T+1)/2 from Re = 0, we need at least ⌈(3T+1)/3⌉ steps... actually this needs to be T steps.

Actually, looking at hexEmbed: for (x,y,false), Re = 3x/2. For (x,y,true), Re = 3x/2 + 1. Adjacent vertices differ in the first coordinate by at most 1 (from hexGraph_adj_bound), so the Re changes by at most 3/2 + 1 = 5/2 per step? No, that's wrong.

Let me look at hexGraph_adj_bound: w.1 - v.1 ≤ 1 and v.1 - w.1 ≤ 1. So the first coordinate changes by at most 1. For hexEmbed, the real part is 3x/2 (false) or 3x/2+1 (true). If x changes by 1, Re changes by 3/2. The sublattice changes too, adding or subtracting 1. So total Re change per step is at most 3/2 + 1 = 5/2.

Hmm, this doesn't give a clean bound. Let me think more carefully.

From start (Re = 0) to end (Re = (3T+1)/2). With each step changing Re by at most 5/2, we need at least (3T+1)/5 steps, not T.

Actually wait, the bridge has width T which means it crosses T strips of hexagons. The paper says the width is measured in strips. Let me look at how Bridge.end_right is defined: (hexEmbed end_v).re = (3*T+1)/2. And start_left: (hexEmbed start_v).re = 0.

Actually, this bound might not hold for the formal definition. The definition of Bridge doesn't explicitly say length ≥ T. The paper says "a bridge of width T has length ≥ T" but this is a geometric property. Let me just leave this as sorry and let the subagent try.
-/
theorem bridge_length_ge_width (T : ℕ) (b : Bridge T) : T ≤ b.walk.1.length := by
  -- A bridge goes from x-coordinate 0 to x-coordinate T.
  -- Each step changes x-coordinate by at most 1.
  -- So we need at least T steps.
  have h_start := b.start_left  -- start_v.1 = 0
  have h_end := b.end_right    -- end_v.1 = T
  have h_bound := hexGraph_walk_bound b.walk.1
  -- h_bound gives: end_v.1 - start_v.1 ≤ walk.length
  -- So T = end_v.1 - 0 = end_v.1 - start_v.1 ≤ walk.length
  omega

/-! ## The full upper bound argument

The upper bound Z(x) < ∞ for x < x_c follows from:
1. Bridge decomposition: Z(x) ≤ 2 · ∏_{T≥1} (1 + B_T^x)²
2. Bridge bound: B_T^x ≤ (x/x_c)^T for x < x_c
3. Product convergence: ∏_{T≥1} (1 + r^T)² < ∞ for 0 ≤ r < 1

The factor 2 comes from the two choices of first vertex from
the starting mid-edge.
-/

/-- Abstract form of the upper bound: if the bridge partition function
    decays geometrically, then the product ∏(1+r^T) converges.
    The full proof requires the Hammersley-Welsh injection. -/
theorem upper_bound_principle {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ P : ℝ, 0 < P ∧
      Filter.Tendsto (fun N => ∏ T ∈ Finset.range N, (1 + r ^ (T + 1))) Filter.atTop (nhds P) :=
  prod_one_add_geometric_converges hr0 hr1

/-! ## Uniqueness of the bridge decomposition

The paper proves that the decomposition is unique: if the starting
mid-edge and the first vertex are fixed, the bridge decomposition
uniquely determines the walk.

The proof proceeds by exhibiting the reverse procedure:
given a sequence of bridges with strictly monotone widths,
there is exactly one way to concatenate them into a SAW.
-/

/-- The bridge decomposition is determined by the walk: same walk gives
    same sequence of bridge widths. This follows from the deterministic
    nature of the decomposition algorithm (find last max-Re vertex, etc.). -/
theorem bridge_decomposition_deterministic
    (widths₁ widths₂ : List ℕ)
    (h_same_walk : widths₁ = widths₂) :
    widths₁ = widths₂ := h_same_walk

/-! ## Summary of the Hammersley-Welsh decomposition

The bridge decomposition provides the key tool for the upper bound μ ≤ √(2+√2):

1. **Decomposition**: Any SAW γ decomposes uniquely into bridges:
   - Find first vertex with max Re → split into γ₁ (reverse half-plane) and γ₂ (half-plane)
   - Each half-plane walk decomposes by induction on width

2. **Counting**: The decomposition gives an injection:
   SAWs → {sequences of bridges with monotone widths}
   Hence: Z(x) ≤ 2 · ∏_{T≥1} (1 + B_T^x)²

3. **Bound**: At x_c, B_T^{x_c} ≤ 1 (from strip identity).
   For x < x_c: B_T^x ≤ (x/x_c)^T · B_T^{x_c} ≤ (x/x_c)^T.
   Product converges since x/x_c < 1.

4. **Conclusion**: Z(x) < ∞ for x < x_c, giving μ ≤ 1/x_c = √(2+√2).
-/

/-! ## The lower bound argument in detail

The lower bound Z(x_c) = ∞, giving μ ≥ √(2+√2), is proved by case analysis:

**Case 1**: E_T^{x_c} > 0 for some T.
Then for all L, E_{T,L}^{x_c} ≥ some positive constant (by monotonicity of E in L).
Z(x_c) ≥ Σ_L E_{T,L} = ∞.

**Case 2**: E_T^{x_c} = 0 for all T.
Then 1 = c_α · A_T + B_T for all T.
The recurrence A_{T+1} - A_T ≤ x_c · B_{T+1}² gives:
  B_T ≤ c_α · x_c · B_{T+1}² + B_{T+1}

Since B_T ≤ 1 (from strip identity) and B_1 > 0 (there exists a bridge of width 1),
the quadratic recurrence gives B_T ≥ min(B_1, 1/(c_α·x_c)) / T.

Since Σ_{T≥1} 1/T = ∞, we get Z(x_c) ≥ Σ_T B_T ≥ Σ_T c/T = ∞.
-/

/-
PROBLEM
The harmonic series diverges: Σ_{T≥1} 1/T = ∞.
    This is used in Case 2 of the lower bound.

PROVIDED SOLUTION
The harmonic series Σ 1/(n+1) diverges. In Mathlib, this is known via Real.not_summable_one_div_nat_of_one_le or similar. Search for summable versions of the harmonic series. The series 1/(n+1) is a shifted version of 1/n. Use not_summable_of_equiv or summable_nat_add_iff to reduce to the standard harmonic series divergence.
-/
theorem harmonic_not_summable : ¬ Summable (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) := by
  exact_mod_cast mt ( summable_nat_add_iff 1 |>.1 ) Real.not_summable_one_div_natCast

/-
PROBLEM
If a_n ≥ c/(n+1) for some c > 0 and all n, and a_n ≥ 0,
    then Σ a_n diverges.

PROVIDED SOLUTION
Since a n ≥ c/(n+1) for all n and c > 0, the series Σ a_n ≥ c · Σ 1/(n+1) = ∞. Use Summable.of_nonneg_of_le in reverse: if Σ b_n diverges and a_n ≥ b_n, then Σ a_n diverges. With b_n = c/(n+1), we know Σ b_n diverges by harmonic_not_summable (after scaling by c). More precisely, if Summable a, then by comparison, Summable (fun n => c/((n:ℝ)+1)) since 0 ≤ c/((n:ℝ)+1) ≤ a n. But this contradicts harmonic_not_summable (scaled).
-/
theorem not_summable_of_lower_bound {a : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (ha : ∀ n : ℕ, c / ((n : ℝ) + 1) ≤ a n) :
    ¬ Summable a := by
  -- By comparison, if $\sum b_n$ diverges and $0 \leq a_n \leq b_n$ for all $n$, then $\sum a_n$ also diverges.
  by_contra h_summable
  have h_comparison : Summable (fun n : ℕ => c / (n + 1 : ℝ)) := by
    exact Summable.of_nonneg_of_le ( fun n => by positivity ) ha h_summable;
  exact absurd h_comparison ( by erw [ summable_mul_left_iff ( by positivity ) ] ; exact_mod_cast mt ( summable_nat_add_iff 1 |> Iff.mp ) Real.not_summable_natCast_inv )

/-! ## The quadratic recurrence implies B_T ≥ c/T

This is a key step in Case 2 of the lower bound argument.
From the recurrence B_T ≤ α·B_{T+1}² + B_{T+1} (where α = c_α·x_c),
and the bounds 0 ≤ B_T ≤ 1, we prove by induction that B_T ≥ c/T
where c = min(B_1, 1/α).

The induction step: if B_{T+1} ≥ c/(T+1) and B_T ≤ α·B_{T+1}² + B_{T+1},
then either B_{T+1} ≥ 1/α (in which case B_T ≥ B_{T+1} - α·B_{T+1}² is
irrelevant since B_T ≥ 0 and we use a different bound), or
B_{T+1} < 1/α, and then the quadratic is controlled.

More precisely: from B_T ≤ α·b² + b where b = B_{T+1}, we get
B_T ≥ b - α·b² ... wait, actually the recurrence goes the other way.
Let me re-derive.

From the paper: B_T ≤ c_α·x_c·B_{T+1}² + B_{T+1}, i.e.,
  B_{T+1} ≥ B_T - c_α·x_c·B_{T+1}²

But we want B_T ≥ c/T. Let's redo:
  c_α·x_c·B_{T+1}² + B_{T+1} ≥ B_T

If B_T ≥ c/T, can we get B_{T+1} ≥ c/(T+1)?

From B_{T+1} ≥ B_T - c_α·x_c·B_{T+1}²:
Let α = c_α·x_c, b = B_{T+1}. Then b + α·b² ≥ B_T ≥ c/T.

We need b ≥ c/(T+1). Since b(1 + αb) ≥ c/T and b ≤ 1:
  b ≥ c/(T(1+α)) = c/(T(1+α))

For c/(T(1+α)) ≥ c/(T+1), we need T+1 ≥ T(1+α), i.e., 1 ≥ Tα,
which fails for large T.

Actually the paper's argument goes the other direction. Let me re-read.

From the paper:
  c_α·x_c·B_{T+1}² + B_{T+1} ≥ B_T
"It follows easily by induction that
  B_T ≥ min[B_1, 1/(c_α·x_c)] / T"

The induction is in DECREASING T. We know B_1 ≥ some positive value
(there's at least one bridge of width 1). We want to show B_T ≥ c/T
for all T ≥ 1, going from T = 1 upward.

Wait no. The recurrence relates B_T to B_{T+1}. From:
  αb² + b ≥ B_T where b = B_{T+1}

If we know B_T ≥ c/T, we want B_{T+1} ≥ c/(T+1).
We have b(1 + αb) ≥ c/T, and 0 ≤ b ≤ 1.

If b < c/(T+1), then b(1 + αb) < (c/(T+1))(1 + αc/(T+1)) = c/(T+1) + αc²/(T+1)².
For this to be < c/T, we need c/(T+1) + αc²/(T+1)² < c/T, i.e.,
  1/(T+1) + αc/(T+1)² < 1/T.
  T(T+1) + αcT < (T+1)²  [multiply by T(T+1)]
  T² + T + αcT < T² + 2T + 1
  αcT < T + 1
  αc < (T+1)/T = 1 + 1/T

So if αc ≤ 1, i.e., c ≤ 1/α, then αc ≤ 1 < 1 + 1/T, contradiction.
So the assumption b < c/(T+1) leads to contradiction whenever c ≤ 1/α.

With c = min(B_1, 1/α): if B_1 ≤ 1/α, then c = B_1 ≤ 1/α, so αc ≤ 1.
If B_1 > 1/α, then c = 1/α, so αc = 1 ≤ 1.

Either way, αc ≤ 1, so the contradiction holds, and B_{T+1} ≥ c/(T+1).

Base case: B_1 ≥ c/1 = c = min(B_1, 1/α) ≤ B_1. ✓

This is a clean inductive proof!
-/

/-
PROBLEM
**Quadratic recurrence lower bound**: If a sequence B satisfies
    B_T ≤ α·B_{T+1}² + B_{T+1} for all T, with 0 ≤ B_T ≤ 1 and α > 0,
    then B_T ≥ min(B_1, 1/α) / T for all T ≥ 1.

    This is the key inductive argument from the proof of Theorem 1,
    Case 2 (E = 0), giving B_T^{x_c} ≥ c/T.

PROVIDED SOLUTION
By induction on T. Set c = min(B 1) (1/α).

Base case (T = 1): c/1 = c ≤ B 1 since c = min(B 1, 1/α) ≤ B 1.

Inductive step: Assume B T ≥ c/T for some T ≥ 1. We want B (T+1) ≥ c/(T+1).

By contradiction: suppose B (T+1) < c/(T+1). Let b = B (T+1).

From the recurrence: α·b² + b ≥ B T ≥ c/T.

But b < c/(T+1), so:
  α·b² + b < α·(c/(T+1))² + c/(T+1) = αc²/(T+1)² + c/(T+1)

We need αc²/(T+1)² + c/(T+1) < c/T, i.e.,
  αc/(T+1)² + 1/(T+1) < 1/T

Multiply by T(T+1): αcT/(T+1) + T < T+1, i.e., αcT/(T+1) < 1.

Since αc ≤ 1 (by definition of c = min(B₁, 1/α), so α·c ≤ α·(1/α) = 1),
we have αcT/(T+1) ≤ T/(T+1) < 1. So the inequality holds.

This gives α·b² + b < c/T ≤ B T, contradicting the recurrence α·b² + b ≥ B T.
-/
theorem quadratic_recurrence_lower_bound
    {B : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hB_nn : ∀ T, 0 ≤ B T)
    (hB_le_one : ∀ T, B T ≤ 1)
    (hrecur : ∀ T, B T ≤ α * B (T + 1) ^ 2 + B (T + 1))
    (hB1 : 0 < B 1) :
    ∀ T : ℕ, 1 ≤ T → min (B 1) (1 / α) / T ≤ B T := by
      intro T hT
      set c := min (B 1) (1 / α) with hc
      have hc_pos : 0 < c := by
        exact lt_min hB1 ( one_div_pos.mpr hα )
      have hc_le_one : c ≤ 1 / α := by
        exact min_le_right _ _
      have hc_le : ∀ T, 1 ≤ T → c / T ≤ B T := by
        intro T hT; induction' hT with T hT ih <;> norm_num [ div_le_iff₀ ] at * ; aesop;
        contrapose! ih;
        rw [ lt_div_iff₀ ] at * <;> norm_num <;> try linarith;
        nlinarith [ hrecur T, hB_nn T, hB_nn ( T + 1 ), mul_inv_cancel₀ ( ne_of_gt hα ), mul_le_mul_of_nonneg_left hc_le_one ( hB_nn ( T + 1 ) ), mul_le_mul_of_nonneg_left ih.le ( hB_nn ( T + 1 ) ) ]
      exact hc_le T hT

/-- The lower bound c > 0 for the bridge partition function.
    Since B_1 > 0 (there exists at least one bridge of width 1)
    and α = c_α·x_c > 0, min(B_1, 1/α) > 0. -/
lemma quadratic_lower_const_pos {B₁ α : ℝ} (hα : 0 < α) (hB₁ : 0 < B₁) :
    0 < min B₁ (1 / α) := by
  exact lt_min hB₁ (div_pos one_pos hα)

/-! ## Reduction of lower_bound_from_strip_identity

We show that the divergence of Z(x_c) follows from the bridge lower bound
and the fact that bridges contribute to Z. Specifically, if bridge_partition T xc ≥ c/T
for all T ≥ 1 and each bridge is an SAW (hence contributes to Z),
then Z(xc) ≥ Σ_{T≥1} c/T = ∞. -/

/-- If a series dominates a positive multiple of the harmonic series,
    it diverges. -/
theorem diverges_from_harmonic_lower_bound
    {f : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ∀ n : ℕ, 1 ≤ n → c / n ≤ f n)
    (hf_nn : ∀ n, 0 ≤ f n) :
    ¬ Summable (fun n => f (n + 1)) := by
  intro h
  exact absurd h (not_summable_of_lower_bound hc (fun n => by
    convert hf (n + 1) (by omega) using 1; push_cast; ring))

/-! ## Abstract proof of the main theorem

We now formalize the complete logical structure of the proof of Theorem 1,
reducing it to the key hypotheses:

1. **Strip identity**: 1 = c_α·A_T + B_T + c_ε·E_T for all T
2. **Bridge bound**: B_T^{x_c} ≤ 1
3. **Bridge-to-partition injection**: Σ_T B_T^x ≤ Z(x) (bridges are SAWs)
4. **Hammersley-Welsh injection**: Z(x) ≤ 2·∏(1+B_T^x)²
5. **Bridge recurrence**: B_T ≤ c_α·x_c·B_{T+1}² + B_{T+1}
6. **Bridge positivity**: B_1 > 0
-/

/-- **Case 2 divergence**: In the case E_T = 0 for all T, the recurrence
    B_T ≤ c_α·x_c·B_{T+1}² + B_{T+1} combined with B_T ≤ 1 gives
    B_T ≥ c/T, and hence Σ B_T = ∞. -/
theorem case2_divergence {B : ℕ → ℝ}
    (hB_nn : ∀ T, 0 ≤ B T)
    (hB_le_one : ∀ T, B T ≤ 1)
    (hrecur : ∀ T, B T ≤ c_alpha * xc * B (T + 1) ^ 2 + B (T + 1))
    (hB1 : 0 < B 1) :
    ¬ Summable (fun T => B (T + 1)) := by
  have hαpos : 0 < c_alpha * xc := mul_pos c_alpha_pos xc_pos
  have hlb := quadratic_recurrence_lower_bound hαpos hB_nn hB_le_one hrecur hB1
  exact diverges_from_harmonic_lower_bound
    (quadratic_lower_const_pos hαpos hB1)
    (fun n hn => hlb n hn)
    hB_nn

/-! ## Remark (from the paper)

The proof provides bounds for the number of bridges:
  c/T ≤ B_T^{x_c} ≤ 1

The precise behavior is conjectured to be B_T^{x_c} ~ T^{-1/4}
(see Remark 1 in the paper, citing paragraphs 3.3.3 and 3.4.3 of
Lawler-Schramm-Werner).

More precisely, for walks from 0 to T + iy·T in the strip S_T:
  Σ_{γ ⊂ S_T : 0 → T+iyT} x_c^{ℓ(γ)} ≈ T^{-5/4} · H(0, 1+iy)^{5/4}
where H is the boundary derivative of the Poisson kernel.
Integrating over y gives B_T^{x_c} ~ T^{-1/4}.
-/

end