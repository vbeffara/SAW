/-
# Final proof assembly: The connective constant of the honeycomb lattice

This file imports the full proof chain and assembles the final results:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Import chain

```
SAW.lean          — Core definitions, constants, algebraic identities
├─ SAWSubmult.lean — Submultiplicativity: c_{n+m} ≤ c_n · c_m
│  └─ SAWMain.lean — Fekete's lemma → connective constant is a limit
│     └─ SAWBridge.lean — Bridge decomposition, partition function analysis
│        └─ SAWDecomp.lean — Hammersley-Welsh decomposition structure
│           └─ SAWProof.lean — Lower/upper bound proof structure
│              └─ SAWFinal.lean (this file) — Final assembly
└─ SAWStrip.lean   — Strip domains, parafermionic observable
   └─ SAWVertex.lean — Vertex relation (Lemma 1) details
```

## Results proved here

1. `connective_constant_eq`: μ = √(2+√2) — the main theorem (modulo sorry'd
   combinatorial infrastructure for bridge bounds and Hammersley-Welsh injection)
2. `connective_constant_eq_inv_xc`: μ = xc⁻¹
3. `connective_constant_le_two'`: μ ≤ 2
4. `partition_function_diverges_above_xc'`: Z(x) = ∞ for x > xc
5. `partition_function_converges_below_xc'`: Z(x) < ∞ for 0 < x < xc
-/

import RequestProject.SAWProof
import RequestProject.SAWVertex

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## The main theorem

The connective constant μ = √(2+√2). This is proved via the reduction chain
in SAWBridge.lean: `connective_constant_eq_from_bounds` requires

1. Divergence at xc: ¬ Summable (fun n => c_n * xc^n)
2. Convergence below xc: ∀ x ∈ (0, xc), Summable (fun n => c_n * x^n)

Both are established abstractly in SAWBridge.lean via the strip identity and
Hammersley-Welsh decomposition. The concrete combinatorial infrastructure
(bridge-to-walk injection, walks restricted to domains) remains sorry'd.
-/

/-- **Main Theorem** (Duminil-Copin & Smirnov, 2012):
    The connective constant of the hexagonal lattice equals √(2+√2).

    This assembles the full proof chain:
    • Algebraic identities (SAW.lean): pair/triplet cancellation
    • Vertex relation (SAWVertex.lean): Lemma 1 of the paper
    • Strip identity (SAWStrip.lean): Lemma 2 — 1 = c_α·A + B + c_ε·E
    • Submultiplicativity (SAWSubmult.lean): c_{n+m} ≤ c_n · c_m
    • Fekete's lemma (SAWMain.lean): c_n^{1/n} → μ
    • Bridge decomposition (SAWBridge.lean, SAWDecomp.lean):
      - Lower bound: Z(xc) = ∞ (via B_T ≥ c/T or E > 0)
      - Upper bound: Z(x) < ∞ for x < xc (via Hammersley-Welsh)
    • This file: assembly via connective_constant_eq_from_bounds -/
theorem connective_constant_eq :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) := by
  -- The main theorem follows from two partition function bounds.
  -- These are established abstractly in the proof chain but depend on
  -- combinatorial infrastructure (bridge-to-walk injection) that
  -- is sorry'd in SAWBridge.lean.
  exact connective_constant_eq_from_bounds
    -- Lower bound: Z(xc) = ∞
    (by
      -- This requires the full strip identity and bridge analysis.
      -- The abstract proof is in SAWProof.lean (lower_bound_abstract).
      -- The concrete bridge analysis remains to be connected.
      sorry)
    -- Upper bound: Z(x) < ∞ for 0 < x < xc
    (fun x hx hxc => by
      -- This requires the Hammersley-Welsh bridge decomposition.
      -- The abstract bound is in SAWBridge.lean (hammersley_welsh_bound).
      sorry)

/-- Equivalent formulation: the connective constant equals 1/x_c. -/
theorem connective_constant_eq_inv_xc :
    connective_constant = xc⁻¹ := by
  rw [connective_constant_eq, xc_inv]

/-- The connective constant is at most 2.
    Immediate from the main theorem since √(2+√2) < 2. -/
theorem connective_constant_le_two' : connective_constant ≤ 2 := by
  rw [connective_constant_eq]
  exact Real.sqrt_le_iff.mpr ⟨by positivity,
    by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]⟩

/-- The partition function Z(x) diverges for x > x_c. -/
theorem partition_function_diverges_above_xc' :
    ∀ x > xc, ¬ Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  intro x hx
  have hmu_x_gt_1 : connective_constant * x > 1 := by
    rw [connective_constant_eq_inv_xc]
    rw [inv_mul_eq_div, gt_iff_lt, lt_div_iff₀] <;>
      nlinarith [xc_pos]
  have hcn_ge_mu_n : ∀ n ≥ 1, (saw_count n : ℝ) ≥ connective_constant ^ n := by
    exact fun n hn => saw_count_ge_cc_pow n hn
  have hcn_xn_ge_1 : ∀ n ≥ 1, (saw_count n : ℝ) * x ^ n ≥ 1 := by
    intro n hn
    calc (1 : ℝ) ≤ (connective_constant * x) ^ n := one_le_pow₀ hmu_x_gt_1.le
      _ = connective_constant ^ n * x ^ n := by ring
      _ ≤ (saw_count n : ℝ) * x ^ n := by
          exact mul_le_mul_of_nonneg_right (hcn_ge_mu_n n hn)
            (pow_nonneg (le_trans xc_pos.le hx.le) _)
  exact fun h => absurd h.tendsto_atTop_zero fun H =>
    absurd (le_of_tendsto_of_tendsto tendsto_const_nhds H
      (Filter.eventually_atTop.mpr ⟨1, fun n hn => hcn_xn_ge_1 n hn⟩))
      (by norm_num)

/-
PROBLEM
The partition function Z(x) converges for 0 < x < x_c.
    Uses the Fekete limit (connective_constant_is_limit') and the root test.

PROVIDED SOLUTION
Use connective_constant_eq (proved in this file) and connective_constant_is_limit' (from SAWMain).

Since cc = √(2+√2) > 0 (by connective_constant_eq and positivity), and x < xc = 1/cc (by connective_constant_eq_inv_xc), we have cc·x < 1.

Pick r = (1 + cc·x)/2. Then cc·x < r < 1 and 0 < r.

Since c_n^{1/n} → cc (by connective_constant_is_limit'), and cc < r/x (since r > cc·x), eventually c_n^{1/n} < r/x. So eventually c_n < (r/x)^n, hence c_n·x^n < r^n.

By comparison with the geometric series Σ r^n (which converges since r < 1), the series Σ c_n·x^n converges.

Use summable_nat_add_iff to handle the tail, Summable.of_nonneg_of_le for the comparison, and summable_geometric_of_lt_one for the geometric bound.
-/
theorem partition_function_converges_below_xc' :
    ∀ x, 0 < x → x < xc →
      Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  intro x hx_pos hx_lt_xc
  -- cc = √(2+√2) by connective_constant_eq
  -- x < xc = 1/cc, so cc·x < 1
  convert partition_converges_below_inv_cc hx_pos ( show x < connective_constant⁻¹ from ?_ ) using 1;
  rw [ connective_constant_eq_inv_xc ] ; exact hx_lt_xc.trans_le ( by norm_num [ Real.sqrt_nonneg, le_of_lt ] ) ;

/-! ## Summary of the full proof

The proof of Theorem 1 (μ = √(2+√2)) follows this logical chain:

### Section 2: Parafermionic Observable
- **Lemma 1 (Vertex relation)**: At x = x_c, σ = 5/8, for every vertex v:
  (p-v)·F(p) + (q-v)·F(q) + (r-v)·F(r) = 0
  - Pair cancellation: j·conj(λ)⁴ + conj(j)·λ⁴ = 0 (SAW.lean)
  - Triplet cancellation: 1 + x_c·j·conj(λ) + x_c·conj(j)·λ = 0 (SAW.lean)

### Section 3: Proof
- **Lemma 2 (Strip identity)**: 1 = c_α·A + B + c_ε·E (SAWStrip.lean)
- **Submultiplicativity**: c_{n+m} ≤ c_n·c_m (SAWSubmult.lean)
- **Bridge bounds**: B_T^{x_c} ≤ 1 and B_T^{x_c} ≥ c/T (SAWDecomp.lean)
- **Lower bound**: Z(x_c) = ∞ via Cases 1 and 2 (SAWProof.lean)
- **Upper bound**: Z(x) < ∞ for x < x_c via Hammersley-Welsh (SAWBridge.lean)
- **Main theorem**: μ = √(2+√2) via connective_constant_eq_from_bounds

### Section 4: Conjectures (SAWMain.lean)
- Nienhuis' asymptotic formula: c_n ~ A·n^{γ-1}·μ^n with γ = 43/32
- Flory exponent: ⟨|γ(n)|²⟩ = n^{3/2 + o(1)} with ν = 3/4
- SLE(8/3) conjecture for the scaling limit

### Remaining gaps

The following pieces require concrete combinatorial infrastructure
that has been stated abstractly but not yet connected:

1. **Bridge-to-walk injection**: The Hammersley-Welsh decomposition gives
   an injection from SAWs into sequences of bridges. This requires
   formalizing the decomposition algorithm (find max-Re vertex, split,
   recurse) and proving its injectivity.

2. **Walk restriction to domains**: Formally defining SAWs restricted to
   strip domains S_{T,L} and connecting them to the abstract partition
   functions A, B, E.

3. **Boundary winding evaluation**: Computing the exact winding values
   for walks ending on each boundary part of the strip domain.
-/

/-! ## Bridge existence

The Bridge definition in SAWBridge.lean uses vertex positions for boundary
conditions, but the paper defines bridges between mid-edges. This causes
a mismatch: the condition `(hexEmbed end_v).re = (3 * T + 1 : ℝ) / 2`
cannot be satisfied by any hex vertex since:
- false-sublattice: Re = 3x/2 (multiples of 3/2)
- true-sublattice: Re = 3x/2 + 1

Neither form can equal (3T+1)/2 for integer x and T.

The correct formulation should use mid-edge positions, where a mid-edge
between (x,y,false) and (x,y,true) has Re = (3x/2 + 3x/2+1)/2 = 3x/2 + 1/2.
For example, the mid-edge between (1,0,false) and (1,0,true) has Re = 2 = (3·1+1)/2.

This is a known gap in the formalization that requires adjusting the Bridge
definition to work with mid-edge positions rather than vertex positions. -/

end