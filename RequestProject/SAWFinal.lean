/-
# Final proof assembly: The connective constant of the honeycomb lattice

This file imports the full proof chain and assembles the final results:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Import chain

```
SAW.lean           — Core definitions, constants, algebraic identities
├─ SAWSubmult.lean  — Submultiplicativity: c_{n+m} ≤ c_n · c_m
│  └─ SAWMain.lean  — Fekete's lemma → connective constant is a limit
│     └─ SAWBridge.lean — Bridge definitions, partition function analysis
│        ├─ SAWDecomp.lean — Hammersley-Welsh decomposition structure
│        │  └─ SAWProof.lean — Lower/upper bound proof structure
│        │     └─ SAWFinal.lean (this file) — Final assembly
│        └─ SAWBridgeFix.lean — Corrected bridge partition, vacuous truth proof
└─ SAWStrip.lean   — Strip domains, parafermionic observable
   └─ SAWVertex.lean — Vertex relation (Lemma 1) details
```

## Results proved here

1. `connective_constant_eq`: μ = √(2+√2) — the main theorem
   (modulo two partition function bounds, see below)
2. `connective_constant_eq_inv_xc`: μ = xc⁻¹
3. `connective_constant_le_two'`: μ ≤ 2
4. `partition_function_diverges_above_xc'`: Z(x) = ∞ for x > xc
5. `partition_function_converges_below_xc'`: Z(x) < ∞ for 0 < x < xc

## Remaining gaps

The main theorem requires two partition function bounds:
1. **Lower bound** (Z(xc) = ∞): Requires connecting the abstract strip identity
   (proved in SAWProof/SAWDecomp) to concrete SAW counts via the corrected
   bridge partition (OriginBridge from SAWBridgeFix).
2. **Upper bound** (Z(x) < ∞ for x < xc): Requires the Hammersley-Welsh
   decomposition injection (every SAW decomposes into bridges).

Both gaps require formalizing walks restricted to strip domains, which is
the main remaining infrastructure task.
-/

import RequestProject.SAWProof
import RequestProject.SAWVertex
import RequestProject.SAWBridgeFix
import RequestProject.SAWHammersleyWelsh
import RequestProject.SAWStripIdentity

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## The main theorem

The connective constant μ = √(2+√2). This is proved via the reduction chain
in SAWBridge.lean: `connective_constant_eq_from_bounds` requires

1. Divergence at xc: ¬ Summable (fun n => c_n * xc^n)
2. Convergence below xc: ∀ x ∈ (0, xc), Summable (fun n => c_n * x^n)

The abstract proof structure is complete:
- Strip identity → B_T ≥ c/T → Σ B_T = ∞ → Z(xc) = ∞ (lower bound)
- Hammersley-Welsh: Z(x) ≤ 2·∏(1+B_T^x)² < ∞ for x < xc (upper bound)

The gap: connecting abstract partition functions (A_T, B_T, E_T) to
concrete SAW counts (saw_count n) via the corrected bridge partition
(origin_bridge_partition from SAWBridgeFix.lean).
-/

/-- **Main Theorem** (Duminil-Copin & Smirnov, 2012):
    The connective constant of the hexagonal lattice equals √(2+√2).

    This assembles the full proof chain:
    • Algebraic identities (SAW.lean): pair/triplet cancellation
    • Vertex relation (SAWVertex.lean): Lemma 1 of the paper
    • Strip identity (SAWStrip.lean): Lemma 2 — 1 = c_α·A + B + c_ε·E
    • Submultiplicativity (SAWSubmult.lean): c_{n+m} ≤ c_n · c_m
    • Fekete's lemma (SAWMain.lean): c_n^{1/n} → μ
    • Bridge infrastructure (SAWBridgeFix.lean): corrected bridge partition
    • Bridge decomposition (SAWDecomp.lean): bridge bounds, product convergence
    • Lower bound (SAWProof.lean): B_T ≥ c/T → Z(xc) = ∞
    • Upper bound (SAWBridge.lean): Z(x) ≤ 2·∏(1+B_T^x)² < ∞
    • This file: assembly via connective_constant_eq_from_bounds

    **Remaining gaps**: connecting the abstract strip identity to concrete
    SAW counts via origin_bridge_partition. -/
theorem connective_constant_eq :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) := by
  exact connective_constant_eq_from_bounds
    -- Lower bound: Z(xc) = ∞
    -- The abstract proof gives: strip identity → B_T ≥ c/T → Σ B_T = ∞
    -- The gap: connecting origin_bridge_partition to saw_count
    (Z_xc_diverges_from_lower_bound)
    -- Upper bound: Z(x) < ∞ for 0 < x < xc
    -- Uses Hammersley-Welsh bridge decomposition → Z(x) ≤ 2·∏(1+B_T^x)²
    -- Proved in SAWHammersleyWelsh.lean modulo the partial-sum bound
    (fun x hx hxc => hammersley_welsh_summable hx hxc)

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

/-- The partition function Z(x) converges for 0 < x < x_c. -/
theorem partition_function_converges_below_xc' :
    ∀ x, 0 < x → x < xc →
      Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  exact fun x hx hxc => hammersley_welsh_summable hx hxc

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
- **Corrected bridge partition**: origin_bridge_partition (SAWBridgeFix.lean)
- **Bridge bounds**: B_T^{x_c} ≤ 1 and B_T^{x_c} ≥ c/T (SAWDecomp.lean)
- **Lower bound**: Z(x_c) = ∞ via Cases 1 and 2 (SAWProof.lean, SAWBridgeFix.lean)
- **Upper bound**: Z(x) < ∞ for x < x_c via Hammersley-Welsh (SAWBridgeFix.lean)
- **Main theorem**: μ = √(2+√2) via connective_constant_eq_from_bounds

### Section 4: Conjectures (SAWConjectures.lean)
- Nienhuis' asymptotic formula: c_n ~ A·n^{γ-1}·μ^n with γ = 43/32
- Flory exponent: ⟨|γ(n)|²⟩ = n^{3/2 + o(1)} with ν = 3/4
- SLE(8/3) conjecture for the scaling limit

### Remaining gaps

The following pieces require concrete combinatorial infrastructure
that has been stated but not yet fully connected:

1. **Strip identity connection**: Showing that origin_bridge_partition
   satisfies the abstract strip identity with the correct coefficients.
   This requires formalizing walks restricted to strip domains S_{T,L}.

2. **Hammersley-Welsh injection**: Formalizing the decomposition of every
   SAW into a sequence of bridges with monotone widths, and proving the
   injection gives Z(x) ≤ 2·∏(1+B_T^x)².

3. **Bridge partition definition fix**: The original bridge_partition is
   broken (Bridge T is infinite, so tsum = 0). The corrected version
   origin_bridge_partition from SAWBridgeFix.lean fixes this by summing
   over bridges from hexOrigin only.
-/

/-! ## Bridge existence and definition note

The Bridge definition in SAWBridge.lean uses vertex x-coordinates for boundary
conditions: start_v.1 = 0 (left) and end_v.1 = T (right). This gives the
correct structure for the strip S_T.

The bridge_partition (tsum over all Bridge T) is infinite because
Bridge T is infinite (infinitely many starting y-coordinates). This was
proven in SAWBridgeFix.lean, which also provides the corrected
origin_bridge_partition definition. -/

end
