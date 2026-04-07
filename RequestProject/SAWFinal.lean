/-
# Final proof assembly: The connective constant of the honeycomb lattice

This file imports the full proof chain and assembles the final results:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Import chain (corrected)

```
SAW.lean               — Core definitions, constants, algebraic identities
├─ SAWSubmult.lean      — Submultiplicativity: c_{n+m} ≤ c_n · c_m
│  └─ SAWMain.lean      — Fekete's lemma → connective constant is a limit
│     └─ SAWBridge.lean — Bridge defs, partition function, connective_constant_eq_from_bounds
│        └─ SAWBridgeFix.lean — OriginBridge definition
│           └─ SAWStripIdentityCorrect.lean — PaperBridge, B_paper_le_one_direct
│              └─ SAWDiagBridge.lean → SAWDiagConnection.lean → SAWDiagProof.lean
│                 └─ SAWPaperChain.lean — connective_constant_eq_corrected (main theorem)
└─ SAWDecomp.lean       — Quadratic recurrence, abstract bridge bounds
```

## Results proved here

1. `connective_constant_eq`: μ = √(2+√2) — the main theorem
2. `connective_constant_eq_inv_xc`: μ = xc⁻¹
3. `connective_constant_le_two'`: μ ≤ 2
4. `partition_function_diverges_above_xc'`: Z(x) = ∞ for x > xc
5. `partition_function_converges_below_xc'`: Z(x) < ∞ for 0 < x < xc

## Remaining gaps (sorry's)

The main theorem depends on three sorry'd lemmas:
1. `B_paper_le_one_direct` — the core strip identity (parafermionic observable)
2. `paper_bridge_lower_bound` — bridge lower bound c/T (depends on #1)
3. `paper_bridge_decomp_injection` — Hammersley-Welsh decomposition
-/

import RequestProject.SAWPaperChain

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-- **Main Theorem** (Duminil-Copin & Smirnov, 2012):
    The connective constant of the hexagonal lattice equals √(2+√2). -/
theorem connective_constant_eq :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) :=
  connective_constant_eq_corrected

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
  have hcn_ge_mu_n : ∀ n ≥ 1, (saw_count n : ℝ) ≥ connective_constant ^ n :=
    fun n hn => saw_count_ge_cc_pow n hn
  have hcn_xn_ge_1 : ∀ n ≥ 1, (saw_count n : ℝ) * x ^ n ≥ 1 := by
    intro n hn
    calc (1 : ℝ) ≤ (connective_constant * x) ^ n := one_le_pow₀ hmu_x_gt_1.le
      _ = connective_constant ^ n * x ^ n := by ring
      _ ≤ (saw_count n : ℝ) * x ^ n :=
          mul_le_mul_of_nonneg_right (hcn_ge_mu_n n hn)
            (pow_nonneg (le_trans xc_pos.le hx.le) _)
  exact fun h => absurd h.tendsto_atTop_zero fun H =>
    absurd (le_of_tendsto_of_tendsto tendsto_const_nhds H
      (Filter.eventually_atTop.mpr ⟨1, fun n hn => hcn_xn_ge_1 n hn⟩))
      (by norm_num)

/-- The partition function Z(x) converges for 0 < x < x_c. -/
theorem partition_function_converges_below_xc' {x : ℝ}
    (hx : 0 < x) (hxc : x < xc) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) :=
  hw_summable_corrected hx hxc

end
