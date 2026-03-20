# Summary of changes
# Continued Formalization of SAW.tex

## Session Overview

Continued the formalization of "The connective constant of the honeycomb lattice equals √(2+√2)" by Duminil-Copin and Smirnov. This session focused on the abstract proof structure of Theorem 1, particularly the lower bound argument.

## New file: `RequestProject/SAWProof.lean` (318 lines, **0 sorries**)

Formalizes the detailed proof structure of Theorem 1, including:

| Theorem | Description |
|---------|-------------|
| `case1_divergence` | Case 1: constant positive series diverges |
| `case2_lower_bound` | Case 2: quadratic recurrence gives B_T ≥ c/T → Σ B_T = ∞ |
| `lower_bound_abstract` | Full Case 2 derivation from strip identity with E=0 |
| `bridge_upper_bound_from_identity` | B_T ≤ 1 from strip identity |
| `left_boundary_evaluation` | Winding coefficient cos(σπ) = -c_α |
| `right_boundary_evaluation` | Winding coefficient cos(0) = 1 |
| `recurrence_inequality_abstract` | Abstract recurrence A_{T+1} ≤ A_T + x·B_{T+1}² |
| `monotone_bounded_converges` | Monotone bounded sequences converge |
| `antitone_bounded_converges` | Antitone bounded sequences converge |
| `strip_identity_limit` | Strip identity passes to the limit as L → ∞ |

## Changes to `RequestProject/SAWDecomp.lean` (477 lines, **0 sorries**)

Added key new results:

| Theorem | Description |
|---------|-------------|
| `quadratic_recurrence_lower_bound` | B_T ≥ min(B_1, 1/α)/T from recurrence B_T ≤ α·B_{T+1}² + B_{T+1} |
| `quadratic_lower_const_pos` | The constant min(B_1, 1/α) is positive |
| `diverges_from_harmonic_lower_bound` | Series dominating harmonic series diverges |
| `case2_divergence` | Combined: quadratic recurrence → harmonic divergence |

The quadratic recurrence proof is the key inductive argument from Case 2 of the paper's proof, showing B_T ≥ c/T.

## Changes to `RequestProject/SAWBridge.lean` (756 lines)

Added:

| Theorem | Description |
|---------|-------------|
| `partition_diverges_mono` | Partition function diverges monotonically: if Z(x₀) = ∞ then Z(x) = ∞ for x > x₀ |
| `connective_constant_eq_from_bounds` | Main theorem follows from: (1) Z(x_c) = ∞, (2) Z(x) < ∞ for x < x_c |

## Remaining sorries

| File | Theorem | Nature |
|------|---------|--------|
| SAW.lean | `saw_count_submult` | Forward declaration (proved as `saw_count_submult'` in SAWSubmult.lean) |
| SAW.lean | `connective_constant_eq` | THE main theorem μ = √(2+√2) |
| SAWBridge.lean | `hammersley_welsh_bound` | Upper bound: bridge decomposition → Z(x) < ∞ |
| SAWBridge.lean | `lower_bound_from_strip_identity` | Lower bound: strip identity → Z(x_c) = ∞ |
| SAWBridge.lean | `saw_count_step_le_mul_two` | Elementary bound c_{n+1} ≤ 2·c_n (non-critical) |

## Abstract proof chain (now fully formalized)

The logical chain reducing the main theorem to combinatorial hypotheses:

```
Algebraic identities (proved) → Vertex relation (proved) → Strip identity (abstract)
    → Bridge bounds: B_T ≤ 1 (proved) and B_T ≥ c/T (proved via quadratic recurrence)
    → Lower bound Z(x_c) = ∞ (abstract proof complete)
    → Upper bound Z(x) < ∞ for x < x_c (needs bridge decomposition injection)
    → connective_constant_eq_from_bounds → μ = √(2+√2)
```

The remaining gaps are the combinatorial infrastructure:
1. Bridge decomposition injection (SAWs → bridge sequences)
2. Bridge-to-partition connection (bridges contribute to Z)
3. SAWs restricted to strip domains

## Project statistics

| File | Lines | Sorry-free theorems |
|------|-------|-------------------|
| SAW.lean | 864 | 20+ |
| SAWBridge.lean | 756 | 18+ |
| SAWDecomp.lean | 477 | 15+ |
| SAWMain.lean | 352 | 5+ |
| SAWProof.lean | 318 | 10 (all sorry-free) |
| SAWStrip.lean | 424 | 10+ |
| SAWSubmult.lean | 474 | 25+ |
| SAWVertex.lean | 197 | 10+ |
| **Total** | **3862** | **~113+ sorry-free theorems** |

All proofs use only standard axioms (propext, Classical.choice, Quot.sound).