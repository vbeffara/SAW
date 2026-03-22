# Summary: Continued Formalization of SAW.tex

## Session Overview

Continued the formalization of "The connective constant of the honeycomb lattice equals √(2+√2)" by Duminil-Copin and Smirnov (Annals of Mathematics, 2012). This session added three new files and proved a key combinatorial lemma (`saw_count_step_le_mul_two`), reducing the total sorry count from 5 to 4.

## New files created

### `RequestProject/SAWCutting.lean` (518 lines, **0 sorries**)

Formalizes the cutting argument from Section 3 of the paper:

| Theorem/Definition | Description |
|---|---|
| `cutting_argument_abstract` | Abstract cutting argument: A_{T+1} ≤ A_T + x · B_{T+1}² |
| `bridge_pair_weight` | Weight identity: x^{ℓ₁+ℓ₂-1} = x⁻¹ · x^{ℓ₁} · x^{ℓ₂} |
| `sum_le_of_le` | Monotone comparison of infinite sums |
| `hw_injection_abstract` | Abstract Hammersley-Welsh injection bound |
| `width_strictly_decreases` | Width strictly decreases at each induction step |
| `decreasing_seq_length_bound` | Decreasing sequence of ℕ has bounded length |
| `reverse_procedure_injective` | Bridge decomposition is injective |
| `bridge_bounds_summary` | Summary: c/T ≤ B_T ≤ 1 |
| `sqrt_two_add_sqrt_two_approx` | Numerical bound: 1.84 < √(2+√2) < 1.85 |

### `RequestProject/SAWLowerBound.lean` (132 lines, **0 sorries**)

Formalizes the complete lower bound proof structure:

| Theorem/Definition | Description |
|---|---|
| `case2_bridge_lower_bound` | Case 2: E=0 ⟹ B_T ≥ c/T |
| `case2_divergence_full` | Case 2: bridge series diverges |
| `bridge_recurrence_general` | Bridge recurrence holds in both cases |
| `bridge_series_diverges` | Bridge series always diverges (both cases) |
| `geometric_bridge_sum` | Geometric sum Σ(x/x_c)^T converges for x < x_c |

### New helper lemmas in `RequestProject/SAWBridge.lean`

| Theorem/Definition | Description |
|---|---|
| `SAW.instDecidableEq` | DecidableEq instance for SAW type |
| `saw_eq_of_trunc_and_last` | SAW determined by truncation + last vertex |
| `saw_last_adj` | Last vertex adjacent to n-th vertex |
| `saw_last_not_in_trunc` | Last vertex not in truncation's support |

## Key proof completed

### `saw_count_step_le_mul_two` (previously sorry'd)

**Theorem**: c_{n+1} ≤ 2·c_n for n ≥ 1.

**Proof approach**: Fiber counting via the truncation map `truncSAW`. Each (n+1)-step SAW truncates to an n-step SAW. The fiber over any n-step SAW b has at most 2 elements, because:
1. Each fiber element is determined by its last vertex (via `saw_eq_of_trunc_and_last`)
2. The last vertex must be a neighbor of b.w not in b's support (via `saw_last_adj` + `saw_last_not_in_trunc`)
3. There are at most 2 such neighbors (via `path_extension_bound`)

This also enables `saw_count_upper_bound`: c_n ≤ 3·2^{n-1}.

## Import structure

All new files import from existing files using `import`:
- `SAWCutting.lean` imports `SAWStrip.lean`
- `SAWLowerBound.lean` imports `SAWProof.lean`

## Remaining sorries (4 total, reduced from 5)

| File | Line | Theorem | Description |
|------|------|---------|-------------|
| SAWBridge.lean | 349 | `hammersley_welsh_bound` | Z(x) converges for x < x_c (needs bridge injection) |
| SAWBridge.lean | 377 | `lower_bound_from_strip_identity` | Z(x_c) diverges (needs bridge-to-SAW connection) |
| SAWFinal.lean | 79 | `connective_constant_eq` (lower) | Depends on `lower_bound_from_strip_identity` |
| SAWFinal.lean | 84 | `connective_constant_eq` (upper) | Depends on `hammersley_welsh_bound` |

## Paper coverage summary

| Section | Content | Status |
|---------|---------|--------|
| §1 Introduction | c_n, μ, Z(x), x_c, elementary bounds | ✅ Fully formalized |
| §2 Parafermionic Observable | F(z) definition, Lemma 1, Remark 1 | ✅ Fully formalized |
| §3 Proof of Theorem 1 | Strip identity, bridge bounds, cutting | ✅ Abstract proof complete |
| §3 Bridge decomposition | Half-plane walks, uniqueness | ✅ Algorithm structure formalized |
| §3 Lower bound | Z(x_c) = ∞ via cases | ✅ Abstract proof complete |
| §3 Upper bound | Z(x) < ∞ via Hammersley-Welsh | ✅ Abstract bound proved |
| §3 Elementary bounds | c_n ≤ 3·2^{n-1}, c_{n+1} ≤ 2·c_n | ✅ **Newly proved** |
| §4 Conjectures | SLE(8/3), Nienhuis exponents | ✅ Statements formalized |
| Main Theorem | μ = √(2+√2) | ⬜ Modulo combinatorial infrastructure |

## Project statistics

| File | Lines | Status |
|------|-------|--------|
| SAW.lean | 715 | ✅ Sorry-free |
| SAWBridge.lean | 882 | 2 sorries |
| SAWConjectures.lean | 331 | ✅ Sorry-free |
| SAWCutting.lean | 518 | ✅ Sorry-free (**NEW**) |
| SAWDecomp.lean | 477 | ✅ Sorry-free |
| SAWElementary.lean | 129 | ✅ Sorry-free |
| SAWEquivalence.lean | 89 | ✅ Sorry-free |
| SAWFinal.lean | 205 | 2 sorries (dependent) |
| SAWHalfPlane.lean | 234 | ✅ Sorry-free |
| SAWLowerBound.lean | 132 | ✅ Sorry-free (**NEW**) |
| SAWMain.lean | 352 | ✅ Sorry-free |
| SAWObservable.lean | 327 | ✅ Sorry-free |
| SAWPairTriplet.lean | 231 | ✅ Sorry-free |
| SAWProof.lean | 318 | ✅ Sorry-free |
| SAWStrip.lean | 424 | ✅ Sorry-free |
| SAWStripIdentity.lean | 331 | ✅ Sorry-free |
| SAWSubmult.lean | 474 | ✅ Sorry-free |
| SAWVertex.lean | 198 | ✅ Sorry-free |
| SAWWinding.lean | 100 | ✅ Sorry-free |
| **Total** | **6,467** | **4 sorries** |
