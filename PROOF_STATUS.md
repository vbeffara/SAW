# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq` in `SAWFinal.lean`:
μ = √(2+√2) where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent sorry chains.**

## Sorry Chain 1: Parafermionic Observable (Strip Identity)

**Root sorry:** `B_paper_le_one_strip` in `SAWStripIdentityCorrect.lean` (line 385)
and `infinite_strip_identity` in `SAWRecurrenceProof.lean` (line 49).

These are two formulations of the same mathematical result (Lemma 2 of
Duminil-Copin & Smirnov 2012). The proof requires:
1. The vertex relation (Lemma 1): at each vertex v of the strip,
   (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0.
   - **Algebraic ingredients proved**: `pair_cancellation` and `triplet_cancellation`
   - **Missing**: combinatorial walk partition into pairs/triplets
2. Discrete Stokes: summing vertex relation over all vertices, interior
   mid-edges cancel. **Abstract theorem proved** (`discrete_stokes_abstract`).
3. Boundary evaluation: winding computation for boundary mid-edges.
   **Missing**: winding formalization for walks in strips.
4. Sign analysis: all non-B boundary contributions are non-negative.
   **Boundary positivity proved** (`boundary_cos_pos`).

## Sorry Chain 2: Hammersley-Welsh Decomposition

**Root sorry:** `paper_bridge_decomp_injection` in `SAWPaperChain.lean` (line 258).

This is the classical bridge decomposition of self-avoiding walks. The proof
requires:
1. Half-plane walk decomposition by strong induction on width.
2. General walk splitting at the first vertex of maximal diagonal excursion.
3. Injectivity of the reverse procedure.
4. Weight accounting.

**Bridge decay, product convergence, and summability argument all proved.**
Only the decomposition algorithm and its injectivity remain.

## Proved Results (sorry-free)

### Core framework
- Hexagonal lattice, SAW definitions, decidable adjacency
- Submultiplicativity: c_{n+m} ≤ c_n · c_m (`saw_count_submult'`)
- Fekete's lemma: μ = lim c_n^{1/n} (`connective_constant_is_limit'`)
- Connective constant positivity: μ > 0

### Algebraic identities
- All key constants: x_c, λ, j, σ, c_α, c_ε
- Pair cancellation: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- Triplet cancellation: 1 + x_c·j·conj(λ) + x_c·conj(j)·λ = 0
- Identity x_c⁻¹ = 2cos(π/8)

### New: Iterated submultiplicativity (`SAWVertexRelation.lean`)
- c(k·m) ≤ c(m)^k (`saw_count_mul_le_pow`)
- c(n) ≤ M(m) · c(m)^⌊n/m⌋ (`saw_count_submult_bound`)
- Z(x) < ∞ when ∃m: c(m)·x^m < 1 (`partition_summable_of_small_root`)

### Strip infrastructure
- PaperBridge, PaperInfStrip definitions
- Bridge length ≥ width
- Bridge decay: B_T(x) ≤ (x/xc)^T for x < xc
- Cutting argument: A_{T+1} - A_T ≤ xc · B_{T+1}²
- Bridge recurrence, lower bound, Z(xc) = ∞ (modulo sorry chain 1)
- Bridge partial sum bounds (modulo sorry chain 1)

### Discrete Stokes infrastructure
- Abstract discrete Stokes theorem for finite graphs
- Interior cancellation
- Direction vector computations
- Boundary phase analysis

### Walk infrastructure
- Walk extension (sawExtend, pathExtend)
- Walk splitting at vertices
- Walk diagonal coordinate bounds
- Translation infrastructure for bridges
- Zigzag walk construction (c_{2k} ≥ 2^k)

## File Map

### Main proof chain
```
SAW.lean                   → Core definitions and algebraic identities
  SAWSubmult.lean           → Submultiplicativity c_{n+m} ≤ c_n c_m
    SAWVertexRelation.lean  → Iterated submultiplicativity bounds (NEW, sorry-free)
    SAWMain.lean            → Fekete's lemma, connective constant
      SAWBridge.lean        → Partition function, cc_eq_inv_of_partition_radius
        SAWBridgeFix.lean   → OriginBridge, PaperBridge
          SAWStripIdentityCorrect.lean → B_paper ≤ 1 [SORRY]
            SAWDiagProof.lean → Bridge partial sums ≤ 1/xc
              SAWPaperChain.lean → Main theorem assembly
                SAWFinal.lean → connective_constant_eq
```

### Sorry dependency
- `B_paper_le_one_strip` → `B_paper_le_one_direct` → `paper_bridge_partial_sum_le`
  → `bridge_pair_summable` → `cutting_argument_proved` → `bridge_recurrence_proved`
  → `Z_xc_diverges_corrected` → `connective_constant_eq_corrected`
- `infinite_strip_identity` → `bridge_diff_eq` → `bridge_recurrence_proved` (same chain)
- `paper_bridge_decomp_injection` → `hw_summable_corrected` → `connective_constant_eq_corrected`
