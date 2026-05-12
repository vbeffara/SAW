# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent root sorries** (see below).

## Root Sorries

There are 3 sorry statements on the critical path, but they reduce to
**2 independent mathematical gaps**:

### Sorry #1: `infinite_strip_identity` (SAWRecurrenceProof.lean:49)
```lean
1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc
```
The parafermionic observable identity for the infinite strip.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

**Mathematical content**: Equation (4) of the paper, derived from
Lemma 2 by taking L→∞. Requires the full discrete Stokes argument:
vertex relation (proved algebraically) + interior mid-edge cancellation
+ boundary winding evaluation.

### Sorry #2: `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385)
```lean
B_paper T L xc ≤ 1
```
The core bound from the parafermionic observable (Lemma 2).
Required for: bridge summability → bridge decay → Z(x) < ∞.

**Dependency on Sorry #1**: This sorry FOLLOWS from Sorry #1, as proved
in `SAWStripFromIdentity.lean` (theorem `B_paper_le_one_from_identity`).
The proof: PaperSAW_B injects into PaperBridge, giving
B_paper ≤ xc · paper_bridge_partition ≤ 1 (from #1).

### Sorry #3: `paper_bridge_decomp_injection` (SAWPaperChain.lean:265)
```lean
∑_{n≤N} c_n x^n ≤ 2·(∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}(x))²
```
The Hammersley-Welsh bridge decomposition counting inequality.
Required for: Z(x) < ∞ for x < xc (upper bound μ ≤ √(2+√2)).

**Mathematical content**: The bridge decomposition algorithm from Section 3
of the paper (Proposition 3). Every SAW decomposes into two sequences of
bridges with strictly decreasing widths. The factor 2 comes from the two
choices for the first vertex given a starting mid-edge.

## Independent Sorry Count

**Only 2 independent mathematical gaps remain:**
1. `infinite_strip_identity` — the parafermionic observable / discrete Stokes argument
2. `paper_bridge_decomp_injection` — the Hammersley-Welsh bridge decomposition

Sorry #2 (`B_paper_le_one_strip`) follows from Sorry #1.

## Proof Architecture

```
connective_constant_eq_corrected (SAWPaperChain.lean)
├── Z_xc_diverges_corrected (SAWPaperChain.lean) [LOWER BOUND]
│   └── paper_bridge_lower_bound
│       ├── paper_bridge_partition_one_pos ✓ (sorry-free)
│       └── bridge_recurrence_proved (SAWRecurrenceProof.lean)
│           ├── infinite_strip_identity ← SORRY #1
│           └── cutting_argument_proved ✓
└── hw_summable_corrected (SAWPaperChain.lean) [UPPER BOUND]
    ├── paper_bridge_decomp_injection ← SORRY #3
    └── paper_bridge_decay
        └── paper_bridge_partial_sum_le (SAWDiagProof.lean)
            └── B_paper_le_one_direct
                └── B_paper_le_one_strip ← SORRY #2 (= consequence of #1)
```

## New Helper Lemmas (SAWHWDecompDirect.lean) — ALL SORRY-FREE

The following helper lemmas for the Hammersley-Welsh decomposition
were proved during this session:

- `rhs_ge_two'`: The RHS of the HW bound is ≥ 2 for all N.
- `saw_count_zero'`: saw_count 0 = 1.
- `decomp_injection_N0'`: The HW bound holds trivially for N = 0.
- `powerset_prod_eq'`: ∑_{S⊆range N} ∏_{T∈S} β_T = ∏_{T<N} (1 + β_T).
- `paperBridge_width1b`: A second explicit bridge of width 1.
- `paperBridge_width1_ne_width1b`: The two width-1 bridges are distinct.

## Fully Proved Results (no sorry, on the critical path)

### Core Definitions and Properties
- Hexagonal lattice (`hexGraph`), SAW, `saw_count`
- Connective constant definition and limit (`connective_constant_is_limit'`)
- Critical fugacity `xc`, phase parameters `λ`, `j`, `σ`, `c_α`, `c_ε`

### Algebraic Identities (Lemma 1 infrastructure)
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- `boundary_cos_pos`: cos(3θ/8) > 0 for |θ| ≤ π

### Submultiplicativity and Fekete
- `saw_count_submult'`: c_{n+m} ≤ c_n·c_m
- `saw_count_iter_submult`: c_{km} ≤ c_m^k
- `connective_constant_pos'`: connective constant is positive

### Strip and Bridge Infrastructure
- Strip domain definitions (`PaperInfStrip`, `PaperFinStrip`)
- Strip finiteness, SAW length bounds
- Bridge definitions (`PaperBridge`), bridge length bounds
- Bridge partial sum bounds, bridge decay
- Cutting argument (`cutting_argument_proved`)

### T=1 Special Case (partially sorry-free)
- `paper_bridge_partition_1_eq`: B_inf(1) = 2xc/(1-xc²) ✓ sorry-free
- `B_paper_1_lt_one'`: B_paper(1,L,xc) < 1 for all L ✓ sorry-free

### Re Coordinate Infrastructure (SAWHWReCoord.lean) (sorry-free)
- `hexReScaled`: Integer-valued Re coordinate for hex vertices
- `hexReScaled_adj_bound`: Adjacency bound
- `hexReScaled_walk_bound`: Walk bound
- `hexReScaled_in_strip`: Strip containment
- `hexReScaled_bridge_endpoint`: Bridge endpoint formula

### HW Decomposition Helpers (SAWHWDecompDirect.lean) (sorry-free)
- `rhs_ge_two'`: RHS bound ≥ 2
- `powerset_prod_eq'`: Powerset-product algebraic identity
- `paperBridge_width1b`: Second width-1 bridge construction
- `paperBridge_width1_ne_width1b`: Bridge distinctness

## What Remains to Prove

### For Sorry #1 (Parafermionic Observable / Lemma 2)

The proof requires formalizing the discrete Stokes argument:

1. **Define the observable F** at each mid-edge z of the strip S_{T,L}.
2. **Vertex relation**: At each vertex v, Σ dir(v,w)·F(v,w) = 0.
   This requires partitioning SAWs into pairs/triplets at each vertex.
   The algebraic core (pair/triplet cancellation) is proved.
3. **Discrete Stokes**: Sum over all vertices → 0. Interior cancel,
   boundary survive.
4. **Boundary evaluation**: Winding angles and phase factors.
5. **Limit L→∞**: Finite strip → infinite strip.

### For Sorry #3 (Hammersley-Welsh Decomposition)

The Re coordinate infrastructure (SAWHWReCoord.lean) provides the
foundation. The remaining formalization requires:

1. **Half-plane walks**: Define using hexReScaled.
2. **SAW split**: At the first vertex with min diagCoord.
3. **Bridge extraction**: Induction on width (using last vertex at max hexReScaled).
4. **Translation to PaperBridge**: After coordinate translation.
5. **Injectivity of the decomposition**: Different SAWs give different
   bridge sequences.
6. **Counting inequality**: From the injection + weight bound.

Key algebraic helper (proved):
- `powerset_prod_eq'`: converts powerset sum to product form.

## Build Status
All files compile without errors. No new sorries were introduced.
