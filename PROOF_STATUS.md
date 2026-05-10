# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 3 root sorries** (2 independent chains).

## Root Sorries

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

**Mathematical content**: Follows from the finite strip identity
1 = c_α·A + B + c_ε·E with A,E ≥ 0. Same discrete Stokes argument
as Sorry #1 but for the finite strip S_{T,L}.

**Relationship to Sorry #1**: Both sorries follow from the same
mathematical argument (the parafermionic observable / Lemma 2).
If either is proved, the other can be derived (Sorry #1 from
Sorry #2 via a limit argument; Sorry #2 from Sorry #1 via
paper_bridge_partition ≤ 1/xc).

### Sorry #3: `paper_bridge_decomp_injection` (SAWPaperChain.lean:258)
```lean
∑_{n≤N} c_n x^n ≤ 2·(∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}(x))²
```
The Hammersley-Welsh bridge decomposition counting inequality.
Required for: Z(x) < ∞ for x < xc (upper bound μ ≤ √(2+√2)).

**Mathematical content**: The bridge decomposition algorithm:
1. Split SAW at vertex with extremal diagCoord → two half-plane walks.
2. Each half-plane walk decomposes into bridges of strictly decreasing widths.
3. The decomposition is injective: given bridges, walk is reconstructable.
4. Weight inequality: x^n ≤ ∏ x^{len(bridge_i)} since x ≤ 1.
5. Summing: Z_N(x) ≤ 2·(∏(1+B_T(x)))².

## Proof Architecture

```
connective_constant_eq_corrected (SAWPaperChain.lean)
├── Z_xc_diverges_corrected (SAWPaperChain.lean) [LOWER BOUND]
│   └── paper_bridge_lower_bound
│       ├── paper_bridge_partition_one_pos
│       │   └── paper_bridge_summable ← depends on Sorry #2
│       └── bridge_recurrence_proved (SAWRecurrenceProof.lean)
│           ├── infinite_strip_identity ← SORRY #1
│           └── cutting_argument_proved ✓
└── hw_summable_corrected (SAWPaperChain.lean) [UPPER BOUND]
    ├── paper_bridge_decomp_injection ← SORRY #3
    └── paper_bridge_decay
        └── paper_bridge_partial_sum_le (SAWDiagProof.lean)
            └── B_paper_le_one_direct
                └── B_paper_le_one_strip ← SORRY #2
```

**Note**: Sorry #2 feeds into BOTH the lower and upper bounds (through
bridge summability for the lower bound, and bridge decay for the upper
bound). Sorry #1 feeds only into the lower bound. Sorry #3 feeds only
into the upper bound.

## New Infrastructure (SAWObservableStokes.lean, sorry-free)

Edge direction computations for the hex lattice:
- `hexEdgeDirC`: direction of edge as ℂ (unit length)
- `hexEdgeDirC_F_T_same`: FALSE→TRUE same-coordinate has direction 1
- `hexEdgeDirC_T_F_same`: TRUE→FALSE same-coordinate has direction -1
- `hexEdgeDirC_sum_zero_false`: 3 directions from FALSE vertex sum to 0
- `hexEdgeDirC_sum_zero_true`: 3 directions from TRUE vertex sum to 0
- `hexEdgeDirC_start`: paperStart→hexOrigin has direction -1
- `hexEdgeDirC_antisymm`: dir(v,w) = -dir(w,v)

This infrastructure is the first step toward formalizing the discrete
Stokes argument needed for Sorries #1 and #2.

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
  - `paper_bridge_length_ge`: length ≥ T
  - `paper_bridge_length_ge_tight`: length ≥ 2T−1
- Bridge partial sum bounds, bridge decay
- Cutting argument (`cutting_argument_proved`)

### Bipartite Structure
- `hexGraph_adj_flip_bool`: adjacent vertices differ in sublattice type
- `true_to_false_dc_change`: TRUE→FALSE edges decrease diagCoord by 0 or 1
- `false_to_true_dc_change`: FALSE→TRUE edges increase diagCoord by 0 or 1

### T=1 Special Case (sorry-free)
- `paper_bridge_partition_1_eq`: B_inf(1) = 2xc/(1-xc²)
- `B_paper_1_lt_one'`: B_paper(1,L,xc) < 1 for all L

### HW Decomposition Helpers
- `saw_weight_le_bridge_product`
- `powerset_prod_identity` = `Finset.prod_one_add`
- Half-plane walk infrastructure
- Walk max/min diagCoord properties
- Translation symmetry (`hexShift`) infrastructure

### Lower Bound Infrastructure
- Zigzag SAW construction (sorry-free)
- `saw_count_even_lower_proved`: 2^k ≤ c_{2k}
- c_n ≥ √2^n

## What Remains to Prove

### For Sorries #1 and #2 (Parafermionic Observable / Lemma 2)

Both sorries follow from the discrete Stokes identity for the strip domain.
The algebraic ingredients (pair_cancellation, triplet_cancellation,
boundary_cos_pos) are fully proved. The edge direction infrastructure
(hexEdgeDirC) is now in SAWObservableStokes.lean.

**What still needs formalization:**
1. **Walk partition into pairs/triplets at each vertex**: For each vertex v
   of the strip, partition SAWs ending at mid-edges adjacent to v into
   groups (pairs and triplets) where contributions cancel.
2. **Discrete Stokes summation**: Sum the vertex relation over all strip
   vertices. Interior mid-edges cancel (each appears twice with opposite
   signs). Only boundary mid-edges survive.
3. **Boundary winding evaluation**: For the finite strip, compute the
   winding from the starting mid-edge to each boundary type:
   - Right boundary (β): winding = 0, coefficient = 1
   - Left boundary (α): winding = ±π, coefficient = c_α = cos(3π/8)
   - Escape boundary (ε∪ε̄): winding = ±2π/3, coefficient = c_ε = cos(π/4)
   - Starting mid-edge: F(a) = 1, contributes -1
4. **Limit argument L→∞** (for Sorry #1 only): Show A_paper → A_inf,
   B_paper → xc·paper_bridge_partition, E_paper → E_inf → 0 or handle
   both cases (E_inf > 0 and E_inf = 0).

### For Sorry #3 (Hammersley-Welsh Decomposition)

**What still needs formalization:**
1. **Half-plane walk definition**: SAWs where the start has extremal diagCoord.
2. **Bridge extraction algorithm**: Find the last vertex with minimum
   diagCoord, extract the prefix as a PaperBridge, identify the suffix
   as a smaller half-plane walk.
3. **Injectivity**: Given the set of bridge widths and the bridges
   themselves, the original walk can be uniquely reconstructed.
4. **Weight accounting**: The walk weight x^n ≤ ∏ x^{len(bridge_i)}
   since x ≤ 1 and n ≥ ∑ len(bridge_i).
5. **General SAW splitting**: Split at vertex with extremal diagCoord
   into two half-plane walks. Factor of 2 from starting vertex choice.

## Non-critical-path sorries

Several files contain sorry'd lemmas that are NOT on the critical path
(not imported by the main theorem). These include duplicates, earlier
attempts, and infrastructure that was superseded by the correct
paper-bridge architecture. Files: SAWZigzag.lean, SAWFiniteStrip.lean,
SAWHWDecomp.lean, SAWHWAlgorithm.lean, SAWBridgeDecomp.lean,
SAWBridgeDecompCore.lean, SAWHammersleyWelsh.lean, SAWHWBridge.lean,
SAWHWInject.lean, SAWHWDecompFull.lean, SAWHWDecompNew.lean,
SAWStripIdentity.lean, SAWStokesSkeleton.lean, SAWStripProofDirect.lean,
SAWMainNew.lean, SAWCutting.lean.
