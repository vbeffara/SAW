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
If either is proved, the other can be derived.

### Sorry #3: `paper_bridge_decomp_injection` (SAWPaperChain.lean:265)
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
│       ├── paper_bridge_partition_one_pos ✓ (sorry-free via paper_bridge_partition_1_eq)
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

**Note**: Sorry #2 feeds into the upper bound (through bridge decay).
Sorry #1 feeds into the lower bound (through the bridge recurrence).
Sorry #3 feeds into the upper bound (through the HW decomposition).
`paper_bridge_partition_one_pos` is now sorry-free (uses exact T=1 computation).

## Recent Changes

### paper_bridge_partition_one_pos (SAWPaperChain.lean)
**Previously**: Depended on `paper_bridge_summable` → Sorry #2.
**Now**: Uses `paper_bridge_partition_1_eq` (exact T=1 computation), sorry-free.
This simplifies the dependency chain for the lower bound.

### Blueprint (blueprint/src/content.tex)
Extended with:
- Exact bridge partition for T=1 (proved)
- T=1 infinite strip identity (proved)
- Main theorem assembly (modulo root sorries)
- Chapter on Conjectures (Section 4 of the paper):
  - Asymptotic behavior of c_n (γ = 43/32)
  - Mean-square displacement (ν = 3/4)
  - SLE(8/3) convergence conjecture
  - Observable scaling limit conjecture
  - Bridge decay conjecture (T^{-1/4})
- Root sorries summary

### New file: SAWHWDecompFinal.lean
Infrastructure for the Hammersley-Welsh decomposition:
- SAW diagCoord range bounds
- Powerset product identity wrapper
- Bridge partition function nonnegativity

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

### T=1 Special Case (sorry-free)
- `paper_bridge_partition_1_eq`: B_inf(1) = 2xc/(1-xc²)
- `B_paper_1_lt_one'`: B_paper(1,L,xc) < 1 for all L
- `infinite_strip_identity_T1_clean`: 1 = c_α·A₁ + xc·B₁
- `paper_bridge_partition_one_pos`: B₁(xc) > 0 (now sorry-free)

### HW Decomposition Helpers
- `saw_weight_le_bridge_product`
- `powerset_prod_identity` = `Finset.prod_one_add`
- Half-plane walk infrastructure
- Walk max/min diagCoord properties
- Translation symmetry (`hexShift`) infrastructure

### Edge Direction Infrastructure (SAWObservableStokes.lean)
- `hexEdgeDirC`: direction of edge as ℂ (unit length)
- `hexEdgeDirC_sum_zero_false/true`: 3 directions from vertex sum to 0
- `hexEdgeDirC_start`: paperStart→hexOrigin has direction -1
- `hexEdgeDirC_antisymm`: dir(v,w) = -dir(w,v)

## What Remains to Prove

### For Sorries #1 and #2 (Parafermionic Observable / Lemma 2)

Both sorries follow from the discrete Stokes identity for the strip domain.
The algebraic ingredients are fully proved. What still needs formalization:

1. **Walk partition into pairs/triplets at each vertex**: For each vertex v
   of the strip, partition SAWs ending at mid-edges adjacent to v into
   groups (pairs and triplets) where contributions cancel.
2. **Discrete Stokes summation**: Sum the vertex relation over all strip
   vertices. Interior mid-edges cancel (each appears twice with opposite
   signs). Only boundary mid-edges survive.
3. **Boundary winding evaluation**: Compute the winding from the starting
   mid-edge to each boundary type.
4. **Limit argument L→∞** (for Sorry #1 only).

### For Sorry #3 (Hammersley-Welsh Decomposition)

1. **Half-plane walk decomposition**: Define bridge extraction from
   half-plane walks (find last vertex at max diagCoord, extract bridge).
2. **Injectivity**: Show the decomposition is injective.
3. **SAW splitting**: Split SAW at vertex with min diagCoord into two
   half-plane walks.
4. **Weight accounting**: Walk weight ≤ product of bridge weights.
