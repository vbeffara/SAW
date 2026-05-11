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

## Re Coordinate Resolution (NEW)

The file `SAWHWReCoord.lean` introduces `hexReScaled`, an integer-valued
coordinate that resolves the diagonal-vs-x-coordinate mismatch for the
Hammersley-Welsh decomposition:

```
hexReScaled(x, y, false) = -3(x+y)
hexReScaled(x, y, true)  = -3(x+y) + 2
```

Key properties (all sorry-free):
- `hexReScaled_adj_bound`: Adjacent vertices differ by at most 2.
- `hexReScaled_walk_bound`: Walk of length n changes by at most 2n.
- `hexReScaled_in_strip`: Strip vertices satisfy 0 ≤ hexReScaled ≤ 3T.
- `hexReScaled_bridge_endpoint`: Bridge endpoint has hexReScaled = 3T.

This coordinate gives DISTINCT values to TRUE and FALSE vertices at the
same diagCoord, ensuring the HW bridge extraction produces bridges with
strictly decreasing widths (matching the paper's use of Re(z)).

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
- `saw_count_submult_with_remainder`: c_{qm+r} ≤ c_m^q · c_r
- `connective_constant_pos'`: connective constant is positive

### Strip and Bridge Infrastructure
- Strip domain definitions (`PaperInfStrip`, `PaperFinStrip`)
- Strip finiteness, SAW length bounds
- Bridge definitions (`PaperBridge`), bridge length bounds
- Bridge partial sum bounds, bridge decay
- Cutting argument (`cutting_argument_proved`)

### T=1 Special Case (sorry-free)
- `paper_bridge_partition_1_eq`: B_inf(1) = 2xc/(1-xc²)
- `B_paper_1_lt_one'`: B_paper(1,L,xc) < 1 for all L
- `infinite_strip_identity_T1_clean`: 1 = c_α·A₁ + xc·B₁

### Re Coordinate Infrastructure (SAWHWReCoord.lean) (sorry-free, NEW)
- `hexReScaled`: Integer-valued Re coordinate for hex vertices
- `hexReScaled_adj_bound`: Adjacency bound
- `hexReScaled_walk_bound`: Walk bound
- `hexReScaled_in_strip`: Strip containment
- `hexReScaled_bridge_endpoint`: Bridge endpoint formula

### Edge Direction Infrastructure (SAWObservableStokes.lean)
- `hexEdgeDirC`: direction of edge as ℂ (unit length)
- `hexEdgeDirC_sum_zero_false/true`: 3 directions from vertex sum to 0
- `hexEdgeDirC_start`: paperStart→hexOrigin has direction -1
- `hexEdgeDirC_antisymm`: dir(v,w) = -dir(w,v)

### Parafermionic Observable Infrastructure (SAWParafermionicObservable.lean)
- Edge direction vectors at FALSE and TRUE vertices
- Abstract Stokes theorem (sum of zeros is zero)
- Abstract Stokes boundary decomposition
- Observable vertex relation (pair_cancellation + triplet_cancellation)

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
2. **SAW split**: At the first vertex with max hexReScaled.
3. **Bridge extraction**: Induction on hexReScaled width.
4. **Translation to PaperBridge**: After coordinate translation.
5. **Counting inequality**: From the injection.

## Build Status
All files compile without errors. The full project builds successfully.
