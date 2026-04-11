# Proof Status: The connective constant of the honeycomb lattice equals √(2+√2)

## Main theorem

`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
```
μ = √(2+√2)
```

**Status: 3 sorry's remaining on the critical path.**

## Critical path (dependency tree)

```
SAW.lean (constants, algebraic identities) ✓
├── SAWSubmult.lean (submultiplicativity: c_{n+m} ≤ c_n·c_m) ✓
│   └── SAWMain.lean (Fekete's lemma → connective constant is a limit) ✓
│       └── SAWBridge.lean (partition function, connective_constant_eq_from_bounds) ✓
│           └── SAWBridgeFix.lean (OriginBridge definition, corrections) ✓
│               └── SAWStripIdentityCorrect.lean (Paper strip domain, partition functions)
│                   ├── B_paper_le_one_direct ⚠️ [sorry — Lemma 2, B ≤ 1]
│                   └── SAWDiagBridge.lean → SAWDiagConnection.lean → SAWDiagProof.lean
│                       └── SAWPaperChain.lean (main theorem assembly)
│                           ├── paper_bridge_lower_bound ✓ (proved from recurrence)
│                           │   └── paper_bridge_recurrence ⚠️ [sorry — strip identity + cutting]
│                           ├── paper_bridge_decomp_injection ⚠️ [sorry — HW decomposition]
│                           ├── hw_summable_corrected ✓ (proved from decomposition + decay)
│                           ├── Z_xc_diverges_corrected ✓ (proved from lower bound)
│                           └── connective_constant_eq_corrected ✓ (proved from above)
└── SAWDecomp.lean (quadratic recurrence, abstract bridge bounds) ✓
```

## Remaining sorry's (critical path)

### 1. `B_paper_le_one_direct` (SAWStripIdentityCorrect.lean)
**B_paper(T, L, xc) ≤ 1** — the key consequence of Lemma 2.

**Proof strategy (from the paper):**
Define the parafermionic observable F(z) = Σ exp(-iσW)·xc^ℓ at each
mid-edge. The vertex relation (Lemma 1) holds at each interior vertex
via pair/triplet walk grouping (algebraic core: pair_cancellation +
triplet_cancellation, both proved). Summing over all vertices (discrete
Stokes): interior terms cancel, boundary sum = 0. Right boundary
contributes B_paper (winding = 0). Starting edge contributes -1.
All other boundary contributions have non-negative real part
(cos(3θ/8) > 0, proved as boundary_cos_pos). Hence B_paper ≤ 1.

**What's proved:** All algebraic ingredients (pair/triplet cancellation,
boundary cos positivity, direction factors). **What's missing:**
The combinatorial pair/triplet partition of walks and the discrete
Stokes telescoping argument.

### 2. `paper_bridge_recurrence` (SAWPaperChain.lean)
**∃ α > 0, ∀ T, B_T ≤ α·B_{T+1}² + B_{T+1}**

**Proof strategy:** From the infinite-strip identity and cutting argument.
1. Take L→∞ in the strip identity (monotone convergence)
2. Get 1 = c_α·A_T + B_T + c_ε·E_T for infinite strip
3. Cutting: A_{T+1} - A_T ≤ xc·B_{T+1}²
4. Monotonicity: E_{T+1} ≤ E_T
5. Combine: B_T ≤ c_α·xc·B_{T+1}² + B_{T+1}

**Depends on:** B_paper_le_one_direct (sorry #1).

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean)
**Σ_{n≤N} c_n·x^n ≤ 2·(Σ_{S⊆{1,...,N}} Π_{T∈S} B_{T+1}(x))²**

**Proof strategy (Hammersley-Welsh):**
1. Split any SAW at its deepest vertex (minimum x+y)
2. Each half is a half-plane walk decomposing into bridges
   of strictly decreasing widths
3. The decomposition is injective (given starting vertex)
4. Factor 2 for 2 choices of first vertex from starting mid-edge

**Independent of:** sorry #1 and #2.

## File organization (after cleanup)

### Critical path files
- `SAW.lean` — Key constants, algebraic identities
- `SAWSubmult.lean` — Submultiplicativity c_{n+m} ≤ c_n·c_m
- `SAWStrip.lean` — Strip domain definitions
- `SAWMain.lean` — Fekete's lemma, connective constant
- `SAWBridge.lean` — Partition function, main theorem reduction
- `SAWBridgeFix.lean` — Corrected bridge definitions
- `SAWStripIdentityCorrect.lean` — Paper strip, **B_paper_le_one_direct (sorry)**
- `SAWStripIdentityProof.lean` — Strip identity proof infrastructure
- `SAWDiagBridge.lean` — Diagonal bridge connections
- `SAWDiagConnection.lean` — Bridge-strip connections
- `SAWDiagProof.lean` — Paper bridge infrastructure
- `SAWDecomp.lean` — Quadratic recurrence lower bound
- `SAWPaperChain.lean` — Main theorem assembly, **recurrence (sorry)**, **HW decomp (sorry)**
- `SAWFinal.lean` — Clean main theorem export

### Observable infrastructure (supporting B_paper_le_one_direct)
- `SAWObservable.lean` — Observable definitions
- `SAWObservableProof.lean` — Walk weight, strip finiteness
- `SAWObservableProof2.lean` — Boundary weight properties
- `SAWDiscreteStokes.lean` — Direction factors, interior cancellation
- `SAWStokesSkeleton.lean` — Proof skeleton for discrete Stokes

### Supporting files
- `SAWElementary.lean` — Elementary SAW properties
- `SAWCompute.lean` — Concrete computations, bridge existence
- `SAWSymmetry.lean` — Lattice symmetries (coordinate swap)
- `SAWVertex.lean` — Vertex-level properties
- `SAWVertexRelation.lean` — Vertex relation infrastructure
- `SAWPairTriplet.lean` — Pair/triplet infrastructure
- `SAWWinding.lean` — Winding computations
- `SAWZigzag.lean` — Zigzag walk construction
- `SAWZigzagBuild.lean` — Zigzag counting proofs
- `SAWQuadRecurrence.lean` — Additional recurrence bounds

### Removed (superseded)
18 files removed: SAWFiniteStrip, SAWFiniteness, SAWStripIdentity,
SAWHWBridge, SAWHWDecomp, SAWHWInject, SAWHWAlgorithm, SAWHammersleyWelsh,
SAWStripWalks, SAWStripBridge, SAWLowerBound, SAWLowerBoundProof,
SAWLowerCount, SAWProof, SAWEquivalence, SAWCutting, SAWHalfPlane,
SAWConjectures.
