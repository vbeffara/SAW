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
│                   └── B_paper_le_one_obs ⚠️ [sorry — Lemma 2, B ≤ 1]
│                       └── SAWDiagProof.lean (Paper bridge infrastructure) ✓
│                           └── SAWPaperChain.lean (main theorem assembly)
│                               ├── paper_bridge_recurrence ⚠️ [sorry — strip identity + cutting]
│                               ├── paper_bridge_decomp_injection ⚠️ [sorry — HW decomposition]
│                               ├── paper_bridge_lower_bound ✓ (from recurrence)
│                               ├── hw_summable_corrected ✓ (from decomposition + decay)
│                               ├── Z_xc_diverges_corrected ✓ (from lower bound)
│                               └── connective_constant_eq_corrected ✓ (from above)
└── SAWDecomp.lean (quadratic recurrence, abstract bridge bounds) ✓
```

## Remaining sorry's (critical path)

### 1. `B_paper_le_one_obs` (SAWStripIdentityCorrect.lean, line 344)
**B_paper(T, L, xc) ≤ 1** — Lemma 2 of the paper.

**Proof strategy (from the paper):**
Define the parafermionic observable F(z) = Σ exp(-iσW)·xc^ℓ at each
mid-edge. The vertex relation (Lemma 1) holds at each interior vertex
via pair/triplet walk grouping. Summing over all vertices (discrete
Stokes): interior terms cancel, boundary sum = 0. Right boundary
contributes B_paper (winding = 0). Starting edge contributes -1.
All other boundary contributions have non-negative real part.
Hence B_paper ≤ 1.

**What's proved:** All algebraic ingredients:
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- `boundary_cos_pos`: cos(3θ/8) > 0 for |θ| ≤ π
- Direction vector sums at vertices: false_vertex_dir_sum, true_vertex_dir_sum
- Interior edge cancellation
- Observable definitions: F_directed, F_midedge, StripSAW

**What's missing:** The combinatorial pair/triplet partition of walks
at each vertex, and the discrete Stokes telescoping argument.

### 2. `paper_bridge_recurrence` (SAWPaperChain.lean, line 131)
**∃ α > 0, ∀ T, B_T ≤ α·B_{T+1}² + B_{T+1}**

**Proof strategy:** From the infinite-strip identity and cutting argument.
1. Take L→∞ in the strip identity (monotone convergence)
2. Get 1 = c_α·A_T + B_T + c_ε·E_T for infinite strip
3. Cutting: A_{T+1} - A_T ≤ xc·B_{T+1}²
4. E is monotone decreasing in T
5. Combine: B_T ≤ c_α·xc·B_{T+1}² + B_{T+1}

**Depends on:** B_paper_le_one_obs (sorry #1).

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean, line 257)
**Σ_{n≤N} c_n·x^n ≤ 2·(Σ_{S⊆{1,...,N}} Π_{T∈S} B_{T+1}(x))²**

**Proof strategy (Hammersley-Welsh):**
1. Split any SAW at its deepest vertex (minimum diagonal coordinate)
2. Each half is a half-plane walk decomposing into bridges
   of strictly decreasing widths
3. The decomposition is injective
4. For x ≤ 1, walk weight ≤ product of bridge weights
5. Factor 2 for 2 choices of starting direction

**Independent of:** sorry #1 and #2.

## File organization

### Critical path files (transitively imported by SAWPaperChain)
- `SAW.lean` — Key constants, algebraic identities (pair/triplet cancellation)
- `SAWSubmult.lean` — Submultiplicativity c_{n+m} ≤ c_n·c_m
- `SAWMain.lean` — Fekete's lemma, connective constant definition
- `SAWBridge.lean` — Partition function, main theorem reduction
- `SAWBridgeFix.lean` — Corrected bridge definitions
- `SAWStripIdentityCorrect.lean` — Paper strip, **B_paper_le_one_obs (sorry)**
- `SAWStripIdentityProof.lean` — Strip identity proof infrastructure
- `SAWDiagBridge.lean` — Diagonal bridge connections
- `SAWDiagConnection.lean` — Bridge-strip connections
- `SAWDiagProof.lean` — Paper bridge infrastructure
- `SAWDecomp.lean` — Quadratic recurrence lower bound
- `SAWPaperChain.lean` — Main theorem assembly, **recurrence + HW (sorry)**

### Supporting files (not on critical path)
- `SAWObservable.lean`, `SAWObservableProof.lean`, `SAWObservableProof2.lean` — Observable definitions
- `SAWDiscreteStokes.lean` — Direction factors, interior cancellation
- `SAWStokesSkeleton.lean` — Vertex relation statement (sorry)
- `SAWVertexRelProof.lean` — Vertex relation algebraic components
- `SAWVertexRelation.lean` — Vertex relation decomposition
- `SAWPairTriplet.lean` — Pair/triplet winding computations
- `SAWBridgeDecomp.lean` — Bridge decomposition infrastructure (sorry)
- `SAWHWAlgorithm.lean`, `SAWHWBridge.lean`, `SAWHWDecomp.lean`, `SAWHWInject.lean` — HW infrastructure (sorry)
- `SAWHammersleyWelsh.lean` — HW summability infrastructure (sorry)
- `SAWElementary.lean`, `SAWCompute.lean` — Elementary SAW properties
- `SAWSymmetry.lean` — Lattice symmetries
- `SAWWinding.lean` — Winding computations
- `SAWZigzag.lean`, `SAWZigzagBuild.lean` — Zigzag walk construction
- `SAWStrip.lean`, `SAWFiniteStrip.lean`, `SAWStripWalks.lean` — Strip domain definitions
- `SAWVertex.lean`, `SAWQuadRecurrence.lean` — Additional infrastructure
- `SAWFinal.lean` — Clean main theorem export
- `SAWLowerBound.lean`, `SAWLowerBoundProof.lean`, `SAWLowerCount.lean` — Lower bound attempts
- `SAWConjectures.lean`, `SAWEquivalence.lean`, `SAWCutting.lean`, `SAWHalfPlane.lean` — Various
- `SAWProof.lean`, `SAWStripIdentity.lean`, `SAWStripBridge.lean` — Older versions

## Blueprint

The blueprint in `blueprint/src/content.tex` documents:
1. All definitions and their Lean formalization status
2. The algebraic identities (all proved)
3. The parafermionic observable framework
4. The vertex relation proof structure (detailed decomposition into
   pair/triplet grouping, with exhaustiveness conditions)
5. The bridge decomposition algorithm (half-plane walks, recursive
   extraction, weight factorization)
6. The three remaining gaps and their dependencies
