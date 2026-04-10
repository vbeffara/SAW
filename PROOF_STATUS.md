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
│                   ├── SAWObservableProof.lean (observable definitions) ✓
│                   └── SAWDiagProof.lean (paper bridge infrastructure) ✓
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

**What this says:** For T ≥ 1, L ≥ 1, the weighted count of SAWs
from paperStart to the right boundary of the finite strip S_{T,L},
weighted by xc^{length+1}, is at most 1.

**Proof strategy (from the paper):**
The parafermionic observable F(z) satisfies the vertex relation at
each interior vertex v (Lemma 1). Summing over all vertices yields
a boundary sum identity (discrete Stokes): 0 = Σ_{boundary z} (z−v) F(z).
Evaluating boundary contributions gives 1 = c_α A + B + c_ε E,
hence B ≤ 1.

**What's proved:**
- Pair cancellation: j · conj(λ)⁴ + conj(j) · λ⁴ = 0 ✓
- Triplet cancellation: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0 ✓
- Interior cancellation (algebraic): (w−v) + (v−w) = 0 ✓
- Boundary cos positivity: cos(3θ/8) > 0 for |θ| ≤ π ✓
- Boundary weight non-negativity: all 6 edge types ✓
- Right boundary weight = 1 ✓
- Starting direction factor = −1 ✓

**What's missing:**
- Formal definition of the parafermionic observable F(z)
  as a sum over SAWs with winding weights
- The pair/triplet partition of walks at each vertex
  (connecting the algebraic identities to actual walks)
- The discrete Stokes argument (summing vertex relations,
  showing interior terms cancel at the mid-edge level)
- Boundary evaluation (computing specific winding values
  for each boundary type)

**Infrastructure files:**
- SAWObservableProof.lean: defines walk weight, direction factors,
  strip vertex enumeration
- SAWObservableProof2.lean: boundary weight properties
- SAWDiscreteStokes.lean: direction factor computations
- SAWStokesSkeleton.lean: proof skeleton with definitions

### 2. `paper_bridge_recurrence` (SAWPaperChain.lean)
**∃ α > 0, ∀ T, paper_bridge_partition T xc ≤ α · (paper_bridge_partition (T+1) xc)² + paper_bridge_partition (T+1) xc**

**Proof strategy:** Follows from the infinite-strip identity and cutting argument.

1. **Infinite strip identity:** Taking L → ∞ in Lemma 2 gives
   1 = c_α A_T + B_T + c_ε E_T for the infinite strip.
2. **Case split:** Either E_T > 0 for some T (giving Z(xc) = ∞ directly)
   or E_T = 0 for all T (simplifying to 1 = c_α A_T + B_T).
3. **Cutting argument:** A walk in A_{T+1} \ A_T visits the right boundary
   of S_{T+1}. Cutting at the first such vertex gives two bridges.
   This yields A_{T+1} − A_T ≤ xc⁻¹ · B_{T+1}².
4. **Combine:** B_T − B_{T+1} = c_α(A_{T+1} − A_T) ≤ c_α xc⁻¹ B_{T+1}²,
   so B_T ≤ c_α xc⁻¹ B_{T+1}² + B_{T+1}.

**Dependencies:** Depends on B_paper_le_one_direct (sorry #1).

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean)
**∑_{n≤N} c_n x^n ≤ 2 · (∑_{S⊆{1,...,N}} ∏_{T∈S} B_{T+1}^x)²**

**This is the Hammersley–Welsh bridge decomposition.** Independent of #1.

**Proof strategy:**
1. Any SAW γ from paperStart can be split at its "deepest" vertex
   (minimum diagonal coordinate) into two half-plane walks.
2. Each half-plane walk decomposes into bridges with strictly
   decreasing widths (by induction on width).
3. The decomposition is injective (given the first vertex).
4. The factor 2 accounts for 2 choices of first vertex.
5. Each decomposed walk contributes at most the product of
   bridge partition functions for its bridge widths.
6. Summing over all possible width subsets gives the bound.

**What's proved:**
- Walk splitting utilities (walk_max_x, walk_max_x_bound) ✓
- Bridge-to-SAW injection ✓
- Walk coordinate bounds ✓
- Translation symmetry of hexGraph ✓

**What's missing:**
- The formal bridge decomposition algorithm
- Injectivity of the decomposition
- Weight accounting (walk length ≥ sum of bridge lengths)

## Fully proved components (no sorry dependencies)

- Hexagonal lattice definition and basic properties ✓
- Self-avoiding walk counting (c_n, finiteness, small values) ✓
- Graph automorphisms and vertex independence ✓
- Submultiplicativity: c_{n+m} ≤ c_n · c_m ✓
- Fekete's lemma and connective constant as limit ✓
- Connective constant positivity ✓
- Partition function radius of convergence ✓
- Main theorem reduction to partition function bounds ✓
- Paper strip domain (PaperInfStrip, PaperFinStrip) ✓
- Paper-compatible partition functions (A_paper, B_paper, E_paper) ✓
- Paper bridge definition and basic properties ✓
- Paper bridge positivity (bridges exist for all widths) ✓
- Quadratic recurrence lower bound (abstract) ✓
- Harmonic series divergence lemma ✓
- Subset product identity ✓
- Product convergence for geometric bounds ✓
- Monotone/antitone bounded convergence ✓
- Winding telescoping on hex lattice ✓
- Zigzag lower bound construction ✓

## Components proved modulo sorry's

The following are fully proved in Lean but depend transitively
on one or more of the 3 sorry'd lemmas:

- Paper bridge summability (depends on #1 via paper_bridge_upper_bound)
- Paper bridge finite sum bound ✓ (independent)
- Paper bridge sum ≤ Z(xc) ✓ (independent)
- Paper bridge upper bound (≤ 1/xc) (depends on #1)
- Paper bridge decay ((x/xc)^T / xc for x < xc) (depends on #1)
- Bridge-to-SAW injection (paper_bridge_filter_card_le) ✓ (independent)
- Paper bridge lower bound (c/T) (depends on #2 → #1)
- Z(xc) diverges (depends on #2 → #1)
- HW summability (depends on #3)
- Main theorem assembly (depends on all 3)

## File organization

### Critical path files
- `SAW.lean` — Key constants (xc, λ, j, σ, c_α, c_ε), algebraic identities
- `SAWSubmult.lean` — Submultiplicativity c_{n+m} ≤ c_n c_m
- `SAWStrip.lean` — Strip domain definitions
- `SAWMain.lean` — Fekete's lemma, connective constant
- `SAWBridge.lean` — Partition function, radius of convergence, main theorem reduction
- `SAWBridgeFix.lean` — Corrected bridge definitions
- `SAWStripIdentityCorrect.lean` — Paper strip, partition functions, **B_paper_le_one_direct (sorry)**
- `SAWDiagBridge.lean` — Diagonal bridge connections
- `SAWDiagConnection.lean` — Bridge-strip connections
- `SAWStripIdentityProof.lean` — Strip identity proof infrastructure
- `SAWDiagProof.lean` — Paper bridge infrastructure, partial sum bounds
- `SAWDecomp.lean` — Quadratic recurrence lower bound
- `SAWPaperChain.lean` — Main theorem assembly, **paper_bridge_recurrence (sorry)**, **paper_bridge_decomp_injection (sorry)**

### Observable infrastructure (supporting critical path)
- `SAWObservable.lean` — Observable definitions
- `SAWObservableProof.lean` — Walk weight, strip finiteness
- `SAWObservableProof2.lean` — Boundary weight properties
- `SAWDiscreteStokes.lean` — Direction factors, interior cancellation
- `SAWStokesSkeleton.lean` — Proof skeleton for discrete Stokes

### Supporting files (not on critical path)
- `SAWFiniteness.lean`, `SAWCompute.lean`, `SAWElementary.lean` — Elementary properties
- `SAWSymmetry.lean`, `SAWVertex.lean`, `SAWVertexRelation.lean` — Lattice symmetries
- `SAWWinding.lean`, `SAWPairTriplet.lean` — Winding and pair/triplet infrastructure
- `SAWZigzag.lean`, `SAWZigzagBuild.lean` — Lower bound constructions
- `SAWQuadRecurrence.lean` — Additional recurrence bounds

### Superseded files (earlier approaches, not on critical path)
- `SAWFiniteStrip.lean` — Earlier finite strip approach (3 sorry's, superseded by SAWStripIdentityCorrect)
- `SAWStripIdentity.lean` — Earlier Z divergence (superseded by SAWPaperChain)
- `SAWHWBridge.lean`, `SAWHWDecomp.lean`, `SAWHWInject.lean`, `SAWHWAlgorithm.lean` — Earlier HW decomposition using origin_bridge_partition (superseded by paper_bridge_decomp_injection)
- `SAWHammersleyWelsh.lean` — Earlier HW formalization (superseded)
- `SAWStripBridge.lean`, `SAWStripWalks.lean` — Earlier strip infrastructure (superseded)
- `SAWLowerBound.lean`, `SAWLowerBoundProof.lean`, `SAWLowerCount.lean` — Earlier lower bound approaches (superseded)
- `SAWProof.lean`, `SAWFinal.lean`, `SAWEquivalence.lean` — Earlier proof assembly (superseded by SAWPaperChain)
- `SAWCutting.lean`, `SAWHalfPlane.lean` — Earlier cutting/half-plane infrastructure
- `SAWConjectures.lean` — Conjectures (not on main theorem path)
