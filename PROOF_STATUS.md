# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq` in `SAWFinal.lean`:
μ = √(2+√2) where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 3 sorry statements in 2 independent sorry chains.**

## Sorry Chain 1: Parafermionic Observable (Strip Identity)

### Sorry 1: `B_paper_le_one_strip` in `SAWStripIdentityCorrect.lean` (line 385)
B_paper(T,L,xc) ≤ 1 for the finite strip S_{T,L}.

### Sorry 2: `infinite_strip_identity` in `SAWRecurrenceProof.lean` (line 49)
1 = c_α · A_inf(T,xc) + xc · paper_bridge_partition(T,xc).

These are two formulations of Lemma 2 of Duminil-Copin & Smirnov (2012).
Sorry 1 implies Sorry 2 (by taking limits), but the code structure
currently treats them as independent.

**What is proved:**
- Algebraic identities: pair_cancellation, triplet_cancellation
- Abstract discrete Stokes theorem (discrete_stokes_abstract)
- Direction vector computations at hex vertices
- Boundary phase analysis (boundary_cos_pos)
- xc properties, strip domain definitions
- B_paper ≤ 1 follows from infinite_strip_identity (SAWParafermionicProof.lean)
- Bridge recurrence follows from infinite_strip_identity + cutting argument

**What is missing:**
- The combinatorial walk partition into pairs/triplets at each vertex
- The discrete Stokes summation for the hex lattice strip
- Winding evaluation for boundary mid-edges

## Sorry Chain 2: Hammersley-Welsh Decomposition

### Sorry 3: `paper_bridge_decomp_injection` in `SAWPaperChain.lean` (line 258)
∑_{n≤N} c_n x^n ≤ 2 · (∏_{T=1}^N (1+B_T(x)))²

**What is proved:**
- Bridge decay: B_T(x) ≤ (x/xc)^T (uses Sorry 1)
- Product convergence: ∏(1+B_T(x)) < ∞ for x < xc
- Summability framework: Z(x) < ∞ follows from the injection + decay
- Bridge positivity, bridge-to-SAW injection bounds

**What is missing:**
- The bridge decomposition algorithm (half-plane walk induction on width)
- General walk splitting at first vertex of minimal diagCoord
- Injectivity of the decomposition
- Weight accounting (walk length = sum of bridge lengths + skips)

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

### Iterated submultiplicativity (`SAWVertexRelation.lean`)
- c(k·m) ≤ c(m)^k (`saw_count_mul_le_pow`)
- c(n) ≤ M(m) · c(m)^⌊n/m⌋ (`saw_count_submult_bound`)
- Z(x) < ∞ when ∃m: c(m)·x^m < 1 (`partition_summable_of_small_root`)

### Walk partition infrastructure (`SAWWalkPartition.lean`) — NEW
- DiagCoord adjacency bound: |d(w)-d(v)| ≤ 1 (`diagCoord_adj_bound`)
- FALSE vertex neighbors: explicit 3-element list (`false_vertex_adj`)
- TRUE vertex neighbors: explicit 3-element list (`true_vertex_adj`)
- SAW count c_0 = 1 (`saw_count_zero`)

### Walk splitting infrastructure (`SAWHWWalkSplit.lean`) — NEW
- Walk minimum diagCoord: definition and basic properties
- Min diagCoord ≤ start (`walk_min_diagCoord_le_start`)
- Min diagCoord bounds all vertices (`walk_min_diagCoord_bound`)
- Min diagCoord is achieved (`walk_min_diagCoord_achieved`)
- SAW count c_1 = 3 (`saw_count_one`)
- SAW count c_2 = 6 (`saw_count_two`)

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
    SAWVertexRelation.lean  → Iterated submultiplicativity bounds
    SAWWalkPartition.lean   → Walk partition helpers (NEW)
    SAWHWWalkSplit.lean     → Walk splitting helpers (NEW)
    SAWMain.lean            → Fekete's lemma, connective constant
      SAWBridge.lean        → Partition function, cc_eq_inv_of_partition_radius
        SAWBridgeFix.lean   → OriginBridge, PaperBridge
          SAWStripIdentityCorrect.lean → B_paper ≤ 1 [SORRY 1]
            SAWDiagProof.lean → Bridge partial sums ≤ 1/xc
              SAWCuttingProof.lean → Cutting argument
                SAWRecurrenceProof.lean → Bridge recurrence [SORRY 2]
                  SAWPaperChain.lean → Main theorem assembly [SORRY 3]
                    SAWFinal.lean → connective_constant_eq
```
