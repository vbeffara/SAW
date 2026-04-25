# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected : connective_constant = Real.sqrt (2 + Real.sqrt 2)`

**Status: Compiles with sorry.** The theorem and its complete proof chain compile in Lean.
All sorries ultimately reduce to TWO independent fundamental gaps.

## What Is Fully Proved (no sorry dependencies)

### Foundation
- Hexagonal lattice definition, adjacency, decidability, local finiteness
- Self-avoiding walk (SAW) definition, finiteness, counting
- Translation and flip automorphisms of the hex lattice
- SAW count is vertex-independent: `saw_count_vertex_independent`
- SAW counts: c₁ = 3, c₂ = 6
- Submultiplicativity: c_{n+m} ≤ c_n · c_m
- Fekete's lemma (submultiplicative sequences)
- Connective constant as limit of c_n^{1/n}
- Connective constant positivity (μ > 0)

### Elementary Bounds
- c_{n+1} ≤ 3·c_n (degree bound)
- c_{n+1} ≤ 2·c_n for n ≥ 1
- c_n ≤ 3·2^{n-1} (upper bound)
- μ ≥ 1, μ ≤ 2
- Zigzag walk construction: c_{2k} ≥ 2^k
- 2^n ≤ c_n²
- μ ≥ √2

### Algebraic Core (Lemma 1 of the paper)
- Constants: xc, λ, j, σ, c_α, c_ε with all basic properties
- Pair cancellation: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- Triplet cancellation: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- √(2+√2) = 2·cos(π/8)
- xc·c_alpha = (√2-1)/2
- Strip T=1 algebraic identity: 2xc²/(1-xc²)·(√2+1)/2 = 1

### Geometric Infrastructure
- Hex embedding into ℂ with unit edge length
- Direction vectors sum to zero at each vertex
- Direction ratios: dir(F→T₂)/dir(F→T₁) = j, dir(F→T₃)/dir(F→T₁) = j²
- Boundary cosine positivity: cos(3θ/8) > 0 for |θ| ≤ π
- Right boundary direction = (1,0), starting direction = (-1,0)
- Interior cancellation: opposite direction factors cancel

### Width-1 Strip Infrastructure (NEW - SAWStripT1Exact.lean)
- **Path graph structure** (`strip1_at_most_2_neighbors`): each vertex in PaperInfStrip 1 has at most 2 strip-neighbors
- **Position function** (`strip1_pos`): assigns integer position to each strip vertex, with adjacent vertices differing by ±1
- **Position injectivity** (`strip1_pos_injective`): position uniquely determines the vertex
- **Constant sign** (`strip1_path_constant_sign`): consecutive position differences along a SAW are constant (all +1 or all -1)
- **Monotonicity** (`strip1_saw_monotone`): position is strictly monotone along any SAW in the strip
- **Right bridge existence** (`exists_right_bridge`): for each m≥0, a PaperBridge 1 of length 2m+1 ending at (m,-m-1,false)
- **Left bridge existence** (`exists_left_bridge`): for each m≥0, a PaperBridge 1 of length 2m+1 ending at (-m-1,m,false)
- **Partition function lower bound** (`paper_bridge_partition_1_ge`): paper_bridge_partition 1 xc ≥ 2xc/(1-xc²)

### Bipartiteness and Walk Structure
- Walk bipartiteness: walks from TRUE to FALSE have odd length
- PaperBridge 1 has odd length
- Strip-1 TRUE/FALSE vertex neighbor characterization
- paperStart has exactly 2 strip-1 neighbors
- Two explicit width-1 bridges constructed
- Length-1 bridge classification

### Strip Domain Infrastructure
- Paper-compatible strip domains (PaperInfStrip, PaperFinStrip)
- Partition functions A_paper, B_paper, E_paper
- Paper bridges (PaperBridge) and partition function
- Bridge length ≥ width, bridge fits in finite strip
- PaperSAW_B injection into NegDiagOriginBridge
- Bridge partial sum ≤ 1/xc (modulo strip identity)
- Paper bridge decay: B_T^x ≤ (x/xc)^T / xc

### Abstract Proof Chain (fully proved modulo the two gaps)
- Strip identity → B_paper ≤ 1
- Cutting argument: A_{T+1} - A_T ≤ xc · B_{T+1}²
- Bridge recurrence from strip identity + cutting
- Quadratic recurrence lower bound: B_T ≥ min(B₁, 1/α) / T
- Bridge lower bound: ∃ c > 0, B_T ≥ c/T
- Z(xc) diverges from bridge lower bound + harmonic divergence
- Bridge-to-SAW injection: B_T ≤ Z(x) for each T
- Product convergence: ∏(1+r^T) converges for r < 1
- HW partial sum bound → summability of Z(x) for x < xc
- Main theorem assembly: μ = √(2+√2)

## Fundamental Gap 1: Strip Identity (Parafermionic Observable)

**Location:** `strip_identity_genuine` in `SAWStripIdentityCorrect.lean`
and `infinite_strip_identity` in `SAWRecurrenceProof.lean`

**What remains:**
- Bridge uniqueness for T=1 (`paper_bridge_1_unique_by_endpoint`): proving that on the path graph, SAWs from a fixed start to a fixed end are unique. The monotonicity infrastructure is proved but the final uniqueness step needs induction on walk structure.
- Endpoint classification for T=1 bridges
- Upper bound on T=1 bridge partition function  
- General T: walk partition into pairs/triplets at each vertex, discrete Stokes summation, boundary evaluation

## Fundamental Gap 2: Hammersley-Welsh Bridge Decomposition

**Location:** `paper_bridge_decomp_injection` in `SAWPaperChain.lean`

**What remains:**
- Half-plane walk decomposition algorithm (by induction on width)
- General SAW splitting at first min-diagCoord vertex
- Injectivity of the decomposition
- Weight accounting

## Files Overview

| File | Status | Description |
|------|--------|-------------|
| SAW.lean | ✅ Proved | Core definitions, constants, algebraic identities |
| SAWSubmult.lean | ✅ Proved | Submultiplicativity |
| SAWMain.lean | ✅ Proved | Fekete → connective constant |
| SAWStripT1Exact.lean | ⚠️ 4 sorries | T=1 strip exact partition functions (NEW) |
| SAWStripT1Walks.lean | ✅ Proved | T=1 walk characterization |
| SAWStripT1Identity.lean | ⚠️ Depends on T1Exact | T=1 identity from walk enumeration |
| SAWStripIdentityCorrect.lean | ❌ Sorry | Strip identity (fundamental gap) |
| SAWRecurrenceProof.lean | ❌ Sorry | Infinite strip identity (fundamental gap) |
| SAWPaperChain.lean | ❌ Sorry | HW decomposition (fundamental gap) |
| SAWFinal.lean | ✅ Proved | Main theorem assembly |
| SAWCuttingProof.lean | ✅ Proved | Cutting argument |
| SAWDecomp.lean | ✅ Proved | Quadratic recurrence |
| SAWStripT1.lean | ✅ Proved | T=1 algebraic identity |
