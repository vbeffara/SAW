# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq : connective_constant = Real.sqrt (2 + Real.sqrt 2)`

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
- Zigzag walk construction: c_{2k} ≥ 2^k (`saw_count_even_lower_proved`)
- 2^n ≤ c_n² (`saw_count_sq_ge_two_pow_proved`)
- μ ≥ √2 (`connective_constant_ge_sqrt_two`)

### Algebraic Core (Lemma 1 of the paper)
- Constants: xc, λ, j, σ, c_α, c_ε with all basic properties
- Pair cancellation: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- Triplet cancellation: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- √(2+√2) = 2·cos(π/8)
- xc·c_alpha = (√2-1)/2 (NEW)
- Strip T=1 algebraic identity: 2xc²/(1-xc²)·(√2+1)/2 = 1 (NEW)

### Geometric Infrastructure
- Hex embedding into ℂ with unit edge length
- Direction vectors sum to zero at each vertex
- Direction ratios: dir(F→T₂)/dir(F→T₁) = j, dir(F→T₃)/dir(F→T₁) = j² (NEW)
- Boundary cosine positivity: cos(3θ/8) > 0 for |θ| ≤ π
- Right boundary direction = (1,0), starting direction = (-1,0)
- Interior cancellation: opposite direction factors cancel

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
- Cutting argument: A_{T+1} - A_T ≤ xc · B_{T+1}² (SAWCuttingProof)
- Bridge recurrence from strip identity + cutting
- Quadratic recurrence lower bound: B_T ≥ min(B₁, 1/α) / T
- Bridge lower bound: ∃ c > 0, B_T ≥ c/T
- Z(xc) diverges from bridge lower bound + harmonic divergence
- Bridge-to-SAW injection: B_T ≤ Z(x) for each T
- Product convergence: ∏(1+r^T) converges for r < 1
- HW partial sum bound → summability of Z(x) for x < xc
- Main theorem assembly: μ = √(2+√2)

### SAW diagCoord Bounds (NEW)
- saw_maxDiag_le': diagCoord(u) ≤ n for SAW of length n
- saw_minDiag_ge': -n ≤ diagCoord(u) for SAW of length n
- saw_diagCoord_abs_le: |diagCoord(u)| ≤ n

## Fundamental Gap 1: Strip Identity (Parafermionic Observable)

**Location:** `strip_identity_genuine` in `SAWStripIdentityCorrect.lean`
and `infinite_strip_identity` in `SAWRecurrenceProof.lean`

**Statement:** For the finite strip S_{T,L}:
∃ A_m E_m ≥ 0, 1 = c_α · A_m + B_paper(T,L,xc) + c_ε · E_m

**What is proved:**
- All algebraic identities (pair/triplet cancellation)
- Direction vector relationships (ratios = j, j²)
- Boundary cosine positivity
- Interior cancellation
- The T=1 algebraic identity (verifying the formula at the algebraic level)

**What remains:**
- Combinatorial walk partition into pairs/triplets at each vertex
- Discrete Stokes summation (formal telescoping)
- Boundary winding evaluation
- Assembly of the strip identity from the boundary sum

## Fundamental Gap 2: Hammersley-Welsh Bridge Decomposition

**Location:** `paper_bridge_decomp_injection` in `SAWPaperChain.lean`

**Statement:**
∑_{n≤N} c_n x^n ≤ 2 · (∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}^x)²

**What is proved:**
- Powerset product identity
- Bridge decay bounds
- Walk diagCoord bounds
- Walk splitting infrastructure (takeUntil, dropUntil)

**What remains:**
- Half-plane walk decomposition algorithm (by induction on width)
- General SAW splitting at first min-diagCoord vertex
- Injectivity of the decomposition
- Weight accounting (walk length ≥ sum of bridge lengths)

## Dead/Superseded Sorries (16 total, not on critical path)

These are in files from the old "column bridge" chain or have been
proved in alternative files:
- SAWZigzag.lean (2): proved in SAWZigzagBuild.lean
- SAWCutting.lean (1): proved in SAWCuttingProof.lean  
- SAWHammersleyWelsh.lean (2): superseded by SAWPaperChain.lean
- SAWHWDecomp.lean, SAWHWInject.lean, etc. (8): old column bridge chain
- SAWStokesSkeleton.lean, SAWStripIdentity.lean, SAWFiniteStrip.lean (3): old strip infrastructure
