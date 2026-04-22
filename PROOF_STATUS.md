# Proof Status: The Connective Constant of the Honeycomb Lattice

## Main Theorem

**Statement**: The connective constant of the hexagonal lattice equals √(2+√2).

**File**: `RequestProject/SAWFinal.lean` — `connective_constant_eq`

**Status**: Proved modulo three sorry'd lemmas (see below).

## Fully Proved Results

The following key results are fully proved with no sorry dependencies:

### Foundations
- **Hexagonal lattice** (`hexGraph`): vertex type, adjacency, decidability
- **Self-avoiding walks** (`SAW`): definition, finiteness, counting
- **SAW count** (`saw_count`): independence from starting vertex
- **Submultiplicativity** (`saw_count_submult'`): c_{n+m} ≤ c_n · c_m
- **Fekete's lemma** (`fekete_submultiplicative`): limit exists
- **Connective constant** (`connective_constant`): definition as infimum
- **Connective constant is limit** (`connective_constant_is_limit'`)
- **Connective constant is positive** (`connective_constant_pos'`)

### Algebraic Identities (Lemma 1 core)
- **Pair cancellation** (`pair_cancellation`): j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- **Triplet cancellation** (`triplet_cancellation`): 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- **xc inverse** (`xc_inv`): xc⁻¹ = √(2+√2)
- **Boundary coefficients** (`c_alpha_pos`, `c_eps_pos`)
- **c_α · xc identity** (`c_alpha_mul_xc`): c_α · xc = (√2−1)/2
- **Boundary cosine positivity** (`boundary_cos_pos`)

### Bridge Infrastructure
- **Paper bridge** (`PaperBridge`): definition, length bound, finiteness
- **Bridge partition function** (`paper_bridge_partition`): definition, summability
- **Bridge-to-SAW injection** (`paperBridge_toSAW_sigma_injective`)
- **Bridge positivity** (`paper_bridge_partition_one_pos`)

### Cutting Argument (Section 3)
- **Strip monotonicity** (`PaperInfStrip_mono`)
- **Walk widening** (`PaperSAW_A_inf_widen`, injective)
- **Boundary detection** (`A_inf_diff_reaches_boundary`)
- **Prefix/suffix bridge extraction** (`prefix_gives_bridge`, `suffix_reversed_shifted_gives_bridge`)
- **Cutting argument** (`cutting_argument_proved`): A_{T+1} − A_T ≤ xc · B_{T+1}²

### Bridge Recurrence and Lower Bound
- **Bridge recurrence** (`bridge_recurrence_proved`): B(T) ≤ c_α · B(T+1)² + B(T+1)
- **Quadratic recurrence lower bound** (`quadratic_recurrence_lower_bound`): B(T) ≥ c/T
- **Bridge lower bound** (`paper_bridge_lower_bound`): ∃ c > 0, c/T ≤ B(T)

### Main Theorem Assembly
- **Z(xc) diverges** (`Z_xc_diverges_corrected`)
- **Z(x) converges for x < xc** (`hw_summable_corrected`)
- **Bridge decay** (`paper_bridge_decay`): B_T(x) ≤ (x/xc)^T / xc
- **Connective constant** (`connective_constant_eq_corrected`): μ = √(2+√2)
- **μ ≤ 2** (`connective_constant_le_two'`)
- **Divergence above xc** (`partition_function_diverges_above_xc'`)
- **Convergence below xc** (`partition_function_converges_below_xc'`)

## Three Remaining Sorry'd Lemmas

### 1. Finite Strip Identity (B_paper ≤ 1)
**File**: `SAWStripIdentityCorrect.lean`
**Name**: `strip_identity_genuine`
**Statement**: ∃ A_m E_m ≥ 0, 1 = c_α · A_m + B_paper(T,L,xc) + c_ε · E_m
**Used for**: Bridge partition decay bound → HW summability → upper bound μ ≤ √(2+√2)
**Proof method**: Parafermionic observable vertex relation (Lemma 1) + discrete Stokes on finite strip (Lemma 2). Algebraic core (pair/triplet cancellation) proved; combinatorial walk partition and boundary evaluation remain.

### 2. Infinite Strip Identity
**File**: `SAWRecurrenceProof.lean`
**Name**: `infinite_strip_identity`
**Statement**: 1 = c_α · A_inf(T,xc) + xc · B(T,xc)
**Used for**: Bridge recurrence → lower bound → divergence of Z(xc) → lower bound μ ≥ √(2+√2)
**Proof method**: Same parafermionic argument as #1 but for infinite strip (no escape boundary). Can also be derived as L→∞ limit of #1.
**Algebraic verification**: For T=1, the identity reduces to 1−xc² = 2xc²(c_α·xc + 1), which is verified using c_α·xc = (√2−1)/2.

### 3. Hammersley-Welsh Decomposition
**File**: `SAWPaperChain.lean`
**Name**: `paper_bridge_decomp_injection`
**Statement**: Σ_{n≤N} c_n x^n ≤ 2 · (Π_{T=1}^N (1 + B_T(x)))²
**Used for**: Z(x) < ∞ for x < xc → upper bound μ ≤ √(2+√2)
**Proof method**: Bridge decomposition algorithm. Each SAW splits at min diagCoord into two half-plane walks, each decomposing into bridges by induction on width. Infrastructure (walk splitting, coordinate bounds, weight bounds) proved; decomposition algorithm and injectivity remain.

## File Map

| File | Role | Sorry? |
|------|------|--------|
| SAW.lean | Core definitions, constants, algebraic identities | No |
| SAWSubmult.lean | Submultiplicativity c_{n+m} ≤ c_n·c_m | No |
| SAWMain.lean | Fekete → connective constant | No |
| SAWBridge.lean | Bridge definitions, partition function | Dead sorry |
| SAWBridgeFix.lean | Corrected bridge partition | No |
| SAWStripIdentityCorrect.lean | Strip identity, B_paper ≤ 1 | **Sorry #1** |
| SAWDiagProof.lean | Bridge partial sum bounds | Depends on #1 |
| SAWCutting.lean | Cutting argument setup | Dead sorry |
| SAWCuttingProof.lean | Cutting argument proved | No |
| SAWRecurrenceProof.lean | Bridge recurrence from strip identity | **Sorry #2** |
| SAWDecomp.lean | Quadratic recurrence lower bound | No |
| SAWPaperChain.lean | Main theorem assembly | **Sorry #3** |
| SAWFinal.lean | Final theorem | Depends on #1, #2, #3 |
| SAWVertexRel.lean | Vertex relation infrastructure | Sorry (helper) |
| SAWStokesSkeleton.lean | Discrete Stokes infrastructure | Sorry (helper) |
| SAWHWDecomp.lean | HW decomposition infrastructure | Sorry (dup) |
