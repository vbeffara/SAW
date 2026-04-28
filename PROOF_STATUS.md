# Proof Status: The Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq : connective_constant = Real.sqrt (2 + Real.sqrt 2)`

**Status**: Compiles with 2 independent sorry chains. The main theorem depends on `sorryAx`.

## Sorry Chain 1: Parafermionic Observable (Strip Identity)

**Location**: `SAWStripIdentityCorrect.lean:361` (`strip_identity_genuine`)
and `SAWRecurrenceProof.lean:49` (`infinite_strip_identity`)

**What it proves**: For the finite strip S_{T,L} with T ≥ 1, L ≥ 1:
  B_paper(T, L, xc) ≤ 1

**Why it's needed**: This is the core bound from Lemma 2 of the paper.
It implies bridge partition function bounds, the bridge recurrence,
bridge lower bounds c/T, and ultimately Z(xc) = ∞ (divergence at
the critical point).

**What's proved (sorry-free)**:
- Pair cancellation: `j * conj(λ)⁴ + conj(j) * λ⁴ = 0` ✓
- Triplet cancellation: `1 + xc * j * conj(λ) + xc * conj(j) * λ = 0` ✓
- Boundary coefficient positivity: `c_alpha > 0`, `c_eps > 0` ✓
- Direction vectors are cube roots of unity ✓
- Walk extension infrastructure (sawExtend, pathExtend) ✓
- Cutting argument: `A_inf(T+1) - A_inf(T) ≤ xc · B(T+1)²` ✓
- Bridge recurrence (from infinite_strip_identity) ✓
- Bridge lower bound: `∃ c > 0, c/T ≤ B(T)` (from recurrence) ✓
- Z(xc) diverges (from lower bound) ✓

**What remains**:
- The combinatorial walk partition into pairs and triplets at each vertex
- The discrete Stokes summation (summing vertex relations over all strip vertices)
- Boundary contribution evaluation

## Sorry Chain 2: Hammersley-Welsh Decomposition

**Location**: `SAWPaperChain.lean:258` (`paper_bridge_decomp_injection`)

**What it proves**: For 0 < x < xc:
  ∑_{n≤N} c_n x^n ≤ 2 · (∏_{T=1}^N (1 + B_T(x)))²

**Why it's needed**: Combined with bridge decay B_T(x) ≤ (x/xc)^T
and geometric product convergence, this gives Z(x) < ∞ for x < xc.

**What's proved (sorry-free)**:
- Subset-product identity: `∑_{S⊆range(N)} ∏_{T∈S} a_T = ∏(1+a_T)` ✓
- Bridge decay: `B_T(x) ≤ (x/xc)^T` for x < xc ✓
- Product convergence: `∏(1 + r^T)` converges for 0 ≤ r < 1 ✓
- Upper bound assembly from decay + product convergence ✓
- Z(x) summability from partial sum bound ✓

**What remains**:
- The decomposition algorithm (splitting SAWs at maximal diagonal excursion)
- Extracting bridges by induction on width
- Injectivity of the decomposition (reverse procedure)

## Other Sorries (not on critical path)

- `SAWZigzag.lean`: `saw_count_even_lower`, `saw_count_odd_lower` —
  proved in `SAWZigzagBuild.lean` but can't be imported due to
  circular dependency. These are used for lower bounds on c_n.
- `SAWBridge.lean:357`: dead code, superseded by `SAWPaperChain`
- `SAWFiniteStrip.lean`: old strip infrastructure, superseded
- Various other files with legacy sorry's not on the critical path

## Files

### Core definitions
- `SAW.lean`: Constants, algebraic identities, connective constant definition
- `SAWSubmult.lean`: Submultiplicativity c_{n+m} ≤ c_n · c_m

### Strip domain
- `SAWStripIdentityCorrect.lean`: Paper-compatible strip, B_paper definition, **sorry chain 1**
- `SAWDiagProof.lean`: PaperBridge, partition functions, bridge bounds
- `SAWCutting.lean`, `SAWCuttingProof.lean`: Cutting argument (proved)
- `SAWRecurrenceProof.lean`: Bridge recurrence, **sorry chain 2**

### Bridge decomposition
- `SAWPaperChain.lean`: Assembly of divergence + convergence, **sorry chain 2**
- `SAWDecomp.lean`: Abstract bridge decomposition bounds
- `SAWHammersleyWelsh.lean`: HW summability framework

### Infrastructure
- `SAWVertexCore.lean`: Walk extension (sawExtend, pathExtend)
- `SAWTripletInfra.lean`: Direction vectors, j-rotations
- `SAWParafermionic.lean`: Walk reconstruction

### Assembly
- `SAWMain.lean`: Fekete's lemma → connective constant
- `SAWBridge.lean`: Bridge definitions, partition function radius
- `SAWFinal.lean`: Main theorem assembly
