# Proof Status: The Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq : connective_constant = Real.sqrt (2 + Real.sqrt 2)`

**Status**: Compiles with 2 independent sorry chains (3 sorry locations).

## Sorry Chain 1: Parafermionic Observable (Strip Identity)

**Locations**:
- `SAWStripIdentityCorrect.lean:361` (`strip_identity_genuine`)
- `SAWRecurrenceProof.lean:49` (`infinite_strip_identity`)

**What they prove**: For the finite strip S_{T,L} with T ≥ 1, L ≥ 1:
  B_paper(T, L, xc) ≤ 1  (strip_identity_genuine, existential form)
  1 = c_α · A_inf(T) + xc · B(T)  (infinite_strip_identity)

**Why they're needed**: The core bound from Lemma 2 of the paper.
The strip identity implies bridge partition function bounds, the bridge
recurrence, bridge lower bounds c/T, and ultimately Z(xc) = ∞.

**What's proved (sorry-free)**:
- Pair cancellation: `j * conj(λ)⁴ + conj(j) * λ⁴ = 0` ✓
- Triplet cancellation: `1 + xc * j * conj(λ) + xc * conj(j) * λ = 0` ✓
- Boundary coefficient positivity: `c_alpha > 0`, `c_eps > 0` ✓
- Direction vectors are cube roots of unity ✓
- Walk extension infrastructure (sawExtend, pathExtend) ✓
- Abstract discrete Stokes theorem (discrete_stokes_abstract) ✓
- Interior cancellation for mid-edges ✓
- Cutting argument: `A_inf(T+1) - A_inf(T) ≤ xc · B(T+1)²` ✓
- Bridge recurrence (from infinite_strip_identity) ✓
- Bridge lower bound: `∃ c > 0, c/T ≤ B(T)` (from recurrence) ✓
- Z(xc) diverges (from lower bound) ✓
- Walk diagonal coordinate bounds (walk_dc_bound) ✓
- SAW diagonal bounds (saw_dc_lower, saw_dc_upper) ✓

**What remains**:
- The combinatorial walk partition into pairs and triplets at each vertex
  (the "vertex relation" / Lemma 1 of the paper)
- Applying the abstract Stokes theorem to derive the boundary sum = 0
- Boundary contribution evaluation (winding computation)

## Sorry Chain 2: Hammersley-Welsh Decomposition

**Location**: `SAWPaperChain.lean:258` (`paper_bridge_decomp_injection`)

**What it proves**: For 0 < x < xc:
  ∑_{n≤N} c_n x^n ≤ 2 · (∏_{T=1}^N (1 + B_T(x)))²

**Why it's needed**: Combined with bridge decay B_T(x) ≤ (x/xc)^T
and geometric product convergence, this gives Z(x) < ∞ for x < xc.
This is essential for the upper bound μ ≤ 1/xc. The convergence
Z(x) < ∞ for x < 1/μ follows automatically from submultiplicativity,
but showing Z(x) < ∞ for x < xc (= 1/μ) requires the HW decomposition
to establish that xc IS the radius of convergence.

**What's proved (sorry-free)**:
- Subset-product identity: `∑_{S⊆range(N)} ∏_{T∈S} a_T = ∏(1+a_T)` ✓
- Bridge decay: `B_T(x) ≤ (x/xc)^T` for x < xc ✓
- Product convergence: `∏(1 + r^T)` converges for 0 ≤ r < 1 ✓
- Upper bound assembly from decay + product convergence ✓
- Z(x) summability from partial sum bound ✓
- Translation infrastructure: hexShift, shiftWalk, etc. ✓
- Diagonal coordinate bounds for walks ✓

**What remains**:
- The decomposition algorithm (splitting SAWs at maximal diagonal excursion)
- Extracting bridges by induction on width
- Injectivity of the decomposition (reverse procedure)

## Files

### Core definitions
- `SAW.lean`: Constants, algebraic identities, connective constant definition
- `SAWSubmult.lean`: Submultiplicativity c_{n+m} ≤ c_n · c_m

### Strip domain
- `SAWStripIdentityCorrect.lean`: Paper-compatible strip, B_paper definition, **sorry chain 1**
- `SAWDiagProof.lean`: PaperBridge, partition functions, bridge bounds
- `SAWCutting.lean`, `SAWCuttingProof.lean`: Cutting argument (proved)
- `SAWRecurrenceProof.lean`: Bridge recurrence, **sorry chain 1**

### Bridge decomposition
- `SAWPaperChain.lean`: Assembly of divergence + convergence, **sorry chain 2**
- `SAWDecomp.lean`: Abstract bridge decomposition bounds
- `SAWHammersleyWelsh.lean`: HW summability framework
- `SAWHWDecompAlgo.lean`: Walk diagonal bounds, strip monotonicity (proved)
- `SAWHWAlgorithm.lean`: Translation infrastructure (proved)
- `SAWBridgeDecompCore.lean`: Diagonal coordinate, product-powerset identity

### Observable infrastructure
- `SAWVertexCore.lean`: Walk extension (sawExtend, pathExtend)
- `SAWTripletInfra.lean`: Direction vectors, j-rotations
- `SAWVertexPartition.lean`: Pair/triplet residuals
- `SAWObservableProof.lean`: Observable definitions
- `SAWDiscreteStokesProof.lean`: Abstract Stokes theorem (proved)
- `SAWStokesSkeleton.lean`: Stokes proof skeleton

### Assembly
- `SAWMain.lean`: Fekete's lemma → connective constant
- `SAWBridge.lean`: Bridge definitions, partition function radius
- `SAWFinal.lean`: Main theorem assembly
