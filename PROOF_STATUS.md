# Proof Status: The Connective Constant of the Honeycomb Lattice

## Main Theorem

**Statement**: The connective constant of the hexagonal lattice equals √(2+√2).

**File**: `RequestProject/SAWFinal.lean` — `connective_constant_eq`

**Status**: Proved modulo two independent sorry'd lemmas.

## Two Remaining Sorry'd Lemmas

### 1. Infinite Strip Identity
**File**: `SAWRecurrenceProof.lean` (`infinite_strip_identity`)

**Statement**: `1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc`

**Used for**: Bridge recurrence → lower bound μ ≥ √(2+√2);
also implies B_paper ≤ 1 (via SAWParafermionicProof.lean).

**Proof method**: Parafermionic observable vertex relation (Lemma 1 of
Duminil-Copin & Smirnov 2012) summed over the strip (discrete Stokes).

**Infrastructure proved**:
- Pair cancellation (`pair_cancellation`): j·conj(λ)⁴ + conj(j)·λ⁴ = 0 ✓
- Triplet cancellation (`triplet_cancellation`): 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0 ✓
- **Triplet winding property** (`triplet_winding_property`): fullWinding of extended walk = fullWinding + hexTurn ✓ (NEW)
- **Full winding factoring** (`fullWinding_cons_cons`): winding factors through first edge ✓ (NEW)
- **Walk winding factoring** (`walkWindingInt_cons_cons`): walkWindingInt = hexTurn + tail winding ✓ (NEW)
- Direction factors at hex vertices (all proved) ✓
- Hex turn values (all 18 lemmas proved) ✓
- `walkWindingInt` definition **fixed** (bug: previously used end-of-walk vertex instead of next vertex in hexTurn)

**Missing**: Combinatorial walk partition into pairs/triplets at each vertex,
and discrete Stokes summation.

### 2. Hammersley–Welsh Decomposition
**File**: `SAWPaperChain.lean`
**Name**: `paper_bridge_decomp_injection`

**Statement**: `∑ n ≤ N, c_n x^n ≤ 2 · (∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}(x))²`

**Used for**: Z(x) < ∞ for x < xc → upper bound μ ≤ √(2+√2)

**Infrastructure proved**:
- Walk max diagCoord (`maxDiagInWalk'_ge`, `maxDiagInWalk'_achieved`) ✓ (NEW)
- Walk width ≤ length (`walk_width_le_length'`) ✓ (NEW)
- Product-powerset identity (`prod_one_add_eq`) ✓ (NEW)
- Walk diagonal coordinate bounds (`walk_diagCoordZ_bound`) ✓
- Walk minimum/maximum diagCoord (`walkMinDiagCoord_le`, `walkMaxDiagCoord_ge`) ✓
- Walk min/max achievement (`walkMinDiagCoord_achieved`, `walkMaxDiagCoord_achieved`) ✓
- Walk splitting at vertex (`walk_split_at_vertex`) ✓
- Translation of walks (`hexShift`, `shiftWalk`, `shiftWalk_isPath`) ✓
- Bridge-to-origin translation (`bridgeToOriginBridge_false`) ✓

**Missing**: Half-plane walk decomposition algorithm and injectivity proof.

## Fully Proved Results

### Foundations
- **Hexagonal lattice** (`hexGraph`): vertex type, adjacency, decidability
- **Self-avoiding walks** (`SAW`): definition, finiteness, counting
- **SAW count** (`saw_count`): independence from starting vertex
- **Submultiplicativity** (`saw_count_submult'`): c_{n+m} ≤ c_n · c_m
- **Fekete's lemma** (`fekete_submultiplicative`): limit exists
- **Connective constant** (`connective_constant`): definition as infimum
- **Connective constant is limit** (`connective_constant_is_limit'`)
- **Connective constant is positive** (`connective_constant_pos'`)
- **Elementary upper bound** (`saw_count_upper_bound`): c_n ≤ 3 · 2^{n-1}

### Algebraic Identities (Lemma 1 core)
- **Pair cancellation** (`pair_cancellation`): j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- **Triplet cancellation** (`triplet_cancellation`): 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- **xc inverse** (`xc_inv`): xc⁻¹ = √(2+√2)
- **Boundary coefficients** (`c_alpha_pos`, `c_eps_pos`)

### Winding Infrastructure (NEW — Lemma 1 support)
- **walkWindingInt definition** (FIXED): correctly computes sum of hexTurns at interior vertices
- **walkWindingInt_cons_cons**: winding factors through first edge (definitional)
- **walkLastDir_cons_cons**: walkLastDir factors through first edge (definitional)
- **fullWinding_cons_cons**: full winding factors through first edge
- **triplet_winding_property**: extending a walk by one step adds a constant hexTurn
- **walkLastDir_isSome**: walks of length ≥ 1 have defined last direction
- **hexEdgeDir_adj_isSome**: adjacent vertices have defined edge direction

### Walk Width Infrastructure (NEW)
- **maxDiagInWalk'**: maximum diagCoord in walk support
- **maxDiagInWalk'_ge**: bound on all vertices
- **maxDiagInWalk'_achieved**: max is achieved
- **walk_width_le_length'**: max - min ≤ length

### Cutting Argument (Section 3)
- **Cutting argument** (`cutting_argument_proved`): A_{T+1} − A_T ≤ xc · B_{T+1}²

### Bridge Recurrence and Lower Bound
- **Bridge recurrence** (`bridge_recurrence_proved`): B(T) ≤ c_α · B(T+1)² + B(T+1)
- **Bridge lower bound** (`paper_bridge_lower_bound`): ∃ c > 0, c/T ≤ B(T)

### Main Theorem Assembly
- **Z(xc) diverges** (`Z_xc_diverges_corrected`)
- **Z(x) converges for x < xc** (`hw_summable_corrected`)
- **Bridge decay** (`paper_bridge_decay`): B_T(x) ≤ (x/xc)^T / xc
- **Connective constant** (`connective_constant_eq_corrected`): μ = √(2+√2)

## New Files Created This Session

| File | Role | Sorry? |
|------|------|--------|
| SAWHWDecompose.lean | Walk max diagCoord, width bound, product identity | **No** |
