# Proof Status: The Connective Constant of the Honeycomb Lattice

## Main Theorem

**Statement**: The connective constant of the hexagonal lattice equals √(2+√2).

**File**: `RequestProject/SAWFinal.lean` — `connective_constant_eq`

**Status**: Proved modulo two independent sorry'd lemmas.

## Two Remaining Sorry'd Lemmas

### 1. Infinite Strip Identity / Finite Strip Identity
**Files**: `SAWRecurrenceProof.lean` (`infinite_strip_identity`) and
`SAWStripIdentityCorrect.lean` (`strip_identity_genuine`)

**Statement**: `1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc`
(infinite strip) or equivalently `∃ A_m E_m ≥ 0, 1 = c_α A_m + B_paper + c_ε E_m`
(finite strip)

**Used for**: Bridge recurrence → lower bound μ ≥ √(2+√2);
also B_paper ≤ 1 → bridge upper bound → bridge decay

**Proof method**: Parafermionic observable vertex relation (Lemma 1 of
Duminil-Copin & Smirnov 2012) summed over the strip (discrete Stokes).
Algebraic core (pair_cancellation, triplet_cancellation) is proved.
Missing: combinatorial walk partition and boundary evaluation.

**New reduction** (`SAWStripProof.lean`): `strip_identity_of_B_le_one` shows
the strip identity follows from B_paper ≤ 1.

### 2. Hammersley–Welsh Decomposition
**File**: `SAWPaperChain.lean`
**Name**: `paper_bridge_decomp_injection`

**Statement**: `∑ n ≤ N, c_n x^n ≤ 2 · (∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}(x))²`

**Used for**: Z(x) < ∞ for x < xc → upper bound μ ≤ √(2+√2)

**Proof method**: Bridge decomposition algorithm (each SAW → two half-plane
walks → bridge sequences with strictly decreasing widths).

**Infrastructure proved**:
- Walk diagonal coordinate bounds (`walk_diagCoordZ_bound`)
- Walk minimum/maximum diagCoord (`walkMinDiagCoord_le`, `walkMaxDiagCoord_ge`)
- Walk min/max achievement (`walkMinDiagCoord_achieved`, `walkMaxDiagCoord_achieved`)
- Walk width ≤ walk length (`walkWidth_le_length`)
- Walk has min/max vertex (`walk_has_min_vertex`, `walk_has_max_vertex`)
- Walk splitting preserves length (`walk_split_total_length`)
- PaperFinStrip monotonicity in L (`PaperFinStrip_mono_L`)
- Bridge weight bounds (`pow_le_prod_pow`)
- Walk splitting at vertex (`walk_split_at_vertex`)
- Translation of walks (`hexShift`, `shiftWalk`, `shiftWalk_isPath`)
- Bridge-to-origin translation (`bridgeToOriginBridge_false`)

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
- **c_α · xc identity** (`c_alpha_mul_xc`)
- **Boundary cosine positivity** (`boundary_cos_pos`)

### Walk Width Infrastructure (NEW)
- **Walk max diagCoord** (`walkMaxDiagCoord_ge`, `walkMaxDiagCoord_achieved`)
- **Walk width** (`walkWidth`, `walkWidth_nonneg`, `walkWidth_le_length`)
- **Walk min/max vertex existence** (`walk_has_min_vertex`, `walk_has_max_vertex`)
- **Walk splitting** (`walk_split_total_length`, `takeUntil_min_le`, `dropUntil_min_le'`)
- **PaperFinStrip L-monotonicity** (`PaperFinStrip_mono_L`)

### Bridge Infrastructure
- **Paper bridge** (`PaperBridge`): definition, length bound, finiteness
- **Bridge partition function** (`paper_bridge_partition`): definition, summability
- **Bridge-to-SAW injection** (`paperBridge_toSAW_sigma_injective`)
- **Bridge positivity** (`paper_bridge_partition_one_pos`)

### Strip Identity Consequences
- **PaperSAW_B → PaperBridge injection** (`PaperSAW_B_to_PaperBridge_injective'`)
- **B_paper ≤ xc · bridge partition** (`B_paper_le_xc_bridge'`)
- **Strip identity from infinite** (`strip_identity_from_infinite'`)
- **B_paper ≤ 1 from infinite** (`B_paper_le_one_from_infinite'`)
- **B ≤ 1 implies strip identity** (`strip_identity_of_B_le_one`) (NEW)

### Cutting Argument (Section 3)
- **Strip monotonicity** (`PaperInfStrip_mono`)
- **Walk widening** (`PaperSAW_A_inf_widen`, injective)
- **Boundary detection** (`A_inf_diff_reaches_boundary`)
- **Prefix/suffix bridge extraction** (`prefix_gives_bridge`, `suffix_reversed_shifted_gives_bridge`)
- **Cutting argument** (`cutting_argument_proved`): A_{T+1} − A_T ≤ xc · B_{T+1}²

### Bridge Recurrence and Lower Bound
- **Bridge recurrence** (`bridge_recurrence_proved`): B(T) ≤ c_α · B(T+1)² + B(T+1)
- **Quadratic recurrence lower bound** (`quadratic_recurrence_lower_bound`)
- **Bridge lower bound** (`paper_bridge_lower_bound`): ∃ c > 0, c/T ≤ B(T)

### Main Theorem Assembly
- **Z(xc) diverges** (`Z_xc_diverges_corrected`)
- **Z(x) converges for x < xc** (`hw_summable_corrected`)
- **Bridge decay** (`paper_bridge_decay`): B_T(x) ≤ (x/xc)^T / xc
- **Connective constant** (`connective_constant_eq_corrected`): μ = √(2+√2)
- **μ ≤ 2** (`connective_constant_le_two'`)
- **Divergence above xc** (`partition_function_diverges_above_xc'`)
- **Convergence below xc** (`partition_function_converges_below_xc'`)

## File Map

| File | Role | Sorry? |
|------|------|--------|
| SAW.lean | Core definitions, constants, algebraic identities | No |
| SAWSubmult.lean | Submultiplicativity c_{n+m} ≤ c_n·c_m | No |
| SAWMain.lean | Fekete → connective constant | No |
| SAWBridgeFix.lean | Corrected bridge partition | No |
| SAWStripIdentityCorrect.lean | Strip identity, B_paper ≤ 1 | **Sorry #1** |
| SAWDiagProof.lean | Bridge partial sum bounds | Depends on #1 |
| SAWCuttingProof.lean | Cutting argument proved | No |
| SAWRecurrenceProof.lean | Bridge recurrence from strip identity | **Sorry #1** |
| SAWDecomp.lean | Quadratic recurrence lower bound | No |
| SAWPaperChain.lean | Main theorem assembly | **Sorry #2** |
| SAWParafermionicProof.lean | Finite from infinite strip identity | No |
| SAWStripProof.lean | B ≤ 1 implies strip identity | No (NEW) |
| SAWHWDecompProof.lean | Walk max diagCoord infrastructure | No (NEW) |
| SAWObservableVertex.lean | Walk width, splitting infrastructure | No (NEW) |
| SAWInfStripFromFinite.lean | Strip monotonicity in L | No (NEW) |
| SAWHWCore.lean | DiagCoord bounds, walk splitting | No |
| SAWHWAlgorithm.lean | Translation, bipartiteness, walk analysis | No |
| SAWFinal.lean | Final theorem | Depends on #1, #2 |
