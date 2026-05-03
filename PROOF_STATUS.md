# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem

`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
The connective constant μ of the hexagonal lattice equals √(2+√2).

**Status: depends on 3 sorry'd lemmas (2 independent chains).**

## Root Sorry Dependencies

### 1. `strip_identity_genuine` (SAWStripIdentityCorrect.lean:361)

**Statement:** For the finite strip S_{T,L} with T ≥ 1 and L ≥ 1:
∃ A_m E_m ≥ 0, 1 = c_α · A_m + B_paper(T,L,xc) + c_ε · E_m

**Equivalent to:** B_paper(T,L,xc) ≤ 1

**What it requires mathematically:**
The parafermionic observable argument (Lemma 2 of the paper):
1. Define F(z) at each mid-edge z of S_{T,L}
2. Vertex relation at each interior vertex (uses pair_cancellation, triplet_cancellation — PROVED)
3. Discrete Stokes summation (interior mid-edges cancel — direction antisymmetry PROVED)
4. Boundary evaluation (direction factors, phase computations — ALL PROVED)

**Proved algebraic/computational ingredients:**
- pair_cancellation ✓
- triplet_cancellation ✓
- interior_edge_cancel' ✓ (discrete Stokes key property)
- right_boundary_dir ✓ (+1)
- left_boundary_dir ✓ (-1)
- starting_dir' ✓ (-1)
- left_boundary_phase_re ✓ (-c_alpha)
- right_boundary_phase_re ✓ (1)
- boundary_cos_pos ✓
- boundary_weight_re_nonneg ✓

**Remaining gap:** The COMBINATORIAL walk partitioning (pairing/tripling walks at each vertex)
and the discrete Stokes SUMMATION framework (iterating interior cancellation over all vertices).

### 2. `infinite_strip_identity` (SAWRecurrenceProof.lean:49)

**Statement:** 1 = c_α · A_inf(T,xc) + xc · paper_bridge_partition(T,xc)

**Note:** This follows from strip_identity_genuine by taking L → ∞
(see SAWParafermionicProof.lean: strip_identity_from_infinite').
Monotonicity B_paper(T,L) ↑ in L is now PROVED (B_paper_mono_L ✓).

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean:258)

**Statement:** ∑_{n≤N} c_n x^n ≤ 2 · (∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}(x))²

**What it requires (Hammersley-Welsh decomposition):**
1. Split any SAW at the first vertex of minimum diagCoord
2. Each half is a half-plane walk
3. Half-plane walks decompose into bridges (induction on width)
4. The decomposition is at most 2-to-1
5. Walk length ≥ sum of bridge lengths

**Proved infrastructure:**
- walk_max_dc, walk_min_dc infrastructure ✓
- walk_width_le_length ✓
- bridge_product_expansion (= Finset.sum_powerset_prod_eq_prod_add_one) ✓

## Proved Infrastructure (sorry-free)

### NEW: Walk splitting and monotonicity (SAWWalkSplit.lean) ✓
- `walk_split_lengths'`: walk length = prefix length + suffix length ✓
- `PaperFinStrip_mono_L`: strip monotone in L ✓
- `PaperSAW_B_widen`: injection from narrow to wide strip ✓
- `PaperSAW_B_widen_injective`: the injection is injective ✓
- `B_paper_mono_L`: B_paper monotone increasing in L ✓

### NEW: Vertex relation infrastructure (SAWVertexRelation.lean) ✓
- `hexDir_antisymm'`: direction vectors antisymmetric ✓
- `interior_edge_cancel'`: interior edge contributions cancel ✓
- `right_boundary_dir`: right boundary direction = +1 ✓
- `left_boundary_dir`: left boundary direction = -1 ✓
- `starting_dir'`: starting direction = -1 ✓
- `left_boundary_phase_re`: left boundary phase Re = -c_alpha ✓
- `right_boundary_phase_re`: right boundary phase Re = 1 ✓
- `cos_sigma_pi'`: cos(σπ) = -c_alpha ✓

### NEW: HW proof infrastructure (SAWHWProofNew.lean) ✓
- `HalfPlaneSAW`: definition of half-plane SAW ✓
- `HalfPlaneSAW.width`: width of half-plane SAW ✓
- `HalfPlaneSAW.width_zero_iff`: width 0 iff all at same level ✓
- `bridge_product_expansion`: powerset product identity ✓

### Bridge decomposition infrastructure (SAWBridgeDecompNew.lean) ✓
- `walk_max_dc`: maximum diagCoord over walk support ✓
- `le_walk_max_dc`: max diagCoord ≥ any vertex's diagCoord ✓
- `walk_max_dc_achieved`: max diagCoord is achieved by some vertex ✓
- `walk_max_dc_le_start_add_length`: max diagCoord ≤ start + length ✓
- `Finset.sum_powerset_prod_eq_prod_add_one`: powerset product identity ✓

### Finite-to-infinite strip connection (SAWFiniteToInfinite.lean) ✓
- `paperSAWB_to_bridge`: map from PaperSAW_B to PaperBridge ✓
- `paperSAWB_to_bridge_injective`: the map is injective ✓
- `B_paper_le_xc_mul_bridge`: B_paper ≤ xc · bridge_partition ✓

### Core algebraic identities (SAW.lean) ✓
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0 ✓
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0 ✓
- `c_alpha_pos`, `c_eps_pos`, `xc_pos`, `xc_lt_one'` ✓
- `bridge_bound_of_strip_identity` ✓
- `quadratic_recurrence_lower_bound` ✓

### Cutting argument (SAWCuttingProof.lean) ✓
- `cutting_argument_proved`: A_{T+1} - A_T ≤ xc · B_{T+1}² ✓

### Bridge infrastructure (SAWDiagProof.lean)
- `PaperBridge` structure, `paper_bridge_partition` ✓
- `paper_bridge_length_ge`: bridge length ≥ T ✓
- `paper_bridge_partial_sum_le`: partial sums ≤ 1/xc (depends on strip_identity_genuine)
- `paper_bridge_upper_bound`: B(T,xc) ≤ 1/xc (depends on strip_identity_genuine)

### Walk analysis (SAWHWDecompHelper.lean) ✓
- `walk_min_dc_le`, `walk_min_dc_achieved` ✓
- `walk_width_le_length` ✓
- `suffix_dc_bound` ✓

### Submultiplicativity and Fekete (SAWSubmult.lean, SAW.lean) ✓
- `saw_count_submult'`: c_{m+n} ≤ c_m · c_n ✓
- `fekete_submultiplicative`: lim c_n^{1/n} exists ✓
- `connective_constant_eq_from_bounds`: μ = √(2+√2) from Z bounds ✓

### Walk counting (SAWZigzagBuild.lean) ✓
- `saw_count_pos`: c_n ≥ 1 for all n ✓
- `saw_count_vertex_independent` ✓

### Algebraic bounds (SAWStripT1L1.lean) ✓
- `three_xc_sq_lt_one` ✓
- `two_xc_sq_lt_one` ✓
