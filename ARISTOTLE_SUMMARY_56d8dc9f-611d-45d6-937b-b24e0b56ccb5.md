# Summary of changes
## Summary of work on Hammersley-Welsh formalization

### Key Discovery: Bridge Definition Mismatch

A critical issue was identified: the existing `Bridge` type in `SAWBridge.lean` uses **x-coordinate strips** (`v.1 ∈ [0, T]`), but the paper defines strips using the **diagonal coordinate** `x + y` (corresponding to the real part of the embedding). This mismatch is significant:

- The strip identity `B_T^{x_c} ≤ 1` holds only for **diagonal strips**, not column strips.
- For column strips, the bridge partition function can exceed 1 (numerical analysis suggests B₁^{xc} > 1.2 for T=1 column bridges).
- This means `origin_bridge_upper_bound` as currently stated may be mathematically **false** for the existing `Bridge` definition.

### New File: `RequestProject/SAWDiagBridge.lean`

Created a new file with corrected diagonal-strip bridge definitions:

- **`hexGraph_adj_sum_bound`**: Each hex step changes `x+y` by at most 1 (✓ proved).
- **`hexGraph_walk_sum_bound_pos/neg`**: Walk bounds for `x+y` coordinate (✓ proved).
- **`DiagBridge T`**: Diagonal bridge matching the paper (walk from `x+y=0` to `x+y=T`, staying in `0 ≤ x+y ≤ T`).
- **`DiagOriginBridge T`**: Diagonal bridge from `paperStart = (0,0,true)`.
- **`diag_bridge_partition T x`**: Partition function for diagonal origin bridges.
- **`diag_bridge_length_ge_width`**: Each diagonal bridge of width T has length ≥ T (✓ proved).
- **`saw_sum_le_length`**: SAW x+y coordinate bound (✓ proved).

### Blueprint Updates (`blueprint/src/content.tex`)

1. Added **Remark on coordinate system** (rem:coord_system) explaining the column vs diagonal strip issue.
2. Added **DiagBridge definition** (def:diag_bridge) and diagonal bridge partition function (def:diag_bridge_partition).
3. Added **diagonal bridge length theorem** (thm:diag_bridge_length), hex adjacency sum bound (lem:hex_sum_bound), and walk sum bound (lem:walk_sum_bound).
4. Updated the strip identity proof section with detailed status of what is proved vs. what remains.
5. Updated `blueprint/lean_decls` with new declarations.

### Current Sorry Status for Hammersley-Welsh

The two fundamental bottlenecks are:

1. **`strip_identity_exists`** (SAWStripIdentityCorrect.lean): The parafermionic observable identity. Requires formalizing the observable, discrete Stokes theorem, and boundary evaluation. The algebraic core (pair/triplet cancellation) and geometric core (boundary cosine positivity) are proved. What remains is the summation framework.

2. **`bridge_decomposition_injection_proof`** (SAWHWDecomp.lean): The Hammersley-Welsh bridge decomposition injection. Requires formalizing the half-plane walk decomposition algorithm, proving injectivity, and establishing the weight inequality. Infrastructure for walk splitting (takeUntil/dropUntil) and bridge translation (hexShift, bridgeToOriginBridge_false) is available.

All other HW sorry's cascade from these two. The project builds cleanly with 8062 jobs.