# Summary of changes
## Summary of Progress on Hammersley-Welsh Formalization

### New Theorems Proved (sorry-free)

**In `RequestProject/SAWHWBridge.lean`** (all 3 new, all sorry-free):

1. **`bridge_sigma_injective`**: The combined injection from `(T : ℕ) × OriginBridge T` to `(n : ℕ) × SAW hexOrigin n` (via `bridgeToSAW`) is injective. Key insight: bridges of different widths end at different x-coordinates, so they give distinct SAWs.

2. **`combined_bridge_finite_sum_le_Z`**: For any finite collection of bridges from different widths 1, ..., N, their total weight is bounded by Z(x) = Σ c_n x^n. Uses `bridge_sigma_injective`.

3. **`bridge_sum_le_Z`**: For finitely many widths, Σ_T B_{T+1}^x ≤ Z(x). This is the key disjoint bridge injection lemma needed for the lower bound argument. Proved from `combined_bridge_finite_sum_le_Z`.

**In `RequestProject/SAWStripIdentity.lean`** (rewritten, sorry-free):

4. **`Z_xc_diverges_from_lower_bound`**: If `origin_bridge_lower_bound` holds (∃ c > 0 s.t. B_T ≥ c/T), then Z(x_c) = ∞. Proved by contradiction: assuming Z(x_c) converges, `bridge_sum_le_Z` gives Σ B_{T+1} ≤ Z(x_c) < ∞, but B_{T+1} ≥ c/(T+1) contradicts harmonic series divergence.

### Import Chain Improvements

- **`SAWFinal.lean`** now uses `Z_xc_diverges_from_lower_bound` (proved) instead of `Z_xc_diverges` (sorry'd in SAWBridgeFix.lean) for the lower bound of the main theorem. Added import of `SAWStripIdentity`.

- **`SAWStripIdentity.lean`** was refactored to remove duplicate declarations (`bridgeToSAW`, `bridgeToSAW_injective`, `bridge_filter_card_le`, `origin_bridge_partition_le_Z`) that clashed with `SAWHWBridge.lean`. Now imports `SAWHWBridge` directly.

### Blueprint Updates (`blueprint/src/content.tex`)

- Added entries for `bridge_sigma_injective`, `combined_bridge_finite_sum_le_Z` with `\leanok` markers
- Updated `bridge_sum_le_Z` from sorry to `\leanok`
- Updated `Z_xc_diverges_from_lower_bound` from sorry to `\leanok` with proof description
- Updated "Remaining sorry gaps" section to reflect that the lower bound assembly is now complete (modulo `origin_bridge_lower_bound`)

### Remaining Sorry Gaps (on the main theorem path)

The main theorem `connective_constant_eq` in `SAWFinal.lean` now depends on:

1. **Strip identity** (`strip_identity_concrete` in SAWFiniteStrip.lean): 1 = c_α A + B + c_ε E. Requires formalizing the parafermionic observable summation.

2. **Bridge partition bounds** (SAWBridgeFix.lean):
   - `origin_bridge_upper_bound`: B_T^{x_c} ≤ 1 (from strip identity)
   - `origin_bridge_lower_bound`: ∃ c > 0, B_T ≥ c/T (from strip identity + quadratic recurrence)

3. **Bridge decomposition injection** (`bridge_decomposition_injection_proof` in SAWHWDecomp.lean): The core Hammersley-Welsh counting inequality. Requires formalizing the recursive half-plane walk decomposition into bridges.

4. **B_T_inf connection** (`B_T_inf_eq_origin_bridge` in SAWFiniteStrip.lean): Connecting sup_L B_{T,L} to origin_bridge_partition.

Items not on the main theorem path (ignored per instructions):
- `saw_count_odd_lower` (SAWZigzag.lean) - elementary bound
- `bridge_decomp_injection_from_algorithm` (SAWHWAlgorithm.lean) - duplicate of #3