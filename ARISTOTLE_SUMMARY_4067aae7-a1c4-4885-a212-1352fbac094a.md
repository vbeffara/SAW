# Summary of changes
## Summary of Progress

I continued formalizing SAW.tex (Duminil-Copin & Smirnov's proof that μ = √(2+√2)) by adding new infrastructure, proving several lemmas, and updating the blueprint.

### New Files Created

- **`RequestProject/SAWVertexRelation.lean`**: Decomposition of the B_paper ≤ 1 proof into smaller pieces:
  - `paperSAW_B_length_ge` ✅ **Proved**: Each PaperSAW_B walk has length ≥ T (since it traverses T diagonal units)
  - `B_paper_fintype_sum` ✅ **Proved**: B_paper is a finite sum (using tsum_fintype)
  - `B_paper_le_one_from_partial_bound` ✅ **Proved**: Reduces B_paper ≤ 1 to bounding all finite partial sums

### Existing Files Extended

- **`RequestProject/SAWDiagProof.lean`**: Connecting paper bridges to the strip identity:
  - `paperBridgeToSAWB` ✅ **Defined**: Maps a PaperBridge to PaperSAW_B (given strip fit)
  - `paperBridgeToSAWB_len` ✅ **Proved**: The mapping preserves walk length
  - `paperBridgeToSAWB_injective` ✅ **Proved**: The mapping is injective
  - `paper_bridge_partial_sum_shifted_le` ✅ **Proved**: ∑ xc^{len+1} ≤ 1 for bridges fitting in a strip (using B_paper ≤ 1)
  - `paper_bridge_partial_sum_le` ✅ **Proved**: ∑ xc^{len} ≤ 1/xc for any finite set of paper bridges (previously sorry'd)

### Blueprint Updated

- `blueprint/src/content.tex`: Added entries for all new lemmas with `\lean{}`, `\leanok`, `\uses{}`, and proof blocks
- `blueprint/lean_decls`: Added all new declaration names
- `PROOF_STATUS.md`: Updated to reflect current state

### Sorry Status

**Eliminated 1 sorry** on the critical path:
- `paper_bridge_partial_sum_le` in SAWDiagProof.lean — now proved (modulo B_paper_le_one_direct)

**Remaining critical sorry's** (unchanged, on path to main theorem):
1. `B_paper_le_one_direct` — THE FUNDAMENTAL GAP. Requires the parafermionic observable vertex relation (walk matching into pairs/triplets). Algebraic cancellation identities are proved; the combinatorial matching infrastructure is the main remaining task.
2. `origin_bridge_upper_bound` / `origin_bridge_lower_bound` — depend on #1
3. `bridge_decomposition_injection_proof` — independent, requires Hammersley-Welsh bridge decomposition algorithm

### Architecture Notes

No statements were duplicated; all new code uses `import` to reference existing declarations. The new file `SAWVertexRelation.lean` imports from `SAWObservableProof` and `SAWDiagBridge`, while the extended `SAWDiagProof.lean` now also imports `SAWStripIdentityCorrect` for access to `B_paper_le_one_direct`.