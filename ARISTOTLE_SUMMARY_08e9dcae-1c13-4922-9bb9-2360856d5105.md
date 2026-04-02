# Summary of changes
## Summary of formalization progress

### New file: `RequestProject/SAWDiagConnection.lean` (fully proved, 0 sorry's)
This file formalizes the connection between the paper's diagonal-strip bridges and the PaperSAW_B partition function, including:

1. **Hex lattice reflection** (`hexReflect`): The graph automorphism (x,y,b) ↦ (-y,-x,¬b) that reverses the diagonal coordinate x+y. Proved: involution, injectivity, diagonal reversal, sublattice flip, and **adjacency preservation** (`hexReflect_adj`).

2. **Negative diagonal bridges** (`NegDiagBridge`): Bridges matching the paper's convention (x+y from 0 to -T). Proved: length ≥ width.

3. **PaperSAW_B embedding**: Every PaperSAW_B walk determines a negative diagonal bridge (`paperSAW_B_to_negDiagBridge`). Proved: length preservation and **injectivity** (`paperSAW_B_to_negDiagBridge_injective`).

4. **Architectural documentation**: Identified and documented the critical column-vs-diagonal coordinate mismatch between the original `Bridge` definition (column coordinates) and the paper's strip identity (diagonal coordinates).

### Modified file: `RequestProject/SAWStripIdentityCorrect.lean`
**Proved** `strip_identity_from_B_bound`: Reduced the strip identity existence proof to the single key bound B_paper ≤ 1. Given B_paper(T,L,xc) ≤ 1, the strip identity follows by setting A_m = (1 - B_paper)/c_α and E_m = 0. This replaces the previously sorry'd `strip_identity_exists` with a cleaner decomposition into `B_paper_le_one_direct` (the remaining sorry).

### Blueprint updates (`blueprint/src/content.tex`)
- Documented the reduction of strip_identity_exists to B_paper_le_one_direct
- Added explanation of the column vs. diagonal coordinate mismatch between `Bridge` (SAWBridgeFix.lean) and the paper's diagonal strip domain
- Noted that `origin_bridge_upper_bound` for column bridges does NOT follow from the paper's strip identity for diagonal bridges
- Documented the hex lattice reflection automorphism connecting positive and negative diagonal directions

### Key architectural finding
The original `Bridge` definition uses x-coordinate strips (column bridges), but the paper's strips use x+y coordinates (diagonal bridges). The boundary geometry differs, so the strip identity B_paper ≤ 1 applies to diagonal bridges but not column bridges. The correct formalization path requires either:
1. Proving B_paper_le_one_direct (the vertex relation + telescoping argument), or
2. Restructuring all downstream proofs to use PaperSAW_B throughout

### Remaining sorry's on the critical path
- `B_paper_le_one_direct` (SAWStripIdentityCorrect.lean): The core mathematical result, requiring the parafermionic observable + vertex relation + discrete Stokes theorem
- `bridge_decomposition_injection_proof` (SAWHWDecomp.lean): The Hammersley-Welsh bridge decomposition algorithm
- `origin_bridge_upper_bound`, `origin_bridge_lower_bound` (SAWBridgeFix.lean): Column-bridge bounds (may need restructuring due to coordinate mismatch)

All existing proofs compile cleanly. No axioms beyond propext, Classical.choice, and Quot.sound are used.