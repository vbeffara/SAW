# Summary of changes
## Summary of work done

### Blueprint updates

Updated `blueprint/src/content.tex` with significantly improved documentation of the remaining gaps in the formalization:

1. **Restructured "Remaining gaps" section** into clearly separated subsections:
   - **Gap 1: Strip identity (discrete Stokes theorem)** — `B_paper_le_one_direct` in `SAWStripIdentityCorrect.lean`. Documented the precise 3-step proof outline (interior cancellation, boundary evaluation, assembly) and what infrastructure is proved vs missing.
   - **Gap 2: Hammersley-Welsh bridge decomposition** — `bridge_decomposition_injection_proof` in `SAWHWDecomp.lean`. Listed the 4 required sub-steps.
   - **Architectural issue: column vs. diagonal coordinates** — Documented a critical mismatch between the formalization (which uses column bridges via `OriginBridge`) and the paper (which uses diagonal bridges via `PaperSAW_B`). The strip identity B ≤ 1 holds for diagonal strips but not column strips. Listed three resolution strategies (restructure to diagonal, prove column identity with different constants, or find lattice automorphism).
   - **Superseded and non-critical sorries** — Documented which sorry'd declarations are dead code or superseded by proved versions.

2. **Removed duplicate documentation** of the column/diagonal issue.

### Verification

- The project builds successfully with `lake build` (8067 jobs, no errors).
- All sorry-free results (Fekete's lemma, submultiplicativity, connective constant is a limit, pair/triplet cancellation, zigzag lower bounds, etc.) depend only on standard axioms (propext, Classical.choice, Quot.sound).
- The main theorem `connective_constant_eq` depends on `sorryAx` due to the two gaps.

### What remains

The main theorem `connective_constant_eq : connective_constant = √(2+√2)` compiles but depends on two sorry'd lemmas:

1. **`B_paper_le_one_direct`** (strip identity): Requires formalizing the discrete Stokes theorem — when summing the vertex relation over all strip vertices, interior mid-edge contributions cancel telescopically, leaving only boundary terms. The algebraic core (pair and triplet cancellation) is fully proved; the missing piece is the combinatorial bookkeeping of the telescoping sum.

2. **`bridge_decomposition_injection_proof`** (Hammersley-Welsh): Requires formalizing the recursive bridge decomposition algorithm — splitting SAWs at their maximum x-coordinate vertex, decomposing each half into bridges by strong induction on width, proving injectivity of the reverse procedure, and accounting for walk weights.

Additionally, a **column vs. diagonal coordinate mismatch** exists: the proof chain uses column bridges (`OriginBridge`, `origin_bridge_partition`), but the strip identity only directly bounds diagonal bridges (`PaperSAW_B`, `B_paper`). Resolving this requires either restructuring the proof to use diagonal bridges throughout, or establishing a connection between the two coordinate systems.