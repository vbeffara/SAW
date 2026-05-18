# Summary of changes for run 01f66c80-070b-488b-b22d-d8455caaa9a5
## Summary of Changes

### New Sorry-Free Proofs: `RequestProject/SAWStripProofNew.lean`

Created a new file with two fully proved lemmas that establish the algebraic core of the vertex relation (Lemma 1 of the paper) for the parafermionic observable:

- **`false_vertex_triplet_zero`**: At any FALSE vertex of the hex lattice, for any accumulated winding W, the triplet contribution to the vertex relation vanishes:
  ```
  1 · windingPhase(W) + j · windingPhase(W-1) · xc + conj(j) · windingPhase(W+1) · xc = 0
  ```

- **`true_vertex_triplet_zero`**: The analogous result at TRUE vertices:
  ```
  (-1) · windingPhase(W) + (-j) · windingPhase(W-1) · xc + (-conj(j)) · windingPhase(W+1) · xc = 0
  ```

These lemmas are the algebraic engine of the discrete Stokes argument: they show that at each vertex of the strip, the direction-weighted observable contributions from any walk and its one-step extensions cancel, regardless of the walk's accumulated winding. They connect `triplet_cancellation` (the abstract algebraic identity) to the concrete vertex geometry via `windingPhase` (the complex phase for a given winding in units of π/3).

Both lemmas compile without sorry and use only standard axioms (propext, Classical.choice, Quot.sound).

### Blueprint Updates: `blueprint/src/content.tex`

Added entries for:
- `windingPhase` definition with `\leanok`
- `false_vertex_triplet_zero` lemma with `\leanok` and proof
- `true_vertex_triplet_zero` lemma with `\leanok` and proof
- Proper `\uses{}` dependency tags linking to `triplet_cancellation`

### Documentation Updates: `PROOF_STATUS.md`

Completely rewritten with:
- Clear statement that there are only **2 independent root sorries** (#1/#2 parafermionic, #3 HW decomposition)
- New section documenting the vertex relation infrastructure
- Updated roadmap showing which steps of the parafermionic proof are now complete
- Detailed list of remaining gaps for each sorry

### What Remains

The main theorem `connective_constant_eq_corrected` (μ = √(2+√2)) is proved modulo 2 independent root sorries:

1. **Parafermionic identity** (Sorry #1/#2): The algebraic ingredients (pair cancellation, triplet cancellation, vertex triplet zero at both vertex types) are all fully proved. What remains is the combinatorial discrete Stokes argument: properly defining the observable at each mid-edge, showing interior edges cancel in the vertex relation sum, handling "blocked extensions" via pair cancellation, and evaluating boundary contributions.

2. **Hammersley-Welsh decomposition** (Sorry #3): Requires formalizing the bridge extraction algorithm, proving its injectivity, and deriving the counting inequality. Infrastructure exists in multiple files but the main combinatorial construction is not yet complete.

### No T=1 Special Case Work

This session focused entirely on the general case (arbitrary T, L), establishing the vertex relation infrastructure for general strips rather than exploiting the T=1 special case.

# Summary of changes for run 3c0a2b1e-2890-415f-bb24-6fe0e85fb7a2
## Session Summary

### What Was Done

**1. New Sorry-Free Helper Lemmas** (`RequestProject/SAWHWProved2.lean`):
Created a new file with proved lemmas advancing the Hammersley-Welsh decomposition infrastructure:
- `diagCoord_adj_le` / `diagCoord_adj_ge`: diagonal coordinate changes by at most 1 per hex lattice step
- `walk_diagCoord_bound`: walk endpoint diagCoord bounded by walk length
- `walk_support_diagCoord_bound`: all vertices in a walk's support have diagCoord within length distance of start
- `Finset.sum_powerset_prod_eq_prod_add_one`: the powerset-product identity (∑_{S⊆F} ∏_{i∈S} a_i = ∏_{i∈F} (1+a_i))

All lemmas compile without sorry.

**2. Blueprint Updates** (`blueprint/src/content.tex`):
- Updated `\lean{}` references for diagCoord adjacency to point to the proved versions
- Added new blueprint entries for `walk_diagCoord_bound` and `walk_support_diagCoord_bound` with `\leanok` and `\uses{}` tags

**3. Proof Status Documentation** (`PROOF_STATUS.md`):
Comprehensive rewrite documenting:
- The 3 root sorries with precise file/line locations
- Complete dependency trees for both bounds
- Full inventory of what IS proved (sorry-free)
- Detailed roadmap for resolving each remaining sorry

**4. Duplication Analysis**:
Identified `diagCoord` defined in 6 different files. Noted in documentation for future cleanup using imports.

### What Was NOT Accomplished

**Neither of the two big remaining steps could be proved.** Both require substantial infrastructure that doesn't yet exist:

- **Parafermionic identity** (`infinite_strip_identity` / `B_paper_le_one_strip`): Requires formalizing the pair/triplet partition of walks at each vertex, the discrete Stokes summation argument, and boundary evaluation. Estimated ~30 new lemmas.

- **Hammersley-Welsh decomposition** (`paper_bridge_decomp_injection`): Requires defining the bridge extraction algorithm, proving injectivity via the reverse procedure, and careful handling of sublattice/direction issues. Estimated ~40 new lemmas.

Both were attempted extensively but the combinatorial infrastructure needed is too deep for a single session.

### Current State
The main theorem `connective_constant_eq_corrected` (μ = √(2+√2)) is **proved modulo 3 root sorries**. The T=1 case of the infinite strip identity remains independently proved (sorry-free in `SAWAInf1Lower.lean`). All files compile cleanly.

# Session Summary

## Task
Continue formalizing SAW.tex (Duminil-Copin & Smirnov 2012), avoiding duplication,
keeping the blueprint updated, and attempting to prove at least one of the two
remaining big steps.

## What Was Done

### 1. New Sorry-Free Helper Lemmas (SAWHWProved2.lean)
Created a new file with proved helper lemmas for the Hammersley-Welsh decomposition:
- `diagCoord`: definition of diagonal coordinate (v.1 + v.2.1)
- `diagCoord_adj_le` / `diagCoord_adj_ge`: diagonal coordinate changes by at most 1 per hex step
- `walk_diagCoord_bound`: walk endpoint diagCoord bounded by walk length
- `walk_support_diagCoord_bound`: all support vertices within length distance of start
- `Finset.sum_powerset_prod_eq_prod_add_one`: the powerset-product identity ∑_{S⊆F} ∏_{i∈S} a_i = ∏_{i∈F} (1+a_i)

All lemmas in this file are **sorry-free** and compile cleanly.

### 2. Blueprint Updates (blueprint/src/content.tex)
- Updated `\lean{}` references for `diagCoord_adj_bound` to point to the proved versions (`diagCoord_adj_le`, `diagCoord_adj_ge`)
- Added new blueprint entries for `walk_diagCoord_bound` and `walk_support_diagCoord_bound` with `\leanok` tags
- All new entries include proper `\uses{}` dependency links

### 3. Proof Status Documentation (PROOF_STATUS.md)
Completely rewrote the proof status document with:
- Clear listing of all 3 root sorries
- Complete dependency tree for both bounds
- Comprehensive list of what IS proved (sorry-free)
- Detailed roadmap for what remains for each sorry

### 4. Identified Duplication Issues
Found multiple duplicate definitions across the codebase:
- `diagCoord` defined in 6 different files (SAWBridgeDecomp, SAWHWCore, SAWHWDecompCore2, SAWHWDecompHelper, SAWHWPaperProof, SAWHWProved2)
- Various other duplicated definitions (hexShift, shiftWalk, etc.)
These should be consolidated using imports in a future cleanup.

### 5. Attempted Proofs of Big Steps
Extensive attempts were made on both remaining big steps:

**Parafermionic Identity** (`infinite_strip_identity` / `B_paper_le_one_strip`):
- Analyzed the discrete Stokes argument in detail
- Identified precise infrastructure needed: pair/triplet walk partition, observable definition, boundary evaluation
- The proof requires ~30 lemmas of new infrastructure for the walk partitioning and Stokes argument

**Hammersley-Welsh Decomposition** (`paper_bridge_decomp_injection`):
- Analyzed the bridge decomposition algorithm
- Identified key challenges: diagCoord direction issues, sublattice handling, translation between bridges from different starting points
- The proof requires ~40 lemmas for the constructive decomposition and injectivity

Neither could be completed in this session due to the extensive infrastructure requirements.

## Remaining Root Sorries (unchanged)
1. `infinite_strip_identity` (SAWRecurrenceProof.lean:49) — for lower bound
2. `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385) — for upper bound
3. `paper_bridge_decomp_injection` (SAWPaperChain.lean:265) — for upper bound

## Build Status
All files compile without errors. New SAWHWProved2.lean is completely sorry-free.
