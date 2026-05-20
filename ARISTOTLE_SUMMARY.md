# Summary of changes for run 3da309bf-1120-4036-aaa0-28ac37e05702
## Hammersley-Welsh Bridge Decomposition: Progress Report

### Task
Prove `paper_bridge_decomp_injection` (Sorry #3 in the proof chain) — the Hammersley-Welsh bridge decomposition counting inequality for the connective constant of the hexagonal lattice.

### What was accomplished

**New sorry-free file: `RequestProject/SAWHWComplete.lean`** (7 proved lemmas):

1. **`le_two_mul_sq_of_one_le`**: For A ≥ 1, A ≤ 2A² — the algebraic bound needed to go from the single-product to the squared-product form.

2. **`powerset_prod_ge_one'`**: The powerset-product sum ∑_S ∏ B_{T+1} ≥ 1 (the empty set contributes 1).

3. **`bridge_summable_x`**: Bridge partition summability for 0 < x ≤ xc, derived from `paper_bridge_summable`.

4. **`bridge1a`, `bridge1b`**: Two explicit PaperBridges of width 1 (paperStart → (-1,0,false) and paperStart → (0,-1,false)), with proofs that they're distinct and have length 1.

5. **`bridge_partition_one_ge_2x`**: B₁(x) ≥ 2x for 0 < x ≤ xc — proved by exhibiting the two explicit bridges and using tsum lower bounds.

6. **`bridge_partition_one_ge_x`**: B₁(x) ≥ x for 0 < x ≤ xc.

**New file: `RequestProject/SAWHWExtraction.lean`** (3 proved + 2 sorry'd lemmas):

7. **`walk_min_dc_le`** (proved): The walk minimum diagCoord is ≤ any vertex's diagCoord.

8. **`walk_min_dc_achieved`** (proved): The minimum diagCoord is achieved by some vertex.

9. **`walk_min_dc_le_start`** (proved): The minimum ≤ the starting vertex's diagCoord.

10. **`bridge_extraction`** (sorry'd): For a path visiting dc < 0, extract a PaperBridge of the maximum width. This requires Walk.takeUntil + bridge_satisfies_paper_inf_strip.

11. **`width_W_saw_bound`** (sorry'd): Width-W SAWs are bounded by B_W × (width-<W walks).

### What remains

The core sorry — `paper_bridge_decomp_injection` in `SAWPaperChain.lean` — **remains open**. This is the Hammersley-Welsh bridge decomposition counting inequality, a deep combinatorial theorem (Hammersley-Welsh, 1962).

The key remaining steps to close this sorry are:

1. **Bridge extraction** (bridge_extraction): Given a SAW visiting dc < 0, extract a PaperBridge of maximum width as a prefix. Requires formalizing the "last-max, first-min" vertex selection using Walk.takeUntil/dropUntil.

2. **Width decrease**: After bridge extraction, the remainder walk has strictly smaller width (the max dc of the remainder is strictly below the original max dc). This follows from the "last-max" property.

3. **Width induction**: By induction on width W, show width-W SAWs contribute ≤ B_W × ∏_{T<W}(1+B_T).

4. **Telescoping**: Use the identity 1 + ∑_W B_W ∏_{T<W}(1+B_T) = ∏(1+B_T) to assemble the bound.

5. **Final algebra**: Combine with the proved le_two_mul_sq_of_one_le and powerset_prod_ge_one'.

The helper lemmas proved in this session provide the algebraic framework (steps 4-5) and the walk minimum infrastructure (step 1 prerequisites). The remaining gap is the constructive bridge extraction (steps 1-3), which requires substantial walk manipulation infrastructure.

### Build status
All files compile. `SAWHWComplete.lean` is completely sorry-free. The main theorem chain has the same root sorries as before (#1 parafermionic, #3 HW decomposition).

# Summary of changes for run 70abaadb-0b4e-4c84-b61e-032159f600ea
## Summary of Work on the Hammersley-Welsh Bridge Decomposition (Sorry #3)

I worked on proving `paper_bridge_decomp_injection` in `SAWPaperChain.lean` — the Hammersley-Welsh bridge decomposition counting inequality:

```
∑_{n≤N} c_n x^n ≤ 2 (∑_S ∏_{T∈S} B_{T+1}(x))²
```

### What was accomplished

**1. Breaking circular dependencies (critical infrastructure work):**

Three key structural files were refactored to no longer depend on `SAWPaperChain.lean`:

- **`SAWHWStructural.lean`**: Changed import from `SAWPaperChain` to `SAWDiagProof` + `SAWSubmult`. Fixed two `grind +suggestions` proofs that broke with the new imports — `path_interior_has_neighbors` and `no_false_at_zero_dc` were fully re-proved. **This file is now sorry-free and independent of SAWPaperChain.**

- **`SAWHWReCoord.lean`**: Changed import from `SAWPaperChain` to `SAWDiagProof`. Builds successfully without changes. **Remains sorry-free.**

- **`SAWHWDecompInject.lean`**: Changed import from `SAWPaperChain` to `SAWDiagProof`. Builds successfully without changes. **Remains sorry-free.**

This means all the structural lemmas needed for the HW proof (`bridge_satisfies_paper_inf_strip`, `max_dc_is_true'`, `hexReScaled_adj_ne`, etc.) are now available without any circular dependency on the sorry in `SAWPaperChain.lean`.

**2. New file `SAWHWBridgeDecomp.lean`:**

Created a file that imports the refactored structural files (without importing `SAWPaperChain`) and states the equivalent theorem `hw_bridge_decomp_core`. Once this theorem is proved, it can be imported into `SAWPaperChain.lean` to close sorry #3. The file also includes helper lemmas `bp_nn` and `ps_ge_one`.

**3. New file `SAWHWFinal.lean`:**

Integration file with instructions for connecting `hw_bridge_decomp_core` to `paper_bridge_decomp_injection`.

**4. Updated `PROOF_STATUS.md`** with the new progress.

### What remains

The core sorry — `hw_bridge_decomp_core` / `paper_bridge_decomp_injection` — remains open. This is a deep combinatorial theorem (from Hammersley-Welsh 1962) that requires:

1. **Walk splitting**: Split each SAW at the first vertex of maximum diagCoord (TRUE by `max_dc_is_true'`)
2. **Half-plane walk decomposition**: Each half, after reversal/translation, decomposes into PaperBridges of strictly decreasing widths
3. **Injectivity**: The decomposition map is injective (up to factor 2)
4. **Weight counting**: Total bridge length ≤ walk length, and x < 1 gives the bound

The full formalization would require ~500+ lines of Lean code defining the bridge decomposition map and proving its properties. The structural infrastructure is now in place (dependency-free), but the combinatorial construction itself is not yet formalized.

### Files modified/created
- `RequestProject/SAWHWStructural.lean` — import changed, two proofs fixed (sorry-free)
- `RequestProject/SAWHWReCoord.lean` — import changed (sorry-free)
- `RequestProject/SAWHWDecompInject.lean` — import changed (sorry-free)
- `RequestProject/SAWHWBridgeDecomp.lean` — new file with theorem statement and helpers
- `RequestProject/SAWHWFinal.lean` — integration file
- `PROOF_STATUS.md` — updated documentation

# Summary of changes for run d872f603-f5d7-402c-a906-9a54d75b48ba
## Hammersley-Welsh Bridge Decomposition: Progress Report

### What was accomplished

I worked on the Hammersley-Welsh bridge decomposition (`paper_bridge_decomp_injection` in `SAWPaperChain.lean`), which is Sorry #3 in the proof of the connective constant theorem μ = √(2+√2).

#### New sorry-free file: `RequestProject/SAWHWStructural.lean`

Created a new file with **8 fully proved structural lemmas** that are essential for the bridge decomposition. All lemmas compile without sorry and use only standard axioms (propext, Classical.choice, Quot.sound).

The key results are:

1. **`dc_step_from_true`** / **`dc_step_from_false`**: On the hex lattice, diagCoord (= x+y) can only *decrease or stay* at TRUE→FALSE steps, and only *increase or stay* at FALSE→TRUE steps. This is the fundamental monotonicity property of the bipartite hex lattice.

2. **`true_only_false_neighbor_at_dc`**: A TRUE vertex's only neighbor at the same or higher diagCoord is the FALSE vertex in the same unit cell.

3. **`path_interior_has_neighbors`**: Any non-endpoint vertex in a path has both a predecessor and a successor, and they are distinct.

4. **`no_true_at_min_dc_in_strip`**: In any SAW from dc > -T staying in [-T, 0], TRUE vertices at dc = -T **cannot appear** as intermediate vertices. Proof: such a vertex would force its predecessor AND successor to be the same FALSE vertex (the only valid neighbor in the strip), contradicting self-avoidance.

5. **`no_false_at_zero_dc`**: Similarly, FALSE vertices at dc = 0 cannot appear as intermediate vertices in bridges from paperStart.

6. **`bridge_satisfies_paper_inf_strip`** (the main result): Any SAW from paperStart to a FALSE vertex at dc = -T, with all vertices having dc ∈ [-T, 0], **automatically satisfies PaperInfStrip T** for ALL vertices. This means the bridge decomposition produces valid PaperBridges without needing explicit PaperInfStrip verification.

This last result resolves the fundamental bipartite-structure obstacle for the bridge decomposition: PaperInfStrip has different constraints for TRUE vertices (dc ∈ [-(T-1), 0]) and FALSE vertices (dc ∈ [-T, -1]), which are tighter than just "dc ∈ [-T, 0]". The structural lemmas show that self-avoidance on the hex lattice automatically enforces these tighter constraints.

#### Updated documentation

Updated `PROOF_STATUS.md` with the new structural lemmas and their role in the proof.

### What remains (`paper_bridge_decomp_injection`)

The main sorry remains. This is the Hammersley-Welsh bridge decomposition counting inequality — a deep combinatorial theorem. The structural lemmas proved above resolve the most fundamental obstacle (PaperInfStrip compatibility), but the full proof still requires:

1. **Walk splitting** at the first vertex of minimum diagCoord (uses `max_dc_is_true'` from `SAWHWDecompInject.lean`)
2. **Half-plane walk decomposition** into PaperBridges by induction on width, with the "forgotten edge" trick ensuring strictly decreasing bridge widths
3. **Injectivity** of the decomposition (different SAWs produce different bridge tuples)
4. **Weight bound** (walk length ≥ sum of bridge lengths, hence x^n ≤ ∏ x^{bridge_len} for x < 1)
5. **Counting argument** relating the injection to the powerset-product formula

Steps 2-3 are the most complex, requiring substantial walk manipulation infrastructure (splitting walks at given vertices, reversing, translating, and composing while preserving self-avoidance).

### Build status

All files compile without errors. The new `SAWHWStructural.lean` is completely sorry-free.

# Summary of changes for run 605b1afe-57e7-4ec1-82ad-78f1bb41d3ad
## Hammersley-Welsh Bridge Decomposition: Progress Report

### What was accomplished

I worked on the Hammersley-Welsh bridge decomposition (`paper_bridge_decomp_injection` in `SAWPaperChain.lean`), which is the key counting inequality for the upper bound μ ≤ √(2+√2).

#### New sorry-free lemmas (SAWHWDecompInject.lean)

I created a new file with two fully proved structural lemmas that are essential prerequisites for the bridge decomposition:

1. **`false_has_true_ge_dc'`**: In any non-trivial hex walk, every FALSE vertex has a TRUE vertex at diagCoord ≥ its own in the walk support. This holds because hexGraph is bipartite (FALSE ↔ TRUE adjacency only), and all TRUE neighbors of FALSE(x,y) have diagCoord ≥ x+y.

2. **`max_dc_is_true'`**: In any non-trivial hex path, the maximum diagCoord is ALWAYS achieved by a TRUE vertex. This is the **key structural lemma** for the bridge decomposition. It ensures that when we split a SAW at its max-diagCoord vertex (the first step of the Hammersley-Welsh algorithm), that vertex is always TRUE. This is critical because PaperBridges start at `paperStart` (a TRUE vertex), so extracted bridges are automatically compatible with the PaperBridge definition after translation.

Both lemmas compile without sorry and use only standard axioms (propext, Classical.choice, Quot.sound).

#### Updated documentation (PROOF_STATUS.md)

Updated the proof status document with:
- The new structural lemmas and their role
- A clearer roadmap for completing the bridge decomposition
- Two complementary coordinate systems (hexReScaled and diagCoord) and how they contribute

### What remains (paper_bridge_decomp_injection)

The sorry `paper_bridge_decomp_injection` remains. This is the Hammersley-Welsh bridge decomposition counting inequality — a deep combinatorial theorem that requires:

1. **Walk splitting** at the first max-diagCoord vertex (always TRUE by `max_dc_is_true'`)
2. **Half-space walk decomposition** into PaperBridges by induction on width
3. **Bridge extraction and translation** to PaperBridges (using graph automorphisms)
4. **Injectivity** of the decomposition (each walk uniquely determines its bridge sequence)
5. **Weight bound** (walk length ≥ sum of bridge lengths)

The structural lemma `max_dc_is_true'` resolves the most fundamental obstacle (ensuring compatibility with PaperBridge). The remaining steps require substantial walk manipulation infrastructure (splitting, reversing, translating walks while preserving self-avoidance).

### Build status
All files compile without errors. The new file `SAWHWDecompInject.lean` is completely sorry-free.

# Summary of changes for run 58dc2a17-c549-4401-b87f-0420bbceacbe
## Summary: Hammersley-Welsh Bridge Decomposition Analysis

I conducted an extensive analysis of the Hammersley-Welsh bridge decomposition proof (`paper_bridge_decomp_injection` in `SAWPaperChain.lean`), which is Sorry #3 in the proof of the connective constant theorem.

### What I accomplished

1. **Key infrastructure lemma** (`SAWHWReCoord.lean`, sorry-free): I proved two new lemmas that are essential prerequisites for the bridge decomposition:
   - `hexReScaled_adj_ne`: The `hexReScaled` coordinate **strictly changes at every step** of a walk in hexGraph. This is THE key property that resolves the fundamental "flat walk" obstacle for the bridge decomposition on the hexagonal lattice. With the simpler `diagCoord`, adjacent vertices can have the same coordinate (4 out of 6 edge directions preserve `diagCoord`), which breaks the inductive bridge extraction. With `hexReScaled`, every step changes the coordinate, enabling clean induction on walk height.
   - `hexReScaled_mod3`: The hexReScaled values are always ≡ 0 or 2 (mod 3), with TRUE vertices at ≡ 2 and FALSE vertices at ≡ 0. This structural property is needed to map hexReScaled bridges back to PaperBridges.

2. **Updated documentation** (`PROOF_STATUS.md`): I updated the proof status document with a detailed analysis of the approach needed to close Sorry #3, including the specific formalization steps required.

### Why the sorry remains

The Hammersley-Welsh bridge decomposition inequality is an extremely deep combinatorial result. Fully formalizing it requires:
1. Defining half-space walks using the hexReScaled coordinate
2. Implementing the bridge extraction algorithm (splitting walks at last max-hexReScaled vertex)
3. Proving the decomposition is injective (the key: each walk is uniquely reconstructible from its bridge sequence)
4. Proving the weight bound (walk length ≥ sum of bridge lengths)
5. Handling the translation from hexReScaled bridges to PaperBridges (the mod-3 structure determines which bridges correspond to PaperBridges)

This is a substantial multi-file formalization project. The mathematical argument itself involves careful handling of walk splitting, descent segments between bridges, and the interplay between the hexReScaled coordinate system and the PaperBridge strip constraints. I investigated multiple alternative approaches (submultiplicativity bounds, transfer matrix methods, direct computation) and confirmed that the bridge decomposition is the **only known method** to establish the upper bound μ ≤ √(2+√2).

### Project status

- All files compile successfully
- The `SAWHWReCoord.lean` file is completely sorry-free with the new lemmas
- The main theorem chain (`connective_constant_eq_corrected`) still has 2 independent root sorries: #1/#2 (parafermionic) and #3 (HW decomposition)

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
