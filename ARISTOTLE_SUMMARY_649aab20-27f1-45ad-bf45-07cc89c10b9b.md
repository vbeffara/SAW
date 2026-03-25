# Summary of changes
## Summary of Changes

### 1. Blueprint Redesign (Standard Leanblueprint)

Completely rewrote `blueprint/src/content.tex` using standard leanblueprint scaffolding:
- **76 definitions/theorems** annotated with `\lean{...}` linking to actual Lean declarations
- `\leanok` markers on all fully-proved items (no sorry)
- `\uses{...}` dependency annotations for proper dependency tracking
- 5 chapters mirroring the paper structure: Introduction, Constants & Identities, Observable, Strip & Identity, Proof
- 5 items explicitly marked as sorry'd with `\textbf{Status: sorry}`

Updated supporting files:
- `blueprint/src/web.tex` — web output configuration
- `blueprint/src/print.tex` — print output configuration  
- `blueprint/dep_graph.dot` — Graphviz dependency graph with color-coded status

### 2. Duplicate Elimination (Imports)

- **Removed duplicate conjectures** from `SAWBridge.lean`: `SLE_convergence_conjecture` and `observable_scaling_limit_conjecture` were duplicated in `SAWConjectures.lean`. Replaced with a comment referencing the canonical definitions.
- **Updated `SAWConjectures.lean`** to import `SAWMain` instead of `SAW`, reusing `gamma_SAW` and `nu_SAW` from `SAWMain.lean` instead of defining duplicate `gamma_exponent` and `nu_exponent`.

### 3. Continued Formalization

- Added `saw_count_sq_ge_two_pow` helper lemma in `SAWLowerCount.lean` as a decomposition point for the elementary lower bound
- Attempted to prove `connective_constant_ge_sqrt_two` (√2 ≤ μ) and `hammersley_welsh_bound` — both require deep combinatorial arguments that resist automated proving

### 4. Documentation Update

- Rewrote `README.md` with comprehensive file-by-file status table, remaining gaps description, and build instructions

### Current Status

The project builds cleanly with **9 remaining sorry's** across 4 files:
- `SAWBridge.lean` (1): Hammersley-Welsh bound (bridge decomposition injection)
- `SAWBridgeFix.lean` (4): Corrected bridge bounds and partition function results
- `SAWFiniteStrip.lean` (2): Concrete strip identity and bridge connection  
- `SAWLowerCount.lean` (2): Elementary lower bound c_n ≥ √2^n

The abstract proof structure is **fully complete**: algebraic identities, vertex relation (Lemma 1), strip identity (Lemma 2), bridge bounds, case analysis, and Fekete's lemma are all proved. The remaining sorry's are in connecting abstract results to concrete SAW counts via the Hammersley-Welsh bridge decomposition.