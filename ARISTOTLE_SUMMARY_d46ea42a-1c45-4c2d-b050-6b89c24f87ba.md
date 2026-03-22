# Summary of changes
## Summary of Changes

### Blueprint Setup
Created a comprehensive blueprint in `blueprint/` with:

- **`blueprint/src/content.tex`**: Full blueprint with `\lean`, `\leanok`, and `\uses` annotations mapping every definition, lemma, theorem, and conjecture from the paper to its Lean formalization. Organized into 5 chapters matching the paper's structure.
- **`blueprint/dep_graph.dot`**: Graphviz dependency graph showing all ~50 formalized statements and their dependencies, color-coded by chapter, with dashed borders for sorry'd items.
- **`blueprint/README.md`**: Comprehensive overview with a Mermaid dependency graph (renders on GitHub), file structure table, paper-to-Lean mapping, and import dependency tree.
- **`blueprint/plastex.cfg`** and **`blueprint/src/print.tex`**, **`blueprint/src/web.tex`**: Configuration for building HTML/PDF versions via `leanblueprint web`.

### Code Improvements

1. **Fixed the `Bridge` definition** (`SAWBridge.lean`): The previous definition used `(hexEmbed end_v).re = (3 * T + 1) / 2` for the right boundary condition, which was impossible to satisfy (the hexagonal embedding gives real parts of the form `3x/2` or `3x/2 + 1`, neither of which equals `(3T+1)/2` for integer x and T). The `Bridge` type was provably empty! Fixed to use integer x-coordinates: `start_v.1 = 0`, `end_v.1 = T`, `∀ v, 0 ≤ v.1 ∧ v.1 ≤ T`.

2. **Simplified `bridge_length_ge_width`** (`SAWDecomp.lean`): With the corrected Bridge definition, the proof that a bridge of width T has length ≥ T now follows directly from `hexGraph_walk_bound` and `omega`, replacing the previous complex case analysis.

3. **Removed duplicate instances** (`SAWStrip.lean`): Removed the duplicate `hexGraph_decidableAdj` and `hexGraph_locallyFinite` instances (and their helper `hexNeighborFinset` definitions) that were already defined in `SAW.lean` (as `hexGraph_decidableAdj'` and `hexGraph_locallyFinite'`). These are typeclass instances imported via `import RequestProject.SAW`.

4. **Updated `README.md`**: Added project overview, file structure table, build instructions, and pointer to the blueprint.

### Current State
- **18 Lean files**, ~6500 lines, 0 new sorry's introduced
- **2 remaining sorry's** (unchanged from before), both in `SAWBridge.lean`:
  - `hammersley_welsh_bound`: The Hammersley-Welsh bound (upper bound direction)
  - `lower_bound_from_strip_identity`: The lower bound from strip identity
  
  Both require formalizing the injection from SAWs into sequences of bridges (the Hammersley-Welsh decomposition), which is a substantial piece of combinatorial infrastructure. All other components of the proof chain (algebraic identities, vertex relation, strip identity, bridge bounds, Fekete's lemma, submultiplicativity) are fully proved.
