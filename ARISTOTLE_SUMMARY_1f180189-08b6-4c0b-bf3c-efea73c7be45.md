# Summary of changes
## Summary of Work: Hammersley-Welsh Bridge Decomposition Infrastructure

### New File Created: `RequestProject/SAWHWAlgorithm.lean`

This file (243 lines) provides core infrastructure for the Hammersley-Welsh bridge decomposition, focusing on the tools needed to prove `bridge_decomposition_injection_proof`. It imports from `SAWHWInject` (avoiding duplication) and establishes:

**Proved lemmas (no sorry):**

1. **Translation symmetry** (`hexShift`, `hexShift_adj`, `hexShift_injective`): The hexagonal lattice has translation symmetry — shifting vertices by (dx, dy) preserves adjacency and is injective.

2. **Walk translation** (`shiftWalk`, `shiftWalk_length`, `shiftWalk_support`, `shiftWalk_isPath`): Walks can be translated along the lattice, preserving length and the path (self-avoiding) property.

3. **Bipartiteness** (`hexGraph_bipartite`): The hexagonal lattice is bipartite — every edge connects a false-sublattice vertex to a true-sublattice vertex.

4. **Walk sublattice parity** (`walk_sublattice_parity`): In any walk from hexOrigin, the vertex at step i has sublattice type `decide(i % 2 = 1)`. Even steps give false-sublattice vertices, odd steps give true-sublattice.

5. **Even-length SAW endpoint** (`saw_even_end_false`): A SAW from hexOrigin of even length ends at a false-sublattice vertex.

6. **Bridge translation** (`bridgeToOriginBridge_false`, `bridgeToOriginBridge_false_length`): A bridge starting from a false-sublattice vertex at x=0 can be translated vertically to become an origin bridge of the same width and length.

7. **Walk splitting** (`path_split_length`, `takeUntil_x_le_max`, `dropUntil_x_le_max`): Path splitting at a vertex preserves total length, and both parts have x-coordinates bounded by the original walk's maximum.

**Remaining sorry:**
- `bridge_decomp_injection_from_algorithm`: The full counting inequality (mirrors `bridge_decomposition_injection_proof` from SAWHWDecomp). This is the core combinatorial gap requiring the full decomposition algorithm.

### Blueprint Updates: `blueprint/src/content.tex` and `blueprint/lean_decls`

Added 9 new entries to the blueprint (all with `\leanok` for both statement and proof):

- **Hexagonal lattice bipartiteness** (`lem:hex_bipartite`)
- **Walk sublattice parity** (`lem:walk_parity`)
- **Even-length SAW endpoint** (`lem:saw_even_false`)
- **Translation preserves adjacency** (`lem:hex_shift_adj`)
- **Translation is injective** (`lem:hex_shift_inj`)
- **Shifted walk is a path** (`lem:shift_walk_path`)
- **Bridge translation to origin bridge** (`lem:bridge_to_origin`)
- **Path splitting length** (`lem:path_split_length`)
- **takeUntil/dropUntil x-coordinate bounds** (`lem:takeUntil_x_bound`, `lem:dropUntil_x_bound`)

Updated the dependency graph for `thm:bridge_decomp_inj_proof` to reference the new helper lemmas.

Updated `blueprint/lean_decls` with all new Lean declaration names.

### Current Sorry Status

The project has 11 sorry's across 6 files. The Hammersley-Welsh chain has these key sorries:
- `bridge_decomposition_injection_proof` / `bridge_decomp_injection_from_algorithm`: The core bridge decomposition counting inequality (hardest remaining theorem — requires formalizing the full HW decomposition algorithm)
- `origin_bridge_upper_bound`: B_T^{xc} ≤ 1 (depends on strip identity)
- `origin_bridge_lower_bound`: B_T^{xc} ≥ c/T (depends on strip identity + recurrence)
- `strip_identity_concrete`: The strip identity Lemma 2 (depends on parafermionic observable)

All other Hammersley-Welsh theorems (`origin_bridge_decay`, `hw_upper_bound_abstract`, `hw_partial_sum_bound`, `hammersley_welsh_summable`, etc.) are fully proved.

### Project Status

The full project builds successfully (8057 jobs, no errors). No statements were duplicated — the new file imports from existing infrastructure via `RequestProject.SAWHWInject`.