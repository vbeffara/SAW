# Summary of changes
## Summary of changes

### Blueprint fixes (3 issues resolved)

1. **Output path fix**: Moved `plastex.cfg` from `blueprint/plastex.cfg` to `blueprint/src/plastex.cfg` (the standard location expected by `leanblueprint web`, which runs `plastex -c plastex.cfg` from `blueprint/src/`). The old location was silently ignored by plasTeX, causing it to use defaults.

2. **Renderer and plugins fix**: Changed `plastex.cfg` to use:
   - `renderer=HTML5` (was `DocHTMLTheme`, a non-standard renderer)
   - Added `plugins=plastexdepgraph plastexshowmore leanblueprint` (was missing entirely)
   - This enables the dependency graph generation and `\lean{...}`, `\leanok`, `\uses{...}` macros

3. **Web output structure fix**: The output now goes directly to `blueprint/web/` (not `blueprint/web/web/`). The `leanblueprint serve` command will now correctly serve `index.html` at the root instead of showing just a link to a `web/` subfolder.

**Additional blueprint infrastructure created:**
- `blueprint/src/web.tex` — Rewritten with proper `\usepackage[showmore, dep_graph]{blueprint}` and inline theorem environments
- `blueprint/src/print.tex` — Rewritten with proper print-mode macros
- `blueprint/src/blueprint.sty` — Standard stub style file
- `blueprint/src/macros/` — Standard macro directory (common.tex, web.tex, print.tex)
- `blueprint/src/extra_styles.css` — CSS styling for theorem borders
- `blueprint/README.md` — Updated with build instructions
- Cleaned up old stale output directories and build artifacts

The dependency graph is now properly generated (265+ nodes visible in `dep_graph_document.html`).

### Formalization progress

1. **Proved `zigzag_sum_eq_neg`** (SAWZigzag.lean): Shows that positions in the zigzag walk satisfy x+y = -i at step i. Previously sorry'd.

2. **Proved `zigzag_positions_nodup`** (SAWZigzag.lean): Shows all zigzag positions are distinct (using the strictly decreasing x+y values). Previously sorry'd.

3. **Proved `saw_count_sq_ge_two_pow'`** (SAWZigzag.lean): Shows 2^n ≤ c_n² by splitting into even/odd cases. Previously sorry'd. Uses `saw_count_even_lower` and `saw_count_odd_lower` (still sorry'd).

4. **Connected `saw_count_sq_ge_two_pow`** (SAWLowerCount.lean): Updated to import SAWZigzag and delegate to `saw_count_sq_ge_two_pow'` instead of having its own sorry. Fixed `exact?` placeholder in SAWZigzag.lean.

5. **Removed incorrect `\leanok`** from `connective_constant_le_two'` in the blueprint (it depends on `connective_constant_eq` which uses sorry).

### Remaining sorry's

The project still has sorry's in:
- `SAWZigzag.lean`: `saw_count_even_lower`, `saw_count_odd_lower` (require constructing explicit zigzag SAW witnesses — hard to automate)
- `SAWBridge.lean`: `hammersley_welsh_bound` (requires full bridge decomposition proof)
- `SAWBridgeFix.lean`: `origin_bridge_upper_bound`, `origin_bridge_lower_bound`, `Z_xc_diverges`, `hammersley_welsh_injection` (require connecting abstract and concrete strip definitions)
- `SAWFiniteStrip.lean`: `strip_identity_concrete`, `B_T_inf_eq_origin_bridge` (require bridging abstract vertex-relation summing with concrete partition functions)

All files compile successfully with `lake build`.