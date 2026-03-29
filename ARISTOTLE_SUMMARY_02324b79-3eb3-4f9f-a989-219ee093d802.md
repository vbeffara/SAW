# Summary of changes
## Summary of Hammersley-Welsh Formalization Progress

### New Results Proved (sorry-free)

1. **`saw_count_even_lower_proved`** (SAWZigzagBuild.lean): Proved that $2^k \leq c_{2k}$ (the even lower bound on SAW count). This was a key sorry in the project. The proof constructs an injection from `Fin k → Bool` to `SAW hexOrigin (2*k)` using the zigzag walk construction (`zigzagToSAW`), and proves injectivity via `zigzag_scanl_injective`. This result is fully sorry-free (verified via `#print axioms`).

2. **Supporting infrastructure** proved along the way:
   - `zigzag_scanl_injective`: If two choice sequences produce the same scanl under zigzag_step from the same start, the sequences are equal.
   - `buildZigzagWalk_isPath`: The zigzag walk is self-avoiding (uses the decreasing x+y invariant).
   - `buildZigzagWalk_support_structure`: Characterizes the support of zigzag walks.
   - `zigzagToSAW`: Constructs a concrete SAW from a choice list.

### Sorry Status

The remaining sorry-containing declarations for the Hammersley-Welsh argument:

| Sorry | File | Description |
|-------|------|-------------|
| `strip_identity_concrete` | SAWFiniteStrip.lean | Lemma 2: $1 = c_\alpha A + B + c_\varepsilon E$ (the strip identity). Requires formalizing the vertex relation summing argument. |
| `origin_bridge_upper_bound` | SAWBridgeFix.lean | $B_T^{x_c} \leq 1$. Follows from strip identity. |
| `origin_bridge_lower_bound` | SAWBridgeFix.lean | $\exists c > 0, B_T^{x_c} \geq c/T$. Follows from strip identity + quadratic recurrence. |
| `bridge_decomposition_injection_proof` | SAWHWDecomp.lean | The core H-W counting inequality. Requires formalizing the bridge decomposition algorithm and its injectivity. |
| `saw_count_odd_lower_proved` | SAWZigzagBuild.lean | $3 \cdot 2^k \leq c_{2k+1}$. Requires building shifted zigzag walks from each neighbor of hexOrigin. |

### Blueprint Updates

Updated `blueprint/src/content.tex` with:
- Marked `lem:saw_even_lower` as `\leanok` with lean reference to the proved `saw_count_even_lower_proved`
- Added proof block for the even lower bound
- Added new subsection "Hammersley-Welsh algorithm infrastructure" documenting `walk_max_x_achieved`, `bridgeToOriginBridge_false`, `zigzag_scanl_injective`, `buildZigzagWalk_isPath`
- Added new subsection "Remaining sorry gaps" listing the 4 key sorries for the H-W argument
- Updated `lem:saw_odd_lower` status description
- All entries use standard LaTeX macros (no HTML)

### Architecture Notes

- No statements were duplicated; the proved `saw_count_even_lower_proved` is in SAWZigzagBuild.lean (which imports SAWZigzag.lean). The sorry'd `saw_count_even_lower` in SAWZigzag.lean is left as-is for backward compatibility.
- The dependency chain for H-W summability is: strip_identity_concrete → origin_bridge_upper/lower_bound → bridge summability/decay → bridge_decomposition_injection → hw_partial_sum_bound → hammersley_welsh_summable. The first and last links are the key remaining sorries.
- The abstract versions of bridge_bound, bridge_lower_bound, and recurrence results (in SAWDecomp.lean) are fully proved. Only the concrete instantiations connecting to the strip domain are sorry'd.