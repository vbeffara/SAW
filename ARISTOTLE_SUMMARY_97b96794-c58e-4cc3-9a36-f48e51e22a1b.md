# Summary of changes
## Summary of changes to `strip_identity_concrete`

### Problem identified
The previous `paper_strip_identity` in `RequestProject/SAWStripIdentityCorrect.lean` stated the exact identity:
```
1 = c_alpha * A_paper T L xc + B_paper T L xc + c_eps * E_paper T L xc
```
This statement was **FALSE** — the vertex-based partition function `E_paper` undercounts walks at corner vertices (vertices adjacent to boundary mid-edges of multiple types). The paper's proof works at the mid-edge level, where walks at corner vertices are counted in each corresponding partition function.

### Changes made

**`RequestProject/SAWStripIdentityCorrect.lean`** (main file):
- Removed the false `paper_strip_identity` theorem
- Replaced it with `B_paper_le_one`, which directly states `B_paper T L xc ≤ 1` — the correct and sufficient result needed downstream
- Added detailed documentation explaining the proof strategy (parafermionic observable boundary sum argument) and why the previous exact identity was incorrect
- Preserved all helper lemmas (`left_boundary_exit_angle`, `right_boundary_exit_angle`, `cos_five_pi_eight`, non-negativity lemmas, etc.)
- The `B_paper_le_one` theorem has a `sorry` — proving it requires formalizing the full parafermionic observable theory (discrete Stokes theorem + boundary winding evaluation), while the algebraic core (pair/triplet cancellation) is already proved

**`RequestProject/SAWFiniteStrip.lean`**:
- Updated `strip_identity_concrete` to state `B_paper T L xc ≤ 1` (delegating to `B_paper_le_one`) instead of the false exact identity
- All downstream code (`B_TL_le_one`, etc.) continues to compile correctly

**`blueprint/src/content.tex`** (blueprint):
- Updated `thm:strip_identity_concrete` to reflect the corrected statement (`B_paper ≤ 1`), marked as `\leanok` (statement is formalized)
- Replaced `thm:paper_strip_identity` with `thm:B_paper_le_one_proof` documenting the proof strategy from the parafermionic observable
- Updated `thm:B_paper_le_one` to reference the new proof structure
- No HTML was added; all content uses standard LaTeX

### Status
- **Statement**: Correct (was false before)
- **Proof**: Sorry — requires formalizing the discrete Stokes theorem (interior mid-edge cancellation) and boundary winding evaluation. The algebraic core (pair_cancellation, triplet_cancellation) is already proved.
- **Downstream**: All files build correctly; `strip_identity_concrete` and `B_TL_le_one` delegate to `B_paper_le_one`
- **Full project build**: Successful (8061 jobs)