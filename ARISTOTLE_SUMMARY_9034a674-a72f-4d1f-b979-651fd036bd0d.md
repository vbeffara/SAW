# Summary of changes
## Work on `strip_identity_concrete`

### Key finding: the current statement is **false**

Through careful analysis of the hexagonal lattice adjacency structure (`hexGraph`), I discovered that `strip_identity_concrete` as stated cannot be proved because the statement is incorrect. The issues are:

1. **Overlapping boundary types**: `StripSAW_A` (walks with endpoint x=0) and `StripSAW_E` (walks with |2y-x|=2L) overlap at corner vertices. For example, with T=1, L=1, the walk `hexOrigin → (0,1,true)` satisfies both conditions. This causes the sum `c_alpha * A_TL + B_TL + c_eps * E_TL` to double-count walks at corners.

2. **Incorrect sublattice classification**: `StripSAW_B` counts walks ending at ANY vertex with x=T, including true-sublattice vertices. But in `hexGraph`, `TRUE(T,y)` has neighbors `FALSE(T,y)`, `FALSE(T-1,y)`, `FALSE(T,y-1)` — none with x > T. So true vertices at x=T have no right-boundary mid-edge and are **interior** vertices. Only `FALSE(T,y)` has neighbor `TRUE(T+1,y)` outside the strip, creating a right-boundary mid-edge. The paper's B should only count walks to FALSE vertices at x=T. Similarly, left-boundary mid-edges connect `TRUE(0,y)` to `FALSE(-1,y)`, so the paper's A should only count walks to TRUE vertices at x=0.

3. **Weight discrepancy**: The paper's partition functions count walks from mid-edge a (between hexOrigin and (0,0,true)), weighting by x^ℓ where ℓ = number of vertices visited. The Lean SAWs start at vertex hexOrigin, weighting by x^n where n = number of edges. The paper counts walks in both directions from a, while Lean only counts walks from hexOrigin.

### Changes made

**`RequestProject/SAWFiniteStrip.lean`**:
- Added extensive documentation (in a section comment) explaining why the identity is false, with the three issues described above.
- Commented out the false statement (preserved in a block comment for reference).
- Added corrected structure definitions `StripSAW_A'` (TRUE vertices at x=0) and `StripSAW_B'` (FALSE vertices at x=T) with proper sublattice conditions.
- Added corresponding partition functions `A_TL'` and `B_TL'`.
- Kept the active `strip_identity_concrete` as sorry (unchanged from before) because downstream code (`B_TL_le_one`, `origin_bridge_partial_sum_le_one`, etc.) depends on it. These downstream results are also affected by the incorrect statement.

**`blueprint/src/content.tex`**:
- Updated the `thm:strip_identity_concrete` entry to document the incorrectness, explaining the overlapping boundaries, incorrect sublattice classification, and the correct boundary mid-edge analysis. No HTML was added.

### What's needed to complete the formalization

A correct strip identity proof requires:
1. Fixing the partition function definitions to match the paper's mid-edge-based boundary classification (using the corrected `StripSAW_A'`, `StripSAW_B'`, plus a corrected escape type).
2. Handling the weight convention (mid-edge walks vs vertex walks), likely by defining walks from both endpoints of mid-edge a.
3. Formalizing the parafermionic observable summing argument (vertex relation + telescopic cancellation + boundary winding computation).
4. Updating downstream theorems (`B_TL_le_one`, etc.) to use the corrected definitions.