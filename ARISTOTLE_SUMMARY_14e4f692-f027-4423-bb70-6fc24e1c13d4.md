# Summary of changes
## Work on `strip_identity_concrete`

### Analysis and findings

Through careful analysis of the hexagonal lattice structure, the paper's geometry, and the Lean formalization, I identified three fundamental issues with the `strip_identity_concrete` theorem in `SAWFiniteStrip.lean`:

1. **Boundary overlap**: The partition functions `StripSAW_A`, `StripSAW_B`, `StripSAW_E` use vertex-based classification that is non-disjoint (a walk can be counted in multiple categories).

2. **Starting point mismatch**: The walks start from `hexOrigin = (0,0,false)`, but in the paper's correct honeycomb embedding, `hexOrigin` is in the **interior** of the strip domain (not on the boundary). The paper's strip identity requires the starting mid-edge `a` to be on the left boundary, which means the walk should start from `(0,0,true)` — the interior endpoint of mid-edge `a`.

3. **Domain mismatch**: The `FiniteStrip` domain uses `0 ≤ v.1 ≤ T`, which does not correspond to the paper's strip defined by `0 ≤ Re(z) ≤ (3T+1)/2`. In the correct honeycomb embedding, the Re coordinate depends on `x + y` (not just `x`), so the paper's domain has different constraints for the two sublattices.

The "1" in the identity `1 = c_α·A + B + c_ε·E` comes from `F(a) = 1` at the starting mid-edge, which only works when `a` is on the boundary. With `hexOrigin` interior, this term cancels in the telescopic summation, making the stated identity false.

### New file created

**`RequestProject/SAWStripIdentityCorrect.lean`** — Contains:

- **`PaperInfStrip T`** and **`PaperFinStrip T L`**: The paper-compatible strip domain, defined using `x + y` constraints that match the paper's `Re` condition:
  - FALSE(x,y): `-T ≤ x+y ≤ -1`  
  - TRUE(x,y): `-T ≤ x+y ≤ 0`

- **`paperStart := (0, 0, true)`**: The correct starting vertex (interior endpoint of mid-edge `a`).

- Verified that `hexOrigin` is **outside** the paper strip (`hexOrigin_not_in_strip`) and `paperStart` is **inside** (`paperStart_in_fin_strip`).

- **`PaperSAW_A`**, **`PaperSAW_B`**, **`PaperSAW_E`**: Corrected partition function structures using the paper's boundary classification (left boundary at `x+y = 0`, right boundary at `x+y = -T`).

- **`paper_strip_identity`** (sorry): The corrected strip identity `1 = c_α·A_paper + B_paper + c_ε·E_paper`, with a detailed proof sketch referencing pair/triplet cancellation, telescopic cancellation, and boundary winding analysis.

- **`B_paper_le_one`** (proved): The consequence `B_paper T L xc ≤ 1`, proved from the strip identity using non-negativity of A and E and positivity of c_α, c_ε.

- **`paper_fin_strip_finite`** (proved): Finiteness of the paper strip vertex set.

- **`paper_B_summable`** (proved): Summability of the B partition function (since there are finitely many SAWs in a finite strip).

The file compiles with exactly 1 sorry: the `paper_strip_identity` theorem itself.

### Blueprint updates

Updated `blueprint/src/content.tex`:
- Shortened the `thm:strip_identity_concrete` entry to note that the statement is incorrect and refer to the corrected version.
- Added `thm:paper_strip_identity`: the corrected strip identity with full description of the paper-compatible domain, boundary classification, and proof sketch.
- Added `thm:B_paper_le_one` with `\leanok` tags (proved from the strip identity).

No HTML was added to the blueprint.