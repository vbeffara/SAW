# Summary of changes for run ed94f152-8f24-439f-8ee6-9e9da2ba7c95
## Hammersley-Welsh Formalization Progress

I made significant progress on the Hammersley-Welsh part of the proof that μ = √(2+√2), proving 18+ new lemmas and creating 4 new files of infrastructure.

### New files created

1. **`RequestProject/SAWHWLastVertex.lean`** — 6 lemmas, all proved
   - `lastDCIndex`: Definition finding the last index at a given dc value using `Finset.max'`
   - `lastDCIndex_le_length`, `lastDCIndex_dc`, `lastDCIndex_is_max`: Basic properties
   - `after_lastDCIndex_no_dc`: No vertex after the last has the same dc
   - `lastDCIndex_is_false`: The last vertex at dc=-(W+1) is FALSE (key structural lemma)
   - `suffix_after_last_narrow`: After the last dc=-(W+1) vertex, all subsequent vertices have dc ∈ [-W, 0]

2. **`RequestProject/SAWHWMinDC.lean`** — 7 lemmas, all proved
   - `minDCVal`, `firstMinDCIdx`: Definitions for minimum dc value and first index achieving it
   - `minDCVal_le`, `minDCVal_achieved`, `firstMinDCIdx_le_length`, `firstMinDCIdx_dc`: Properties
   - `minDCVal_paperStart_le`, `neg_minDCVal_le_length`: Bounds from paperStart
   - `firstMinDC_is_false`: The first min-dc vertex is FALSE when minDCVal < 0 (key for SAW decomposition)

3. **`RequestProject/SAWHWExtraProof.lean`** — 2 lemmas, all proved
   - `hp_walk_count_mono`: Wider strip allows more walks (monotonicity)
   - `hex_origin_strip_sum_le`: hexOrigin strip GF ≤ (1+x)·hp_sum

4. **`RequestProject/SAWHWSawBound.lean`** — 3 proved, 2 sorry
   - `saw_count_nonneg_dc`, `saw_count_neg_dc`: Split SAWs by dc sign
   - `saw_count_split` ✓: saw_count = nonneg + neg partition
   - `saw_nonneg_le_hex_strip` ✓: Nonneg-dc walks bounded by hex strip (via hexFlip injection)
   - `saw_neg_le_hp_conv` — SORRY: Neg-dc walks bounded by hp convolution (injection needed)
   - `saw_sum_le_hp_sq_proof` — SORRY: Depends on saw_neg_le_hp_conv

### Import restructuring
- Removed unnecessary imports from `SAWHWLastVertex.lean` to break circular dependencies
- Added `SAWHWLastVertex` import to `SAWHWStepHelpers.lean` and `SAWHWHalfPlane.lean`

### Remaining sorries in the HW chain

The 2 original HW sorries (`extra_sum_le` and `saw_sum_le_hp_sq`) have been decomposed into 2 cleaner root sorries:

1. **`extra_sum_le`** (SAWHWStepHelpers.lean): The bridge-suffix decomposition at the last dc=-(W+1) vertex. All infrastructure is in place (lastDCIndex, suffix_after_last_narrow, etc.). The remaining work is composing Walk.take/drop with hexTranslate_walk/hexFlip_walk to construct the explicit injection.

2. **`saw_neg_le_hp_conv`** (SAWHWSawBound.lean): The SAW decomposition at the first min-dc vertex. All infrastructure is in place (firstMinDCIdx, firstMinDC_is_false, etc.). The remaining work is the same: composing walk operations for the injection.

Both require constructing explicit walk decomposition injections in Lean, composing Walk.take, Walk.drop, Walk.reverse, hexTranslate_walk, and hexFlip_walk while verifying IsPath preservation and strip constraints. Each individual operation has full Lean API support; the challenge is the technical composition.

### Build status
All files compile successfully. See `PROOF_STATUS.md` for the complete proof architecture diagram.

# Summary of changes for run 16419d4e-b876-42af-b9f6-8ec6e9506312
## Hammersley-Welsh Formalization Progress

I made significant infrastructure progress toward proving the Hammersley-Welsh upper bound (μ ≤ √(2+√2)) in the connective constant proof.

### New file: `RequestProject/SAWHWStepHelpers.lean`

Created a new file with **10 proved lemmas** that reduce `hp_sum_step` to a single remaining sorry (`extra_sum_le`):

**Key results proved:**
1. `hp_walk_count_split` — Decomposes hp_walk_count(W+1, n) into walks staying in dc∈[-W,0] + "extra" walks visiting dc=-(W+1)
2. `hexOrigin_only_neighbor_in_strip` — From hexOrigin in the strip, the only valid neighbor is paperStart
3. `dropFirstHexSub` + `dropFirstHexSub_injective` — An injection from strip-constrained SAWs at hexOrigin to SAWs at paperStart, by dropping the forced first step
4. `hex_origin_strip_le_hp` — hex_origin_strip_count(W, m) ≤ hp_walk_count(W, m-1) for m ≥ 1
5. `hp_walk_count_zero` / `hp_sum_ge_one` — Base case bounds
6. `hp_sum_step_from_helpers` — hp_sum_step follows automatically from extra_sum_le

### Remaining sorries in the HW chain

The HW chain now has **2 independent remaining sorries** (reduced from 3 previously):

1. **`extra_sum_le`** (SAWHWStepHelpers.lean) — The generating function bound ∑ extra_count(W,n)·x^n ≤ 6·B_{W+1}·hp_sum(W). This is the core bridge-suffix decomposition inequality. Once proved, `hp_sum_step` follows automatically via `hp_sum_step_from_helpers`.

2. **`saw_sum_le_hp_sq`** (SAWHWHalfPlane.lean) — The SAW-to-half-plane-walk reduction ∑c_n·x^n ≤ 2·hp_sum(N)².

Both require constructing explicit walk decomposition injections in Lean — splitting walks at specific vertices, translating+flipping suffixes, and proving injectivity. The mathematical arguments are well-understood (documented in PROOF_STATUS.md and code comments), but the Lean formalization of walk manipulation (pattern matching on Walk constructors, transporting along equalities) is extremely challenging.

### Build status
All proof targets build successfully: `SAWPaperChain`, `SAWHWFinalProof`, `SAWHWStepHelpers`.

See `PROOF_STATUS.md` for the full proof architecture diagram.

# Summary of changes for run caaa36fa-ecc8-4b1b-a0a1-d8e2c7d507cd
## Hammersley-Welsh Formalization Progress

### What was accomplished

I made significant progress on the Hammersley-Welsh part of the proof that μ = √(2+√2). The HW sorry chain was restructured from 3 sorries (in the previous session) to **2 cleaner, more precisely formulated sorries**, with several important structural improvements.

#### Sorries eliminated (5 proved)
1. **`hp_walk_count_zero_ge2`** — No SAW of length ≥ 2 from paperStart stays at dc=0 (the base case structural lemma)
2. **`hp_walk_count_zero_zero_le`** — At most 1 walk of length 0 at dc=0
3. **`hp_walk_count_zero_one_le`** — At most 1 walk of length 1 at dc=0
4. **`hp_sum_zero_le`** — hp_sum at width 0 is ≤ 1+x (the full base case, proved from the above three)
5. **`paper_bridge_partition_lt_one`** — This was **discovered to be FALSE** (B₁(xc) ≈ 1.53 > 1 in the vertex formulation!) and removed

#### Proved infrastructure (no remaining sorries)
- **`hp_sum_le_prod`** — hp_sum(W) ≤ 2·∏(1+6·B_T) (product bound from inductive step)
- **`hw_injection_bound_correct`** — ∑c_n x^n ≤ 8·(∏(1+6·B_T))² (combined HW inequality)
- **`hw_injection_bound`** and **`paper_bridge_decomp_bound`** — wrappers
- **`hw_summable_corrected`** — Z(x) < ∞ for x < xc (fully proved from the product bound + bridge decay + exponential product convergence)

#### Key structural change: from (1+B) to (1+6B) form
The previous formulation used `hp_sum(W+1) ≤ (1+B)·hp_sum(W)`, which requires the suffix of a bridge-decomposed walk to be counted by `hp_walk_count(W,·)`. In the vertex formulation (as opposed to the paper's mid-edge formulation), the suffix maps to `hp_walk_count(W+1,·)` — the **same** width, not smaller — because hexFlip+translate doesn't reduce the dc range.

This led to two critical issues:
1. The self-referential bound `hp_sum(W+1) ≤ hp_sum(W) + B·hp_sum(W+1)` requires dividing by `(1-B)`, but **B_T can exceed 1** in the vertex formulation (B₁(xc) ≈ 1.53).
2. The product `∏(1-B_T)` can be negative, making the bound useless.

**Solution**: Using `hp_sum ≥ 1` (trivial walk), absorb the additive suffix constant into a multiplicative bound: `hp_sum(W+1) ≤ (1+6B)·hp_sum(W)` where the constant 6 comes from `1+3x+2x² ≤ 6` for `x ≤ 1`. The product `∏(1+6B_T)` always converges when `∑B_T < ∞`, regardless of whether individual B_T exceed 1.

### Remaining sorries (2 in the HW chain)

1. **`hp_sum_step`** (SAWHWHalfPlane.lean:121): The inductive step `hp_sum(W+1) ≤ (1+6B)·hp_sum(W)`. Requires formalizing the bridge decomposition at the last vertex of minimum dc, suffix counting via translate+hexFlip, and the convolution bound.

2. **`saw_sum_le_hp_sq`** (SAWHWHalfPlane.lean:152): The SAW-to-half-plane-walk reduction `∑c_n x^n ≤ 2·hp_sum(N)²`. Requires splitting SAWs at the vertex of minimum diagCoord into two half-plane walks.

Both are deep combinatorial arguments requiring walk decomposition, injection proofs, and counting arguments. They represent the core of the Hammersley-Welsh bridge decomposition theorem.

### Build status
All proof targets build successfully: `SAWPaperChain`, `SAWHWFinalProof`, `SAWHWHalfPlane`.

See `PROOF_STATUS.md` for the updated proof architecture diagram.

# Summary of changes for current session
## Hammersley-Welsh Infrastructure Progress

### What was accomplished

Significant infrastructure progress toward proving `hp_sum_step` and `saw_sum_le_hp_sq`, 
the two remaining Hammersley-Welsh sorries.

### New file: `RequestProject/SAWHWStepHelpers.lean`

Created a new file with 10 proved lemmas providing the infrastructure for `hp_sum_step`:

1. **`hp_walk_count_split`** ✓ — Splits hp_walk_count(W+1, n) = hp_walk_count(W, n) + extra_count(W, n)
2. **`hp_sum_split`** ✓ — Generating function version of the split
3. **`hexOrigin_only_neighbor_in_strip`** ✓ — From hexOrigin in strip, only neighbor is paperStart
4. **`walk_copy_isPath`** ✓ — Walk.copy preserves IsPath
5. **`hex_origin_strip_zero`** ✓ — hex_origin_strip_count(W, 0) = 1
6. **`dropFirstHexSub`** ✓ — Injection: SAW hexOrigin (m+1) in strip → SAW paperStart m in strip
7. **`dropFirstHexSub_injective`** ✓ — The injection is injective
8. **`hex_origin_strip_le_hp`** ✓ — hex_origin_strip_count(W, m) ≤ hp_walk_count(W, m-1)
9. **`hp_walk_count_zero`** ✓ — hp_walk_count(W, 0) = 1
10. **`hp_sum_ge_one`** ✓ — hp_sum(W, N, x) ≥ 1

Plus the key theorem:
- **`hp_sum_step_from_helpers`** ✓ — hp_sum_step follows from extra_sum_le

### What this means

The proof of `hp_sum_step` has been **reduced to a single lemma**: `extra_sum_le`.
This lemma says ∑ extra_count(W,n)·x^n ≤ 6·B_{W+1}·hp_sum(W).
Once `extra_sum_le` is proved, `hp_sum_step` follows automatically.

### Remaining sorry: `extra_sum_le`

The remaining sorry requires the bridge-suffix decomposition injection:
- Decompose each "extra walk" (visiting dc=-(W+1)) at the LAST vertex at dc=-(W+1)
- Extract bridge prefix (PaperBridge) + suffix
- Show suffix (after translate+flip) maps to hexOrigin strip walks
- Use Cauchy product inequality + suffix GF bound

The analytical components (suffix bound, Cauchy product, arithmetic) are straightforward 
given the infrastructure. The hard part is constructing the walk decomposition injection 
in Lean (finding the last vertex, splitting the walk, translating+flipping the suffix, 
and proving injectivity).
