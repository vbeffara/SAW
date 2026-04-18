# Proof Status: The connective constant of the honeycomb lattice equals √(2+√2)

## Main theorem

`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
```
μ = √(2+√2)
```

**Status: 4 sorry's remain on the critical path.**

## Critical path (dependency tree)

```
SAW.lean (constants, algebraic identities) ✓
├── SAWSubmult.lean (submultiplicativity: c_{n+m} ≤ c_n·c_m) ✓
│   └── SAWMain.lean (Fekete's lemma → connective constant is a limit) ✓
│       └── SAWBridge.lean (partition function, connective_constant_eq_from_bounds) ✓
│           └── SAWBridgeFix.lean (OriginBridge definition, corrections) ✓
│               └── SAWStripIdentityCorrect.lean (Paper strip domain, partition functions)
│                   ├── strip_identity_genuine ⚠️ [sorry — Lemma 2, parafermionic observable]
│                   └── B_paper_le_one_obs ✓ [proved FROM strip_identity_genuine]
│                       └── SAWDiagProof.lean (Paper bridge infrastructure) ✓
│                           └── SAWPaperChain.lean (main theorem assembly)
│                               ├── paper_bridge_recurrence ⚠️ [sorry — recurrence]
│                               ├── paper_bridge_decomp_injection ⚠️ [sorry — HW decomposition]
│                               ├── paper_bridge_lower_bound ✓ (from recurrence)
│                               ├── hw_summable_corrected ✓ (from decomposition + decay)
│                               ├── Z_xc_diverges_corrected ✓ (from lower bound)
│                               └── connective_constant_eq_corrected ✓ (from above)
├── SAWCutting.lean (cutting argument infrastructure)
│   ├── PaperInfStrip_mono ✓
│   ├── PaperSAW_A_inf_widen ✓
│   ├── PaperSAW_A_inf_widen_injective ✓
│   ├── A_inf_diff_reaches_boundary ✓
│   └── cutting_argument ⚠️ [sorry — depends on extra_walk_sum_le]
├── SAWCuttingProof.lean [Cutting argument decomposition]
│   ├── embed_in_strip ✓
│   ├── embed_in_strip_injective ✓
│   ├── A_inf_summable_of_succ ✓
│   ├── in_strip_sum_le ✓
│   ├── extra_walk_decomp ✓
│   ├── extra_walk_sum_le ⚠️ [sorry — requires cutting map injectivity]
│   └── cutting_argument_proved ✓ [reduces to in_strip_sum_le + extra_walk_sum_le]
├── SAWParafermionic.lean [NEW — Walk reconstruction infrastructure]
│   ├── path_determined_by_parts ✓ [walk = takeUntil ++ dropUntil]
│   ├── walk_reverse_injective ✓ [reverse is injective]
│   ├── shiftWalk_injective_walks ✓ [shift is injective on walks]
│   ├── extraWalkCutData, extraWalkB1, extraWalkB2 ✓ [cutting map defined]
│   ├── extraWalk_length_rel ✓ [s.len = b1.len + b2.len]
│   └── extra_walk_sum_le_proved ⚠️ [sorry — needs injection proof]
├── SAWCuttingHelpers.lean [all proved]
│   ├── prefix_gives_bridge ✓
│   ├── suffix_reversed_shifted_gives_bridge ✓
│   ├── hexShift_preserves_strip ✓
│   └── walk_split_lengths ✓
└── SAWVertexTriple.lean [Vertex relation triplet structure, all proved]
```

## Remaining critical-path sorries

### 1. `strip_identity_genuine` (SAWStripIdentityCorrect.lean)
**Statement:** ∃ A E ≥ 0, 1 = c_α·A + B_paper T L xc + c_ε·E
**Equivalent to:** B_paper(T, L, xc) ≤ 1
**Status:** Requires full parafermionic observable proof (Lemma 2 of the paper).
**Proved infrastructure:**
- pair_cancellation and triplet_cancellation ✓ (algebraic core)
- boundary_weight_re_nonneg ✓ (boundary weights have non-negative Re)
- false_directions ✓ (direction vectors = cube roots of unity)
- false_to_true_dir ✓ (right boundary direction = +1)
- starting_direction ✓ (starting direction = -1)
- cos_five_pi_eight ✓ (cos(5π/8) = -c_α)
**Remaining:** Combinatorial partition of walks into pairs/triplets at each vertex + discrete Stokes summation.

### 2. `extra_walk_sum_le` / `extra_walk_sum_le_proved` (SAWCuttingProof/SAWParafermionic.lean)
**Statement:** For F ⊆ {extra walks}, Σ xc^{|s|+1} ≤ xc · B(T+1)²
**Status:** Requires proving injectivity of the cutting map s ↦ (b1(s), b2(s)).
**Proved infrastructure (this session):**
- path_determined_by_parts ✓ (walk = takeUntil ++ dropUntil)
- walk_reverse_injective ✓ (reverse is injective)
- shiftWalk_injective_walks ✓ (shift is injective)
- extraWalkCutData, extraWalkB1, extraWalkB2 ✓ (cutting map defined)
- extraWalk_length_rel ✓ (s.len = b1.len + b2.len)
**Remaining:** Injectivity of (extraWalkB1, extraWalkB2) and tsum comparison.

### 3. `paper_bridge_recurrence` (SAWPaperChain.lean)
**Statement:** ∃ α > 0, ∀ T, B_T ≤ α·B_{T+1}² + B_{T+1}
**Depends on:** strip_identity_genuine (#1) + cutting_argument (depends on #2)
**Infrastructure:** bridge_recurrence_from_cutting ✓ derives the recurrence
from the cutting argument and strip identity as explicit hypotheses.

### 4. `paper_bridge_decomp_injection` (SAWPaperChain.lean)
**Statement:** ∑_{n≤N} c_n·x^n ≤ 2·(∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}(x))²
**Independent of:** sorries #1, #2, #3.
**Status:** Requires Hammersley-Welsh bridge decomposition algorithm.

## New work this session

### New file: SAWParafermionic.lean
Walk reconstruction infrastructure for the cutting map:
- `path_determined_by_parts` ✓ — A path is determined by its takeUntil and dropUntil at any support vertex
- `walk_reverse_injective` ✓ — Walk reversal is injective
- `shiftWalk_injective_walks` ✓ — Walk shifting is injective
- `extraWalkCutData` ✓ — Extract cut vertex from extra walk
- `extraWalkB1` ✓ — Prefix bridge from cutting
- `extraWalkB2` ✓ — Suffix bridge from cutting
- `extraWalk_length_rel` ✓ — Length relation: s.len = b1.len + b2.len
- `extra_walk_sum_le_proved` ⚠️ — Needs injection + tsum comparison
