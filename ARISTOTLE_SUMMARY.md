# Summary of changes for run 02b44626-7e76-4453-83ec-54f25813fbab
## Hammersley-Welsh Proof Progress

I made significant structural progress on the Hammersley-Welsh bridge decomposition inequality, which is the second of two independent sorry chains in the proof that μ = √(2+√2).

### What was accomplished

**The old monolithic sorry `hw_injection_bound` has been eliminated** by decomposing it into a clean proof architecture with three smaller, well-defined lemmas.

#### New file: `RequestProject/SAWHWHalfPlane.lean`
Contains the half-plane walk machinery:
- **`hp_walk_count(W, n)`**: Counts SAWs of length n from `paperStart` staying in dc ∈ [-W, 0]
- **`hp_sum(W, N, x)`**: Finite partition function ∑_{n≤N} hp_walk_count(W,n)·x^n
- **`hp_sum_le_prod`** (PROVED): Inductive bound hp_sum(W) ≤ (1+x)·∏(1+B_T) — proved by induction on W from `hp_sum_zero_le` + `hp_sum_step`
- **`hw_injection_bound_correct`** (PROVED): Combined HW inequality ∑c_n x^n ≤ 8·(∏(1+B_T))² — proved from `hp_sum_le_prod` + `saw_sum_le_hp_sq`
- **`PaperInfStrip_width_mono`** (PROVED): PaperInfStrip monotonicity in width

#### Modified files
- **`SAWHWFinalProof.lean`**: `hw_injection_bound` now has zero sorries — it directly invokes `hw_injection_bound_correct`
- **`SAWPaperChain.lean`**: Updated to use constant 8 (vs 2); the downstream proof `hw_summable_corrected` still proves Z(x) < ∞ for x < xc

### Remaining sorries (3 in the HW chain)

1. **`hp_sum_zero_le`** (line 57): Base case — hp_sum at width 0 is ≤ 1+x. Straightforward: at dc=0, only the trivial walk and one step to (0,0,false) are possible.

2. **`hp_sum_step`** (line 69): Inductive step — hp_sum(W+1) ≤ (1+B_{W+1})·hp_sum(W). This is the core combinatorial argument: walks reaching dc -(W+1) decompose into a PaperBridge plus remaining walk. Uses existing infrastructure (`prefix_to_first_min_is_bridge`, `bridge_satisfies_paper_inf_strip`).

3. **`saw_sum_le_hp_sq`** (line 100): SAW splitting — ∑c_n x^n ≤ 2·hp_sum(N)². Split each SAW at the first vertex of minimum diagCoord into two half-plane walks.

### Key design decisions

- **Constant 8 vs 2**: The paper uses mid-edges where the width-0 strip is trivial (weight 1). Our vertex formulation has hp_sum(0) = 1+x ≤ 2, giving an extra factor of 4 = 2². Since the downstream proof only needs Z(x) < ∞ (not the exact constant), this makes no difference.

- **Raw dc constraint vs PaperInfStrip**: Using PaperInfStrip W for hp_walk_count fails because PaperInfStrip 0 is empty (kills the induction base). The raw dc ∈ [-W, 0] constraint works: at W=0, the walks at dc=0 give hp_sum(0) = 1+x, and the induction step uses bridge extraction to show width strictly decreases.

### Build status
All proof targets build successfully: `SAWFinal`, `SAWPaperChain`, `SAWHWFinalProof`.

# Summary of changes for run ee825e92-0ccc-41be-8537-935d34f2b10e
# Project Cleanup Summary

## Overview
Performed a major tidying of the connective constant project, reducing it from 147 files (~21,400 lines) to 32 files (~5,900 lines) — a 73% reduction in code size.

## What was done

### 1. Removed 115 unused files
Traced the import graph from the main proof targets (`SAWFinal.lean`, `SAWPaperChain.lean`, `SAWMainNew.lean`, `SAWHWDecompFresh.lean`) and deleted all 115 files not in any transitive import chain. These included abandoned proof attempts, duplicate approaches, superseded infrastructure, and unused conjectures.

### 2. Cleaned up remaining files
- **SAWBridge.lean** (918→313 lines): Removed `HalfPlaneWalk`, `BridgeSequence`, the sorry'd `hammersley_welsh_bound`, Section 4 conjectures, and verbose solver comment blocks.
- **SAWMain.lean** (352→50 lines): Removed all conjectures (Nienhuis, Flory exponent, SLE, bridge decay), verbose comments, and unused definitions. Kept only `connective_constant_is_limit'` and `connective_constant_pos'`.
- **SAWDecomp.lean** (475→59 lines): Stripped to just `quadratic_recurrence_lower_bound` and `not_summable_of_lower_bound` (the only externally-used results).
- **SAWBridgeFix.lean** (191→57 lines): Removed unused proofs about non-summability, vacuousness, and `bridge_endpoints_differ`.
- **SAWStripIdentityCorrect.lean** (484→413 lines): Consolidated 6 duplicate versions of `B_paper_le_one` and 5 of the strip identity into simple aliases.
- **SAWCutting.lean**: Removed the dead sorry'd `cutting_argument` (superseded by `cutting_argument_proved` in `SAWCuttingProof.lean`).
- **SAW.lean, SAWSubmult.lean, SAWHWAlgorithm.lean, SAWHWInject.lean**: Removed verbose PROBLEM/PROVIDED SOLUTION comment blocks (leftover solver logs).

### 3. Sorry status (unchanged)
Two independent root sorries remain:
1. `infinite_strip_identity` (SAWRecurrenceProof.lean) — parafermionic observable identity
2. `hw_injection_bound` (SAWHWFinalProof.lean) — Hammersley-Welsh counting inequality

One dead sorry was removed (`cutting_argument` in SAWCutting.lean).

### 4. Build verification
All proof targets build successfully: `SAWFinal`, `SAWMainNew`, `SAWHWDecompFresh`.

See `PROOF_STATUS.md` for the updated proof architecture and `ARISTOTLE_SUMMARY.md` for detailed notes.

# Project Cleanup Summary

## What was done

Major tidying of the project to reduce size and remove dead code, making it easier to focus on the remaining open problems (the two root sorries).

### Files deleted (115 files)
Removed 115 Lean files that were not transitively imported by any of the main proof targets (`SAWFinal`, `SAWPaperChain`, `SAWMainNew`, `SAWHWDecompFresh`). These included abandoned proof attempts, duplicate approaches, unused conjectures, and superseded infrastructure.

### Files cleaned (key files)
- **SAWBridge.lean**: 918 → 313 lines. Removed unused definitions (`HalfPlaneWalk`, `BridgeSequence`, `hammersley_welsh_bound` sorry), Section 4 conjectures (`sigma_is_five_eighths`, `conformal_spin_exponent`), and verbose PROBLEM/PROVIDED SOLUTION comment blocks. Fixed a `grind` proof that broke during cleanup.
- **SAWMain.lean**: 352 → 50 lines. Removed all conjectures (`nienhuis_asymptotic_conjecture`, `flory_exponent_conjecture`, etc.), verbose solver comments, and unused definitions.
- **SAWDecomp.lean**: 475 → 59 lines. Kept only the two externally-used results (`quadratic_recurrence_lower_bound`, `not_summable_of_lower_bound`), removed all unused abstract bridge decomposition infrastructure.
- **SAWBridgeFix.lean**: 191 → 57 lines. Removed unused proofs about bridge_partition being zero, the vacuousness proof, and `bridge_endpoints_differ`.
- **SAWStripIdentityCorrect.lean**: 484 → 413 lines. Consolidated 6 duplicate versions of `B_paper_le_one` and 5 duplicate versions of the strip identity into simple aliases pointing to the root sorry.
- **SAWCutting.lean**: Removed the dead sorry'd `cutting_argument` (superseded by `cutting_argument_proved` in `SAWCuttingProof.lean`).
- **SAW.lean, SAWSubmult.lean, SAWHWAlgorithm.lean, SAWHWInject.lean**: Removed verbose PROBLEM/PROVIDED SOLUTION comment blocks (leftover solver logs).

### Size reduction
- **Before**: 147 files, ~21,400 lines
- **After**: 32 files, ~5,900 lines
- **Reduction**: 73% fewer lines, 78% fewer files

### Sorry status (unchanged)
The two independent root sorries remain:
1. `infinite_strip_identity` — parafermionic observable identity for infinite strip
2. `hw_injection_bound` — Hammersley-Welsh bridge decomposition counting inequality

No new sorries were introduced. One dead sorry was removed (`cutting_argument`).

### Build verification
All three proof targets build successfully:
- `RequestProject.SAWFinal` ✓
- `RequestProject.SAWMainNew` ✓  
- `RequestProject.SAWHWDecompFresh` ✓
