# Proof Status: μ = √(2+√2)

## Main Theorem

```
theorem connective_constant_eq : connective_constant = Real.sqrt (2 + Real.sqrt 2)
```

**Location:** `RequestProject/SAWFinal.lean`

## Critical Path — Two Independent Sorry Chains

### Chain A: Vertex Relation → Strip Identity → Z(x) < ∞

**Root cause:** `hex_closed_trail_turning_number` (SAWTurningNumber.lean:92)

The discrete Gauss-Bonnet theorem for simple closed hex trails:
for a simple closed trail L on the hex lattice, hexWalkWinding L + closure = ±2π.

This is the discrete analogue of the turning tangent theorem (Umlaufsatz):
a simple closed polygon has total exterior angle ±2π.

**Full chain:**
```
hex_closed_trail_turning_number (SORRY — root cause)
  → pair_winding_relation (SORRY — needs turning number)
    → pair_exp_cancellation (PROVED)
      → pair_contrib_cancels (PROVED)
        → freshVertexSum_pair_part_zero_proved (PROVED)
          → fresh_vertex_relation (PROVED) [= Lemma 1]
            → finite_strip_identity_from_vr (SORRY — needs discrete Stokes)
              → B_paper_le_one_from_vr (PROVED)
                → paper_bridge_partial_sum_shifted_le (PROVED, in SAWDiagProof)
                  → paper_bridge_partial_sum_le (PROVED)
                    → bridge_decay → HW bound
                      → hw_summable_corrected [Z(x) < ∞ for x < xc]
```

### Chain B: Infinite Strip Identity → Z(xc) = ∞

**Root cause:** `infinite_strip_identity` (SAWRecurrenceProof.lean:56)

The identity 1 = c_α·A_inf + xc·B for the infinite strip. This is the
L→∞ limit of the finite strip identity (Chain A).

```
infinite_strip_identity (SORRY)
  → bridge_recurrence_proved (PROVED)
    → Z_xc_diverges_corrected [Z(xc) = ∞]
```

**Note:** Chains A and B could potentially be unified by deriving
`infinite_strip_identity` from `finite_strip_identity_from_vr` via
a monotone convergence argument (L→∞).

## All Sorry Locations (12 total)

### Critical path (4 sorry's):
1. `hex_closed_trail_turning_number` (SAWTurningNumber.lean:92) — **ROOT CAUSE A**
2. `pair_winding_relation` (SAWPairCancellation.lean:173) — needs #1
3. `finite_strip_identity_from_vr` (SAWStripIdentityFromVR.lean:84) — needs vertex relation + discrete Stokes
4. `infinite_strip_identity` (SAWRecurrenceProof.lean:56) — **ROOT CAUSE B** (limit of #3)

### Preparation for future use (2 sorry's):
5. `prefix_penultimate_is_neighbor` (SAWPairWindingProof.lean:43) — helper for #2
6. `pair_inner_loop_trail_rev` (SAWWindingDecomp.lean:91) — helper for winding decomposition

### Dead branches (6 sorry's, NOT on critical path):
7. `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385) — **SUPERSEDED** by
   B_paper_le_one_from_vr (SAWStripIdentityFromVR.lean). The main theorem now
   goes through the vertex relation chain instead.
8. `trail_vertex_relation` (SAWCancellationIdentity.lean:305) — superseded by fresh version
9. `strip_observable_summable` (SAWStripObservable.lean:173) — not needed
10. `triplet_part_zero` (SAWTrailVertexRelation.lean:274) — superseded
11. `pair_part_zero` (SAWTrailVertexRelation.lean:282) — superseded
12. `hex_simple_closed_trail_winding` (SAWWindingDiff.lean:72) — general turning number

## Refactored Import Architecture

**Key change:** SAWDiagProof now imports SAWStripIdentityFromVR, connecting
the vertex relation chain to the bridge partition bounds. This eliminates
`B_paper_le_one_strip` from the critical path.

```
SAWStripIdentityFromVR (vertex relation → finite strip identity → B ≤ 1)
  ↓ imported by
SAWDiagProof (uses B_paper_le_one_from_vr instead of B_paper_le_one_strip)
  ↓ imported by
SAWPaperChain (main theorem assembly)
```

SAWStripIdentityFromVR does NOT import SAWDiagProof (avoiding circular dependency).

## Fully Proved Components

### Hammersley-Welsh Decomposition (FULLY PROVED ✓)
All SAWHW*.lean files are sorry-free:
- `hw_injection_bound` — SAW count ≤ 8 · (∏(1+12·B_T))²
- Bridge decomposition algorithm and injection
- Extra walk bounds and fiber counting

### Algebraic Identities (FULLY PROVED ✓)
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0 ✓
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0 ✓
- `xc_inv`: xc⁻¹ = √(2+√2) ✓
- `fin3_other_pair_cancel` ✓
- `exp_shift_minus'`, `exp_shift_plus'` ✓

### Vertex Relation / Lemma 1 (PROVED modulo pair_winding_relation)
- `fresh_vertex_relation` (SAWPairInvolutionProof.lean) ✓
- Triplet cancellation: `freshVertexSum_triplet_part_zero` ✓
- Pair cancellation: `freshVertexSum_pair_part_zero_proved` ✓
- Pair involution: `pairSigmaInvol_injective` ✓
- Extension maps: `freshExtensionMap_injective`, `fresh_outgoing_surj` ✓

### Winding Infrastructure (MOSTLY PROVED ✓)
- `hexWalkWinding_split` ✓ — winding additivity
- `hex_turn_value` ✓ — all hex turns are ±π/3
- `hex_edge_norm_one` ✓ — all hex edges have unit length
- `hexWalkWinding_reverse_list'` ✓ — winding reversal
- `pair_suffix_hex_trail` ✓
- `pair_suffix_winding_neg` ✓

### Bridge Recurrence (PROVED modulo infinite_strip_identity)
- `bridge_recurrence_proved`: B(T) ≤ c_α·B(T+1)² + B(T+1) ✓
- `cutting_argument_proved`: A(T+1) - A(T) ≤ xc·B(T+1)² ✓

### Connective Constant Infrastructure (FULLY PROVED ✓)
- `saw_count_submult'`: c_{n+m} ≤ c_n · c_m ✓
- `connective_constant_is_limit'`: μ = lim c_n^{1/n} ✓
- `connective_constant_eq_from_bounds`: Z diverges + Z converges → μ = √(2+√2) ✓

## File Organization

All files that contribute to the proof are imported transitively from `SAWFinal.lean`.

### Key file groups:
- **Core:** SAW.lean, SAWSubmult.lean, SAWMain.lean
- **Bridges:** SAWBridge.lean, SAWBridgeFix.lean, SAWDiagBridge.lean, SAWDiagConnection.lean, SAWDiagProof.lean
- **Strip identity:** SAWStripIdentityCorrect.lean, SAWStripIdentityFromVR.lean
- **Parafermionic observable:** SAWObservable.lean, SAWObservableDef.lean, SAWObservableFormal.lean
- **Vertex relation:** SAWPathVertexRelation.lean, SAWVertexRelationProof.lean, SAWCancellationProved.lean
- **Pair involution:** SAWPairInvolution.lean, SAWPairInvolutionHelpers.lean, SAWPairInvolutionProof.lean
- **Pair cancellation:** SAWPairCancellation.lean, SAWPairWinding.lean, SAWPairWindingProof.lean
- **Winding:** SAWWindingGeneral.lean, SAWWindingLemma.lean, SAWWindingReverse.lean, SAWWindingDecomp.lean, SAWWindingDiff.lean
- **Turning number:** SAWTurningNumber.lean
- **Discrete Stokes:** SAWDiscreteStokes.lean, SAWStokesAbstract.lean, SAWStripAlgebra.lean
- **HW decomposition:** SAWHW*.lean (15+ files, all sorry-free)
- **Recurrence:** SAWRecurrenceProof.lean, SAWCuttingProof.lean, SAWCutting.lean
- **Final assembly:** SAWPaperChain.lean, SAWMainNew.lean, SAWFinal.lean

### Preparation files (linked but not on critical path):
- `SAWWindingDecomp.lean` — pair_inner_loop_trail_rev (preparation for pair_winding_relation)
- `SAWPairWindingProof.lean` — prefix_penultimate_is_neighbor (preparation for pair_winding_relation)
- `SAWPairWindingRelation.lean` — alternative pair cancellation via winding
- `SAWObservableSum.lean` — observable as formal sum over trails
- `SAWStripAlgebra.lean` — algebraic identities for strip boundary evaluation
- `SAWDiscreteStokes.lean` — Abstract discrete Stokes framework
- `SAWStokesAbstract.lean` — Abstract combinatorial Stokes lemma
