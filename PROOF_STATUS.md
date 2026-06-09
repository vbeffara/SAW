# Proof Status: μ = √(2+√2)

## Main Theorem

```
theorem connective_constant_eq : connective_constant = Real.sqrt (2 + Real.sqrt 2)
```

**Location:** `RequestProject/SAWFinal.lean`

## Critical Path — Two Independent Sorry Chains

### Chain A: Vertex Relation → Strip Identity → Z(x) < ∞

**Root cause:** `hex_closed_trail_turning_number` (SAWTurningNumber.lean:74)

The discrete Gauss-Bonnet theorem for simple closed hex trails:
for a simple closed trail L on the hex lattice, hexWalkWinding L + closure = ±2π.

This is the discrete analogue of the Umlaufsatz (Hopf's turning tangent theorem):
a simple closed polygon has total exterior angle ±2π. This result is not
currently available in Mathlib and is a deep topological fact equivalent
in difficulty to the Jordan curve theorem for polygons.

**Full chain:**
```
hex_closed_trail_turning_number (SORRY — root cause, Umlaufsatz)
  → pair_winding_relation (SORRY — needs turning number + orientation)
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

## All Sorry Locations (10 total, down from 12)

### Critical path (4 sorry's):
1. `hex_closed_trail_turning_number` (SAWTurningNumber.lean:74) — **ROOT CAUSE A**
   The discrete Umlaufsatz for hex lattice polygons. Requires proving that
   a simple closed polygon has turning number ±1.
2. `pair_winding_relation` (SAWPairCancellation.lean:173) — needs #1 + orientation
   Also needs the correct SIGN of the turning number (determined by planarity
   of the hex lattice embedding).
3. `finite_strip_identity_from_vr` (SAWStripIdentityFromVR.lean:84) — discrete Stokes
   Requires formalizing the summation of the vertex relation over all vertices,
   cancellation of interior mid-edges, and boundary evaluation.
4. `infinite_strip_identity` (SAWRecurrenceProof.lean:56) — **ROOT CAUSE B**
   L→∞ limit of #3, or direct vertex relation argument on infinite strip.

### Dead branches (6 sorry's, NOT on critical path):
5. `trail_vertex_relation` (SAWCancellationIdentity.lean:305) — superseded by fresh version
6. `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385) — **SUPERSEDED** by
   B_paper_le_one_from_vr (SAWStripIdentityFromVR.lean)
7. `strip_observable_summable` (SAWStripObservable.lean:173) — not needed
8. `triplet_part_zero` (SAWTrailVertexRelation.lean:274) — superseded
9. `pair_part_zero` (SAWTrailVertexRelation.lean:282) — superseded
10. `hex_simple_closed_trail_winding` (SAWWindingDiff.lean:72) — alternative turning number

### Recently proved (previously sorry):
- `prefix_penultimate_is_neighbor` (SAWPairWindingProof.lean) — ✓ PROVED
  The penultimate vertex of the prefix is a neighbor of v, distinct from
  both k and exitIdx. Key preparation for pair_winding_relation.
- `pair_inner_loop_trail_rev` (SAWWindingDecomp.lean) — ✓ PROVED
  The reversed inner loop forms a hex trail list. Uses the fact that
  pairInvol constructs a valid trail walk.

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
- `strip_algebraic_identity`: 2·c_α·xc³ + 3·xc² = 1 ✓
- `fin3_other_pair_cancel` ✓
- `exp_shift_minus'`, `exp_shift_plus'` ✓

### Vertex Relation / Lemma 1 (PROVED modulo pair_winding_relation)
- `fresh_vertex_relation` (SAWPairInvolutionProof.lean) ✓
- Triplet cancellation: `freshVertexSum_triplet_part_zero` ✓
- Pair cancellation: `freshVertexSum_pair_part_zero_proved` ✓
- Pair involution: `pairSigmaInvol_injective` ✓
- Extension maps: `freshExtensionMap_injective`, `fresh_outgoing_surj` ✓

### Winding Infrastructure (FULLY PROVED ✓)
- `hexWalkWinding_split` ✓ — winding additivity
- `hex_turn_value` ✓ — all hex turns are ±π/3
- `hex_edge_norm_one` ✓ — all hex edges have unit length
- `hexWalkWinding_reverse_list'` ✓ — winding reversal
- `pair_suffix_hex_trail` ✓
- `pair_suffix_winding_neg` ✓
- `prefix_penultimate_is_neighbor` ✓ — **NEWLY PROVED**
- `pair_inner_loop_trail_rev` ✓ — **NEWLY PROVED**

### Bridge Recurrence (PROVED modulo infinite_strip_identity)
- `bridge_recurrence_proved`: B(T) ≤ c_α·B(T+1)² + B(T+1) ✓
- `cutting_argument_proved`: A(T+1) - A(T) ≤ xc·B(T+1)² ✓

### Connective Constant Infrastructure (FULLY PROVED ✓)
- `saw_count_submult'`: c_{n+m} ≤ c_n · c_m ✓
- `connective_constant_is_limit'`: μ = lim c_n^{1/n} ✓
- `connective_constant_eq_from_bounds`: Z diverges + Z converges → μ = √(2+√2) ✓

## Why the Remaining Sorry's Are Hard

### hex_closed_trail_turning_number (Umlaufsatz)
This is equivalent to proving that a simple closed polygon in the plane
has total exterior angle ±2π. This is a fundamental theorem in discrete
differential geometry (Hopf's Umlaufsatz, 1935) that requires either:
- The Jordan curve theorem (not in Mathlib)
- A constructive ear-clipping argument (complex on hex lattice: girth 6)
- A signed area / winding number argument (requires JCT for polygons)
None of these foundational results are currently in Mathlib.

### pair_winding_relation (Turning Number + Orientation)
Beyond the turning number theorem, this requires determining the SIGN
of the turning (CW vs CCW). The sign is determined by the planarity of
the hex lattice embedding and the CCW ordering of neighbors (d₁ = j·d₀
with j = exp(2πi/3)). Formalizing this planarity argument is non-trivial.

### finite_strip_identity_from_vr (Discrete Stokes)
This requires formalizing the full discrete Stokes argument:
1. Define interior/boundary vertices of the strip
2. Show vertex relation at each interior vertex (done: vertex_relation_at_interior)
3. Show interior mid-edges cancel (need edge-pairing infrastructure)
4. Evaluate boundary contributions (winding at each boundary type)
Each step is conceptually simple but requires substantial bookkeeping.

### infinite_strip_identity (Limit)
Can be derived from finite_strip_identity_from_vr by taking L→∞, but
this requires monotone convergence of A_paper, B_paper in L, and showing
the E term vanishes. Alternatively, a direct vertex relation argument
on the infinite strip, which has similar complexity to #3.

## File Organization

All files that contribute to the proof are imported transitively from `SAWFinal.lean`.
The project builds successfully with `lake build`.
