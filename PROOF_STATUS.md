# Proof Status: μ = √(2+√2)

## Main Theorem

```
theorem connective_constant_eq : connective_constant = Real.sqrt (2 + Real.sqrt 2)
```

**Location:** `RequestProject/SAWFinal.lean`

## Sorry Chain (Critical Path)

The main theorem has **3 remaining sorry's** on the critical path, all related to the
parafermionic observable argument:

### 1. `pair_winding_relation` (SAWPairCancellation.lean:167)
**The deepest sorry.** States that for a pair of walks (original and loop-reversed),
the windings satisfy:
- γ.winding = W_common - 4π/3
- (pairInvol γ).winding = W_common + 4π/3

This is the discrete turning number argument: reversing the inner loop of a pair on the
hex lattice changes the winding by ±8π/3. All downstream sorry's depend transitively on
this one through the vertex relation.

**Helper lemmas proved in SAWPairWindingProof.lean:**
- `pair_indices_are_fin3_other` ✓ — k and exitIdx form fin3_other j
- `original_fullSupport_eq` ✓ — structure of original walk's full support
- `paired_fullSupport_eq` ✓ — structure of paired walk's full support

**What remains:** The winding decomposition and turning number computation.

### 2. `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385)
The core bound B_paper(T,L,xc) ≤ 1 from Lemma 2 (strip identity). Requires:
1. Vertex relation at each interior vertex (proved as `fresh_vertex_relation`, modulo #1)
2. Discrete Stokes: summing vertex relations cancels interior mid-edges
3. Boundary evaluation: classify boundary contributions

**Equivalent sorry:** `finite_strip_identity_from_vr` (SAWStripIdentityFromVR.lean:80)
provides the same result via a different import path. Both reduce to the vertex relation + 
discrete Stokes.

### 3. `infinite_strip_identity` (SAWRecurrenceProof.lean:49)
The identity 1 = c_α·A_inf(T) + xc·B(T) for the infinite strip. Follows from
the finite strip identity by taking L→∞. Same dependency chain as #2.

## Proved Components

### Hammersley-Welsh Decomposition (FULLY PROVED ✓)
All SAWHW*.lean files are sorry-free:
- `hw_injection_bound` — SAW count ≤ 8 · (∏(1+12·B_T))²
- Bridge decomposition algorithm and injection
- Extra walk bounds and fiber counting

### Vertex Relation / Lemma 1 (PROVED modulo pair_winding_relation)
- `fresh_vertex_relation` (SAWPairInvolutionProof.lean) ✓ (modulo #1)
- Triplet cancellation: `freshVertexSum_triplet_part_zero` ✓
- Pair cancellation: `freshVertexSum_pair_part_zero_proved` ✓ (modulo #1)
- Pair involution: `pairSigmaInvol_injective` ✓
- Extension maps: `freshExtensionMap_injective`, `fresh_outgoing_surj` ✓

### Algebraic Identities (FULLY PROVED ✓)
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0 ✓
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0 ✓
- `xc_inv`: xc⁻¹ = √(2+√2) ✓

### Bridge Recurrence (PROVED modulo infinite_strip_identity)
- `bridge_recurrence_proved`: B(T) ≤ c_α·B(T+1)² + B(T+1) ✓ (modulo #3)
- `cutting_argument_proved`: A(T+1) - A(T) ≤ xc·B(T+1)² ✓

### Connective Constant Infrastructure (FULLY PROVED ✓)
- `saw_count_submult'`: c_{n+m} ≤ c_n · c_m ✓
- `connective_constant_is_limit'`: μ = lim c_n^{1/n} ✓
- `connective_constant_eq_from_bounds`: Z diverges + Z converges → μ = √(2+√2) ✓

## Dead Branches (NOT on critical path)

These sorry's exist in the codebase but are NOT needed for the main theorem:
- `trail_vertex_relation` (SAWCancellationIdentity.lean) — superseded by fresh version
- `triplet_part_zero` / `pair_part_zero` (SAWTrailVertexRelation.lean) — non-fresh version
- `strip_observable_summable` (SAWStripObservable.lean) — not needed
- `hex_simple_closed_trail_winding` (SAWWindingDiff.lean) — general turning number
  (would imply pair_winding_relation but is more general than needed)

## File Organization

All files that contribute to the proof are imported transitively from `SAWFinal.lean`.
The import structure is documented in `SAWFinal.lean`'s header comment.
