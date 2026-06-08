# Proof Status: μ = √(2+√2)

## Main Theorem

```
theorem connective_constant_eq : connective_constant = Real.sqrt (2 + Real.sqrt 2)
```

**Location:** `RequestProject/SAWFinal.lean`

## Sorry Chain (Critical Path)

The main theorem has **3 remaining sorry's** on the critical path:

### 1. `pair_winding_relation` (SAWPairCancellation.lean:173)
**Corrected formulation.** States that for a pair of walks (original and loop-reversed),
the windings satisfy one of two orderings:
- EITHER: k = (fin3_other j).1, exit = .2, W_orig = W-4π/3, W_paired = W+4π/3
- OR: k = (fin3_other j).2, exit = .1, W_orig = W+4π/3, W_paired = W-4π/3

The disjunction covers both loop orientations (clockwise/counterclockwise).
This was corrected from a previous version that only stated one ordering
(which was incorrect for half the cases).

**Depends on:** The discrete turning number theorem for simple closed curves
on the hex lattice (`hex_closed_trail_turning_number` in SAWTurningNumber.lean).

**Proved helpers:**
- `pair_suffix_hex_trail` ✓ — suffix forms a hex trail list
- `pair_suffix_hex_trail_rev` ✓ — reversed suffix forms a hex trail list  
- `pair_suffix_reverse` ✓ — reversed suffix is the reverse of the suffix
- `pair_suffix_winding_neg` ✓ — reversed suffix has negated winding
- `pair_suffix_length` ✓ — suffix has length ≥ 3
- `pair_inner_loop_trail` ✓ — full support with prefix forms hex trail list
- `hexWalkWinding_split` ✓ — winding additivity at 2-vertex overlap
- `pair_indices_are_fin3_other` ✓ — k and exitIdx form fin3_other j

### 2. `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385)
The core bound B_paper(T,L,xc) ≤ 1 from Lemma 2 (strip identity). Requires:
1. Vertex relation at each interior vertex (proved as `fresh_vertex_relation`, modulo #1)
2. Discrete Stokes: summing vertex relations cancels interior mid-edges
3. Boundary evaluation: classify boundary contributions

**Equivalent sorry:** `finite_strip_identity_from_vr` (SAWStripIdentityFromVR.lean:80)
provides the same result via a different import path. Both reduce to the vertex relation + 
discrete Stokes.

### 3. `infinite_strip_identity` (SAWRecurrenceProof.lean:56)
The identity 1 = c_α·A_inf(T) + xc·B(T) for the infinite strip. Follows from
the finite strip identity by taking L→∞. Same dependency chain as #2.

### 4. `hex_closed_trail_turning_number` (SAWTurningNumber.lean:75)
**NEW.** The discrete turning number theorem for simple closed hex trails:
  hexWalkWinding L + closure = ±2π
This is the deepest unproved mathematical fact. It is the discrete analogue
of the Gauss-Bonnet theorem: a simple closed polygon has total exterior
angle ±2π.

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

### Winding Infrastructure (MOSTLY PROVED ✓)
- `hexWalkWinding_split` ✓ — winding additivity for list splitting
- `hex_turn_value` ✓ — all hex turns are ±π/3
- `hexWalkWinding_reverse_list'` ✓ — winding reversal for hex trails
- `pair_suffix_hex_trail` ✓ — suffix is a hex trail list
- `pair_suffix_hex_trail_rev` ✓ — reversed suffix is a hex trail list
- `pair_suffix_reverse` ✓ — reversed suffix = reverse of suffix
- `pair_suffix_winding_neg` ✓ — reversed suffix winding is negated
- `pair_inner_loop_trail` ✓ — full walk support is hex trail

### Algebraic Identities (FULLY PROVED ✓)
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0 ✓
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0 ✓
- `xc_inv`: xc⁻¹ = √(2+√2) ✓
- `fin3_other_pair_cancel` ✓ — pair algebraic cancellation for all j_idx
- `exp_shift_minus'`, `exp_shift_plus'` ✓ — exponential shift formulas

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
- `finite_strip_identity_from_vr` (SAWStripIdentityFromVR.lean) — equivalent to
  B_paper_le_one_strip via different import path
- `prefix_penultimate_is_neighbor` (SAWPairWindingProof.lean) — helper, not yet used
- `pair_inner_loop_trail_rev` (SAWWindingDecomp.lean) — preparation for future use

## File Organization

All files that contribute to the proof are imported transitively from `SAWFinal.lean`.
New files added:
- `SAWWindingDecomp.lean` — winding decomposition infrastructure for pairs
- `SAWTurningNumber.lean` — discrete turning number theorem (sorry'd)
