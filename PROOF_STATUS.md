# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 root sorries** (both are instances of the same
mathematical argument — the parafermionic observable / discrete Stokes theorem).

## Root Sorries

### Sorry #1: `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean)
**Statement:** `B_paper T L xc ≤ 1` for T ≥ 1, L ≥ 1.

This says the bridge partition function in the finite strip is bounded by 1.
It follows from Lemma 2 of Duminil-Copin & Smirnov (2012): the identity
`1 = c_α · A + B + c_ε · E` with A, E ≥ 0 implies B ≤ 1.

**Required for:** The Hammersley-Welsh upper bound (via `paper_bridge_partial_sum_le`
→ `paper_bridge_decay` → `hw_summable_corrected`), and the cutting argument
(via `bridge_pair_summable` → `extra_walk_sum_le_proved` → `cutting_argument_proved`).

### Sorry #2: `infinite_strip_identity` (SAWRecurrenceProof.lean)
**Statement:** `1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc`

The parafermionic observable identity for the infinite strip.
This is the infinite-L limit of the finite strip identity.

**Required for:** The bridge recurrence (Z(xc) = ∞, the lower bound μ ≥ √(2+√2)).

### Relationship between the two sorries

Both are consequences of the **same** mathematical result: Lemma 2 of
Duminil-Copin & Smirnov 2012 (the discrete Stokes / parafermionic
observable argument). Specifically:

1. The **finite strip identity** (`strip_boundary_identity`):
   `1 = c_α · A_{T,L} + B_{T,L} + c_ε · E_{T,L}` for the strip S_{T,L}.
   This directly implies Sorry #1 (`B_paper_le_one_strip`).

2. Taking L → ∞ and assuming E → 0 gives the **infinite strip identity**
   (Sorry #2: `infinite_strip_identity`).

Both require the same proof mechanism: the vertex relation
(pair_cancellation + triplet_cancellation applied to walk groupings)
plus discrete Stokes (interior mid-edge cancellation).

## What needs to be formalized to eliminate both sorries

### Already proved (algebraic ingredients)
- `pair_cancellation`: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
- `triplet_cancellation`: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0
- `boundary_cos_pos`: cos(3θ/8) > 0 for |θ| ≤ π
- `c_alpha_pos`, `c_eps_pos`, `xc_pos`
- Direction computations: `false_to_true_dir`, `starting_direction`, etc.

### Remaining formalization (combinatorial + analytic)

1. **Walk pairing/tripling at each vertex**: At each vertex v of the strip,
   walks ending at mid-edges adjacent to v can be partitioned into:
   - Pairs: walks visiting all three mid-edges of v (cancel by `pair_cancellation`)
   - Triplets: walk visiting one mid-edge + two extensions (cancel by `triplet_cancellation`)
   This partition must be shown exhaustive.

2. **Discrete Stokes theorem**: Summing the vertex relation over all vertices,
   interior mid-edges cancel (each appears twice with opposite signs).
   Only boundary mid-edges survive.

3. **Winding telescoping**: The winding W of a walk equals θ_final - θ_initial,
   where θ is the edge direction angle. Since θ_initial = 0, W = θ_final.

4. **Boundary evaluation**: For each boundary type:
   - Starting mid-edge: contributes -1 (trivial walk, direction -1)
   - Right boundary: contributes B (winding 0, coefficient 1)
   - Left boundary: contributes c_α · A (winding π, cos(3π/8))
   - Escape boundary: contributes c_ε · E (winding ±2π/3, cos(π/4))

5. **Limiting argument** (for Sorry #2 only): Taking L → ∞ in the finite
   strip identity, using monotonicity and boundedness of A, B, E.

## Proof Architecture

### Hammersley-Welsh chain (upper bound μ ≤ √(2+√2))
```
B_paper_le_one_strip (sorry #1)
  → paper_bridge_partial_sum_le
    → paper_bridge_decay, bridge_summable
      → hw_summable_corrected (Z(x) < ∞ for x < xc)
```
Also feeds the cutting argument:
```
B_paper_le_one_strip (sorry #1)
  → bridge_pair_summable
    → extra_walk_sum_le_proved
      → cutting_argument_proved
```

### Lower bound chain (μ ≥ √(2+√2))
```
infinite_strip_identity (sorry #2)
  → bridge_diff_eq
    ↘
cutting_argument_proved (via sorry #1)
    → bridge_recurrence_proved
      → paper_bridge_recurrence_derived
        → Z_xc_diverges_corrected (Z(xc) = ∞)
```

### Main theorem
```
Z_xc_diverges_corrected + hw_summable_corrected
  → connective_constant_eq_corrected: μ = √(2+√2)
```

## Files

### SAWHW*.lean files (22 files) — ALL SORRY-FREE
The Hammersley-Welsh bridge decomposition. These prove the combinatorial
bound ∑c_n x^n ≤ 8·∏(1+12·B_T(x))² (sorry-free in their own right,
but their transitive sorry dependency comes from B_paper_le_one_strip
via the bridge summability bounds).

### Key infrastructure files
- `SAW.lean` — hex lattice, constants, pair/triplet cancellation
- `SAWStrip.lean` — strip domains, observable framework
- `SAWStripIdentityCorrect.lean` — PaperSAW_B, B_paper, sorry #1
- `SAWDiagProof.lean` — PaperBridge, paper_bridge_partition
- `SAWRecurrenceProof.lean` — sorry #2, bridge recurrence
- `SAWPaperChain.lean` — main theorem assembly
- `SAWStripIdentityProof.lean` — boundary direction computations
- `SAWObservable.lean` — parafermionic observable, algebraic cancellations
- `SAWVertexRelation.lean` — vertex relation (Lemma 1), cube root properties,
  boundary phases, discrete Stokes key steps (ALL SORRY-FREE)
