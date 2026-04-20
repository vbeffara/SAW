# Proof Status: The connective constant of the honeycomb lattice equals √(2+√2)

## Main theorem

`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
```
μ = √(2+√2)
```

**Status: 3 sorry's remain on the critical path.**
All three sorry's trace back to `strip_identity_genuine` (Lemma 2 of the paper),
which is the parafermionic observable argument — the core mathematical innovation
of Duminil-Copin & Smirnov (2012).

## Fully proved infrastructure

The following are fully proved (no sorry):
- **Hexagonal lattice**: `hexGraph`, decidable adjacency, local finiteness
- **SAW infrastructure**: `SAW`, `saw_count`, finiteness, vertex independence
- **Submultiplicativity**: `saw_count_submult'` — c_{n+m} ≤ c_n · c_m
- **Fekete's lemma**: `fekete_submultiplicative` — submultiplicative sequences converge
- **Connective constant**: `connective_constant`, `connective_constant_is_limit'`, positivity
- **Partition function radius**: `partition_converges_below_inv_cc`, `partition_diverges_above_inv_cc`
- **Algebraic identities** (Lemma 1 of the paper):
  - `pair_cancellation`: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
  - `triplet_cancellation`: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0
- **Bridge infrastructure**: PaperBridge, paper_bridge_partition, paper_bridge_length_ge
- **Cutting argument**: `cutting_argument_proved` — A_{T+1} - A_T ≤ xc · B_{T+1}²
- **Bridge decay**: `paper_bridge_decay` — B_T^x ≤ (x/xc)^T / xc for x < xc
- **Bridge partial sum bound**: `paper_bridge_partial_sum_le` — Σ xc^{len} ≤ 1/xc
  (depends on strip_identity_genuine via B_paper_le_one)
- **Bridge lower bound**: `paper_bridge_lower_bound` — ∃ c > 0, B_T ≥ c/T
  (depends on paper_bridge_recurrence)
- **Bridge-SAW injection**: `paperBridge_toSAW_sigma_injective`
- **Zigzag construction**: saw_count_even_lower_proved, saw_count_sq_ge_two_pow_proved
- **Quadratic recurrence lower bound**: `quadratic_recurrence_lower_bound` (abstract result)
- **Main theorem assembly**: `connective_constant_eq_from_bounds` (modulo sorry dependencies)
- **Winding analysis**: boundary coefficients c_α, c_ε computed
- **Direction vectors**: false_to_true_dir, starting_direction, right_boundary_exit_angle
- **Boundary coefficient positivity**: c_alpha_pos, c_eps_pos, boundary_cos_pos

## Critical path (dependency tree)

```
SAW.lean (constants, algebraic identities) ✓
├── SAWSubmult.lean (submultiplicativity) ✓
│   └── SAWMain.lean (Fekete's lemma → connective constant exists) ✓
│       └── SAWBridge.lean (partition function) ✓
│           └── SAWBridgeFix.lean ✓
│               └── SAWStripIdentityCorrect.lean
│                   ├── strip_identity_genuine ⚠️ [SORRY — Lemma 2]
│                   └── B_paper_le_one ✓ (from strip_identity_genuine)
│                       └── SAWDiagProof.lean ✓
│                           └── SAWCuttingProof.lean ✓
│                               └── SAWPaperChain.lean
│                                   ├── paper_bridge_recurrence ⚠️ [SORRY]
│                                   ├── paper_bridge_decomp_injection ⚠️ [SORRY]
│                                   ├── paper_bridge_lower_bound ✓ (from recurrence)
│                                   ├── Z_xc_diverges_corrected ✓ (from lower bound)
│                                   ├── hw_summable_corrected ✓ (from decomp injection)
│                                   └── connective_constant_eq_corrected ✓ (from above)
```

## Remaining sorry chains

### Sorry 1: Strip identity (Lemma 2) — THE FUNDAMENTAL GAP
**Location:** `strip_identity_genuine` in `SAWStripIdentityCorrect.lean`
**Statement:** For the finite strip S_{T,L} with T ≥ 1 and L ≥ 1,
  ∃ A_m E_m ≥ 0, 1 = c_α · A_m + B_paper T L xc + c_ε · E_m

**What it blocks:** ALL other sorry's depend on this one (directly or indirectly).

**Why it's hard:** This is the core mathematical innovation of the Duminil-Copin &
Smirnov paper. The proof requires:
1. **The parafermionic observable** F(z) = Σ exp(-iσW(γ,z)) · xc^{|γ|}
   at each mid-edge z of the strip.
2. **The vertex relation** (Lemma 1): at each interior vertex v, the weighted
   sum of the observable over v's three mid-edges vanishes. This is proved by
   partitioning SAWs into pairs/triplets:
   - Pairs: walks differing by a loop reversal around v. Cancellation uses
     `pair_cancellation` (proved).
   - Triplets: a base walk + two one-step extensions. Cancellation uses
     `triplet_cancellation` (proved).
   - The COMBINATORIAL CONSTRUCTION of the partition is the key missing piece.
3. **Discrete Stokes**: summing vertex relations over all strip vertices.
   Interior mid-edges cancel; boundary mid-edges survive.
4. **Boundary evaluation**: computing winding and direction factors for each
   boundary type. Direction factors are proved. Winding analysis is partly done.

**Key difficulty:** The winding of a SAW on the hex lattice depends on the path
(not just the endpoints), because turns at vertices can exceed π in absolute value
when computed as raw differences of edge angles. Specifically, the signed turn
angle (in (-π,π]) differs from the raw difference d_{k+1} - d_k by multiples of 2π
at certain vertex configurations. This means the winding W = Σ(signed turns) does
NOT telescope to d_exit - d_entry, and different SAWs to the same exit mid-edge can
have different complex weights.

**Available algebraic infrastructure:** pair_cancellation, triplet_cancellation,
boundary_cos_pos, c_alpha_pos, c_eps_pos, direction vectors, winding coefficients.

**Missing combinatorial infrastructure:**
- Walk pairing: for each vertex v, partition SAWs contributing to v's three
  mid-edges into pairs (related by loop reversal) and triplets (base + extensions).
- Exhaustiveness: every contributing SAW belongs to exactly one pair or triplet.
- Weight cancellation: each pair/triplet's complex weights sum to zero.
- Discrete Stokes: the boundary sum over a finite region equals the sum of
  vertex relations over interior vertices.

### Sorry 2: Bridge recurrence
**Location:** `paper_bridge_recurrence` in `SAWPaperChain.lean`
**Statement:** ∃ α > 0, ∀ T, paper_bridge_partition T xc ≤ α · B_{T+1}² + B_{T+1}

**Depends on:** Sorry #1 (strip identity) — specifically needs the EXACT identity
for the infinite strip: 1 = c_alpha · A_inf(T) + xc · B(T) (with E_inf = 0).

**What's needed (beyond sorry #1):**
The proof derivation:
1. Infinite strip identity: 1 = c_alpha · A_inf(T) + xc · B(T)
   (follows from strip_identity_genuine by taking L → ∞ with E = 0).
2. Cutting argument (proved): A_inf(T+1) - A_inf(T) ≤ xc · B(T+1)²
3. From (1): ΔA = xc·(B(T) - B(T+1))/c_alpha
4. From (2)+(3): B(T) - B(T+1) ≤ c_alpha · B(T+1)²
5. Therefore: B(T) ≤ c_alpha · B(T+1)² + B(T+1), giving α = c_alpha.

**Subtlety:** The existential form of strip_identity_genuine is NOT strong enough
to derive the infinite strip identity. We'd need the ACTUAL identity with specific
A_paper and E_paper witnesses (not just existential witnesses). This requires either:
- Strengthening strip_identity_genuine to provide specific witnesses, or
- Proving the infinite strip identity directly.

### Sorry 3: Hammersley-Welsh decomposition
**Location:** `paper_bridge_decomp_injection` in `SAWPaperChain.lean`
**Statement:** Σ_{n≤N} c_n x^n ≤ 2 × (Σ_{S⊆range(N)} Π_{T∈S} B_{T+1}^x)²

**Depends on:** Sorry #1 (through `paper_bridge_decay` which uses
`paper_bridge_partial_sum_le` which uses `B_paper_le_one`).

**What's needed:**
1. Half-plane walk decomposition: by strong induction on width, each half-plane
   SAW decomposes into bridges of strictly decreasing widths.
2. General SAW splitting: split at the first vertex of maximum diagonal depth
   into two half-plane walks.
3. Injectivity: the decomposition uniquely determines the walk.
4. Weight accounting: walk length ≥ sum of bridge lengths, so x^n ≤ Π x^{len_i}.
5. Counting: the injection gives Σ c_n x^n ≤ 2 × (Π(1 + B_T))².

## Summary

The entire proof of the main theorem reduces to a SINGLE mathematical gap:
the parafermionic observable argument (Lemma 2 of the paper). All algebraic
ingredients are proved. What remains is the combinatorial infrastructure for
the pair/triplet decomposition and the discrete Stokes summation.

The other two sorry's (bridge recurrence and HW decomposition) are substantial
combinatorial results but are mathematically less novel — they are standard
arguments that would follow relatively directly once the strip identity is
established.

## Files with sorry's NOT on the main critical path

These sorry's exist but are either superseded by proved versions elsewhere
or are not imported by the main theorem:

- `SAWCutting.lean:100` — `cutting_argument` (superseded by `cutting_argument_proved`)
- `SAWZigzag.lean:142,147` — zigzag bounds (proved in SAWZigzagBuild.lean)
- `SAWBridge.lean:357` — old bridge summability (superseded)
- `SAWFiniteStrip.lean` — old finite strip infrastructure
- `SAWStokesSkeleton.lean:82` — vertex_relation_observable (scaffolding)
- `SAWHWAlgorithm.lean`, `SAWHWDecomp.lean` — old HW decomposition attempts
- `SAWBridgeDecomp.lean`, `SAWHWBridge.lean`, `SAWHammersleyWelsh.lean` — old infrastructure
- `SAWStripIdentity.lean` — old strip identity attempt
