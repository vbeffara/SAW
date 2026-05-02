# Proof Status: The Connective Constant of the Honeycomb Lattice

## Main Theorem

`connective_constant_eq` in `SAWFinal.lean`:
The connective constant of the hexagonal lattice equals √(2+√2).

**Status**: Proved modulo 3 sorries (2 independent chains).

## Sorry Chain Summary

The main theorem depends on exactly **3 sorry'd lemmas** in **2 independent chains**:

### Chain 1: Strip Identity (Parafermionic Observable)

**Root sorries**:
- `strip_identity_genuine` in `SAWStripIdentityCorrect.lean` (line 361) — the finite strip identity
- `infinite_strip_identity` in `SAWRecurrenceProof.lean` (line 49) — the infinite strip version

**Mathematical content**: Lemma 2 of Duminil-Copin & Smirnov (2012).

`strip_identity_genuine`: For the finite strip S_{T,L}, ∃ A, E ≥ 0 such that
1 = c_α·A + B_paper(T,L,xc) + c_ε·E. This gives B_paper ≤ 1.

`infinite_strip_identity`: For the infinite strip S_T,
1 = c_α · A_inf(T, xc) + xc · paper_bridge_partition(T, xc).
This gives the bridge recurrence.

**What is proved** (sorry-free):
- Pair cancellation: j·conj(λ)^4 + conj(j)·λ^4 = 0
- Triplet cancellation: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- Boundary direction characterization (left = -1, right = +1 in ℂ)
- Boundary coefficient positivity (c_α > 0, c_ε > 0, cos(3θ/8) > 0)
- Direction sum identity (d₀ + d₁ + d₂ = 0 at each vertex)
- Abstract bridge bound: if 1 = c_α·A + B + c_ε·E with A,E ≥ 0, then B ≤ 1
- Cutting argument: A_{T+1} - A_T ≤ xc · B_{T+1}² (cutting_argument_proved)
- Bridge recurrence: B_T ≤ c_α·B_{T+1}² + B_{T+1} (derived from infinite_strip_identity + cutting)
- Bridge lower bound: ∃ c > 0, c/T ≤ B_T (from recurrence)
- Z(xc) = +∞ (divergence at critical point, from bridge lower bound)
- Strip identity for T=1 (strip_identity_genuine_T1', sorry-free)
- Exact bridge partition: paper_bridge_partition 1 xc = 2xc/(1-xc²)

**What remains (for both strip_identity_genuine and infinite_strip_identity)**:
- The discrete Stokes argument: defining the parafermionic observable F(z)
  at each mid-edge z, proving the vertex relation ∑_{w~v} (w-v)·F(v→w) = 0
  at each vertex v (using pair/triplet cancellation), and evaluating the
  boundary sum to get the identity 1 = c_α·A + B + c_ε·E.
- For infinite_strip_identity: taking L → ∞ in the finite strip identity.

### Chain 2: Hammersley-Welsh Decomposition

**Root sorry**: `paper_bridge_decomp_injection` in `SAWPaperChain.lean` (line 258)

**Mathematical content**: Every SAW decomposes into a pair of bridge sequences
with monotone widths, giving ∑ c_n·x^n ≤ 2·(∏(1+B_T(x)))².

**What is proved** (sorry-free):
- Subset-product identity: ∑_{S⊆{1,...,N}} ∏_{T∈S} b_T = ∏(1+b_T)
- Bridge decay: B_T(x) ≤ (x/xc)^T for x < xc
- Product convergence: ∏(1+r^T) < ∞ for r < 1
- Z(x) < ∞ for x < xc (from decomposition injection + decay)
- HW base case: c_0 = 1 ≤ 2 (hw_base_case)
- Powerset product ≥ 1 (powerset_prod_ge_one)
- c_0 = 1 (saw_count_zero')

**What remains**:
- Splitting a SAW at the first vertex achieving minimum diagCoord
- Half-plane walk decomposition into bridges of STRICTLY decreasing widths
  (strictly decreasing follows from integrality of diagCoord on hex lattice)
- Translation invariance: bridge counts from any vertex at diagCoord 0 equal
  paper_bridge_partition (via hexShift preserving adjacency)
- Injectivity of the decomposition (up to factor 2)
- Walk length accounting (lengths sum correctly)

## Infrastructure (sorry-free)

### SAWHWDecompProved.lean — Walk diagCoord infrastructure
- `walkMinDC_le` / `walkMaxDC_ge`: bounds on diagCoord of walk vertices ✓
- `walkMinDC_achieved` / `walkMaxDC_achieved`: extrema are achieved ✓
- `walk_dc_bound`: vertices in walks from paperStart have |dc| ≤ length ✓
- `walkDCWidth_le_length`: diagCoord width ≤ walk length ✓

### SAWVertexRelProof4.lean — Path extension
- `extendPath`: extend a path by one edge (preserves self-avoidance) ✓
- `extendPath_length`: extended path has length + 1 ✓
- `extendPath_support`: extended path support = original ++ [w] ✓
- `extendSAW`: extend a SAW by one step ✓

### SAWHWProof.lean — HW decomposition helpers
- `saw_dc_bound`: |hexDiagCoord(u)| ≤ n for n-step SAW vertices ✓
- `powerset_prod_ge_one`: Σ_{S} ∏_{T∈S} f(T) ≥ 1 for f ≥ 0 ✓
- `saw_count_zero'`: c₀ = 1 ✓
- `hw_base_case`: HW inequality for N = 0 ✓

### Core algebraic infrastructure (SAW.lean)
- `pair_cancellation`: j·conj(λ)^4 + conj(j)·λ^4 = 0 ✓
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0 ✓
- `c_alpha_pos`: cos(3π/8) > 0 ✓
- `c_eps_pos`: cos(π/4) > 0 ✓
- `xc_pos`: xc > 0 ✓
- `xc_inv`: xc⁻¹ = √(2+√2) ✓

### Submultiplicativity and Fekete's lemma (SAWSubmult.lean, SAWMain.lean)
- `saw_count_submult'`: c_{n+m} ≤ c_n · c_m ✓
- `connective_constant_is_limit'`: c_n^{1/n} → μ ✓
- `connective_constant_pos'`: μ > 0 ✓
- `partition_converges_below_inv_cc`: Z(x) < ∞ for x < 1/μ ✓
- `partition_diverges_above_inv_cc`: Z(x) = ∞ for x > 1/μ ✓

### Bridge infrastructure (SAWDiagProof.lean)
- `paper_bridge_length_ge`: bridge of width T has length ≥ T ✓
- `paper_bridge_in_fin_strip`: bridges fit in finite strips ✓
- `paper_bridge_partial_sum_le`: partial sums ≤ 1/xc (from B_paper ≤ 1) ✓
- `paper_bridge_upper_bound`: B_T(xc) ≤ 1/xc ✓

### Cutting argument (SAWCuttingProof.lean)
- `cutting_argument_proved`: A(T+1) - A(T) ≤ xc · B(T+1)² ✓
- `extra_walk_sum_le`: sum over extra walks bounded ✓

## File Organization

```
SAWFinal.lean          ← Main theorem (imports SAWPaperChain)
SAWPaperChain.lean     ← Assembly: Z diverges + Z converges → μ = √(2+√2)
  ├─ SAWDiagProof.lean      ← Bridge infrastructure
  │  └─ SAWStripIdentityCorrect.lean  ← SORRY: strip_identity_genuine
  ├─ SAWCuttingProof.lean    ← Cutting argument (proved)
  ├─ SAWRecurrenceProof.lean ← SORRY: infinite_strip_identity
  └─ SAWDecomp.lean          ← Quadratic recurrence (proved)
SAWHWDecompProved.lean ← Walk diagCoord infrastructure (sorry-free)
SAWVertexRelProof4.lean ← Path extension (sorry-free)
SAWHWProof.lean         ← HW base case and helpers (sorry-free)
SAWParafermionicKey.lean ← Reduction: strip_identity_genuine ← B_paper ≤ 1
SAWStripT1Direct.lean   ← Strip identity for T=1 (sorry-free)
SAWStripT1Exact.lean    ← Exact bridge partition for T=1 (sorry-free)
```
