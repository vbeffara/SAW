# Proof Status: The connective constant of the honeycomb lattice equals √(2+√2)

## Main Theorem

**`connective_constant_eq`** in `SAWFinal.lean`: μ = √(2+√2)  
**Status**: Proved modulo 2 root sorry chains (see below).

## What is Proved (sorry-free)

### Core infrastructure
- Hexagonal lattice graph (`hexGraph`) with decidable adjacency and local finiteness
- Self-avoiding walks (`SAW`) with `Fintype` instance
- SAW counting (`saw_count`) with c₁ = 3, c₂ = 6

### Submultiplicativity and connective constant
- `saw_count_submult'`: c_{n+m} ≤ c_n · c_m
- `saw_count_vertex_independent`: count is the same from any vertex
- `fekete_submultiplicative`: Fekete's lemma for submultiplicative sequences
- `connective_constant_is_limit'`: μ = lim c_n^{1/n}
- `connective_constant_pos'`: μ > 0

### Algebraic identities
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- Direction vectors are cube roots of unity

### Vertex relation algebraic infrastructure (NEW)
- `pair_residual_j_blocked`: 1 + xc·conj(j)·λ = -(xc·j·conj(λ))
- `pair_residual_conjj_blocked`: 1 + xc·j·conj(λ) = -(xc·conj(j)·λ)
- `singleton_residual`: 1 = -(xc·j·conj(λ) + xc·conj(j)·λ)
- `pair_residuals_cancel`: weighted sum of pair residuals

### Strip identity for T = 1
- `paper_bridge_partition_1_eq`: B₁ = 2xc/(1-xc²) (exact value)
- `infinite_strip_identity_T1`: the T=1 case proved sorry-free
- `strip_identity_genuine_T1'`: B_paper(1,L,xc) ≤ 1

### Walk infrastructure
- Walk extension (`extendPath`): extending a SAW by one step
- Walk splitting at vertices
- Bridge length bounds (bridge width T → length ≥ T)
- Walk bipartiteness and diagCoord bounds

### Cutting argument
- `cutting_argument_proved`: A_{T+1} - A_T ≤ xc · B_{T+1}²

### Bridge recurrence and lower bound
- `bridge_recurrence_proved`: B_T ≤ c_α · B_{T+1}² + B_{T+1}
- `paper_bridge_lower_bound`: ∃ c > 0, B_T ≥ c/T

### Abstract discrete Stokes theorem
- `discrete_stokes_abstract`: If f is antisymmetric and the vertex
  relation holds at each interior vertex, then the boundary sum is zero.

### Bridge decomposition infrastructure (NEW)
- `hexDiagCoord`: diagonal coordinate x+y
- `hexDiagCoord_adj_bound`: adjacent vertices differ by at most 1
- `finset_powerset_prod_eq'`: ∑_{S⊆range N} ∏_{T∈S} a_T = ∏(1+a_T)
- `paperBridge_dc_range`: bridge vertices have diagCoord in [-T, 0]

### Main theorem assembly (modulo sorry)
- `Z_xc_diverges_corrected`: Z(xc) = +∞
- `hw_summable_corrected`: Z(x) < ∞ for x < xc
- `connective_constant_eq_corrected`: μ = √(2+√2)

## Root Sorry Chains (2 remaining)

### 1. Strip identity / Vertex relation (Lemma 1 + Lemma 2)

**Files**: `SAWStripIdentityCorrect.lean` (strip_identity_genuine),
`SAWRecurrenceProof.lean` (infinite_strip_identity)

**What's needed**: The vertex relation at each interior vertex of the strip.
This says that walks to the three mid-edges of a vertex can be partitioned
into pairs and triplets whose weighted contributions cancel. The algebraic
core (pair_cancellation, triplet_cancellation) is proved. The abstract
Stokes summation (discrete_stokes_abstract) is proved. What remains is
the combinatorial walk partition: constructing the bijection between
walks that forms pairs and triplets.

**Key insight**: Triplets (both exits free) cancel by triplet_cancellation.
Pair residuals (one exit blocked) are characterized by pair_residual_j_blocked
and pair_residual_conjj_blocked. The global cancellation of pair residuals
uses the pair_cancellation identity.

### 2. Hammersley-Welsh decomposition

**File**: `SAWPaperChain.lean` (paper_bridge_decomp_injection),
`SAWBridgeDecompCore.lean` (hw_counting_bound)

**What's needed**: The bridge decomposition injection showing that
∑ c_n x^n ≤ 2 · (∏(1 + B_T))². This requires implementing the
canonical decomposition of SAWs into bridges with monotone widths,
and proving the decomposition map is injective.

**Infrastructure available**: hexDiagCoord, adj bound, product-powerset
identity, bridge diagCoord range, walk splitting at vertices.

## File Organization

- `SAW.lean` — Core definitions, algebraic identities
- `SAWSubmult.lean` — Submultiplicativity
- `SAWMain.lean` — Fekete's lemma → connective constant
- `SAWStripIdentityCorrect.lean` — Strip domain, partition functions, strip identity
- `SAWDiagProof.lean` — PaperBridge, partition function bounds
- `SAWCuttingProof.lean` — Cutting argument (proved)
- `SAWRecurrenceProof.lean` — Bridge recurrence from infinite strip identity
- `SAWPaperChain.lean` — Main theorem assembly
- `SAWFinal.lean` — Final theorem
- `SAWDiscreteStokesProof.lean` — Abstract discrete Stokes theorem (proved)
- `SAWVertexRelDirect.lean` — Walk extension infrastructure (proved)
- `SAWVertexPartition.lean` — Pair/triplet residual identities (proved, NEW)
- `SAWBridgeDecompCore.lean` — HW decomposition infrastructure (NEW)
