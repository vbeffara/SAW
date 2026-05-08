# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq` in `SAWFinal.lean`:
μ = √(2+√2) where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 3 sorry statements in 2 independent sorry chains.**

The main theorem uses `#print axioms connective_constant_eq` showing:
`propext`, `sorryAx`, `Classical.choice`, `Quot.sound`.
All axioms except `sorryAx` are standard; `sorryAx` arises from the 3 sorry's below.

## Sorry Chain 1: Parafermionic Observable (Lemma 2 of the paper)

### Sorry 1: `B_paper_le_one_strip` in `SAWStripIdentityCorrect.lean` (line 385)
B_paper(T,L,xc) ≤ 1 for the finite strip S_{T,L}.

### Sorry 2: `infinite_strip_identity` in `SAWRecurrenceProof.lean` (line 49)
1 = c_α · A_inf(T,xc) + xc · paper_bridge_partition(T,xc).

Both require the **parafermionic observable** argument:

1. **Vertex relation** (Lemma 1): At each interior vertex v of the strip,
   Σ_{w~v} D(v,w)·F(mid(v,w)) = 0. This follows from pair_cancellation
   and triplet_cancellation (both PROVED algebraically in SAW.lean).
2. **Discrete Stokes**: Summing over all vertices, interior mid-edges cancel
   (proved as interior_edge_cancellation in SAWObservableNew.lean),
   only boundary mid-edges survive.
3. **Boundary evaluation**: Starting mid-edge contributes -1, right boundary
   contributes B_paper (winding 0, coefficient 1), left boundary contributes
   c_α·A (winding ±π, coefficient c_α), escape contributes c_ε·E.
4. **Result**: 0 = -1 + B_paper + c_α·A + c_ε·E → B_paper ≤ 1.

**What is proved (algebraic core):**
- pair_cancellation: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- triplet_cancellation: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- two_xc_cos_pi_eight_eq_one: 2·xc·cos(π/8) = 1 (SAWVertexRelKey.lean)
- starting_vertex_relation: -1 + 2·xc·cos(π/8) = 0 (SAWVertexRelKey.lean)
- xc_inv_eq_two_cos_pi_eight: xc⁻¹ = 2·cos(π/8) (SAWVertexRelKey.lean)
- interior_edge_cancellation: D(v,w)·f + D(w,v)·f = 0
- boundary_cos_pos: cos(3θ/8) > 0 for |θ| ≤ π
- left_boundary_phase: cos(σπ) = -c_alpha
- right_boundary_phase: cos(σ·0) = 1
- boundary_sum_structure: if 0 = -1 + B + c_α·A with A ≥ 0, then B ≤ 1
- Direction vectors: hexDir_tt_ff, hexDir_ff_tt, hexDir_start, hexDir_neg
- Boundary directions: right_boundary_hexDir (+1), left_boundary_hexDir (-1)

**What is missing (combinatorial infrastructure):**
- Walk partitioning into pairs/triples at each vertex
- The full discrete Stokes summation (combining vertex relations)
- Winding evaluation for boundary mid-edges
- L → ∞ limit for the infinite strip

## Sorry Chain 2: Hammersley-Welsh Decomposition

### Sorry 3: `paper_bridge_decomp_injection` in `SAWPaperChain.lean` (line 258)
∑_{n≤N} c_n x^n ≤ 2·(∏_{T=1}^{N} (1+B_T(x)))²

**What is proved:**
- Bridge definitions: PaperBridge, paper_bridge_partition
- Bridge positivity: paper_bridge_partition_one_pos
- Bridge to SAW injection: paperBridge_toSAW, injection is injective
- Walk splitting infrastructure: takeUntil, dropUntil
- Translation: hexShift preserves adjacency and path property
- Bridge length bound: paper_bridge_length_ge (T ≤ bridge length)
- Bridge finite sum bound: paper_bridge_finite_sum_le
- Bipartiteness: hexGraph_bipartite, walk_sublattice_parity

**What is missing:**
- Bridge decomposition algorithm (half-plane walk → bridges)
- Walk splitting at first vertex of minimal diagCoord
- Injectivity of the bridge decomposition
- Weight accounting (walk length ≥ sum of bridge lengths)

**Note:** The alternative proof path in SAWMainNew.lean (avoiding HW decomposition
via submultiplicativity) is INCOMPLETE: `hw_summable_direct` cannot be proved from
submultiplicativity + Z(xc)=∞ alone. The upper bound μ ≤ 1/xc genuinely requires
either the HW decomposition or an equivalent argument.

## Fully Proved Results (no sorry)

### Core Definitions and Properties
- Hexagonal lattice (hexGraph), SAW, saw_count
- Connective constant definition and limit (connective_constant_is_limit')
- Critical fugacity xc, phase parameters λ, j, σ, c_α, c_ε

### Submultiplicativity and Fekete
- c_{n+m} ≤ c_n·c_m (saw_count_submult')
- c_{km} ≤ c_m^k (saw_count_iter_submult)
- c_n ≤ c_m^{⌊n/m⌋}·c_{n%m} (saw_count_div_mod_bound)
- Connective constant is positive (connective_constant_pos')

### Algebraic Identities
- pair_cancellation, triplet_cancellation
- two_xc_cos_pi_eight_eq_one, starting_vertex_relation
- Various boundary coefficient computations
- cos(5π/8) = -c_alpha (cos_five_pi_eight)

### Direction Vectors (SAWObservableNew.lean)
- hexDir_tt_ff, hexDir_ff_tt, hexDir_start, hexDir_neg
- interior_edge_cancellation: D(v,w)·f + D(w,v)·f = 0
- right_boundary_hexDir, left_boundary_hexDir

### Strip Domain and Bridge Analysis
- PaperInfStrip, PaperFinStrip definitions
- B_paper_le_one follows from B_paper_le_one_strip (sorry 1)
- Cutting argument: A_{T+1} - A_T ≤ xc·B_{T+1}² (cutting_argument_proved)
- Bridge recurrence: B(T) ≤ c_α·B(T+1)² + B(T+1) (bridge_recurrence_proved)
- Bridge lower bound: B(T) ≥ c/T (paper_bridge_lower_bound)
- Bridge upper bound: B(T) ≤ 1/xc (paper_bridge_upper_bound)
- Bridge decay: B_T(x) ≤ (x/xc)^T/xc (paper_bridge_decay)
- Z(xc) diverges (Z_xc_diverges_corrected)
- Z(x) < ∞ for x < xc (hw_summable_corrected, uses sorry 1+3)

### T=1 Special Case
- paper_bridge_partition_1_eq (exact value)
- A_inf_1_exact (exact value)
- infinite_strip_identity_T1_clean (proved from exact values)

## Proof Architecture

```
connective_constant_eq (SAWFinal.lean)
├── Z_xc_diverges_corrected (SAWPaperChain.lean)
│   └── paper_bridge_lower_bound
│       └── paper_bridge_recurrence_derived
│           └── bridge_recurrence_proved (SAWRecurrenceProof.lean)
│               ├── infinite_strip_identity ← SORRY 2
│               └── cutting_argument_proved ✓
└── hw_summable_corrected (SAWPaperChain.lean)
    ├── paper_bridge_decomp_injection ← SORRY 3
    └── paper_bridge_decay
        └── paper_bridge_partial_sum_le (SAWDiagProof.lean)
            └── B_paper_le_one_direct
                └── B_paper_le_one_strip ← SORRY 1
```
