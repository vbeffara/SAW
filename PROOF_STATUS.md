# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq` in `SAWFinal.lean`:
μ = √(2+√2) where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 3 sorry statements in 2 independent sorry chains.**

## Sorry Chain 1: Parafermionic Observable (Lemma 2 of the paper)

### Sorry 1: `B_paper_le_one_strip` in `SAWStripIdentityCorrect.lean` (line 385)
B_paper(T,L,xc) ≤ 1 for the finite strip S_{T,L}.

### Sorry 2: `infinite_strip_identity` in `SAWRecurrenceProof.lean` (line 49)
1 = c_α · A_inf(T,xc) + xc · paper_bridge_partition(T,xc).

Both require the **parafermionic observable** argument:
1. **Vertex relation** (Lemma 1): pair_cancellation + triplet_cancellation
   give cancellation at each vertex. Algebraic identities PROVED.
2. **Discrete Stokes**: Summing over vertices, interior mid-edges cancel.
   Interior cancellation PROVED (interior_edge_cancellation).
3. **Boundary evaluation**: Starting mid-edge contributes -1, right boundary
   contributes B, left boundary contributes c_α·A.
4. **Missing**: Walk partitioning into pairs/triplets at each vertex,
   full discrete Stokes summation, boundary winding evaluation.

## Sorry Chain 2: Hammersley-Welsh Decomposition

### Sorry 3: `paper_bridge_decomp_injection` in `SAWPaperChain.lean` (line 258)
∑_{n≤N} c_n x^n ≤ 2·(∏_{T=1}^{N} (1+B_T(x)))²

**Proved helpers:**
- `saw_weight_le_bridge_product` (SAWHWDecompFull.lean): x^n ≤ ∏ x^{w_i} when sum w_i ≤ n
- `powerset_prod_eq` (SAWHWDecompFull.lean): ∑_{S⊆F} ∏_{i∈S} a_i = ∏_{i∈F} (1+a_i)
- Bridge definitions, positivity, length bounds, injection into SAWs
- Walk splitting infrastructure (takeUntil, dropUntil, min/max diagCoord)

**Missing:**
- Half-plane walk bridge extraction algorithm
- Injectivity of the bridge decomposition
- Weight accounting (walk length ≥ sum of bridge lengths)

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

### Bridge Analysis (modulo sorry #1)
- PaperInfStrip, PaperFinStrip definitions
- B_paper_le_one follows from B_paper_le_one_strip (sorry #1)
- Cutting argument: A_{T+1} - A_T ≤ xc·B_{T+1}² (cutting_argument_proved)
- Bridge recurrence: B(T) ≤ c_α·B(T+1)² + B(T+1) (bridge_recurrence_proved)
- Bridge lower bound: B(T) ≥ c/T (paper_bridge_lower_bound)
- Bridge decay: B_T(x) ≤ (x/xc)^T/xc (paper_bridge_decay)
- Z(xc) diverges (Z_xc_diverges_corrected)

### HW Decomposition Helpers
- saw_weight_le_bridge_product: x^n ≤ ∏ x^{w_i} when sum ≤ n
- powerset_prod_eq: ∑_{S⊆F} ∏_{i∈S} a_i = ∏_{i∈F} (1+a_i)

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
