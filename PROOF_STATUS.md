# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
μ = √(2+√2) where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent sorry chains (reduced from 3).**

## Sorry Chains

### Sorry Chain 1: Parafermionic Observable (Lemma 2 of the paper)

#### Sorry: `infinite_strip_identity` in `SAWRecurrenceProof.lean` (line 49)
1 = c_α · A_inf(T) + xc · paper_bridge_partition(T).

This is the parafermionic observable identity for the infinite strip.
All algebraic ingredients are proved (pair_cancellation, triplet_cancellation).
What remains is the combinatorial infrastructure: walk pairing/tripling,
discrete Stokes summation, and boundary winding evaluation.

**Key insight (new):** `B_paper_le_one_strip` (formerly sorry #1) now
FOLLOWS from `infinite_strip_identity` via the injection from finite
strip walks to infinite strip bridges (proved in `SAWStripFromIdentity.lean`).
This reduces the independent sorry count from 3 to 2.

The derivation chain:
- `infinite_strip_identity` → `B_paper_le_one_from_identity`
  (via injection PaperSAW_B → PaperBridge and A_inf_nonneg)
- `B_paper_le_one_strip` in SAWStripIdentityCorrect.lean still has sorry
  but could be replaced by B_paper_le_one_from_identity if the dependency
  cycle is resolved.

### Sorry Chain 2: Hammersley-Welsh Decomposition

#### Sorry: `paper_bridge_decomp_injection` in `SAWPaperChain.lean` (line 258)
∑_{n≤N} c_n x^n ≤ 2·(∏_{T=1}^{N} (1+B_T(x)))²

This is the Hammersley-Welsh bridge decomposition bound. Requires:
- Half-plane walk bridge extraction algorithm
- Injectivity of the decomposition  
- Weight accounting (walk length ≥ sum of bridge lengths)

**Proved helpers:**
- `saw_weight_le_bridge_product`: x^n ≤ ∏ x^{w_i} when sum ≤ n
- `powerset_prod_eq`: ∑_{S⊆F} ∏_{i∈S} a_i = ∏_{i∈F} (1+a_i)

## New Infrastructure: SAWStripFromIdentity.lean

This file proves that sorry #1 follows from sorry #2:

- `paperSAWB_to_bridge`: injection from PaperSAW_B T L to PaperBridge T
- `paperSAWB_to_bridge_injective`: the injection is injective
- `B_paper_le_xc_mul_bridge`: B_paper(T,L,xc) ≤ xc · paper_bridge_partition(T)
- `B_paper_le_one_from_identity`: B_paper(T,L,xc) ≤ 1 from infinite_strip_identity

All four lemmas are sorry-free. The key insight: every finite strip walk
injects into the infinite strip, and infinite_strip_identity bounds the
infinite strip partition function.

## Proof Architecture (updated)

```
connective_constant_eq_corrected (SAWPaperChain.lean)
├── Z_xc_diverges_corrected (SAWPaperChain.lean)
│   └── paper_bridge_lower_bound
│       └── bridge_recurrence_proved (SAWRecurrenceProof.lean)
│           ├── infinite_strip_identity ← SORRY (Chain 1)
│           └── cutting_argument_proved ✓
└── hw_summable_corrected (SAWPaperChain.lean)
    ├── paper_bridge_decomp_injection ← SORRY (Chain 2)
    └── paper_bridge_decay
        └── paper_bridge_partial_sum_le (SAWDiagProof.lean)
            └── B_paper_le_one_direct
                └── B_paper_le_one_strip ← follows from Chain 1
                    (via SAWStripFromIdentity.lean)
```

## Fully Proved Results (no sorry, on the critical path)

### Core Definitions and Properties
- Hexagonal lattice (hexGraph), SAW, saw_count
- Connective constant definition and limit (connective_constant_is_limit')
- Critical fugacity xc, phase parameters λ, j, σ, c_α, c_ε

### Submultiplicativity and Fekete
- c_{n+m} ≤ c_n·c_m (saw_count_submult')
- c_{km} ≤ c_m^k (saw_count_iter_submult)
- Connective constant is positive (connective_constant_pos')

### Algebraic Identities (Lemma 1 infrastructure)
- pair_cancellation: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- triplet_cancellation: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0

### Strip and Bridge Infrastructure
- Strip domain definitions (PaperInfStrip, PaperFinStrip)
- Strip finiteness, SAW length bounds
- Bridge definitions (PaperBridge), bridge length bounds
- Bridge partial sum bounds, bridge decay
- Cutting argument (cutting_argument_proved)
- **NEW: B_paper ≤ 1 derived from infinite_strip_identity**

### T=1 Special Case
- paper_bridge_partition_1_eq: B_inf(1) = 2xc/(1-xc²)
- B_paper_1_lt_one': B_paper(1,L,xc) < 1 for all L

### HW Decomposition Helpers
- saw_weight_le_bridge_product
- powerset_prod_eq
