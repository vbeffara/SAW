# Proof Status: The connective constant of the honeycomb lattice equals √(2+√2)

## Main theorem

`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
```
μ = √(2+√2)
```

**Status: 3 sorry's remaining on the critical path.**

## Critical path

```
SAW.lean (constants, algebraic identities) ✓
├── SAWSubmult.lean (submultiplicativity: c_{n+m} ≤ c_n·c_m) ✓
│   └── SAWMain.lean (Fekete's lemma → connective constant is a limit) ✓
│       └── SAWBridge.lean (Bridge defs, connective_constant_eq_from_bounds) ✓
│           └── SAWBridgeFix.lean (OriginBridge definition) ✓
│               └── SAWStripIdentityCorrect.lean
│                   └── B_paper_le_one_direct ⚠️ [sorry — Lemma 2, B ≤ 1]
│                       └── SAWDiagProof.lean (paper bridge infrastructure) ✓
│                           └── SAWPaperChain.lean
│                               ├── paper_bridge_lower_bound ✓ (proved from recurrence)
│                               │   └── paper_bridge_recurrence ⚠️ [sorry — needs strip identity]
│                               ├── paper_bridge_decomp_injection ⚠️ [sorry — HW decomposition]
│                               └── connective_constant_eq_corrected ✓ (proved from above)
└── SAWDecomp.lean (quadratic recurrence, abstract bridge bounds) ✓
```

## Remaining sorry's (critical path)

### 1. `B_paper_le_one_direct` (SAWStripIdentityCorrect.lean)
**B_paper ≤ 1** (the key consequence of Lemma 2): For T ≥ 1, L ≥ 1:
  B_paper(T, L, xc) ≤ 1

**Important correction:** The exact vertex-based identity
  `1 = c_α · A_paper + B_paper + c_ε · E_paper`
does NOT hold (verified computationally for T=1, L=2). The paper's
identity uses mid-edge-based partition functions, which differ from
vertex-based ones at corner vertices of the strip.

However, `B_paper = B_mid` (each right boundary vertex has exactly
one right boundary mid-edge), so the bound `B_paper ≤ 1` follows
from the mid-edge identity via:
  0 = Re(boundary sum)
  0 = -1/2 + (1/2)·B_mid + (non-negative terms)
  ⟹ B_mid ≤ 1

The proof requires:
- The parafermionic observable F(z) at each mid-edge z
- The vertex relation: pair + triplet cancellation (proved)
- The discrete Stokes theorem: summing vertex relations over all strip
  vertices, interior mid-edges cancel, boundary survives
- Boundary evaluation: cos(3θ/8) > 0 for all hex angles (proved)

### 2. `paper_bridge_recurrence` (SAWPaperChain.lean)
∃ α > 0, ∀ T, paper_bridge_partition T xc ≤ α · (paper_bridge_partition (T+1) xc)² + paper_bridge_partition (T+1) xc

This follows from:
- The infinite-strip identity: 1 = c_α A_T + B_T (where E_T = 0
  since there is no escape boundary in the infinite strip)
- The cutting argument: A_{T+1} - A_T ≤ C · B_{T+1}²
- Subtracting identities at T and T+1 gives the recurrence

**Note:** paper_bridge_lower_bound is PROVED from paper_bridge_recurrence
via quadratic_recurrence_lower_bound.

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean)
∑_{n≤N} c_n x^n ≤ 2 · (∑_{S⊆{1,...,N}} ∏_{T∈S} B_{T+1}^x)²

This is the Hammersley-Welsh bridge decomposition. Independent of the
strip identity. Requires formalizing the decomposition algorithm:
any SAW can be uniquely decomposed into bridges with monotone widths.

## Fully proved components

- Hexagonal lattice definition and basic properties ✓
- Self-avoiding walk counting (c_n, finiteness, small values) ✓
- Graph automorphisms and vertex independence ✓
- Submultiplicativity: c_{n+m} ≤ c_n·c_m ✓
- Fekete's lemma and connective constant as limit ✓
- Connective constant positivity ✓
- Algebraic identities (pair/triplet cancellation, x_c = 1/(2cos(π/8))) ✓
- Interior cancellation (discrete Stokes core) ✓
- Boundary cos positivity ✓
- Boundary weight non-negativity (all 6 edge types) ✓
- Paper strip domain (PaperInfStrip, PaperFinStrip) ✓
- Paper-compatible partition functions (A_paper, B_paper, E_paper) ✓
- Paper bridge definition and basic properties ✓
- Paper bridge positivity (bridges exist for all widths) ✓
- Paper bridge summability ✓
- Paper bridge finite sum bound ✓
- Paper bridge sum ≤ Z(xc) ✓
- Paper bridge upper bound (≤ 1/xc) ✓ (modulo B_paper_le_one_direct)
- Paper bridge decay ((x/xc)^T / xc for x < xc) ✓ (modulo B_paper_le_one_direct)
- Bridge-to-SAW injection (paper_bridge_filter_card_le) ✓
- Paper bridge lower bound (c/T) ✓ (proved from paper_bridge_recurrence)
- Quadratic recurrence lower bound (abstract) ✓
- Harmonic series divergence lemma ✓
- Z(xc) diverges ✓ (modulo paper_bridge_recurrence)
- HW summability ✓ (modulo paper_bridge_decomp_injection)
- Main theorem assembly ✓ (modulo sorry's)
- Subset product identity ✓
- Product convergence for geometric bounds ✓
- Monotone/antitone bounded convergence ✓
- Winding telescoping on hex lattice ✓
- Zigzag lower bound construction ✓
