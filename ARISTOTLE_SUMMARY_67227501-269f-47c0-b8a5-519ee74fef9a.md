# Summary of changes
## Summary of work done

I continued formalizing SAW.tex (the Duminil-Copin & Smirnov paper on the connective constant of the honeycomb lattice) by adding a new file and proving key infrastructure lemmas.

### New file: `RequestProject/SAWFiniteness.lean`

This file establishes finiteness and summability infrastructure for self-avoiding walks in finite strip domains, which is essential for connecting the abstract proof structure to the concrete partition functions. All lemmas are proved (zero sorries):

1. **`finiteStrip_finite`** — The set of vertices in the finite strip FiniteStrip T L is finite (contained in a bounded product of integer intervals).

2. **`saw_length_bound_in_strip`** — Any SAW staying within a finite strip has length bounded by the number of vertices in the strip (since paths visit each vertex at most once).

3. **`B_TL_summable`**, **`A_TL_summable`**, **`E_TL_summable`** — The partition functions B_{T,L}^x, A_{T,L}^x, E_{T,L}^x (defined as tsum over StripSAW types) are summable. This is proved by showing each StripSAW type is a Finite type (walks have bounded length in a finite domain, and for each length there are finitely many SAWs).

4. **`A_TL_mono`**, **`B_TL_mono`** — The partition functions A_{T,L} and B_{T,L} are monotone in L (enlarging the strip gives more walks, using `finite_strip_monotone`).

### Relationship to the paper

These results formalize properties that are implicit in Section 3 of the paper, where the partition functions A, B, E are used freely as finite sums:
- The paper defines A_{T,L}^x, B_{T,L}^x, E_{T,L}^x as sums over walks in the finite strip S_{T,L}
- Finiteness ensures these sums are well-defined
- Monotonicity in L is used in the passage from finite strips to infinite strips (as L → ∞)

The file imports from `SAWFiniteStrip.lean` (which defines the partition functions and strip domains) and does not duplicate any existing statements.

### Remaining sorry'd theorems

The project still has 7 sorry'd theorems in three files, which represent the deep combinatorial gaps:
- `strip_identity_concrete` — the concrete strip identity (Lemma 2), requiring the full parafermionic observable argument
- `origin_bridge_upper_bound/lower_bound` — bridge partition bounds, depending on the strip identity
- `Z_xc_diverges` — divergence of Z(x_c), depending on the bridge lower bound
- `hammersley_welsh_bound/injection` — the Hammersley-Welsh decomposition, requiring the bridge decomposition algorithm
- `B_T_inf_eq_origin_bridge` — connecting two equivalent bridge partition definitions

These remain the key gaps between the abstract proof structure (which is complete) and the concrete SAW counts on the hexagonal lattice.