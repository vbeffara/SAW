# Summary of changes
## Summary of progress on SAW.tex formalization

### New files created (all sorry-free, fully compiled)

1. **`RequestProject/SAWQuadRecurrence.lean`** — Formalizes the abstract quadratic recurrence argument from Case 2 of the proof of Theorem 1 (Section 3 of the paper). Contains three fully proved lemmas:
   - `quadratic_lower_step`: If α·x² + x ≥ y with x ∈ (0,1], then x ≥ y/(1+α·y)
   - `quadratic_recurrence_lower_bound`: If B(T) ∈ (0,1] satisfies α·B(T+1)² + B(T+1) ≥ B(T), then B(T) ≥ min(B(1), 1/α)/T
   - `quadratic_recurrence_exists_lower`: Existence form of the above bound

2. **`RequestProject/SAWLowerBoundProof.lean`** — Formalizes the Case 2 lower bound structure from the paper. Contains four fully proved lemmas:
   - `not_summable_harmonic_lower`: If b(n) ≥ c/(n+1) with c > 0, then Σ b(n) diverges
   - `case2_B_lower_bound`: If 1 = c_α·A(T) + B(T) and A(T+1)-A(T) ≤ α·B(T+1)², then ∃ c > 0, B(T) ≥ c/T
   - `case2_bridge_sum_diverges`: Under Case 2 hypotheses, Σ B(T) = ∞

3. **`RequestProject/SAWObservableProof.lean`** — Infrastructure for the parafermionic observable proof. Contains three fully proved lemmas:
   - `paper_fin_strip_finite`: The finite strip PaperFinStrip T L has finitely many vertices
   - `paper_saw_b_finite`: The type PaperSAW_B T L is finite
   - `B_paper_eq_finsum`: B_paper is a finite sum (since the underlying type is finite)

### Blueprint updated

The blueprint (`blueprint/src/content.tex`) was updated with new sections documenting:
- The quadratic recurrence infrastructure (Section: "Quadratic recurrence")
- The observable infrastructure (Section: "Observable infrastructure")
- All new lemmas are linked to their Lean declarations with `\lean{}` and marked `\leanok`

### Remaining sorries on the critical path

The main theorem `connective_constant_eq` (μ = √(2+√2)) depends on three root sorry'd statements:

1. **`B_paper_le_one_direct`** (SAWStripIdentityCorrect.lean): The key consequence of the parafermionic observable — B_paper(T,L,xc) ≤ 1. This requires formalizing: (a) the discrete Stokes theorem on the hex lattice, (b) walk winding computations, (c) boundary contribution evaluation. This is the **fundamental gap** in the formalization.

2. **`bridge_decomposition_injection_proof`** (SAWHWDecomp.lean): The Hammersley-Welsh bridge decomposition counting inequality. Requires formalizing the recursive walk decomposition algorithm, injectivity, and weight accounting.

3. **`origin_bridge_lower_bound`** / **`origin_bridge_upper_bound`** (SAWBridgeFix.lean): Bridge partition function bounds for column bridges. Note: there is a **coordinate mismatch** between the column bridges used in the existing code (x-coordinate strips) and the paper's diagonal strips (x+y coordinate). The strip identity (B_paper ≤ 1) uses diagonal coordinates, but the Hammersley-Welsh infrastructure uses column coordinates. Resolving this mismatch is a key remaining task.

### Architecture notes

- The new quadratic recurrence results (`SAWQuadRecurrence.lean`) provide exactly the induction argument needed for the paper's Case 2 lower bound, once the strip identity is established
- The Case 2 bridge sum divergence (`SAWLowerBoundProof.lean`) cleanly composes the quadratic recurrence with harmonic series divergence
- The finiteness results (`SAWObservableProof.lean`) establish that B_paper is a finite sum, which is prerequisite for any computational or combinatorial proof of B_paper ≤ 1