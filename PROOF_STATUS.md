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

These are two formulations of Lemma 2 of Duminil-Copin & Smirnov (2012).
Both require the full parafermionic observable argument:

**The discrete Stokes argument:**
1. Define the parafermionic observable F(z) at each mid-edge z of the strip
2. The vertex relation (Lemma 1): at each vertex v, Σ_{w~v} D(v,w)·F(mid(v,w)) = 0
   This follows from pair_cancellation and triplet_cancellation (both PROVED)
3. Sum over all vertices (discrete Stokes): interior mid-edges cancel because
   D(u,v) + D(v,u) = 0 (proved as interior_edge_cancellation in SAWObservableNew.lean)
4. Only boundary mid-edges survive
5. Boundary evaluation:
   - Starting mid-edge a: F(a) = 1, direction = -1, contributes -1
   - Right boundary β: winding = 0, direction = +1, contributes B_paper/xc
   - Left boundary α\{a}: winding = ±π, contributes c_α · A/xc  
   - Escape boundary ε∪ε̄: winding = ±2π/3, contributes c_ε · E/xc
6. Identity: 0 = -1 + B/xc + c_α·A/xc + c_ε·E/xc, hence B_paper ≤ xc < 1

**What is proved:**
- Algebraic identities: pair_cancellation, triplet_cancellation
- Abstract discrete Stokes: interior_edge_cancellation (SAWObservableNew.lean)
- Direction vector computations: hexDir_tt_ff, hexDir_ff_tt, hexDir_start
- Boundary phase analysis: boundary_cos_pos, cos_five_pi_eight
- Left/right boundary directions: right_boundary_hexDir (+1), left_boundary_hexDir (-1)
- xc properties, strip domain definitions, SAW finiteness in finite strip
- B_paper ≤ 1 follows from infinite_strip_identity (SAWParafermionicProof.lean)
- Bridge recurrence follows from infinite_strip_identity + cutting argument
- T=1 special case: infinite_strip_identity_T1_clean (proved exactly)

**What is missing:**
- The combinatorial walk partition into pairs/triplets at each vertex
- The full discrete Stokes summation for the hex lattice strip
- Winding evaluation for boundary mid-edges (connecting to partition functions)
- Taking limits as L → ∞ for the infinite strip

## Sorry Chain 2: Hammersley-Welsh Decomposition

### Sorry 3: `paper_bridge_decomp_injection` in `SAWPaperChain.lean` (line 258)
∑_{n≤N} c_n x^n ≤ 2 · (∏_{T=1}^N (1+B_T(x)))²

**The Hammersley-Welsh argument:**
1. Every SAW γ from paperStart of length n ≤ N can be split at the
   first vertex of minimum diagCoord into two half-plane walks
2. Each half-plane walk decomposes into bridges of strictly decreasing widths
   (by induction on the width: find the last vertex of maximum diagCoord,
   extract the bridge, recurse on the remainder)
3. The bridge widths form subsets of {1,...,N}
4. Walk length ≥ sum of bridge lengths (extra edges for transitions)
5. Two choices for the first half-plane direction (factor of 2)
6. The decomposition uniquely determines the walk (injectivity)

**What is proved:**
- Bridge definitions: PaperBridge, paper_bridge_partition
- Bridge decay: B_T(x) ≤ (x/xc)^T / xc (uses Sorry 1)
- Product convergence: ∏(1+B_T(x)) < ∞ for x < xc
- Summability framework: Z(x) < ∞ follows from the injection + decay
- Bridge positivity, bridge-to-SAW injection bounds
- Powerset product identity: Finset.prod_one_add (from Mathlib)
- Walk splitting infrastructure: takeUntil, dropUntil, walk_split_lengths
- Translation: hexShift preserves adjacency

**What is missing:**
- The bridge decomposition algorithm (half-plane walk induction on width)
- General walk splitting at first vertex of minimal diagCoord
- Translation of extracted bridges to start from paperStart
- Injectivity of the decomposition (reverse reconstruction)
- Weight accounting (walk length ≥ sum of bridge lengths)

## Fully Proved Results (no sorry)

### Core Definitions and Properties
- Hexagonal lattice definition (hexGraph)
- SAW definition, SAW count, vertex independence
- Connective constant definition and limit property
- Critical fugacity xc, phase parameters λ, j, σ

### Submultiplicativity and Fekete
- c_{n+m} ≤ c_n · c_m (saw_count_submult')
- Connective constant is limit of c_n^{1/n} (connective_constant_is_limit')
- Connective constant is positive (connective_constant_pos')
- Iterated submultiplicativity: c_{km} ≤ c_m^k (saw_count_iter_submult)
- With remainder: c_{qm+r} ≤ c_m^q · c_r (saw_count_submult_with_remainder)
- Division-mod bound: c_n ≤ c_m^{⌊n/m⌋} · c_{n%m} (saw_count_div_mod_bound)
- Summability from root bound (partition_summable_of_geometric)

### Algebraic Identities
- pair_cancellation: j·λ̄⁴ + j̄·λ⁴ = 0
- triplet_cancellation: 1 + xc·j·λ̄ + xc·j̄·λ = 0
- Various boundary coefficient computations

### Direction Vectors (SAWObservableNew.lean)
- hexDir_tt_ff, hexDir_ff_tt: unit edge directions
- hexDir_neg: D(w,v) = -D(v,w)
- interior_edge_cancellation: D(v,w)·f + D(w,v)·f = 0
- right_boundary_hexDir, left_boundary_hexDir: boundary edge directions

### Strip Domain Analysis
- Cutting argument: A_{T+1} - A_T ≤ xc·B_{T+1}² (cutting_argument_proved)
- Bridge recurrence: B(T) ≤ c_α·B(T+1)² + B(T+1) (bridge_recurrence_proved)
- Bridge lower bound: B(T) ≥ c/T (paper_bridge_lower_bound)
- Bridge upper bound: B(T) ≤ 1/xc (paper_bridge_upper_bound)
- Z(xc) diverges (Z_xc_diverges_corrected)
- Z(x) convergence for x < xc (hw_summable_corrected, modulo HW decomposition)

### T=1 Special Case
- paper_bridge_partition_1_eq (exact value 2xc/(1-xc²))
- A_inf_1_exact (exact value 2xc³/(1-xc²))
- infinite_strip_identity_T1_clean (proved from exact values)

## File Organization
- `SAW.lean` — Core definitions and algebraic identities
- `SAWSubmult.lean` — Submultiplicativity proof
- `SAWMain.lean` — Fekete's lemma, connective constant
- `SAWIterSubmult.lean` — Iterated submultiplicativity and geometric summability
- `SAWObservableNew.lean` — Direction vector infrastructure for parafermionic observable
- `SAWStripIdentityCorrect.lean` — Strip domain, B_paper definition, B_paper ≤ 1 (sorry)
- `SAWCutting.lean`, `SAWCuttingProof.lean` — Cutting argument (proved)
- `SAWRecurrenceProof.lean` — Bridge recurrence from strip identity (sorry)
- `SAWPaperChain.lean` — Main proof assembly (sorry: HW decomposition)
- `SAWFinal.lean` — Final theorem statement

## Proof Architecture

The proof of μ = √(2+√2) requires exactly three independent facts:
1. **B_paper ≤ 1** (or equivalently the strip identity 1 = c_α·A + B + c_ε·E)
   → gives bridge upper bound B_T ≤ 1/xc
   → gives bridge decay B_T(x) ≤ (x/xc)^T / xc
2. **Bridge recurrence** B(T) ≤ α·B(T+1)² + B(T+1)
   → gives bridge lower bound B(T) ≥ c/T
   → gives Z(xc) = ∞ → μ ≥ 1/xc
3. **Hammersley-Welsh decomposition** Z(x) ≤ 2·(∏(1+B_T))²
   → combined with bridge decay, gives Z(x) < ∞ for x < xc → μ ≤ 1/xc

Facts 1 and 2 both follow from the parafermionic observable (Lemma 2).
Fact 3 is the bridge decomposition (independent of Lemma 2).
