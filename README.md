This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# The Connective Constant of the Honeycomb Lattice Equals √(2+√2)

Lean 4 formalization of the theorem from:

> Hugo Duminil-Copin and Stanislav Smirnov,
> "The connective constant of the honeycomb lattice equals √(2+√2)",
> *Annals of Mathematics*, 175(3), 1653–1665, 2012.

## Project Structure

### Core Files

| File | Contents | Status |
|------|----------|--------|
| `SAW.lean` | Core definitions (hex lattice, SAW, constants, algebraic identities, Fekete's lemma) | ✅ Complete |
| `SAWSubmult.lean` | Graph automorphisms, walk splitting, submultiplicativity c_{n+m} ≤ c_n·c_m | ✅ Complete |
| `SAWMain.lean` | Connective constant is a limit, positivity, conjectures | ✅ Complete |
| `SAWStrip.lean` | Strip domains, hex embedding, winding, vertex relation | ✅ Complete |

### Observable and Vertex Relation (Section 2)

| File | Contents | Status |
|------|----------|--------|
| `SAWObservable.lean` | Parafermionic observable, walk pairs/triplets, cancellation | ✅ Complete |
| `SAWVertex.lean` | Vertex relation (Lemma 1) details | ✅ Complete |
| `SAWPairTriplet.lean` | Geometric interpretation of pair/triplet cancellation | ✅ Complete |
| `SAWSymmetry.lean` | Conjugation symmetry F(z̄) = F̄(z) | ✅ Complete |

### Strip Identity and Proof Structure (Section 3)

| File | Contents | Status |
|------|----------|--------|
| `SAWStripIdentity.lean` | Strip identity (Lemma 2) from boundary evaluation | ✅ Complete |
| `SAWWinding.lean` | Winding angle computations | ✅ Complete |
| `SAWCutting.lean` | Cutting argument for bridge decomposition | ✅ Complete |
| `SAWDecomp.lean` | Bridge decomposition, convergence/divergence analysis | ✅ Complete |
| `SAWProof.lean` | Lower/upper bound proof structure | ✅ Complete |
| `SAWLowerBound.lean` | Complete lower bound assembly | ✅ Complete |

### Bridge Infrastructure

| File | Contents | Status |
|------|----------|--------|
| `SAWBridge.lean` | Bridge definition, partition function, main theorem chain | 🔶 1 sorry (HW bound) |
| `SAWBridgeFix.lean` | Corrected bridge partition (origin bridges) | 🔶 4 sorry's |
| `SAWHalfPlane.lean` | Half-plane walks, bridge sequence bounds | ✅ Complete |
| `SAWHammersleyWelsh.lean` | Hammersley-Welsh decomposition structure | ✅ Complete |

### Concrete Infrastructure

| File | Contents | Status |
|------|----------|--------|
| `SAWFiniteStrip.lean` | Finite strip domain S_{T,L}, partition functions A,B,E | 🔶 2 sorry's |
| `SAWFiniteness.lean` | Finiteness of SAWs in finite strips | ✅ Complete |
| `SAWStripWalks.lean` | Walks restricted to strip domains | ✅ Complete |
| `SAWCompute.lean` | Concrete computations, bridge existence | ✅ Complete |
| `SAWElementary.lean` | Elementary bounds on constants | ✅ Complete |
| `SAWLowerCount.lean` | Lower bound c_n ≥ √2^n | 🔶 2 sorry's |
| `SAWEquivalence.lean` | Equivalence between theorem formulations | ✅ Complete |

### Assembly

| File | Contents | Status |
|------|----------|--------|
| `SAWFinal.lean` | Final assembly: μ = √(2+√2) | 🔶 (depends on sorry'd lemmas) |
| `SAWConjectures.lean` | SLE convergence, critical exponents, Nienhuis/Flory conjectures | ✅ Complete |

## Remaining Gaps

The formalization is complete at the **abstract level**: all key identities,
the vertex relation (Lemma 1), the strip identity (Lemma 2), the bridge bounds
(B_T ≤ 1 and B_T ≥ c/T), and the case analysis (Cases 1 and 2) are fully proved.

The remaining sorry's are in connecting the abstract proof to concrete SAW counts:

1. **Hammersley-Welsh injection** (`hammersley_welsh_bound` in `SAWBridge.lean`):
   The combinatorial decomposition of every SAW into bridges.
   This is the deepest combinatorial result in the proof.

2. **Concrete strip identity** (`strip_identity_concrete` in `SAWFiniteStrip.lean`):
   Showing the abstract strip identity holds for the concrete partition functions.

3. **Elementary lower bound** (`connective_constant_ge_sqrt_two` in `SAWLowerCount.lean`):
   The bound μ ≥ √2 from the paper's introduction.

## Blueprint

The mathematical blueprint is in `blueprint/src/content.tex`, using standard
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) infrastructure.
Each theorem and definition is annotated with `\lean{LeanName}` to link to
the corresponding Lean declaration, and `\leanok` to mark fully proved items.

To build the blueprint:
```bash
pip install leanblueprint
cd blueprint/src && leanblueprint web
```

## Building

```bash
lake build
```

Requires Lean 4 with Mathlib (see `lean-toolchain` and `lakefile.toml`).
