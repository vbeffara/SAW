This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# The Connective Constant of the Honeycomb Lattice Equals √(2+√2)

Lean 4 formalization of the key results from:

> Hugo Duminil-Copin and Stanislav Smirnov,
> "The connective constant of the honeycomb lattice equals √(2+√2)",
> *Annals of Mathematics*, 175(3), 1653–1665, 2012.

## Status

- **18 Lean files**, ~6500 lines of formalized mathematics
- **2 remaining sorry's** in `SAWBridge.lean` (the bridge-to-SAW injection)
- All algebraic identities, vertex relation, strip identity, and proof structure fully proved

## Blueprint

See [`blueprint/README.md`](blueprint/README.md) for:
- Full dependency graph (Mermaid diagram)
- Paper-to-Lean mapping
- File structure overview
- Build instructions

The blueprint source is in `blueprint/src/content.tex` with `\lean` and `\leanok` annotations.
The dependency graph is also available as Graphviz DOT in `blueprint/dep_graph.dot`.

## Building

```bash
lake build
```

## Project Structure

| File | Description |
|------|-------------|
| `SAW.lean` | Core definitions, constants, algebraic identities, Fekete's lemma |
| `SAWSubmult.lean` | Translation/flip automorphisms, submultiplicativity |
| `SAWMain.lean` | Connective constant properties, conjectures |
| `SAWStrip.lean` | Strip domains, hex embedding, vertex relation |
| `SAWObservable.lean` | Parafermionic observable, pair/triplet vanishing |
| `SAWVertex.lean` | Vertex relation details |
| `SAWPairTriplet.lean` | Geometric interpretation |
| `SAWWinding.lean` | Winding angle computations |
| `SAWStripIdentity.lean` | Strip identity from boundary evaluation |
| `SAWElementary.lean` | Elementary bounds |
| `SAWHalfPlane.lean` | Half-plane walks |
| `SAWCutting.lean` | Cutting argument, HW injection |
| `SAWDecomp.lean` | Bridge decomposition analysis |
| `SAWProof.lean` | Lower/upper bound proof structure |
| `SAWLowerBound.lean` | Complete lower bound assembly |
| `SAWBridge.lean` | Bridge definition, partition function (**2 sorry's**) |
| `SAWEquivalence.lean` | Equivalence of formulations |
| `SAWFinal.lean` | Final theorem assembly |
| `SAWConjectures.lean` | SLE convergence, critical exponents |

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).
