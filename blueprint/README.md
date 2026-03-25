# Blueprint for the Connective Constant of the Honeycomb Lattice

This blueprint documents the formalization of the theorem that the connective constant of the hexagonal lattice equals √(2+√2), following the proof by Duminil-Copin and Smirnov (2012).

## Building the blueprint

### Prerequisites

```bash
pip install leanblueprint
```

### Building

From the project root:

```bash
# Build the web version
leanblueprint web

# Build the PDF version
leanblueprint pdf

# Build everything and check declarations
leanblueprint all

# Serve the web version locally
leanblueprint serve
```

## Structure

- `src/content.tex` — Main blueprint content
- `src/web.tex` — Web version wrapper
- `src/print.tex` — Print version wrapper
- `src/macros/` — LaTeX macros
- `src/blueprint.sty` — Blueprint style file
- `plastex.cfg` — PlasTeX configuration
