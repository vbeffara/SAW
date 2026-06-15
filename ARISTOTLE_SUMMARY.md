# Summary of changes for run e1ca65fb-ca29-43d8-8322-d4d6d86119d6
Continued the SAW.tex formalization, working exclusively on the top-priority discrete Hopf Umlaufsatz and leaving all other branches untouched. The whole library still builds successfully (`lake build`, 8116 jobs, including `RequestProject/SAWFinal.lean`); all new declarations live in `RequestProject/SAWUmlaufPolygon.lean`, which is imported transitively from `SAWFinal` (`SAWUmlaufSignedArea → SAWUmlaufPolygon`).

What changed (all in `RequestProject/SAWUmlaufPolygon.lean`):

- The general planar-polygon Umlaufsatz `polygon_umlaufsatz` previously had a single monolithic `sorry`. It is now **proved**, factored into a clean ear-clipping induction:
  - `closeList_eq` (new, sorry-free): the public closing form `V ++ [V[0], V[1]]` equals the index-free `V ++ V.take 2` used by the induction.
  - `polygon_umlaufsatz_take` (new, **proved** modulo the single bundled core below): the Umlaufsatz in `take 2` closing form, by strong induction on `V.length` — base case `V.length = 3` is the already-proved `polyWind_triangle`, and the inductive step clips an ear via `polygon_ear_reduction`, which keeps total turning and orientation fixed while shortening the polygon.
  - `polygon_umlaufsatz` itself is now derived (sorry-free body) from `polygon_umlaufsatz_take` via `closeList_eq`.
  - `arg_ear_local_mod` (new, **proved sorry-free**): a reusable algebraic lemma — removing one vertex between its neighbours changes the local turning by a multiple of 2π (the turn ratios telescope so `exp(I·Δ)=1`). This is the "easy half" of the turning equality and is preparation for the exact ear step.

- All remaining topological content is now concentrated into a single, honestly-stated `sorry` lemma `polygon_ear_reduction` (a simple non-degenerate polygon with ≥4 vertices has an ear whose removal preserves planar simplicity, non-degeneracy, total turning and orientation — the two-ears / Jordan-curve-theorem-level core, absent from Mathlib). The second remaining Umlaufsatz gap, `hexEmbeddedPolygon_edges_disjoint` (honeycomb planarity), is unchanged.

Verification: the new `closeList_eq` and `arg_ear_local_mod` depend only on the standard axioms (`propext, Classical.choice, Quot.sound`); `polygon_umlaufsatz_take` reduces (via `sorryAx`) exactly to `polygon_ear_reduction` as designed. Partial progress is preserved as Lean files with honest sorries, and the documentation (`PROOF_STATUS.md`, `ARISTOTLE_SUMMARY.md`) was updated to reflect the new factoring and the two remaining cores.

# Summary of changes — Umlaufsatz ear-clipping round (newest)

Worked exclusively on the top-priority discrete Hopf Umlaufsatz, leaving all
other branches untouched. The whole library still builds successfully
(`lake build`, 8116 jobs, including `RequestProject/SAWFinal.lean`) and every new
declaration lives in `RequestProject/SAWUmlaufPolygon.lean`, imported
transitively from `SAWFinal` (via `SAWUmlaufSignedArea → SAWUmlaufPolygon`).

**Factored the planar Umlaufsatz into proven induction + one bundled core.**
The general planar-polygon Umlaufsatz `polygon_umlaufsatz`
(`RequestProject/SAWUmlaufPolygon.lean`) previously had a single monolithic
`sorry`. It is now **proved sorry-free from** a clean ear-clipping reduction:

* `closeList_eq` (NEW, sorry-free) — the public closing form
  `V ++ [V[0], V[1]]` equals the index-free `V ++ V.take 2` used by the
  induction.
* `polygon_umlaufsatz_take` (NEW, **proved sorry-free** modulo the bundled
  reduction below) — the Umlaufsatz in `take 2` closing form, by strong
  induction on `V.length`: base case `V.length = 3` is the already-proved
  `polyWind_triangle`; the inductive step clips an ear via
  `polygon_ear_reduction`, which keeps both the total turning and the
  orientation (sign of signed area) fixed while strictly shortening the polygon.
* `polygon_umlaufsatz` (now sorry-free) — derived from `polygon_umlaufsatz_take`
  via `closeList_eq`.
* `arg_ear_local_mod` (NEW, **proved sorry-free**) — the reusable algebraic
  "easy half" of the ear-step turning equality: removing one vertex `b` between
  `a` and `c` (preceded by `p`, followed by `q`) changes the local turning by a
  multiple of `2π` (the three turn ratios telescope to the two merged ratios, so
  `exp(I·Δ) = 1`). Isolates the purely-algebraic content; the exact-equality
  (`k = 0`) upgrade is the convexity content inside `polygon_ear_reduction`.

**Remaining Umlaufsatz gaps (two honest, genuinely-true topological cores):**
1. `polygon_ear_reduction` — ear existence + preservation of planar simplicity /
   non-degeneracy / turning / orientation under ear removal
   (two-ears / Jordan-curve-theorem-level; absent from Mathlib). This now
   concentrates *all* of the remaining topological content of the planar
   Umlaufsatz into a single statement; the base case and the entire inductive
   glue around it are proved sorry-free.
2. `hexEmbeddedPolygon_edges_disjoint` — honeycomb planarity (non-adjacent
   embedded edges are disjoint segments), a lattice-geometry fact absent from
   Mathlib.

All new lemmas depend only on `propext, Classical.choice, Quot.sound` (plus, for
the ones built on top of `polygon_ear_reduction`, the recorded `sorry`).

---

# Summary of changes for run dbbabf08-1f66-48fc-be7c-f6d5ae403050
Worked exclusively on the top-priority discrete Hopf Umlaufsatz, leaving all other branches untouched. The whole library still builds successfully (`lake build`, 8116 jobs) and every new declaration is imported transitively from `RequestProject/SAWFinal.lean` (via `SAWUmlaufSignedArea → SAWUmlaufPolygon`).

**Correctness fix (most important).** The general planar-polygon Umlaufsatz `polygon_umlaufsatz` (in `RequestProject/SAWUmlaufPolygon.lean`) was **false as previously stated**. `PolygonSimple` (`Nodup` + disjointness of non-adjacent edges) does not exclude three consecutive collinear vertices: for the collinear "spike" `a=0, b=2, c=1` the disjointness clause is vacuous and `Nodup` holds, yet `polyWind [a,b,c,a,b] = 2π` while the signed area `HexArea.shoelace2 [a,b,c] = 0`, so the claimed RHS `2π·sign(area)` would be `-2π ≠ 2π`. That made the existing `sorry` unfillable. I added a non-degeneracy hypothesis `polyNondeg (V ++ [V[0], V[1]])` (no flat/spike turns; every cyclic turn has nonzero cross product), which restores truth, and threaded it through the honeycomb consumer `hex_signed_turn_eq_six_sign_shoelace`.

**New sorry-free lemmas (all depend only on `propext, Classical.choice, Quot.sound`):**
- `polyNondeg` predicate + `hexTrailList_map_emb_polyNondeg` (embedding of any hex trail is non-degenerate, via `hex_turn_cross_ne_zero`);
- `hexClosedTrail_dropLast_append_trailList` (the closed vertex cycle `L.dropLast ++ [L[0], L[1]]` is a `HexTrailList`);
- `hexEmbeddedPolygon_polyNondeg` (discharges the new hypothesis for the honeycomb polygon, so the corrected statement is genuinely usable);
- `polyWind_triangle` — the **triangle base case** of the planar Umlaufsatz (`polyWind [a,b,c,a,b] = 2π·sign(signed area)` for a non-degenerate triangle), the base case of the ear-clipping induction.

**Remaining gaps (two clean, genuinely-true topological cores, now correctly stated):**
1. `polygon_umlaufsatz` — the turning-tangent theorem for a non-self-intersecting non-degenerate polygon; the triangle base case is now proved, leaving the ear-clipping induction whose irreducible content is the two-ears / Jordan-curve theorem (absent from Mathlib).
2. `hexEmbeddedPolygon_edges_disjoint` — honeycomb planarity (non-adjacent embedded edges are disjoint segments), a lattice-geometry fact absent from Mathlib.

Status notes were updated in `PROOF_STATUS.md` and `ARISTOTLE_SUMMARY.md`. Net effect: an unfillable (false-statement) `sorry` was replaced by a correct statement plus four verified building blocks, reducing the remaining Umlaufsatz content to two honest, well-documented topological cores.

# Summary of changes — Umlaufsatz round

Worked exclusively on the top-priority discrete Hopf Umlaufsatz, leaving all
other branches untouched. The whole library still builds successfully
(`lake build`, 8116 jobs) and every new declaration is imported transitively
from `RequestProject/SAWFinal.lean` (via
`SAWUmlaufSignedArea → SAWUmlaufPolygon`).

## Correctness fix (most important)

The general planar-polygon Umlaufsatz `polygon_umlaufsatz`
(`RequestProject/SAWUmlaufPolygon.lean`) was **false as previously stated**.
`PolygonSimple` (`Nodup` + disjointness of *non-adjacent* edges) does not
exclude three consecutive collinear vertices: for the collinear "spike"
`a = 0, b = 2, c = 1` the disjointness clause is vacuous and `Nodup` holds, yet
`polyWind [a,b,c,a,b] = arg(-1/2)+arg(1)+arg(-2) = 2π` while
`HexArea.shoelace2 [a,b,c] = 0`, so the claimed RHS `2π·sign(area)` would be
`-2π ≠ 2π`. The previous proof obligation was therefore unfillable.

**Fix.** Added a non-degeneracy hypothesis `polyNondeg (V ++ [V[0], V[1]])`
(every cyclic turn has nonzero cross product, i.e. no three consecutive
collinear vertices) to `polygon_umlaufsatz`, making the statement true. A new
predicate `polyNondeg` is defined for this. The hypothesis is genuinely
satisfied by the honeycomb embedding, and that fact is now **proved sorry-free**
(see below), so the hex Umlaufsatz core `hex_signed_turn_eq_six_sign_shoelace`
(in `SAWUmlaufSignedArea.lean`) still type-checks and is derived from a *true*
general statement.

## New sorry-free lemmas (all depend only on `propext, Classical.choice, Quot.sound`)

In `RequestProject/SAWUmlaufPolygon.lean`:

- `hexTrailList_map_emb_polyNondeg` — for any honeycomb trail `M`, the embedded
  chain `M.map correctHexEmbed` is non-degenerate (each consecutive triple is a
  genuine hex turn with cross `±√3/2 ≠ 0`, via `hex_turn_cross_ne_zero`).
- `hexClosedTrail_dropLast_append_trailList` — the closed honeycomb vertex cycle
  `L.dropLast ++ [L[0], L[1]]` is itself a `HexTrailList` (interior structure
  from `HexTrailList L`; the two closing turns from `hex_closure_adj` /
  `hex_closure_nobacktrack`; the junction no-backtrack from
  `hex_closed_trail_start_not_interior`).
- `hexEmbeddedPolygon_polyNondeg` — discharges the new `polyNondeg` hypothesis of
  `polygon_umlaufsatz` for the embedded honeycomb polygon.
- `polyWind_triangle` — the **triangle base case** of the planar Umlaufsatz:
  for a non-degenerate triangle, `polyWind [a,b,c,a,b] = 2π·sign(signed area)`.
  Proof: the three turn ratios have product `1` (so the arg sum is a multiple of
  `2π` via `Complex.arg_mul_coe_angle`), and the three triangle cross products
  are equal to the signed area (`shoelace2_triple`, `cross_triangle_eq_cross_edges`),
  so the three exterior angles share the area's sign and lie in `(-π,π)`, forcing
  the sum to be `±2π`. This is the base case of the ear-clipping induction.

## Remaining gaps (two clean, genuinely-true topological cores, now correctly stated)

1. `polygon_umlaufsatz` — the classical turning-tangent theorem for a
   non-self-intersecting *non-degenerate* polygon in `ℂ`. The triangle base case
   is now proved (`polyWind_triangle`); what remains is the ear-clipping
   induction whose irreducible content is the two-ears theorem (a simple polygon
   with `≥ 4` vertices has an ear and ear removal preserves planar simplicity) —
   Jordan-curve-theorem-level, absent from Mathlib.
2. `hexEmbeddedPolygon_edges_disjoint` — honeycomb planarity (non-adjacent edges
   of the embedded polygon are disjoint segments), a finite lattice geometry
   fact absent from Mathlib.

All analytic / combinatorial glue connecting the integer signed-turn count ↔
real turning ↔ signed-area sign remains proved sorry-free.
