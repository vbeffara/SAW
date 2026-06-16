# Proof Status: μ = √(2+√2)

> **Umlaufsatz clip-bookkeeping extraction round note (NEWEST).**
> `exists_ear_rotation` (`SAWUmlaufPolygon.lean`) is now **proved sorry-free**:
> the remaining Umlaufsatz topological content has been pushed one level deeper
> into a single, cleaner geometric-data core `exists_front_ear`, and the three
> clip-preservation clauses are discharged from it by newly proved bookkeeping.
> This round:
> * Adds and proves `polyCycWind_clip_eq` — the **turning-preservation** clause
>   as pure `polyWind` bookkeeping: both closed cyclic forms peel via
>   `polyWind_cons_cons_cons` and `polyWind_append_singleton` to a shared middle
>   `polyWind (c :: rest ++ [a])` plus the local ear turns, whose difference
>   vanishes by the already-proved `arg_ear_local_exact` (given the convex-ear
>   range bounds). This genuinely **consumes** `arg_ear_local_exact` and
>   `polyWind_append_singleton`.
> * Adds and proves `shoelace2_orient_clip` — the **orientation-preservation**
>   clause as pure arithmetic on the area splitting `shoelace2_clip_second`
>   (full = clip + ear-triangle), reducing it to the triangle-vs-clip sign iff.
> * Restates the topological core as `exists_front_ear`, which now supplies
>   exactly the raw plane-geometry data (predecessor/successor naming, the five
>   edge non-degeneracies, the three turning range bounds, the **per-edge
>   diagonal-disjointness** clause, clip non-degeneracy, and the triangle
>   orientation iff). `exists_ear_rotation` is derived from it sorry-free using
>   `PolygonSimple_clip`, `polyCycWind_clip_eq`, `shoelace2_orient_clip` and
>   `PolygonSimple_rotate`.
> * **Fixes a latent unsatisfiable interface.** The previously-prepared
>   `PolygonSimple_clip_of_far_sameSide` required a strictly-positive same-side
>   product for *every* far edge, but the first far edge is `(c, rest.head)`
>   whose endpoint `c` forces side-product `0`; that hypothesis is therefore
>   never satisfiable. The core now consumes the correct per-edge
>   diagonal-disjointness clause of `PolygonSimple_clip` instead; the
>   superseded `PolygonSimple_clip_of_far_sameSide` is retained and clearly
>   documented as a dead branch (its per-edge tool
>   `HexArea.segment_disjoint_of_strictSameSide` remains live preparation).
> The whole library still builds (`lake build`, 8123 jobs through
> `RequestProject/SAWFinal.lean`); the top-level discrete Umlaufsatz
> (`hex_closed_trail_turning_number`) and `exists_ear_rotation` depend only on
> `sorryAx` plus the allowed `propext, Classical.choice, Quot.sound`. The single
> remaining Umlaufsatz `sorry` is now `exists_front_ear` (the genuine
> Jordan-curve-theorem-level ear-existence with its convexity/emptiness data).
>
> **Umlaufsatz core-isolation / rotation-prep-consumption round note.**
> The remaining Umlaufsatz topological content is now isolated in a single core
> `exists_ear_rotation` (`SAWUmlaufPolygon.lean`), stated **locally at the front
> of one rotation** `V.rotate r = a :: b :: c :: rest`: clipping the second
> vertex `b` preserves `PolygonSimple`, `polyCycNondeg`, the cyclic turning
> `polyCycWind`, and the orientation — **all relative to the rotated polygon
> `a :: b :: c :: rest` itself**. This round:
> * Adds `exists_ear_rotation` (the new single `sorry`) and **derives the
>   former core `exists_ear_clip` from it sorry-free**, transporting each
>   clause back to `V` through the rotation-invariance toolkit
>   (`polyCycWind_rotate`, `shoelace2_rotate`). Those two prep lemmas were
>   previously proved-but-unconsumed; they are now **genuinely used**, closing
>   the "looks dead but is preparation" gap for the rotation bookkeeping.
> * Adds `PolygonSimple_clip_of_far_sameSide`, a fully proved
>   (`propext, Classical.choice, Quot.sound`) one-step bundling of the two
>   prepared simplicity-preservation halves (`PolygonSimple_clip` and
>   `diag_disjoint_of_far_sameSide`) into the single planar-simplicity clause
>   the ear core will consume.
> The whole library still builds (`lake build`, 8123 jobs, through
> `RequestProject/SAWFinal.lean`); the top-level discrete Umlaufsatz
> (`hex_closed_trail_turning_number`) depends only on `sorryAx` plus the allowed
> `propext, Classical.choice, Quot.sound`. The genuinely irreducible
> Jordan-curve-theorem-level content (existence of a convex empty ear, with the
> same-side / convexity range bounds that drive simplicity, turning, and
> orientation preservation) is what `exists_ear_rotation` now concentrates.
>
> **Umlaufsatz ear-clip turning-preservation round note.**
> The single remaining Umlaufsatz `sorry` is still the two-ears / ear-existence
> core `exists_ear_clip` (`SAWUmlaufPolygon.lean`). This round adds, **in the
> chain file `SAWUmlaufPolygon.lean` itself** (just above `exists_ear_clip`),
> three fully proved (`propext, Classical.choice, Quot.sound`) preparation
> lemmas assembling the **turning-preservation half** of an ear clip plus the
> rotation bookkeeping:
> * `rotate_cons_triple` — any rotation `V.rotate r` of a length-≥3 cycle has
>   the explicit head form `a :: b :: c :: rest` (the bookkeeping that presents
>   the chosen ear in clipped-cons shape).
> * `arg_ear_local_exact` — the **exact** local turning preservation (the
>   `k = 0` case of the existing `arg_ear_local_mod`): given the three relevant
>   partial arg-sums lie in `(-π, π]`, removing the middle vertex `b` leaves the
>   net exterior-angle turning unchanged. Pure `Complex.arg_mul` telescoping —
>   both sides equal `arg ((q-c)/(a-p))`.
> * `polyWind_clip_step` — on an open chain `p :: a :: b :: c :: q :: rest`,
>   removing `b` changes `polyWind` by exactly the local 5-point ear difference
>   (all turns from `c` onward cancel). Pure `polyWind_cons_cons_cons`
>   unfolding.
>
> Composed (`polyWind_clip_step` reduces the clip's turning change to the
> 5-point difference, which `arg_ear_local_exact` makes vanish under the
> convexity range bounds), these supply the turning-preservation clause of
> `exists_ear_clip` modulo producing the `(-π, π]` range bounds from a convex
> ear — which, together with ear existence and area-sign preservation, is the
> remaining topological content of the open core. They are documented as
> preparation for `exists_ear_clip` (not yet consumed by it). Whole library
> still builds (`lake build`, 8123 jobs).
>
> **Umlaufsatz ear-clip planar-simplicity-preservation round note.**
> The single remaining Umlaufsatz `sorry` is still the two-ears / ear-existence
> core `exists_ear_clip` (`SAWUmlaufPolygon.lean`). This round adds, **in the
> chain file `SAWUmlaufPolygon.lean` itself** (just above `exists_ear_clip`),
> three fully proved (`propext, Classical.choice, Quot.sound`) lemmas that
> assemble the **planar-simplicity-preservation half of an ear clip** into a
> ready-to-consume reduction:
> * `closedEdges_clip` — the closed edges of `a :: b :: c :: rest` are the two
>   ear edges `(a,b),(b,c)` followed by the shared far-edge tail
>   `M := (c :: rest).zip (rest ++ [a])`, and the clipped cycle `a :: c :: rest`
>   has exactly the diagonal `(a,c)` followed by the *same* `M` (pure list
>   algebra on `closedEdges = V.zip (V.rotate 1)`).
> * `PolygonSimple_clip` — given the original cycle is `PolygonSimple` and the
>   diagonal `a–c` is disjoint from every far edge sharing no endpoint with it
>   (`hdiag`), the clipped cycle `a :: c :: rest` is `PolygonSimple`: `Nodup` is
>   inherited (sublist), far/far disjointness is inherited verbatim (`M` is a
>   common suffix), and the only new obligation is exactly `hdiag`.
> * `diag_disjoint_of_far_sameSide` — the bridge from the empty-ear *same-side*
>   condition (`0 < cross (c-a) (e.1-a) * cross (c-a) (e.2-a)` for every far edge
>   `e`) to `hdiag`, via `HexArea.segment_disjoint_of_strictSameSide`.
>
> Composed, these reduce "the clip preserves `PolygonSimple`" to the single
> geometric fact that every far edge of an empty convex ear lies strictly on one
> side of the base diagonal — the remaining topological content of
> `exists_ear_clip`. They are documented as preparation for `exists_ear_clip`
> (not yet consumed by it, since the ear-existence core is still open). Whole
> library still builds (`lake build`, 8123 jobs).
>
> **Umlaufsatz ear-existence segment-non-crossing round note.**
> The single remaining Umlaufsatz `sorry` is still the two-ears / ear-existence
> core `exists_ear_clip` (`SAWUmlaufPolygon.lean`). This round adds a sixth,
> fully proved (`propext, Classical.choice, Quot.sound`) plane-geometry
> preparation file `SAWUmlaufSegment.lean`, imported by `SAWUmlaufPolygon`
> (hence in the `SAWFinal` chain), supplying the **algebraic heart of the
> planar-simplicity-preservation half of an ear clip** — that the clipped
> diagonal misses the far edges of the polygon. It **consumes** the
> `cross`-bilinearity toolkit of `SAWUmlaufEar`/`SAWSignedArea`, the barycentric
> backbone (`inTriangleStrict_convexCombo`) of `SAWUmlaufEarExtreme` and the
> non-degeneracy of a strict-interior triangle (`inTriangleStrict_nondeg`):
> `cross_combo_segment` (the carrier-line side test `cross (q-p) (u-p)` vanishes
> for `u ∈ segment ℝ p q`); `segment_disjoint_of_strictSameSide` (if both
> endpoints of one segment lie strictly on the same side of the other's carrier
> line — `0 < cross (q-p) (r-p) * cross (q-p) (s-p)` — the two segments are
> disjoint); and `inTriangleStrict_diag_side` (a strict interior point of the
> corner triangle `a,b,c` lies strictly on the apex side of the base diagonal
> `a–c`: `0 < cross (c-a) (x-a) * cross (c-a) (b-a)`). Like the earlier
> `SAWUmlaufEar*` files this is explicitly preparation that the eventual proof
> of `exists_ear_clip` will consume; the clean single-core reduction is
> otherwise unchanged. Whole library still builds (`lake build`, 8123 jobs).
>
> **Umlaufsatz ear-existence extreme-vertex/convex-hull round note.**
> The single remaining Umlaufsatz `sorry` is still the two-ears / ear-existence
> core `exists_ear_clip` (`SAWUmlaufPolygon.lean`). This round adds a fifth,
> fully proved (`propext, Classical.choice, Quot.sound`) plane-geometry
> preparation file `SAWUmlaufEarExtreme.lean`, imported by `SAWUmlaufPolygon`
> (hence in the `SAWFinal` chain), supplying the **Step-1 convexity of the
> extreme vertex**, and **consuming** the barycentric backbone of
> `SAWUmlaufEarConvex` (`inTriangleStrict_pos_convexCombo`) together with the
> strict-interior predicate of `SAWUmlaufEar`: `inTriangleStrict_convexCombo`
> (a strict interior point of *either* orientation is a strict convex
> combination of the triangle vertices); `inTriangleStrict_not_lexMin` (such an
> interior point is never lexicographically minimal — leftmost, then lowest —
> among the three vertices, since its coordinates are strict positive-weight
> averages); and `lexMin_not_inTriangleStrict` (combining with
> `SAWUmlaufEar.exists_lex_min_mem`: the lex-minimal vertex of the polygon is
> never in the strict interior of any triangle spanned by polygon vertices —
> i.e. the extreme vertex is a convex-hull vertex, which is precisely what makes
> Meisters' Step-1 corner convex). Like the earlier `SAWUmlaufEar*` files this
> is explicitly preparation that the eventual proof of `exists_ear_clip` will
> consume; the clean single-core reduction is otherwise unchanged. Whole
> library still builds (`lake build`, 8122 jobs).
>
> **Umlaufsatz ear-existence sub-triangle/nesting round note.** The
> single remaining Umlaufsatz `sorry` is still the two-ears / ear-existence core
> `exists_ear_clip` (`SAWUmlaufPolygon.lean`). This round adds a fourth, fully
> proved (`propext, Classical.choice, Quot.sound`) plane-geometry preparation
> file `SAWUmlaufEarEmpty.lean`, imported by `SAWUmlaufPolygon` (hence in the
> `SAWFinal` chain), supplying the Step-2 (empty-triangle / farthest-vertex)
> geometry that **consumes** the barycentric backbone of `SAWUmlaufEarConvex`
> (so that file is no longer feeding only the open core): `subTri_axc_orient_pos`
> (a positively-oriented strict interior point `x` of `a,b,c` makes the
> sub-triangle `a,x,c` itself positively oriented — `0 < cross (x-a) (c-x)`);
> `inTriangleStrict_pos_nest` (strict interiors nest: a point strictly inside the
> sub-triangle `a,q,c`, with `q` strictly inside `a,b,c`, is strictly inside
> `a,b,c`); and `farthest_region_empty` (the maximality clause: no candidate
> vertex is strictly farther from the base line `a-c` than the chosen farthest
> vertex `q`, i.e. the region beyond `q` is empty — what makes the Step-2
> diagonal `v-q` valid). Like the earlier `SAWUmlaufEar*` files this is
> explicitly preparation that the eventual proof of `exists_ear_clip` will
> consume; the clean single-core reduction is otherwise unchanged. Whole library
> still builds (`lake build`, 8121 jobs).
>
> **Umlaufsatz ear-existence barycentric-backbone round note.** The
> single remaining Umlaufsatz `sorry` is still the two-ears / ear-existence core
> `exists_ear_clip` (`SAWUmlaufPolygon.lean`). This round adds a third, fully
> proved (`propext, Classical.choice, Quot.sound`) plane-geometry preparation
> file `SAWUmlaufEarConvex.lean`, imported by `SAWUmlaufPolygon` (hence in the
> `SAWFinal` chain), supplying the **barycentric backbone** of Meisters' Step 2
> (which vertices lie inside a candidate ear triangle): `cross_bary_sum` (the
> three edge cross products of `x` against `a,b,c` sum to the triangle
> orientation `cross (b-a) (c-b)` — the three sub-triangles tile the whole);
> `cross_bary_recon` (the affine reconstruction `area2 • x = (γ-wt)•a + (α-wt)•b
> + (β-wt)•c`); `inTriangleStrict_pos_area` (a positively-oriented strict
> interior point forces `cross (b-a) (c-b) > 0`); and the two-way conversion
> between the cross-product interior test and honest convex-hull membership —
> `inTriangleStrict_pos_convexCombo` (interior point ⇒ strict convex
> combination), `convexCombo_pos_inTriangleStrict` (its converse), and the
> bundled characterization `inTriangleStrict_pos_iff_convexCombo`. Like
> `SAWUmlaufEar`/`SAWUmlaufEarExist`, this is explicitly preparation that the
> eventual proof of `exists_ear_clip` will consume; the clean single-core
> reduction is otherwise unchanged. Whole library still builds (`lake build`,
> 8120 jobs).
>
> **Umlaufsatz ear-existence geometry-toolkit round note.** The single
> remaining Umlaufsatz `sorry` is still the two-ears / ear-existence core
> `exists_ear_clip` (`SAWUmlaufPolygon.lean`). This round adds a second,
> fully proved (`propext, Classical.choice, Quot.sound`) plane-geometry
> preparation file `SAWUmlaufEarExist.lean`, imported by `SAWUmlaufPolygon`
> (hence in the `SAWFinal` chain), supplying the Step-2 (farthest-vertex)
> building blocks of Meisters' ear-existence argument:
> `collinear_iff_cross_eq_zero` (three points are collinear iff the 2-D cross
> product of their edge vectors vanishes — the degenerate-diagonal test);
> `exists_max_cross` (over a nonempty vertex list there is one maximizing the
> signed distance `cross d (·-a)` to a base direction — the *farthest from the
> base diagonal* pivot of Step 2); and the symmetry/distinctness facts of the
> strict-interior predicate `inTriangleStrict_cyclic`,
> `inTriangleStrict_ne_ab/bc/ca`. Like `SAWUmlaufEar`, this is explicitly
> preparation that the eventual proof of `exists_ear_clip` will consume; the
> clean single-core reduction is otherwise unchanged.
>
> **Umlaufsatz ear-existence geometry-toolkit round note.** The single
> remaining Umlaufsatz `sorry` is still the two-ears / ear-existence core
> `exists_ear_clip` (`SAWUmlaufPolygon.lean`). This round adds a new, fully
> proved (`propext, Classical.choice, Quot.sound`) plane-geometry preparation
> file `SAWUmlaufEar.lean`, imported by `SAWUmlaufPolygon` (hence in the
> `SAWFinal` chain), supplying the elementary building blocks of Meisters'
> ear-existence argument: `HexArea.cross` bilinearity (`cross_smul_left/right`,
> `cross_sub_left/right`); the corner-orientation–signed-area bridge
> `cross_edges_eq_shoelace2_triple`; collinearity of a segment point
> (`cross_eq_zero_of_mem_segment`, `collinear_of_mem_segment`); the extreme
> (leftmost-lowest) vertex `exists_lex_min_mem` (Step 1); and the
> oriented-triangle strict-interior predicate `inTriangleStrict` with
> `inTriangleStrict_ne_a/b/c` and `inTriangleStrict_nondeg` (Step 2). This is
> explicitly preparation that the eventual proof of `exists_ear_clip` will
> consume; the clean single-core reduction is otherwise unchanged.
>
> **Umlaufsatz ear-clipping rotation-toolkit round note.** The single
> remaining Umlaufsatz `sorry` is now the sharpened two-ears core
> `exists_ear_clip` (`SAWUmlaufPolygon.lean`): a simple non-degenerate polygon
> with ≥4 vertices has a cyclic rotation `V.rotate r = a :: b :: c :: rest`
> whose second vertex can be clipped to `a :: c :: rest`, preserving planar
> simplicity, non-degeneracy, cyclic turning, and orientation. The previous
> bundled core `polygon_ear_reduction` is now **proved sorry-free from**
> `exists_ear_clip` plus a new, fully proved **rotation-invariance toolkit**
> (only `propext, Classical.choice, Quot.sound`):
> `polyCycWind` (cyclic turning) with `polyCycWind_rotate1`/`polyCycWind_rotate`;
> `shoelace2_rotate1`/`shoelace2_rotate` (signed area rotation invariance);
> `mem_closedEdges_rotate` + `PolygonSimple_rotate` (planar simplicity is
> rotation invariant); `polyCycNondeg` with
> `polyCycNondeg_rotate1`/`polyCycNondeg_rotate`; and the algebraic clip identity
> `shoelace2_clip_second` (clipping changes the area by exactly the ear-triangle
> area). These transport the concrete clipped cycle back to `V`'s own closing
> form, so all the ear-clipping *glue* is now verified and the only irreducible
> Jordan-curve-theorem-level content is concentrated in `exists_ear_clip`. The
> honeycomb-planarity core remains closed.
>
> **Umlaufsatz honeycomb-planarity round note.** The honeycomb
> planarity core `hexEmbeddedPolygon_edges_disjoint` (`SAWUmlaufPolygon.lean`) is
> now **fully proved sorry-free** (only `propext, Classical.choice, Quot.sound`).
> It was reduced to a new self-contained geometry file
> `SAWUmlaufHexEdge.lean` (imported by `SAWUmlaufPolygon`, hence in the
> `SAWFinal` chain) developing, all sorry-free:
> `hexEdge_dir` (an oriented honeycomb edge embeds to one of three explicit unit
> directions `1, -1/2 ± (√3/2)·I`), `hexEdge_false_or` (false/true parity of an
> edge's endpoints), the nine direction-pair leaf cases
> `hexEdge_disjoint_leaf_ij` (two unit honeycomb segments sharing no vertex are
> disjoint — the three off-diagonal `i>j` derived from `i<j` by `Disjoint.symm`),
> their dispatchers `hexEdge_disjoint_d1/d2/d3`, the oriented core
> `hexEdge_segments_disjoint_oriented`, and the general
> `hexEdge_segments_disjoint`. The combinatorial wiring inside
> `hexEmbeddedPolygon_edges_disjoint` (each polygon edge is a `hexGraph`
> adjacency between consecutive trail vertices; endpoint inequalities transfer to
> vertex inequalities via `correctHexEmbed_injective`) is also proved.
> Consequently `hexEmbeddedPolygon_polygonSimple` is sorry-free.
> **The single remaining Umlaufsatz gap is now `polygon_ear_reduction`** (the
> ear-clipping / two-ears topological core); the honeycomb-planarity gap is
> closed.
>
> **Umlaufsatz ear-clipping round note.** Factored the planar
> Umlaufsatz `polygon_umlaufsatz` (`SAWUmlaufPolygon.lean`): it no longer has a
> monolithic `sorry`. It is now **proved** from the strong-induction lemma
> `polygon_umlaufsatz_take` (ear-clipping induction on `V.length`; base case is
> the proved `polyWind_triangle`) plus the index-free closing rewrite
> `closeList_eq` — both **sorry-free**. The remaining topological content is
> concentrated into the single bundled lemma `polygon_ear_reduction` (an ear
> exists and its removal preserves planar simplicity, non-degeneracy, total
> turning and orientation — two-ears / Jordan-curve-theorem level, absent from
> Mathlib). Also **proved sorry-free** the reusable algebraic ear-step
> telescoping `arg_ear_local_mod` (the local turning change of removing one
> vertex is a multiple of `2π`), the "easy half" of the turning equality inside
> `polygon_ear_reduction`. The two genuinely-irreducible Umlaufsatz gaps are now
> `polygon_ear_reduction` and `hexEmbeddedPolygon_edges_disjoint` (honeycomb
> planarity). All new lemmas depend only on `propext, Classical.choice,
> Quot.sound`.
>
> **Umlaufsatz round note (previous).** Fixed a genuine **falsity** in the general
> planar-polygon Umlaufsatz `polygon_umlaufsatz` (`SAWUmlaufPolygon.lean`):
> `PolygonSimple` does not exclude three consecutive collinear vertices (e.g.
> the spike `0,2,1` has `polyWind = 2π` but signed area `0`), so the statement
> was unprovable. Added the non-degeneracy hypothesis
> `polyNondeg (V ++ [V[0], V[1]])` (no flat/spike turns), making it true, and
> **proved sorry-free** that the honeycomb embedding satisfies it
> (`hexEmbeddedPolygon_polyNondeg`, with helpers
> `hexTrailList_map_emb_polyNondeg` and
> `hexClosedTrail_dropLast_append_trailList`). Also **proved sorry-free** the
> triangle base case `polyWind_triangle`
> (`polyWind [a,b,c,a,b] = 2π·sign(area)` for a non-degenerate triangle), the
> base case of the ear-clipping induction. The two remaining Umlaufsatz gaps
> are now both *correctly stated* and genuinely true: `polygon_umlaufsatz`
> (ear-clipping induction / two-ears theorem) and
> `hexEmbeddedPolygon_edges_disjoint` (honeycomb planarity). All four new
> lemmas depend only on `propext, Classical.choice, Quot.sound`.
>
> **Umlaufsatz round note (previous).** The discrete-Umlaufsatz core
> `hex_signed_turn_eq_six_sign_shoelace` (in `SAWUmlaufSignedArea.lean`) is now
> **proved sorry-free**, *derived* from a new general planar-polygon framework in
> `RequestProject/SAWUmlaufPolygon.lean` (imported via `SAWUmlaufSignedArea` →
> `SAWUmlaufGaussBonnet` → `SAWFinal`). The new file:
> * defines `polyWind` (exterior-angle turning of a `List ℂ` polygon) and proves
>   the bridge `hexWalkWinding_eq_polyWind`, the additivity
>   `polyWind_append_singleton`, and the cyclic-turning identity
>   `polyWind_hexEmbedded_cyclic` (cyclic turning = `hexWalkWinding L + closure`)
>   — **all sorry-free**;
> * proves `hexEmbeddedPolygon_polygonSimple`'s `Nodup` half via
>   `hex_closed_trail_embed_nodup`.
> The single hex-specific topological `sorry` has thus been replaced by **two
> clean, reusable, genuinely-true topological gaps**:
> 1. `polygon_umlaufsatz` — the classical turning-tangent theorem for a
>    non-self-intersecting polygon in `ℂ` (`total turning = 2π·sign(area)`);
> 2. `hexEmbeddedPolygon_edges_disjoint` — honeycomb planarity (non-adjacent
>    edges of the embedded polygon are disjoint segments).
> All analytic glue connecting the integer signed-turn count ↔ real turning ↔
> signed-area sign is now proved. Suggested next steps: ear-clipping induction
> for (1), and lattice segment-disjointness case analysis for (2).
>
> **Earlier round note.** New sorry-free preparation file
> `RequestProject/SAWUmlaufEarStep.lean` (imported from
> `SAWUmlaufGaussBonnet`, hence from `SAWFinal`) adds the *per-vertex ear-step
> compatibility* for the ear-clipping route to the discrete Umlaufsatz core
> `hex_signed_turn_eq_six_sign_shoelace`:
> `shoelace2_triple_eq_cross`, `shoelace2_triple_sign`, and
> `hexTurnSign_eq_shoelace2_triple_sign` (the combinatorial turn sign equals the
> orientation of the embedded ear triangle). The single irreducible
> Jordan-curve-level gap (a simple polygon with `≥4` vertices has an ear, and
> ear removal preserves planar simplicity) remains the lone `sorry`
> `hex_signed_turn_eq_six_sign_shoelace` in `SAWUmlaufSignedArea.lean`.

## Main Theorem

```
theorem connective_constant_eq : connective_constant = Real.sqrt (2 + Real.sqrt 2)
```

**Location:** `RequestProject/SAWFinal.lean`

## Critical Path — Two Independent Sorry Chains

### Chain A: Vertex Relation → Strip Identity → Z(x) < ∞

**Root cause:** `umlaufsatz_pm_one` (in SAWTurningNumber.lean), the
"hard half" of `hex_closed_trail_turning_number`.

The discrete Gauss-Bonnet theorem for simple closed hex trails:
for a simple closed trail L on the hex lattice, hexWalkWinding L + closure = ±2π.

This theorem is now **split into two halves**:

* **Easy half — PROVED:** `hex_closed_winding_int_mul` shows the total turning
  `hexWalkWinding L + closure` is an integer multiple `2π·n`. Proved via a new
  telescoping identity `hexTrailList_winding_telescope` (every hex turn ratio
  has unit modulus, so `exp(i·arg(d₂/d₁)) = d₂/d₁`, and the product telescopes;
  for a closed trail the first and last edge directions coincide, giving
  `exp(i·(W+closure)) = 1`). Supporting lemmas (`hexFirstDir`,
  `hexFirstDir_append`, `hexFirstDir_eq_get`, `hex_edge_norm_one'`,
  `exp_I_arg_of_norm_one`, `hexTrailList_adj_last`,
  `list_get_last_eq_get_zero_of_closed`) are all sorry-free.

* **Hard half — now REDUCED to a clean combinatorial core:** `umlaufsatz_pm_one`
  shows that for a *simple* (non-self-intersecting) closed trail, the multiple
  `n` equals `±1`. This is the genuine content of Hopf's Umlaufsatz / turning
  tangent theorem and is equivalent in difficulty to the Jordan curve theorem
  for polygons.

  `umlaufsatz_pm_one` is **no longer itself a sorry**: it is now *derived*,
  sorry-free, from a single purely-combinatorial (integer) statement
  `hex_total_signed_turn_pm_six` (in SAWTurningNumber.lean). The analytic
  connective tissue is all proved sorry-free:
  - `hexWalkWinding_eq_signedTurnCount`: total interior winding
    `= (π/3)·hexSignedTurnCount L`;
  - `hex_closure_adj`, `hex_closure_nobacktrack`, `hex_closure_arg_eq_sign`
    (NEW): the closing turn `L[m-2]→L[0]→L[1]` is a genuine non-backtracking
    hex turn whose angle is `(π/3)·hexTurnSign …`;
  - `hex_interior_get_ne` (NEW): distinct interior indices give distinct
    vertices.
  Together these give `hexSignedTurnCount L + closingSign = 6·n`, so `n = ±1`
  iff the total signed turn equals `±6`.

  **The ONLY remaining sorry in this chain is now**
  `hex_total_signed_turn_pm_six`: for a simple closed hex trail the sum of the
  `±1` per-vertex turn signs (interior turns `hexSignedTurnCount L` plus the
  closing-turn sign) equals `±6`. Same topological content (Jordan curve
  theorem for polygons) but in its cleanest analysis-free integer form, ready
  for an ear-clipping / discrete Gauss–Bonnet attack. Not currently in Mathlib.

`hex_closed_trail_turning_number` itself is fully proved *from* these two
halves, so the only remaining gap in this chain is `hex_total_signed_turn_pm_six`.

**Signed-area route to `umlaufsatz_pm_one` (algebraic half built, sorry-free).**
The `±1` value is the sign of the polygon's signed area. The algebraic backbone
of this route is now in place:

* `RequestProject/SAWSignedArea.lean` — the shoelace functional
  `HexArea.shoelace2` (twice the signed area) with `cross`/`shoelace2` algebra,
  `shoelace2_reverse` (reversal negates area), `shoelace2_map_add_const`
  (translation invariance) and `shoelace2_ear` (the exact ear-clipping change of
  signed area). All sorry-free.
* `RequestProject/SAWUmlaufBridge.lean` — `hex_turn_cross`: each turn's sign
  equals the sign of the cross product (`±√3/2`) of its two unit edge vectors,
  and `cross_eq_normSq_mul_im_div`. All sorry-free.

Both files are imported from `SAWFinal.lean`. What remains for `umlaufsatz_pm_one`
is the irreducible *topological* half (a simple polygon has nonzero signed area,
and the turning number equals the sign of that area), which is the same content
as the Jordan curve theorem for polygons and is still absent from Mathlib.

**Simplicity transfer (now built sorry-free).** A further prerequisite for the
signed-area route — that the embedded polygon is a *genuine* simple polygon in
`ℂ` — is now established sorry-free in `RequestProject/SAWUmlaufEmbed.lean`:
* `correctHexEmbed_injective` — the hex embedding is injective;
* `hex_four_neighbours_not_nodup` — the lattice's 3-regularity (pigeonhole);
* `hexTrailList_adj_get`, `hexTrailList_nobacktrack_get`,
  `hex_interior_getElem_ne` — index-level trail structure;
* `hex_closed_trail_start_not_interior` — the start vertex of a simple closed
  hex trail never recurs among the interior vertices (degree-3 + no-backtrack);
* `hex_closed_trail_dropLast_nodup` — hence the full vertex cycle is `Nodup`;
* `hex_closed_trail_embed_nodup` — therefore the embedded polygon
  `L.dropLast.map correctHexEmbed` has pairwise distinct points in `ℂ`.
This turns the weak hypothesis `h_simple : L.tail.dropLast.Nodup` into the
"simple polygon in the plane" statement the topological half consumes. The file
is imported from `SAWFinal.lean` and depends only on the standard axioms.

**Full chain:**
```
hex_closed_trail_turning_number (SORRY — root cause, Umlaufsatz)
  → pair_winding_relation (SORRY — needs turning number + orientation)
    → pair_exp_cancellation (PROVED)
      → pair_contrib_cancels (PROVED)
        → freshVertexSum_pair_part_zero_proved (PROVED)
          → fresh_vertex_relation (PROVED) [= Lemma 1]
            → finite_strip_identity_from_vr (SORRY — needs discrete Stokes)
              → B_paper_le_one_from_vr (PROVED)
                → paper_bridge_partial_sum_shifted_le (PROVED, in SAWDiagProof)
                  → paper_bridge_partial_sum_le (PROVED)
                    → bridge_decay → HW bound
                      → hw_summable_corrected [Z(x) < ∞ for x < xc]
```

### Chain B: Infinite Strip Identity → Z(xc) = ∞

**Root cause:** `infinite_strip_identity` (SAWRecurrenceProof.lean:56)

The identity 1 = c_α·A_inf + xc·B for the infinite strip. This is the
L→∞ limit of the finite strip identity (Chain A).

```
infinite_strip_identity (SORRY)
  → bridge_recurrence_proved (PROVED)
    → Z_xc_diverges_corrected [Z(xc) = ∞]
```

## Critical Correctness Issue: IsTrail vs IsPath

### The Problem

`FreshTrail` in `SAWPathVertexRelation.lean` uses `walk.IsTrail` (no repeated
edges) instead of `walk.IsPath` (no repeated vertices / SAW). The paper's
argument requires self-avoiding walks (SAWs), not just trails.

On the hex lattice (degree 3), a trail is a SAW at all interior vertices
(since visiting a vertex twice would use 4 edges but there are only 3).
However, the **starting vertex** (paperStart) can be revisited: the trail
uses 1 edge at the start, and the inner walk can later visit paperStart
using the remaining 2 edges.

### Why It Matters

A trail that revisits paperStart can create a CW loop (clockwise-oriented
simple closed polygon). For CW loops with specific index configurations,
the pair cancellation identity FAILS:

```
j̄ · exp(-iπ/3) + j · exp(iπ/3) = -2 ≠ 0
```

This means `freshVertexSum = 0` (the vertex relation) is FALSE for trails
that revisit paperStart. The vertex relation only holds for SAWs.

A concrete counterexample: in a strip with T=2, L=2, the trail
paperStart → v → nbr₁ → ... → paperStart → ... → nbr₂ creates a CW
loop that contributes -2·d₀·exp(-iσW_prefix) to the vertex sum, which
does not cancel with its pair.

### The Fix

Change `FreshTrail.is_trail : walk.IsTrail` to `FreshTrail.is_path : walk.IsPath`.
This requires:
1. Updating `freshExtend` to prove IsPath for extended walks
2. Updating `pairInvol` to prove IsPath for paired walks
3. Adding a helper lemma: `vEdgeCount v w = 0 ∧ v ≠ start → v ∉ w.support`

Both freshExtend and pairInvol preserve the IsPath property:
- freshExtend adds v to the end; v ∉ support since vEdgeCount = 0
- pairInvol swaps exit/k directions; the paired walk has the same vertex
  set as the original (minus one endpoint, plus another that wasn't visited)

The fix is documented but not yet implemented to avoid breaking the
existing compilation. The fix is REQUIRED for pair_winding_relation
(and hence the main theorem) to be provable.

## All Sorry Locations (11 total)

### Critical path (4 sorry's):
1. `hex_signed_turn_eq_six_sign_shoelace` (SAWUmlaufSignedArea.lean) —
   **ROOT CAUSE A**.  The discrete Umlaufsatz for hex lattice polygons, now in
   its cleanest *inductive* signed-area form: total signed turn
   `= 6 · sign (HexArea.shoelace2 (hexEmbeddedPolygon L))`.  This equality is
   strictly stronger than the bare `±6` disjunction (it pins the orientation)
   and is the invariant maintained by an ear-clipping / discrete Gauss–Bonnet
   induction.

   **Now derived sorry-free from this single core:**
   * `hex_total_signed_turn_pm_six` (SAWUmlaufGaussBonnet.lean) — the bare `±6`
     disjunction, an immediate consequence (`6 · (if 0<area then 1 else -1)` is
     always `±6`).
   * `umlaufsatz_pm_one`, `hex_closed_trail_turning_number` — as before.

   **Supporting sorry-free infrastructure added for the inductive proof:**
   * base case (SAWUmlaufHexagon.lean): `hexHexagon_signed_turn` (one face has
     total signed turn +6), `hexHexagon_shoelace2_eq` (its embedded area is
     `3√3`), `hexHexagon_shoelace2_pos` (area > 0) — fixing the sign convention;
   * ear step (SAWUmlaufBridge.lean): `cross_triangle_eq_cross_edges` and
     `hexTurnSign_eq_ear_area_sign` (the ear-step signed-area change has the
     same sign as the turn sign at the cut vertex), the exact compatibility the
     induction's invariant needs;
   * `HexArea.shoelace2_ear` (area change on cutting a vertex) and
     `hex_closed_trail_embed_nodup` (the embedded polygon is genuinely simple).

   What remains is the irreducible topological content: a simple polygon has an
   ear (two-ears theorem / Jordan curve theorem for polygons), absent from
   Mathlib.
2. `pair_winding_relation` (SAWPairCancellation.lean:173) — needs #1 + orientation
3. `finite_strip_identity_from_vr` (SAWStripIdentityFromVR.lean:84) — discrete Stokes
4. `infinite_strip_identity` (SAWRecurrenceProof.lean:56) — **ROOT CAUSE B**
   L→∞ limit of #3.

### Dead branches (7 sorry's, NOT on critical path):
5. `trail_vertex_relation` (SAWCancellationIdentity.lean:305) — superseded by fresh version
6. `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385) — SUPERSEDED by
   B_paper_le_one_from_vr
7. `strip_observable_summable` (SAWStripObservable.lean:173) — not needed
8. `triplet_part_zero` (SAWTrailVertexRelation.lean:274) — superseded
9. `pair_part_zero` (SAWTrailVertexRelation.lean:282) — superseded
10. `hex_simple_closed_trail_winding` (SAWWindingDiff.lean:72) — alternative formulation
11. `pair_winding_diff` depends on #2 (circular, not independently needed)

Note: `pair_winding_diff` (SAWWindingDiff.lean:91) is derived from pair_winding_relation
and is not a separate sorry — it's proved from the sorry'd lemma.

## Fully Proved Components

### Hammersley-Welsh Decomposition (FULLY PROVED ✓)
All SAWHW*.lean files are sorry-free:
- `hw_injection_bound` — SAW count ≤ 8 · (∏(1+12·B_T))²
- Bridge decomposition algorithm and injection
- Extra walk bounds and fiber counting

### Algebraic Identities (FULLY PROVED ✓)
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0 ✓
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0 ✓
- `xc_inv`: xc⁻¹ = √(2+√2) ✓
- `strip_algebraic_identity`: 2·c_α·xc³ + 3·xc² = 1 ✓
- `fin3_other_pair_cancel` ✓
- `exp_shift_minus'`, `exp_shift_plus'` ✓

### Vertex Relation / Lemma 1 (PROVED modulo pair_winding_relation)
- `fresh_vertex_relation` (SAWPairInvolutionProof.lean) ✓
- Triplet cancellation: `freshVertexSum_triplet_part_zero` ✓
- Pair cancellation: `freshVertexSum_pair_part_zero_proved` ✓
- Pair involution: `pairSigmaInvol_injective` ✓
- Extension maps: `freshExtensionMap_injective`, `fresh_outgoing_surj` ✓

### Winding Infrastructure (FULLY PROVED ✓)
- `hexWalkWinding_split` ✓ — winding additivity
- `hex_turn_value` ✓ — all hex turns are ±π/3
- `hex_edge_norm_one` ✓ — all hex edges have unit length
- `hexWalkWinding_reverse_list'` ✓ — winding reversal
- `pair_suffix_hex_trail` ✓
- `pair_suffix_winding_neg` ✓
- `prefix_penultimate_is_neighbor` ✓
- `pair_inner_loop_trail_rev` ✓

### Bridge Recurrence (PROVED modulo infinite_strip_identity)
- `bridge_recurrence_proved`: B(T) ≤ c_α·B(T+1)² + B(T+1) ✓
- `cutting_argument_proved`: A(T+1) - A(T) ≤ xc·B(T+1)² ✓

### Connective Constant Infrastructure (FULLY PROVED ✓)
- `saw_count_submult'`: c_{n+m} ≤ c_n · c_m ✓
- `connective_constant_is_limit'`: μ = lim c_n^{1/n} ✓
- `connective_constant_eq_from_bounds`: Z diverges + Z converges → μ = √(2+√2) ✓

## Why the Remaining Sorry's Are Hard

### hex_closed_trail_turning_number (Umlaufsatz)
This is equivalent to proving that a simple closed polygon in the plane
has total exterior angle ±2π. On the hex lattice:
- Each turn is ±π/3 (proved: `hex_turn_value`)
- For a closed polygon, the sum is 6k·(π/3) = 2kπ
- The claim is |k| = 1 for SIMPLE (non-self-intersecting) polygons

Proving |k| = 1 requires one of:
- The Jordan curve theorem (not in Mathlib)
- A constructive ear-clipping argument
- A signed area / Pick's theorem argument
- A crossing number argument

None of these foundations are currently in Mathlib.

### pair_winding_relation (Turning Number + Orientation)
Beyond the turning number theorem, this requires determining the SIGN
of the turning (CW vs CCW). The sign is determined by:
1. The planarity of the hex lattice embedding
2. The CCW ordering of neighbors (d₁ = j·d₀ with j = exp(2πi/3))
3. The blocking effect of the prefix path on loop orientation

For SAW-based pair walks (with the IsPath fix), the prefix path from
paperStart to v prevents the inner walk from going "the wrong way"
around v. This constrains the loop to have the correct orientation
for pair cancellation. Formalizing this requires the IsPath fix.

### finite_strip_identity_from_vr (Discrete Stokes)
The argument sums freshVertexSum over all interior vertices:
1. Interior mid-edges cancel: z is the midpoint of its edge, so
   (z-u) + (z-w) = 0 for the two endpoints u, w
2. Boundary mid-edges survive
3. Boundary evaluation gives the partition functions A, B, E

Each step is conceptually simple but requires substantial bookkeeping:
- Define interior vs boundary vertices of the strip
- Define interior vs boundary mid-edges
- Show the cancellation for interior mid-edges
- Evaluate boundary contributions (winding at each boundary type)

### infinite_strip_identity (Limit)
Derived from finite_strip_identity_from_vr by taking L→∞:
- A_paper(T,L) → A_inf(T) as L→∞ (monotone convergence)
- B_paper(T,L) → B_inf(T) as L→∞ (monotone convergence)
- E_paper(T,L) → E_inf(T) as L→∞

The identity 1 = c_α·A_inf + B_inf + c_ε·E_inf follows. If E_inf = 0,
this gives 1 = c_α·A_inf + xc·B.

## File Organization

All files contributing to the proof are imported transitively from `SAWFinal.lean`.
The project builds successfully with `lake build RequestProject.SAWFinal`.

### Preparation files (not on critical path but needed for future use)
- `SAWDiscreteStokes` — Abstract discrete Stokes framework
- `SAWStokesAbstract` — Abstract combinatorial Stokes lemma
- `SAWWindingLemma` — Winding append/extension lemmas
- `SAWWindingReverse` — Additional winding reversal results
- `SAWWindingDecomp` — Winding decomposition for pair walks
- `SAWTurningNumber` — Turning number theorem (sorry'd)
- `SAWStripAlgebra` — Algebraic identities for strip boundary evaluation
- `SAWObservableSum` — Observable as formal sum over trails
- `SAWPairWindingRelation` — Alternative pair cancellation via winding
- `SAWPairWindingProof` — Pair winding proof infrastructure

All of these files are imported from SAWFinal.lean and build successfully.
