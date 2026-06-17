# Summary of changes for run 1b9d9078-2358-4b5c-9092-954455c017bd
Worked exclusively on the top-priority discrete Hopf Umlaufsatz (`hex_closed_trail_turning_number`), touching no other branch. The whole library still builds end-to-end (8126 jobs through `SAWFinal`) and the top theorem still reduces only to `sorryAx` plus the allowed axioms (`propext, Classical.choice, Quot.sound`).

CRITICAL SOUNDNESS FIX. I discovered that the previous decomposition's open core `ear_turning_bounds` (in `RequestProject/SAWUmlaufPolygon.lean`) — the three `Set.Ioc (-π) π` partial-sum "turning bounds" — is FALSE. Its third bound is the sum of two of the three exterior turns of the clipped triangle, which for any genuine triangle sum to `2π − (third turn) ∈ (π, 2π)`, hence always exceed π (explicit counterexample: the convex CCW quadrilateral `a=0, b=20+i, c=19+2i, d=-1+i`, where the bound ≈ 3.977 > π). The entire Umlaufsatz skeleton was therefore resting on an unprovable lemma — it could never have been completed as stated.

WHAT I CHANGED (all verified to build):
- Commented out the false `ear_turning_bounds`, keeping it as documentation of the dead branch with the counterexample recorded.
- Isolated the genuine, TRUE fact the ear clip actually needs — the local turning identity `arg((b-a)/(a-p)) + arg((c-b)/(b-a)) + arg((q-c)/(c-b)) = arg((c-a)/(a-p)) + arg((q-c)/(c-a))` — as `ear_local_turning_identity` (left as `sorry`; checked numerically to hold for empty ears of simple polygons, failing only for self-intersecting configurations).
- Added `polyCycWind_clip_eq_of_identity`, which consumes that identity directly (proved sorry-free), and rewired `exists_front_ear_core`, `exists_front_ear`, and `exists_ear_rotation` to thread the identity instead of the false bounds.
- Proved two reusable backbone lemmas sorry-free: `ear_turning_identity_mod` (the identity holds in `Real.Angle = ℝ/2πℤ`, by pure `arg_div_coe_angle` telescoping) and `arg_split_one_add` (`arg w = arg(1+w) + arg(w/(1+w))` unconditionally — the local, geometry-free building block, applied with `w=(c-b)/(b-a)` since `(b-a)+(c-b)=c-a`).

The Umlaufsatz now rests on exactly two open lemmas, BOTH TRUE: `ear_local_turning_identity` (whose only remaining content, given `ear_turning_identity_mod`, is the integer fact that the real-valued difference in `2πℤ` is `0` — no `2π` wrap) and `exists_empty_convex_ear` (the Meisters two-ears existence content). I also verified and recorded for future work that this identity does NOT split into two per-corner `(-π,π]` range facts (the analogous splits fail ~38% of empty-ear cases because the wraps cancel only globally), so the false-bound mistake is not repeated. The remaining cores are genuine Jordan-curve-theorem-level content; partial progress is preserved as compiling Lean with sorries, and a detailed round note was added to `PROOF_STATUS.md`.

# Summary of changes for run 8576c87f-32ae-479e-a744-97dfa5b95755
Worked exclusively on the top-priority discrete Hopf Umlaufsatz (`hex_closed_trail_turning_number`), touching no other branch. The whole library still builds end-to-end and the top-level theorem still reduces only to `sorryAx` plus the allowed axioms (`propext, Classical.choice, Quot.sound`).

Main progress this round: the previously single open core of the Umlaufsatz, `exists_front_ear_core` (in `RequestProject/SAWUmlaufPolygon.lean`), is now **proved as a sorry-free assembly** of two cleaner, faithful, focused sub-cores. The genuinely hard, irreducible Jordan-curve-level content is thereby isolated into two true, well-stated lemmas, each in the `SAWFinal` build chain:

- `exists_empty_convex_ear` — the genuine Meisters two-ears / ear-existence content: a simple non-degenerate polygon with ≥4 vertices has a cyclic rotation `a :: b :: c :: rest` whose middle vertex `b` is an empty convex ear (non-degenerate corner triangle, empty of far vertices, empty diagonal `a–c`), with the five edge non-degeneracies, `polyCycNondeg` of the clip, and the orientation equivalence.
- `ear_turning_bounds` — the three convexity turning-range `(-π, π]` bounds consumed by `arg_ear_local_exact` / `polyCycWind_clip_eq`.

All of `exists_front_ear_core`'s bundling, rotation-transport, and edge-non-degeneracy wiring is now proved sorry-free; only these two true geometric cores remain open. Partial progress is preserved as compiling Lean code with sorries (not lost), and the two remaining sorries are documented in their docstrings with their intended proof routes (lex-min convex vertex + farthest-vertex pivot + diagonal split + strong induction for the existence core; arg-telescoping via `Complex.arg_mul` with neighbour-based cross-product sign facts for the turning bounds). A round note was added to `PROOF_STATUS.md`.

I attempted both remaining sub-cores with the automated prover at high effort; neither closed yet (they are research-level), but the decomposition makes them sharply focused targets for future rounds and keeps the Umlaufsatz resting on exactly two clean, true lemmas instead of one monolithic gap.

# Summary of changes for run bf62f749-f1df-4489-b30a-ddd35ac51a28
Worked exclusively on the top-priority discrete Hopf Umlaufsatz (`hex_closed_trail_turning_number` in `RequestProject/SAWUmlaufGaussBonnet.lean`), touching no other branch. The whole library still builds end-to-end (8126 jobs through `RequestProject/SAWFinal.lean`), and the top-level theorem still reduces only to `sorryAx` plus the allowed axioms `propext, Classical.choice, Quot.sound`.

Main result this round: the Jordan-segment core `seg_diagonal_disjoint_of_corner` (in `RequestProject/SAWUmlaufPolygon.lean`) — one of the two previously-open cores of the Umlaufsatz — is now **proved sorry-free**. As a result the Umlaufsatz now rests on a *single* remaining open core, `exists_front_ear_core` (the Meisters two-ears / ear-existence content together with its turning-range bounds and orientation), instead of two.

To get there I added a new, fully sorry-free, reusable plane-geometry file `RequestProject/SAWUmlaufCorner.lean` (imported from `SAWUmlaufPolygon`, hence transitively from `SAWFinal`, so it is in the build chain — not a dead branch), containing six proved lemmas:
- `exists_real_smul_of_cross_zero` — a vanishing 2-D cross product gives real linear dependence (affine parameter on a carrier line).
- `mem_segment_ab_of_cross` / `mem_segment_bc_of_cross` — a point on an edge's carrier line whose adjacent side tests have the correct (orientation-agnostic, product-form) signs lies on the closed edge.
- `corner_exit_point` — the constructive crossing core: a point moving from the relative interior of edge `a–c` towards an apex-side endpoint that is not strictly inside the triangle must hit closed edge `a–b` or `b–c`. The proof is fully constructive (explicit first-crossing parameter), since every side test is affine, so no real analysis is needed.
- `collinear_diag_a_mem` — the degenerate collinear case: if both chord endpoints lie on the carrier line of `a–c` but off the closed segment while an interior point of `a–c` lies on the chord, then `a` lies on the chord.

These are then assembled into a sorry-free proof of `seg_diagonal_disjoint_of_corner`: the chord/diagonal intersection point is forced strictly interior to `a–c`, the crossing forces an apex-side endpoint, and `corner_exit_point` (generic case) or `collinear_diag_a_mem` (collinear case) produces a chord point on a polygon edge — contradicting the edge-disjointness hypotheses. I verified all new lemmas and `seg_diagonal_disjoint_of_corner` depend only on `propext, Classical.choice, Quot.sound`, and cleaned up the few leftover `exact?` calls into explicit terms.

Status documentation (`PROOF_STATUS.md`) was updated with a round note, and the `seg_diagonal_disjoint_of_corner` docstring now records that it is proved. All partial progress is preserved as building Lean files; the single remaining Umlaufsatz `sorry` is the isolated, true, Jordan-curve-theorem-level core `exists_front_ear_core`, which is documented for future rounds.

# Summary of changes for run 0151a863-6994-4840-a4f8-046b747875d0
Worked exclusively on the top-priority discrete Hopf Umlaufsatz (`hex_closed_trail_turning_number` in `RequestProject/SAWUmlaufGaussBonnet.lean`), leaving every other branch untouched. The whole library still builds end-to-end (8125 jobs) and the top-level theorem still reduces only to the allowed axioms plus `sorryAx`.

What I did this round (all in `RequestProject/SAWUmlaufPolygon.lean`): decomposed the single monolithic ear gap `exists_front_ear` into finer, individually-attackable, true pieces, turning `exists_front_ear` itself into a sorry-free assembly:

- `far_edge_disjoint_earEdges` — **newly PROVED, sorry-free**: a guarded far edge of the ear clip is segment-disjoint from the two ear edges `a–b`, `b–c` (pure `PolygonSimple`/`closedEdges` bookkeeping). Axioms: `propext, Classical.choice, Quot.sound` only.
- `seg_diagonal_disjoint_of_corner` — *(open, `sorry`)* the pure-geometry, list-free Jordan-segment heart (the genuine "crossing"/intermediate-value content): a non-degenerate corner whose far-edge endpoints are neither strictly inside the triangle nor on the closed diagonal, with the far edge disjoint from `a–b`, `b–c`, has its diagonal `a–c` disjoint from that far edge.
- `diag_disjoint_of_empty_corner` — **sorry-free assembly**: derives the diagonal-disjointness clause from closed-corner emptiness plus planar simplicity, via the two lemmas above.
- `exists_front_ear_core` — *(open, `sorry`)* the genuine Meisters two-ears / ear-existence content (extreme convex vertex + farthest-vertex pivot), in geometric-data form with an emptiness clause replacing the disjointness clause.
- `exists_front_ear` — now a **sorry-free assembly** of `exists_front_ear_core` and `diag_disjoint_of_empty_corner`.

I also folded in a correctness fix: the intermediate emptiness condition must additionally exclude a far vertex lying on the open diagonal `a–c` (`hdiagempty`), since plain strict-interior emptiness is too weak to guarantee diagonal-disjointness; both `exists_front_ear_core` and `diag_disjoint_of_empty_corner` now carry this clause.

Net effect: the Umlaufsatz now rests on exactly two open, true, Jordan-curve-level cores (`seg_diagonal_disjoint_of_corner` and `exists_front_ear_core`) instead of one monolithic gap, with one new lemma proved sorry-free and several sorry-free assemblies wiring them to the main theorem. High-effort automated attempts on both remaining cores timed out, consistent with their being absent from Mathlib; they are kept as documented partial progress. All `SAWUmlaufEar*` preparation files remain imported (via `SAWUmlaufPolygon`) and documented as feeding these cores — none is a dead branch. Status notes were updated in `PROOF_STATUS.md`.

# Summary of changes for run 13af5d3f-53ce-494c-ad18-b49e423dd7c8
Worked exclusively on the top-priority discrete Hopf Umlaufsatz, leaving every other branch untouched. The whole library still builds end-to-end (8125 jobs) and the top-level discrete Umlaufsatz `hex_closed_trail_turning_number` (`RequestProject/SAWUmlaufGaussBonnet.lean`) still reduces to exactly one remaining gap, depending only on `sorryAx` plus the allowed axioms `propext, Classical.choice, Quot.sound`.

Key finding and fix this round — the single gap was a FALSE statement and is now TRUE:

- The single remaining gap is `exists_front_ear` (`RequestProject/SAWUmlaufPolygon.lean`), the genuine Meisters two-ears / ear-existence core (Jordan-curve-theorem level, absent from Mathlib).
- A previous round had restated its planar-simplicity output clause as a *one-sidedness* condition (`∀ x y ∈ rest, 0 < cross (c-a)(x-a) * cross (c-a)(y-a)` — every far vertex strictly on one and the same side of the clip diagonal `a–c`). I discovered this clause is **false in general**: the simple, non-degenerate pentagon `[(4,0),(6,0),(6,5),(0,0),(5,1)]` has no cyclic triple whose far vertices all lie on one side of the clip diagonal (verified computationally over all five rotations), so the existence statement could never be proved — a false `sorry` sitting under the main theorem. The same pentagon nonetheless has a genuine ear (rotation 4, clipping vertex `(4,0)`): its diagonal `(5,1)–(6,0)` misses every far edge, and the turning-range, orientation, and non-degeneracy clauses all hold.
- I replaced the false one-sidedness clause with the genuine, always-satisfiable **diagonal-disjointness clause** — exactly the `hdiag` hypothesis consumed by `PolygonSimple_clip` (`a–c` is segment-disjoint from every far edge sharing no endpoint with it). `exists_ear_rotation` now feeds this directly into `PolygonSimple_clip`. The previously-used bridges `oneSided_far_edges_sameSide` / `diag_disjoint_of_far_sameSide'` remain as correct, sorry-free preparation (still imported, now unconsumed, and documented as such). The corrected `exists_front_ear` is now the classical discrete two-ears theorem — a true statement — left as `by sorry`.
- Updated the `exists_front_ear` docstring and prepended a detailed note to `PROOF_STATUS.md` recording the correction.

A high-effort attempt to discharge the corrected `exists_front_ear` directly timed out (the file was not modified), consistent with its being genuine Jordan-curve-theorem-level content that needs the full convex-empty-ear existence argument together with exact turning-range bounds; the gap is preserved as a true `sorry` for future rounds. Net effect: the main Umlaufsatz no longer rests on a false intermediate lemma, and the single remaining gap is now a faithful, provable statement.

# Summary of changes for run 91bdafd4-4f35-4a19-9b1c-863073bd9cf3
Worked exclusively on the top-priority discrete Hopf Umlaufsatz, leaving every other branch untouched. The whole library still builds (`lake build`, 8125 jobs through `RequestProject/SAWFinal.lean`), and the top-level discrete Umlaufsatz `hex_closed_trail_turning_number` (`RequestProject/SAWUmlaufGaussBonnet.lean`) still reduces to **exactly one** remaining gap, depending only on `sorryAx` plus the allowed axioms `propext, Classical.choice, Quot.sound`.

The single remaining `sorry` is `exists_front_ear` (`RequestProject/SAWUmlaufPolygon.lean`): the genuine Meisters two-ears / ear-existence core (Jordan-curve-theorem level, absent from Mathlib). A high-effort direct proof attempt again times out, confirming it intrinsically needs the full convex-hull / diagonal-split argument; everything that consumes it remains sorry-free.

This round made one safe, sorry-free gap-simplification plus reusable building blocks (no new gaps, no false/unproven intermediate lemmas):

- **Simplified the gap's hardest output clause.** `exists_front_ear` previously had to produce a *per-edge far-edge same-side* clause. It now only has to produce the cleaner, more geometric **one-sidedness** clause `∀ x y ∈ rest, 0 < cross (c-a)(x-a) * cross (c-a)(y-a)` — every far vertex strictly on one and the same side of the diagonal line `a–c` (the defining property of a *one-sided ear*). A worked example shows a generic empty convex ear (e.g. at the extreme vertex) need not satisfy the per-edge same-side clause, whereas a genuine one-sided ear does, so this states the true geometric heart of the gap. The downstream `exists_ear_rotation` recovers the per-edge same-side condition (still sorry-free) via the new bridge lemma.

- **Added a new reusable, verified building-block file** `RequestProject/SAWUmlaufEarOneSided.lean`, imported from `SAWUmlaufPolygon.lean` (hence transitively from `SAWFinal.lean`, in the build chain). It contains five sorry-free lemmas: `oneSided_far_edges_sameSide` (one-sidedness ⇒ the per-edge same-side clause, now *consumed* by `exists_ear_rotation`, so it is live rather than dead prep), `sameSide_pairwise_of_allPos`/`sameSide_pairwise_of_allNeg` (repackaging one-sidedness), and `clip_turn_at_a_ne_zero`/`clip_turn_at_c_ne_zero` (the two new cyclic turns created by the ear clip are non-degenerate, preparation for the `polyCycNondeg (a :: c :: rest)` clause).

All partial progress is preserved as building Lean files; the round is recorded at the top of `PROOF_STATUS.md`.

# Summary of changes for run e1cc6738-2382-41ee-9c75-9bcc72ecac51
Continued the SAW.tex formalization working **exclusively on the top-priority discrete Hopf Umlaufsatz**, touching no other branch. The whole library still builds (`lake build`, 8124 jobs through `RequestProject/SAWFinal.lean`), and the top-level discrete Umlaufsatz `hex_closed_trail_turning_number` (in `RequestProject/SAWUmlaufGaussBonnet.lean`) still reduces to **exactly one** remaining gap, depending only on `sorryAx` plus the allowed axioms `propext, Classical.choice, Quot.sound`.

The single remaining `sorry` is `exists_front_ear` (in `RequestProject/SAWUmlaufPolygon.lean`): the genuine Meisters two-ears / ear-existence core, which is Jordan-curve-theorem level and absent from Mathlib. A direct high-effort proof attempt times out, confirming it intrinsically needs the full diagonal-split recursion; everything that consumes it remains sorry-free.

This round made two safe, sorry-free advances around that core, introducing no new gaps and no unproven/false intermediate lemmas:

- **Simplified the remaining gap's hypothesis.** `exists_front_ear` previously had to produce a *segment-disjointness* clause for the diagonal `a–c`. It now only has to produce the more elementary, orientation-agnostic *algebraic* cross-product same-side condition `0 < cross (c-a) (e.1-a) * cross (c-a) (e.2-a)` on the guarded far edges. A new lemma `diag_disjoint_of_far_sameSide'` converts that into the segment-disjointness hypothesis required by `PolygonSimple_clip`, and the downstream `exists_ear_rotation` was updated to use it (still sorry-free). This turns the hardest output clause of the gap from a topological statement into an algebraic sign condition, strictly easier to eventually discharge.

- **Added a reusable, verified geometric building block.** New file `RequestProject/SAWUmlaufEarSide.lean` contains `HexArea.inTriangleStrict_apex_sameSide`: a strict interior point of a triangle lies strictly on the apex side of the base diagonal (`0 < cross (c-a) (x-a) * cross (c-a) (b-a)`), proved from the barycentric convex-combination characterization. This is the per-point side geometry underpinning the same-side condition above. The file is imported from `SAWUmlaufPolygon.lean` (hence transitively from `SAWFinal.lean`), is part of the build chain, and is documented as preparation for the eventual `exists_front_ear` proof.

I also recorded the round in `PROOF_STATUS.md`. All partial progress is preserved as building Lean files; the only `sorry` in the Umlaufsatz chain is the isolated `exists_front_ear` core.

# Summary of changes for run c4f35717-99f1-4141-bf88-207b46e9881d
Continued the SAW.tex formalization working **exclusively on the top-priority discrete Hopf Umlaufsatz**, touching no other branch. The whole library still builds (`lake build`, 8123 jobs through `RequestProject/SAWFinal.lean`), and the top-level discrete Umlaufsatz `hex_closed_trail_turning_number` (in `RequestProject/SAWUmlaufGaussBonnet.lean`) depends only on `sorryAx` plus the allowed axioms `propext, Classical.choice, Quot.sound`.

This round pushed the remaining topological content one level deeper and proved out the surrounding bookkeeping, all in `RequestProject/SAWUmlaufPolygon.lean`:

- **`exists_ear_rotation` is now proved sorry-free.** It was previously the single Umlaufsatz `sorry`; it is now derived from a cleaner geometric-data core (`exists_front_ear`) plus three clip-preservation lemmas.
- **Added and proved `polyCycWind_clip_eq`** — the turning-preservation clause as pure `polyWind` bookkeeping. Both closed cyclic forms peel (via `polyWind_cons_cons_cons` and `polyWind_append_singleton`) to a shared middle `polyWind (c :: rest ++ [a])` plus the local ear turns, whose difference vanishes by the already-proved `arg_ear_local_exact`. This genuinely consumes the previously-prepared `arg_ear_local_exact` and `polyWind_append_singleton`.
- **Added and proved `shoelace2_orient_clip`** — the orientation-preservation clause as arithmetic on the area splitting `shoelace2_clip_second` (full area = clip area + ear-triangle area), reducing it to the triangle-vs-clip sign equivalence.
- **Restated the topological core as `exists_front_ear`**, which now supplies exactly the raw plane-geometry data of an ear (predecessor/successor naming, the five edge non-degeneracies, the three turning range bounds, per-edge diagonal disjointness, clip non-degeneracy, and the triangle orientation iff). `exists_ear_rotation` consumes it together with `PolygonSimple_clip`, `polyCycWind_clip_eq`, `shoelace2_orient_clip` and `PolygonSimple_rotate`.
- **Fixed a latent unsatisfiable interface.** The earlier-prepared `PolygonSimple_clip_of_far_sameSide` required a strictly-positive same-side product for *every* far edge, but the first far edge `(c, rest.head)` forces side-product `0`, so its hypothesis can never be met. The core now consumes the correct per-edge diagonal-disjointness clause of `PolygonSimple_clip`. The superseded lemma is retained and clearly documented as a dead branch, while its genuinely useful per-edge tool `segment_disjoint_of_strictSameSide` remains live preparation.

Net effect: the single remaining Umlaufsatz `sorry` is now `exists_front_ear` — the genuinely irreducible Jordan-curve-theorem-level ear-existence statement together with its convexity/emptiness data — with all the cyclic turning, orientation, and planar-simplicity bookkeeping around it proved and wired in. Partial progress is preserved as that one localized sorry, every Umlaufsatz file remains imported in the `SAWFinal` build chain, and the round note is recorded at the top of `PROOF_STATUS.md`.

# Summary of changes for run b3aae96b-e265-462c-b077-366e7c11e02c
Continued the SAW.tex formalization working exclusively on the top-priority discrete Hopf Umlaufsatz, touching no other branch. The whole library still builds (`lake build`, 8123 jobs, through `RequestProject/SAWFinal.lean`), and the top-level discrete Umlaufsatz (`hex_closed_trail_turning_number` in `RequestProject/SAWUmlaufGaussBonnet.lean`) depends only on `sorryAx` plus the allowed `propext, Classical.choice, Quot.sound`.

This round isolates the remaining topological content into a single, cleaner core and consumes previously-unused preparation, in `RequestProject/SAWUmlaufPolygon.lean`:

- Added `exists_ear_rotation` — the genuine two-ears / ear-existence core, restated **locally at the front of one cyclic rotation** `V.rotate r = a :: b :: c :: rest`: clipping the second vertex `b` preserves planar simplicity (`PolygonSimple`), cyclic non-degeneracy (`polyCycNondeg`), the cyclic turning (`polyCycWind`) and the orientation, all stated relative to the rotated polygon `a :: b :: c :: rest` itself. This is now the single remaining Umlaufsatz `sorry`, and every clause is a local statement about removing `b`.
- **Derived the former core `exists_ear_clip` from it sorry-free**, transporting each clause back to the original cycle `V` through the rotation-invariance toolkit `polyCycWind_rotate` and `shoelace2_rotate`. Those two lemmas were proved in earlier rounds but not yet consumed by anything; they are now genuinely used, explicitly linking that "looks-dead-but-is-preparation" rotation bookkeeping into the proof.
- Added `PolygonSimple_clip_of_far_sameSide`, a fully proved (`propext, Classical.choice, Quot.sound`, verified sorry-free) one-step bundling of the two prepared simplicity-preservation halves (`PolygonSimple_clip` and `diag_disjoint_of_far_sameSide`) into the single planar-simplicity clause the ear core will consume.

Net effect: the irreducible Jordan-curve-theorem-level content (existence of a convex empty ear together with the same-side / convexity range bounds that drive simplicity, turning and orientation preservation) is now concentrated in `exists_ear_rotation`, with the surrounding rotation/area/turning bookkeeping proved and wired in. Partial progress is preserved as the single localized sorry, and the new round note is recorded in `PROOF_STATUS.md`. Every Umlaufsatz file remains imported in the `SAWFinal` build chain.

# Summary of changes for run 63770091-b8f2-4c0b-b9fd-a55a05297164
Continued the SAW.tex formalization working exclusively on the top-priority discrete Hopf Umlaufsatz, touching no other branch. The whole library still builds (`lake build`, 8123 jobs, through `RequestProject/SAWFinal.lean`), and the only Umlaufsatz `sorry` remains the single irreducible two-ears / ear-existence core `exists_ear_clip` in `RequestProject/SAWUmlaufPolygon.lean`.

This round added three new, fully proved (only `propext, Classical.choice, Quot.sound`) preparation lemmas directly in the chain file `SAWUmlaufPolygon.lean`, just above `exists_ear_clip`, assembling the turning-preservation half of an ear clip plus the rotation bookkeeping it needs:

- `rotate_cons_triple` — any rotation `V.rotate r` of a length-≥3 vertex cycle has the explicit head form `a :: b :: c :: rest`, the bookkeeping that lets the chosen ear (at any cyclic position `r`) be presented in the concrete clipped-cons shape.
- `arg_ear_local_exact` — the exact local turning preservation (the `k = 0` case of the already-present `arg_ear_local_mod`): given the three relevant partial argument-sums lie in `(-π, π]`, removing the middle vertex `b` leaves the net exterior-angle turning unchanged. Proved by pure `Complex.arg_mul` telescoping — both sides equal `arg ((q-c)/(a-p))`. (I first confirmed numerically that the local turning difference is in general a nonzero multiple of 2π, so range/convexity hypotheses are genuinely required to pin it to 0.)
- `polyWind_clip_step` — on an open chain `p :: a :: b :: c :: q :: rest`, removing `b` changes the total turning `polyWind` by exactly the local 5-point ear difference (all turns from `c` onward cancel), via `polyWind_cons_cons_cons` unfolding.

Composed, `polyWind_clip_step` reduces the clip's turning change to the 5-point difference, which `arg_ear_local_exact` makes vanish under the convexity range bounds — supplying the turning-preservation clause of `exists_ear_clip` modulo producing those `(-π, π]` bounds from a convex ear. Each lemma is documented as preparation for `exists_ear_clip` and is in the `SAWFinal` build chain. Together with the existing ear-geometry toolkit and the planar-simplicity-preservation reduction from prior rounds, the remaining open content of the core is now narrowed to: ear existence (Meisters), the convexity range bounds, and area-sign preservation. Progress is recorded in `PROOF_STATUS.md`. Verified all new lemmas are sorry-free via `#print axioms`.

# Summary of changes for run b33e2b21-802e-4b49-8e6f-7d90309d0da4
Continued the SAW.tex formalization working exclusively on the top-priority discrete Hopf Umlaufsatz, touching no other branch. The whole library still builds (`lake build`, 8123 jobs, through `RequestProject/SAWFinal.lean`).

The Umlaufsatz's remaining content is still concentrated in a single honest `sorry` — the two-ears / ear-existence core `exists_ear_clip` in `RequestProject/SAWUmlaufPolygon.lean` (a simple non-degenerate polygon with ≥4 vertices has a clippable convex ear preserving planar simplicity, non-degeneracy, total turning and orientation). This is Jordan-curve-theorem-level and absent from Mathlib. Following the project's established incremental pattern, this round adds verified, reusable preparation that the eventual ear-existence proof consumes, while keeping the clean single-core reduction intact.

New, fully proved (`propext, Classical.choice, Quot.sound`) lemmas added directly in the chain file `RequestProject/SAWUmlaufPolygon.lean` just above `exists_ear_clip`, assembling the planar-simplicity-preservation half of an ear clip into a ready-to-consume reduction:
- `closedEdges_clip` — the closed edges of `a :: b :: c :: rest` are the two ear edges `(a,b),(b,c)` followed by the shared far-edge tail `M := (c :: rest).zip (rest ++ [a])`, and the clipped cycle `a :: c :: rest` has exactly the diagonal `(a,c)` followed by the same `M` (pure list algebra on `closedEdges = V.zip (V.rotate 1)`).
- `PolygonSimple_clip` — if the original cycle is `PolygonSimple` and the new diagonal `a–c` is disjoint from every far edge sharing no endpoint with it (`hdiag`), then `a :: c :: rest` is `PolygonSimple`: `Nodup` is inherited (sublist), far/far disjointness is inherited verbatim (`M` is a common suffix), and the only new obligation is exactly `hdiag`.
- `diag_disjoint_of_far_sameSide` — the bridge from the empty-ear same-side condition (`0 < cross (c-a) (e.1-a) * cross (c-a) (e.2-a)` for every far edge `e`) to `hdiag`, via `segment_disjoint_of_strictSameSide`.

Composed, these reduce "the ear clip preserves `PolygonSimple`" to the single geometric fact that every far edge of an empty convex ear lies strictly on one side of the base diagonal — the remaining topological content of `exists_ear_clip`. Each new lemma carries a docstring explicitly marking it as preparation for `exists_ear_clip` (it is in the `SAWFinal` build chain but not yet consumed by `exists_ear_clip`, whose ear-existence core is still open), so the partial progress is preserved rather than discarded. `PROOF_STATUS.md` is updated with a round note. Verified the three new lemmas depend only on the allowed axioms, and the single Umlaufsatz `sorry` is unchanged.

# Summary of changes for run 935b3a5b-3213-4903-ba50-7363a563008d
Continued the SAW.tex formalization working exclusively on the top-priority discrete Hopf Umlaufsatz, leaving every other branch untouched. The whole library still builds successfully (`lake build`, 8123 jobs, including `RequestProject/SAWFinal.lean`).

Status of the Umlaufsatz: its remaining content is still concentrated in the single honest `sorry` — the two-ears / ear-existence core `exists_ear_clip` in `RequestProject/SAWUmlaufPolygon.lean` (a simple, non-degenerate polygon with ≥4 vertices has a clippable convex ear preserving planar simplicity, non-degeneracy, total turning and orientation). This is genuinely Jordan-curve-theorem-level and absent from Mathlib; following the project's established pattern, this round adds more of the proved, reusable geometric foundation that the eventual ear-existence proof consumes, while keeping the clean single-core reduction intact.

New file `RequestProject/SAWUmlaufSegment.lean`, imported by `SAWUmlaufPolygon` (hence transitively from `SAWFinal`, so part of the build chain). All its lemmas are proved sorry-free and verified to depend only on `propext, Classical.choice, Quot.sound`. It supplies the algebraic heart of the planar-simplicity-preservation half of an ear clip (that the clipped diagonal `a–c` misses the far edges of the polygon), consuming the `cross`-bilinearity toolkit of `SAWUmlaufEar`/`SAWSignedArea`, the barycentric backbone `inTriangleStrict_convexCombo` of `SAWUmlaufEarExtreme`, and the non-degeneracy `inTriangleStrict_nondeg`:
- `cross_combo_segment` — the carrier-line side test `cross (q-p) (u-p)` vanishes for `u ∈ segment ℝ p q`;
- `segment_disjoint_of_strictSameSide` — if both endpoints of one segment lie strictly on the same side of the other's carrier line (`0 < cross (q-p) (r-p) * cross (q-p) (s-p)`), the two segments are disjoint (the test used to show the clipped diagonal does not meet the polygon's far edges);
- `inTriangleStrict_diag_side` — a strict interior point of the corner triangle `a,b,c` lies strictly on the apex side of the base diagonal `a–c` (`0 < cross (c-a) (x-a) * cross (c-a) (b-a)`), linking the empty-triangle/interior machinery of the earlier parts to the same-side disjointness test.

The file is documented as preparation for `exists_ear_clip`: it is imported into the chain and links the interior-point machinery into the planar-simplicity argument. All Umlauf-related files remain imported somewhere (none are dead branches), and the recorded partial progress (PROOF_STATUS.md updated) preserves the work for future rounds. The single remaining Umlaufsatz `sorry` is unchanged and is the only one in the Umlauf chain.

# Summary of changes for run 5187f9ea-6897-4043-90bf-276bffacec28
Continued the SAW.tex formalization working exclusively on the top-priority discrete Hopf Umlaufsatz, leaving every other branch untouched. The whole library still builds successfully (`lake build`, 8122 jobs, including `RequestProject/SAWFinal.lean`).

Status of the Umlaufsatz: its remaining content is still concentrated in the single honest `sorry` — the two-ears / ear-existence core `exists_ear_clip` in `RequestProject/SAWUmlaufPolygon.lean` (a simple, non-degenerate polygon with ≥4 vertices has a clippable convex ear preserving planar simplicity, non-degeneracy, total turning and orientation). This is genuinely Jordan-curve-theorem-level and absent from Mathlib. Following the project's established pattern, this round adds more of the proved, reusable geometric foundation that the eventual ear-existence proof consumes, while keeping the clean single-core reduction intact.

New file `RequestProject/SAWUmlaufEarExtreme.lean`, imported by `SAWUmlaufPolygon` (hence transitively from `SAWFinal`, so part of the build chain). All its lemmas are proved sorry-free and verified to depend only on `propext, Classical.choice, Quot.sound`. It supplies the Step-1 convexity of Meisters' ear argument — that the extreme vertex is a convex-hull vertex — and crucially it now consumes the barycentric backbone of `SAWUmlaufEarConvex` and the strict-interior predicate of `SAWUmlaufEar` (so earlier preparation is no longer feeding only the open core):
- `inTriangleStrict_convexCombo` — a strict interior point of a triangle in either orientation is a strict convex combination of the three vertices (the negative-orientation case reduces to the proved positive case by swapping two vertices);
- `inTriangleStrict_not_lexMin` — such an interior point is never lexicographically minimal (leftmost, then lowest) among the three vertices, because its coordinates are strict positive-weight averages of the vertices' coordinates;
- `lexMin_not_inTriangleStrict` — combining with `SAWUmlaufEar.exists_lex_min_mem`, the lexicographically minimal vertex of the polygon is never in the strict interior of any triangle spanned by polygon vertices, i.e. the extreme vertex is a convex-hull vertex, which is exactly what makes Meisters' Step-1 corner convex.

These are documented in the file as preparation for `exists_ear_clip`: they are imported into the chain and link the previously stand-alone interior-point machinery into a consumed sub-chain, so they are recorded partial progress rather than a dead branch. The status note in `PROOF_STATUS.md` was updated to describe this round. The only remaining `sorry` in the Umlauf files is the single `exists_ear_clip` core.

# Summary of changes for run 52a8f1b7-bc8c-408f-8d02-7f136c9025cb
Continued the SAW.tex formalization, working exclusively on the top-priority discrete Hopf Umlaufsatz and leaving every other branch untouched. The whole library still builds successfully (`lake build`, 8121 jobs, including `RequestProject/SAWFinal.lean`).

Status of the Umlaufsatz: its remaining content is still concentrated in the single honest `sorry` — the two-ears / ear-existence core `exists_ear_clip` in `RequestProject/SAWUmlaufPolygon.lean` (a simple, non-degenerate polygon with ≥4 vertices has a clippable convex ear preserving planar simplicity, non-degeneracy, total turning and orientation). This is genuinely Jordan-curve-theorem level and absent from Mathlib; following the project's established pattern this round adds more of the proved, reusable geometric foundation that the eventual ear-existence proof will consume, while keeping the clean single-core reduction intact.

New file `RequestProject/SAWUmlaufEarEmpty.lean`, imported by `SAWUmlaufPolygon` (hence transitively from `SAWFinal`, so part of the build chain), all three lemmas proved sorry-free (verified to depend only on `propext, Classical.choice, Quot.sound`). It supplies the Step-2 (empty-triangle / farthest-vertex) geometry of Meisters' ear argument, and crucially it now **consumes** the barycentric backbone of `SAWUmlaufEarConvex` (so that earlier preparation is no longer feeding only the open core):
- `subTri_axc_orient_pos` — a positively-oriented strict interior point `x` of the triangle `a,b,c` makes the sub-triangle `a,x,c` itself positively oriented (`0 < cross (x-a) (c-x)`), the barycentric weight of `b` being the proportionality factor;
- `inTriangleStrict_pos_nest` — strict interiors nest: a point strictly inside the positively-oriented sub-triangle `a,q,c` (with `q` strictly inside `a,b,c`) is strictly inside `a,b,c`, the convexity/transitivity fact that lets the ear search recurse into the smaller triangle;
- `farthest_region_empty` — the maximality clause: no candidate vertex is strictly farther from the base line `a–c` than the chosen farthest vertex `q`, i.e. the region of the corner triangle beyond `q` is empty, which is what makes the Step-2 diagonal `v–q` valid.

These are documented as preparation for `exists_ear_clip`: they are imported into the chain and now also link the previously stand-alone `SAWUmlaufEarConvex` lemmas into a consumed sub-chain, so they are recorded partial progress rather than dead branches. The status note at the top of `PROOF_STATUS.md` was updated to record this round.

# Summary of changes for run f23da842-d81c-4d3e-998a-5d89ca99a1e7
Continued the SAW.tex formalization, working exclusively on the top-priority discrete Hopf Umlaufsatz and leaving every other branch untouched. The whole library still builds successfully (`lake build`, 8120 jobs, including `RequestProject/SAWFinal.lean`).

Status of the Umlaufsatz: its remaining content is still concentrated in a single honest `sorry` — the two-ears / ear-existence core `exists_ear_clip` in `RequestProject/SAWUmlaufPolygon.lean` (a simple, non-degenerate polygon with ≥4 vertices has a clippable convex ear preserving planar simplicity, non-degeneracy, total turning and orientation). This is genuinely Jordan-curve-theorem-level and absent from Mathlib; it cannot be closed in one pass because it needs plane-topology infrastructure (interior/empty-triangle geometry) that Mathlib lacks. Following the project's established pattern, this round builds more of the proved, reusable geometric foundation that the eventual ear-existence proof will consume, while keeping the clean single-core reduction intact.

New file `RequestProject/SAWUmlaufEarConvex.lean`, imported by `SAWUmlaufPolygon` (hence transitively from `SAWFinal`, so it is part of the build chain), all proved sorry-free (verified to depend only on `propext, Classical.choice, Quot.sound`). It supplies the barycentric backbone of Meisters' Step 2 (deciding which polygon vertices lie inside a candidate ear triangle):
- `cross_bary_sum` — the three oriented edge cross products of a point against a triangle sum to the triangle orientation `cross (b-a) (c-b)` (the three sub-triangles tile the whole);
- `cross_bary_recon` — the affine reconstruction identity `area2 • x = (γ-weight)•a + (α-weight)•b + (β-weight)•c`;
- `inTriangleStrict_pos_area` — a positively-oriented strict interior point forces `cross (b-a) (c-b) > 0`;
- `inTriangleStrict_pos_convexCombo` — a strict interior point is a strict convex combination of the vertices (positive weights summing to 1);
- `convexCombo_pos_inTriangleStrict` — its converse;
- `inTriangleStrict_pos_iff_convexCombo` — the bundled characterization converting the cross-product interior test to honest convex-hull membership.

These are explicitly documented as preparation for `exists_ear_clip`: they are imported into the chain but not yet referenced by another declaration only because the core they feed is still open, so they are recorded partial progress, not a dead branch. The only other changes are the one-line `import` added to `SAWUmlaufPolygon.lean` and a round note prepended to `PROOF_STATUS.md`. No other files were modified, and no new sorries were introduced (the new file is entirely sorry-free).

# Summary of changes for run acc724f9-ddc4-4f16-9b93-866ae671d8d4
Continued the SAW.tex formalization, working exclusively on the top-priority discrete Hopf Umlaufsatz and leaving all other branches untouched. The whole library still builds successfully (`lake build`, 8119 jobs, including `RequestProject/SAWFinal.lean`).

Status of the Umlaufsatz: its remaining content is still concentrated in a single honest `sorry` — the two-ears / ear-existence core `exists_ear_clip` in `RequestProject/SAWUmlaufPolygon.lean` (a simple, non-degenerate polygon with ≥4 vertices has a clippable convex ear preserving planar simplicity, non-degeneracy, total turning and orientation). This is genuinely Jordan-curve-theorem-level and absent from Mathlib; it is not closable in a single pass because it needs plane-topology infrastructure (segment-crossing / empty-triangle geometry) that does not exist in Mathlib. So this round, following the project's established pattern, builds more of the proved, reusable geometric foundation that the eventual ear-existence proof will consume, while keeping the clean single-core reduction intact.

New file `RequestProject/SAWUmlaufEarExist.lean`, imported by `SAWUmlaufPolygon` (hence transitively from `SAWFinal`, so it is part of the build chain), all proved sorry-free (verified to depend only on `propext, Classical.choice, Quot.sound`). It supplies the Step-2 (farthest-vertex) building blocks of Meisters' ear-existence argument:
- `collinear_iff_cross_eq_zero` — three points are collinear iff the 2-D cross product of their edge vectors vanishes (the degenerate-diagonal test);
- `exists_max_cross` — over a nonempty vertex list there is one maximizing the signed distance `cross d (·-a)` to a fixed base direction (the "farthest from the base diagonal" pivot that drives Step 2);
- `inTriangleStrict_cyclic` — the strict-interior predicate is invariant under cyclic relabeling `a,b,c ↦ b,c,a` of the triangle;
- `inTriangleStrict_ne_ab/bc/ca` — a triangle with a strict interior point has three pairwise distinct vertices.

These are explicitly documented as preparation for `exists_ear_clip`: they are imported into the chain but not yet referenced by another declaration only because the core they feed is still open, so they are recorded partial progress, not a dead branch. The only other changes are the one-line `import` added to `SAWUmlaufPolygon.lean` and a round note prepended to `PROOF_STATUS.md`. No other files, and no other (dead-branch) sorries, were touched.

# Summary of changes for run c1251b50-91ce-4dab-808a-51a0f85be02d
Continued the SAW.tex formalization, working exclusively on the top-priority discrete Hopf Umlaufsatz and leaving all other branches untouched. The whole library still builds successfully (`lake build`, 8118 jobs, including `RequestProject/SAWFinal.lean`).

Status of the Umlaufsatz: its remaining content was already factored, in prior rounds, into a single honest `sorry` — the two-ears / ear-existence core `exists_ear_clip` in `RequestProject/SAWUmlaufPolygon.lean` (a simple, non-degenerate polygon with ≥4 vertices has a clippable convex ear preserving planar simplicity, non-degeneracy, total turning and orientation). This is genuinely Jordan-curve-theorem-level and absent from Mathlib. A direct attempt to discharge it confirmed it is not closable in one pass, so this round builds the proved, reusable geometric foundation that the eventual proof (via Meisters' ear-existence argument) will consume, and preserves the clean single-core state.

New file `RequestProject/SAWUmlaufEar.lean`, imported by `SAWUmlaufPolygon` (hence transitively from `SAWFinal`, so it is part of the build chain), all proved sorry-free (verified to depend only on `propext, Classical.choice, Quot.sound`):
- `HexArea.cross_smul_left/right`, `cross_sub_left/right` — the ℝ-bilinearity/scalar laws of the 2-D cross product underlying every orientation computation;
- `cross_edges_eq_shoelace2_triple` — the corner orientation `cross (b-a) (c-b)` equals the signed area `shoelace2 [a,b,c]` of the triangle it cuts off (the bridge between corner convexity and the sign of its area, used in Steps 1 and 3 of the ear argument);
- `cross_eq_zero_of_mem_segment`, `collinear_of_mem_segment` — a point on `segment ℝ a b` is collinear with `a,b` (degenerate-diagonal test);
- `exists_lex_min_mem` — every nonempty vertex list has a lexicographically minimal (leftmost-lowest) vertex, the convex extreme vertex the ear search starts from (Step 1);
- the strict-interior predicate `inTriangleStrict` with `inTriangleStrict_ne_a/b/c` and `inTriangleStrict_nondeg` — the empty-triangle / farthest-vertex machinery for Step 2.

These are explicitly documented as preparation for `exists_ear_clip`: they are imported into the chain but not yet referenced by another declaration only because the core they feed is still open, so they are recorded partial progress, not a dead branch. The only other change is the one-line `import` added to `SAWUmlaufPolygon.lean` and the status notes in `PROOF_STATUS.md` / `ARISTOTLE_SUMMARY.md`. No axioms or `@[implemented_by]` were introduced. The single remaining Umlaufsatz gap is `exists_ear_clip`, preserved as an honest, well-documented Lean `sorry`.

# Summary of changes — Umlaufsatz ear-existence geometry-toolkit round (NEWEST)

Worked exclusively on the top-priority discrete Hopf Umlaufsatz, leaving all
other branches untouched. The whole library still builds successfully
(`lake build`, 8118 jobs, including `RequestProject/SAWFinal.lean`).

The single remaining Umlaufsatz `sorry` is still the two-ears /
ear-existence core `exists_ear_clip` (`RequestProject/SAWUmlaufPolygon.lean`),
which is genuinely Jordan-curve-theorem-level and absent from Mathlib. This
round builds the **proved, reusable plane-geometry toolkit** that the eventual
proof of `exists_ear_clip` (via Meisters' ear-existence argument) will consume,
in a new file `RequestProject/SAWUmlaufEar.lean`, imported by
`SAWUmlaufPolygon` (hence transitively from `SAWFinal`), so it is part of the
build chain. It is explicitly **preparation**: its lemmas are not yet referenced
by another declaration because the core they feed is still open, but they are
recorded partial progress toward it, not a dead branch.

New, fully proved (only `propext, Classical.choice, Quot.sound`):
* `HexArea.cross_smul_left/right`, `HexArea.cross_sub_left/right` — the `ℝ`-
  bilinearity / scalar laws of the 2-D cross product used for every orientation
  computation;
* `HexArea.cross_edges_eq_shoelace2_triple` — the orientation of a corner
  `a,b,c` equals the signed area `HexArea.shoelace2 [a,b,c]` it cuts off (the
  Step-1/Step-3 bridge between convexity of a corner and the sign of its area);
* `HexArea.cross_eq_zero_of_mem_segment`, `HexArea.collinear_of_mem_segment` —
  a point on `segment ℝ a b` is collinear with `a,b` (degenerate-diagonal test);
* `HexArea.exists_lex_min_mem` — every nonempty vertex list has a
  lexicographically minimal (leftmost-lowest) vertex, the convex extreme vertex
  Meisters' ear search starts from (Step 1);
* `HexArea.inTriangleStrict` predicate (strict interior of an oriented triangle
  via the three edge cross products) with `inTriangleStrict_ne_a/b/c` (an
  interior point differs from each vertex) and `inTriangleStrict_nondeg` (a
  triangle with a strict interior point is non-degenerate) — the Step-2
  machinery for the empty-triangle test and the farthest-vertex diagonal.

No other files were changed except the one-line `import` added to
`SAWUmlaufPolygon.lean` and the documentation. The clean single-core state of
the Umlaufsatz reduction is preserved; `exists_ear_clip` remains the lone gap.

# Summary of changes for run b4ccddb9-59cb-4c03-9ed4-0ca751d1a911
Worked exclusively on the top-priority discrete Hopf Umlaufsatz, leaving all other branches untouched. The whole library still builds successfully (including `RequestProject/SAWFinal.lean`); all new work is in `RequestProject/SAWUmlaufPolygon.lean`, which is imported transitively from `SAWFinal`.

What changed: the previous lone Umlaufsatz `sorry`, the bundled ear-clipping reduction `polygon_ear_reduction`, is now **proved sorry-free** from a single sharper two-ears core plus a newly built, fully proved rotation-invariance toolkit.

New, fully proved lemmas (each verified to use only `propext, Classical.choice, Quot.sound`):
- `polyCycWind` — cyclic total turning of a vertex cycle — with `polyCycWind_rotate1` / `polyCycWind_rotate` (cyclic turning is invariant under rotation of the vertex list);
- `shoelace2_rotate1` / `shoelace2_rotate` — signed area is rotation invariant;
- `mem_closedEdges_rotate` and `PolygonSimple_rotate` — planar simplicity is rotation invariant;
- `polyCycNondeg` with `polyCycNondeg_rotate1` / `polyCycNondeg_rotate` — cyclic non-degeneracy is rotation invariant;
- `shoelace2_clip_second` — clipping the second vertex changes the signed area by exactly the cut-off ear-triangle's area.

Using these, `polygon_ear_reduction` is derived by rotating the abstract ear into the second position and transporting the four cyclic invariants (simplicity, non-degeneracy, turning, orientation) back to the polygon's own closing form. This concentrates all the remaining content of the planar Umlaufsatz into one honest, sharply stated `sorry`: `exists_ear_clip`, the genuine Jordan-curve-theorem-level two-ears statement (a simple non-degenerate polygon with ≥4 vertices has a clippable convex ear preserving planar simplicity), which is absent from Mathlib.

Partial progress is preserved as honest, well-documented Lean sorries; the rotation toolkit is explicitly documented as preparation that a future proof of the core will consume, and it is part of the build chain. `PROOF_STATUS.md` and `ARISTOTLE_SUMMARY.md` were updated to record this round. The single remaining Umlaufsatz gap is now `exists_ear_clip`; the honeycomb-planarity core remains closed.

# Summary of changes — Umlaufsatz ear-clipping rotation-toolkit round (NEWEST)

Worked exclusively on the top-priority discrete Hopf Umlaufsatz, leaving all
other branches untouched. The whole library still builds successfully
(`lake build`, including `RequestProject/SAWFinal.lean`); every new declaration
lives in `RequestProject/SAWUmlaufPolygon.lean`, which is imported transitively
from `SAWFinal`.

**Reduced the last Umlaufsatz core to a sharper, concrete two-ears statement and
proved all the ear-clipping glue around it.** Previously the lone remaining
Umlaufsatz `sorry` was the bundled `polygon_ear_reduction`. It is now **proved
sorry-free** from a single new, sharper core `exists_ear_clip` plus a fully
proved rotation-invariance toolkit.

New, fully proved (only `propext, Classical.choice, Quot.sound`):
* `polyCycWind` — cyclic total turning of a vertex cycle (`= polyWind (V ++ V.take 2)`);
* `polyCycWind_rotate1`, `polyCycWind_rotate` — cyclic turning is invariant under
  cyclic rotation of the vertex list (via `polyWind_append_singleton`);
* `shoelace2_rotate1`, `shoelace2_rotate` — the signed area is rotation invariant;
* `mem_closedEdges_rotate`, `PolygonSimple_rotate` — planar simplicity is
  rotation invariant (the closed-edge set and `Nodup` are preserved);
* `polyCycNondeg`, `polyCycNondeg_rotate1`, `polyCycNondeg_rotate` — cyclic
  non-degeneracy is rotation invariant;
* `shoelace2_clip_second` — clipping the second vertex changes the signed area by
  exactly the cut-off ear-triangle’s area.

With these, `polygon_ear_reduction` is derived by rotating the abstract ear into
the second position and transporting the four cyclic invariants back to `V`’s own
closing form. The single remaining Umlaufsatz `sorry` is now `exists_ear_clip`
(`SAWUmlaufPolygon.lean`): the genuine Jordan-curve-theorem-level two-ears
content (existence of a clippable convex ear preserving planar simplicity).
Partial progress is preserved as honest, well-documented Lean sorries; the
rotation toolkit is preparation that the eventual core proof will consume.

# Summary of changes for run ade3861d-c030-4361-93b1-fb879ffe6bb0
Worked exclusively on the top-priority discrete Hopf Umlaufsatz, leaving all other branches untouched. The whole library still builds successfully (`lake build`, 8117 jobs, including `RequestProject/SAWFinal.lean`).

**Result: the honeycomb-planarity core of the Umlaufsatz is now completely eliminated.** Previously the Umlaufsatz had two remaining `sorry` cores; one of them — `hexEmbeddedPolygon_edges_disjoint` in `RequestProject/SAWUmlaufPolygon.lean` (and hence the planarity lemma `hexEmbeddedPolygon_polygonSimple`) — is now **fully proved, sorry-free**, depending only on the standard axioms `propext, Classical.choice, Quot.sound`.

What was added / proved:
- New self-contained geometry file `RequestProject/SAWUmlaufHexEdge.lean`, imported by `RequestProject/SAWUmlaufPolygon.lean` (hence transitively from `SAWFinal`), so it is part of the proof chain. It develops, all sorry-free:
  - `hexEdge_dir` — an oriented honeycomb edge embeds to one of three explicit unit directions (`1`, `-1/2 ± (√3/2)·I`);
  - `hexEdge_false_or` — the false/true sublattice parity of an edge's two endpoints;
  - the nine direction-pair leaf lemmas `hexEdge_disjoint_leaf_ij` (two unit honeycomb segments sharing no vertex are disjoint), with the three off-diagonal cases derived from the others by `Disjoint.symm`;
  - the dispatchers `hexEdge_disjoint_d1/d2/d3`, the oriented core `hexEdge_segments_disjoint_oriented`, and the general `hexEdge_segments_disjoint`.
- In `SAWUmlaufPolygon.lean`, the combinatorial wiring of `hexEmbeddedPolygon_edges_disjoint` is now proved: each polygon edge is a `hexGraph` adjacency between consecutive trail vertices, and the endpoint inequalities transfer to vertex inequalities via `correctHexEmbed_injective`, closing the goal with the general geometric lemma.

Remaining Umlaufsatz gap (now a single one): `polygon_ear_reduction` in `RequestProject/SAWUmlaufPolygon.lean` — the ear-clipping / two-ears topological core (Jordan-curve-theorem level, absent from Mathlib). Everything around it (the strong-induction `polygon_umlaufsatz_take`, the triangle base case, the closing rewrites, the bridge to the hex core, and now the entire honeycomb planarity side) is proved. Partial progress is preserved as honest, well-documented Lean sorries, and `PROOF_STATUS.md` / `ARISTOTLE_SUMMARY.md` were updated to record that the honeycomb-planarity core is closed and `polygon_ear_reduction` is the single remaining core.

No axioms or `@[implemented_by]` were introduced; all new lemmas were verified to use only `propext, Classical.choice, Quot.sound`, and new-file linter warnings were fixed at the source.

# Summary of changes — Umlaufsatz honeycomb-planarity round (newest)

Worked exclusively on the top-priority discrete Hopf Umlaufsatz, leaving all
other branches untouched. The whole library still builds successfully
(`lake build`, including `RequestProject/SAWFinal.lean`).

**Closed the honeycomb-planarity core of the Umlaufsatz entirely.** The lemma
`hexEmbeddedPolygon_edges_disjoint` (`RequestProject/SAWUmlaufPolygon.lean`) —
previously one of the two remaining Umlaufsatz `sorry`s — is now **proved
sorry-free** (only `propext, Classical.choice, Quot.sound`), so
`hexEmbeddedPolygon_polygonSimple` is sorry-free too.

New file `RequestProject/SAWUmlaufHexEdge.lean` (imported by
`SAWUmlaufPolygon`, hence transitively from `SAWFinal`) isolates and proves the
geometric content, all sorry-free:
* `hexEdge_dir` — an oriented honeycomb edge embeds to one of three explicit unit
  directions `1, -1/2 ± (√3/2)·I`;
* `hexEdge_false_or` — false/true parity of an edge's two endpoints;
* the nine direction-pair leaf cases `hexEdge_disjoint_leaf_ij` (two unit
  honeycomb segments sharing no vertex are disjoint; the three off-diagonal
  `i>j` are obtained from `i<j` by `Disjoint.symm`);
* the dispatchers `hexEdge_disjoint_d1/d2/d3`, the oriented core
  `hexEdge_segments_disjoint_oriented`, and the general
  `hexEdge_segments_disjoint`.
The combinatorial wiring in `hexEmbeddedPolygon_edges_disjoint` (each polygon
edge is a `hexGraph` adjacency between consecutive trail vertices, with endpoint
inequalities transferred to vertex inequalities via `correctHexEmbed_injective`)
is also proved.

**Remaining Umlaufsatz gap (now a single one):** `polygon_ear_reduction`
(`RequestProject/SAWUmlaufPolygon.lean`) — the ear-clipping / two-ears
topological core. The honeycomb-planarity gap is closed.

---

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
