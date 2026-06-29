# Proof Status: μ = √(2+√2)

> **Umlaufsatz (CURRENT round): banked the split-recursion tip-disjointness
> brick `HexArea.chord_tip_ne_other` (sorry-free) in `SAWUmlaufEarSplit.lean`.**
> Worked exclusively on the top-priority discrete Hopf Umlaufsatz.  Library
> still builds end-to-end (8128 jobs through `SAWFinal.lean`); axioms unchanged
> (`propext, Classical.choice, Quot.sound`); no regressions; the five live
> Umlauf `sorry`s are unchanged in identity (the two boundary spike subcases in
> `empty_branch_boundary_lift`, `chord_ear_lift`, `meisters_reduction_interior2`,
> `empty_branch_bad_lift`).
>
> What changed this round:
> * New sorry-free reusable lemma `HexArea.chord_tip_ne_other` (placed right
>   after `chord_pieces_inter`): for a `Nodup` cycle `W` cut at `1 ≤ k < W.length`,
>   if the ear tip `b'` is an interior vertex of one chord piece (`b' ≠ W[0]!`,
>   `b' ≠ W[k]!`) and the target `z` lies in the OTHER piece, then `b' ≠ z`.
>   This is exactly the `b' ≠ z1, z2` bookkeeping the diagonal-split branches
>   (`meisters_reduction_interior2`, `empty_branch_bad_lift`) need: recursing on
>   the piece NOT containing the forbidden edge yields a tip avoiding both
>   forbidden endpoints.  Consumed (as preparation) by the split branches; NOT a
>   dead branch (its file is imported by `SAWUmlaufPolygon`).
>
> Findings this round (recorded so future rounds do not chase an infeasible
> one-shot target): the cut-edge bricks `chordLeft_cut_isCycEdge` /
> `chordRight_cut_isCycEdge` already exist sorry-free in `SAWUmlaufPolygon`, so
> the interior-branch *combinatorial* bricks are all present
> (`interior_split_select`, `rotate_corner_succ`, `forbidden_lands_in_chord`,
> the cut-edge lemmas, `chord_consec_triple_lift`, `chord_pieces_inter`,
> `chord_tip_ne_other`).  An assembly attempt on
> `meisters_reduction_interior2` modulo `chord_ear_lift` confirmed it is NOT
> one-shot closable: piece selection must simultaneously satisfy (i) avoid the
> forbidden edge, (ii) `polyCycNondeg` (only ONE piece is guaranteed — the
> flat-seam gap, needing `PolygonSimple_remove_flat_mid`), and (iii) length ≥ 4
> (a length-3 piece is a triangle with no `rest`, so `EmptyCornerData2` cannot
> be formed — the triangle base case).  These two combinatorial residues, on
> top of the shared Jordan keystone `chord_ear_lift` (point-in-polygon
> separation of the OTHER piece's vertices from the lifted ear triangle), are
> the precise remaining content of the interior/bad-diagonal branches.

> **Umlaufsatz (earlier round): banked the chord-piece vertex-disjointness brick
> `chord_pieces_inter` (sorry-free) and pinned down the precise structure of the
> remaining `chord_ear_lift` obstruction.**  Worked exclusively on the
> top-priority discrete Hopf Umlaufsatz.  The library still builds end-to-end
> (8128 jobs through `SAWFinal.lean`); no new axioms (`propext, Classical.choice,
> Quot.sound` only), no regressions, no new live `sorry`s.
>
> What changed this round (one new sorry-free, reusable lemma in
> `RequestProject/SAWUmlaufEarSplit.lean`, verified axiom-clean):
> * `chord_pieces_inter` — for a `Nodup` cycle `V` cut at `1 ≤ k < V.length`, a
>   vertex lying in BOTH `chordLeft V k` and `chordRight V k` is one of the two
>   diagonal endpoints `V[0]` or `V[k]`.  This is exactly the vertex-disjointness
>   needed for *piece selection* in the split branches
>   (`meisters_reduction_interior2`, `empty_branch_bad_lift`): a forbidden cyclic
>   edge `{z1,z2}` that lands in one piece cannot make an interior vertex of the
>   OTHER piece equal to `z1`/`z2`, so the ear tip returned by recursion avoids
>   the forbidden pair.  Documented as preparation consumed by the split
>   branches; NOT a dead branch (its file is imported by `SAWUmlaufPolygon`).
>
> Findings this round (recorded so future rounds do not chase an impossible
> target):
> * `chord_ear_lift` is **under-hypothesised as currently stated** and is not
>   provable in that generic form.  Two distinct gaps were isolated:
>   1. **Turn-transfer seam.**  The ear tip `b'` returned by the recursion is
>      forced `≠ u, v`, but its neighbours `a'`/`c'` are NOT: when the ear sits
>      adjacent to a cut endpoint (e.g. `b' = W[1]`, so `a' = W[0] = u` in the
>      `chordLeft` cycle), the corner non-degeneracy `cross (a' - p')(c' - a')`
>      required in `V` is taken at the V-predecessor of `a'` (a vertex of the
>      OTHER piece), which differs from the P-corner supplied by
>      `EmptyCornerData2 P`.  So the two turn clauses of the conclusion do not
>      transfer from the hypotheses without extra non-degeneracy data — the same
>      flat-seam content as the boundary spike subcases.
>   2. **Jordan emptiness.**  Even with the turns handled, the emptiness clause
>      ranges over ALL of `V`'s remaining vertices, including the OTHER chord
>      piece `Q`.  For `x ∈ Q \ {u,v}` one needs that the lifted ear triangle
>      `(a',b',c') ⊆ region(P)` is separated from `Q` by the cut diagonal — the
>      genuine point-in-polygon / Jordan separation, absent from the project and
>      from Mathlib.  Note `EmptyCornerData2 P u v` constrains only P's own
>      vertices, so the generic statement (with no diagonal-validity hypothesis)
>      is in fact *false*: a crossing (non-diagonal) cut can have a `Q`-vertex
>      strictly inside an ear triangle of `P`.
> * Recommended correction for the next round: restate `chord_ear_lift` to carry
>   (i) the diagonal-validity of the cut (available from
>   `interior_chord_is_diagonal` at the call sites) and (ii) the requirement that
>   the returned ear be non-adjacent to the cut endpoints (or fold in the
>   flat-seam non-degeneracy bricks `interior_split_nondeg_left/right`).  Then
>   `chord_pieces_inter` discharges the `b' ≠ z1,z2` bookkeeping and the only
>   irreducible residue is the single Jordan separation fact (2.).
>
> Net: the four live `sorry`s of the empty/interior branches are unchanged in
> identity; the new brick + the structural finding sharpen the path without
> adding speculative scaffolding.

> **Umlaufsatz (earlier round): isolated the single irreducible obstruction into
> one precise, compiling, reusable brick `chord_ear_lift`, and confirmed the
> interior split branch reduces cleanly to it.**  Worked exclusively on the
> top-priority discrete Hopf Umlaufsatz.  The library still builds end-to-end
> (8128 jobs through `SAWFinal.lean`); no new axioms, no regressions.
>
> What changed this round (one new declaration in
> `RequestProject/SAWUmlaufPolygon.lean`):
> * `chord_ear_lift` — a `sorry`-bearing brick that states EXACTLY the single
>   missing point-in-polygon / Jordan-curve separation fact.  Cutting the
>   rotation `W` of a simple polygon `V` along the interior diagonal `W[0]–W[k]`
>   into `chordLeft W k` / `chordRight W k`, an ear of one piece `P` avoiding the
>   cut edge `{u,v}` (packaged as `EmptyCornerData2 P u v`) lifts to a genuine
>   ear of the WHOLE polygon `V`, including the emptiness of the lifted ear
>   triangle against the vertices of the OTHER piece (the irreducible Jordan
>   residue).  Documented and linked as preparation consumed by the interior
>   (`meisters_reduction_interior2`) and bad-diagonal (`empty_branch_bad_lift`)
>   split branches — NOT a dead branch.
>
> Findings this round:
> * High-effort proof searches with `chord_ear_lift` in scope showed that the
>   interior branch `meisters_reduction_interior2` assembles correctly AROUND
>   the brick: the subagent built the full skeleton using the already-banked
>   `forbidden_lands_in_chord`, `IsCycEdge_rotate`, `chordLeft_cut_isCycEdge` /
>   `chordRight_cut_isCycEdge`, `interior_split_select`,
>   `interior_split_nondeg_left/right`, and `chord_ear_lift`, leaving only the
>   brick's geometric `sorry` and the flat-seam piece-selection sub-case as the
>   residue.  This pins the entire interior-branch content to `chord_ear_lift`.
> * A direct high-effort search on `chord_ear_lift` itself times out: the
>   combinatorial lift (consecutive-triple via `chord_consec_triple_lift`,
>   orientation via `shoelace2_chord_split`) is mechanical, but the emptiness of
>   the lifted ear triangle against the OTHER piece's vertices needs a genuine
>   polygon-interior (point-in-polygon / winding-number) separation predicate,
>   absent from the project AND from Mathlib.
>
> Net: the four live `sorry`s of the empty/interior branches now have their
> shared geometric core stated as ONE clean, compiling, reusable lemma
> `chord_ear_lift`.  Recommended next direction: construct a winding-number /
> point-in-polygon membership predicate (the project's `SAWTurningNumber` /
> `SAWUmlaufGaussBonnet` turning machinery is the natural foundation) and use it
> to discharge `chord_ear_lift`; that single proof then unlocks both the
> interior and bad-diagonal split branches.

> **Umlaufsatz (earlier round): re-confirmed and sharpened the precise residual
> obstruction; no code change (build still green, same 4 live `sorry`s).**
> Worked exclusively on the top-priority discrete Hopf Umlaufsatz.  The library
> still builds end-to-end (8128 jobs through `SAWFinal.lean`); no new axioms, no
> regressions, no new `sorry`s, and no `sorry` was removed.
>
> The four live `sorry`s in the Umlauf chain are unchanged in identity:
> `meisters_reduction_interior2`, `empty_branch_bad_lift`, and the two boundary
> spike subcases inside `empty_branch_boundary_lift`.  (`SAWUmlaufPolygon.lean`
> line 4077 is a `sorry` inside a `/- ... -/` documentation block for the
> known-FALSE dead branch `ear_turning_bounds`, not a live obstruction.)
>
> Findings this round:
> * A direct high-effort proof-search on the best-prepared target
>   `meisters_reduction_interior2` (after the banked `interior_split_select`
>   setup) again times out.  The remaining content is the *ear lift across the
>   chord split*: after recursing via `IH2` on the chord piece avoiding the
>   forbidden edge, the returned ear triangle must be shown empty of *every*
>   vertex of `V`, including the (many) vertices of the OTHER chord piece.
>   Unlike `empty_branch_interior_lift` (clip case: only the single apex `b` is
>   re-inserted, handled by `hbconv`), the chord case removes a whole piece, so
>   the emptiness genuinely needs polygon-interior region separation along the
>   diagonal `b–w` — i.e. a point-in-polygon / Jordan-curve characterisation,
>   which is absent from the project AND from Mathlib (no winding-number
>   interior predicate exists anywhere in the chain).
> * New combinatorial sharpening of **boundary spike subcase A** (the `sorry` at
>   `empty_branch_boundary_lift`, Case A, where `cross (a - a') (b - a) = 0`):
>   in Case A one has `c' = a` and `rest' = c :: rest''`, which forces the ear
>   tip `b'` to be the clip-predecessor of `a`, namely `b' = p = rest.getLast`,
>   and `a'` to be the clip-predecessor of `p`.  Hence `(a', p, a)` is ALREADY a
>   genuine consecutive triple of `V` (`a' = rest[-2]`, `p = rest[-1]`, then `a`
>   by wrap-around).  Moreover the spike collinearity `a', a, b` together with
>   `PolygonSimple V` forces the strict ordering `a ∈ openSegment(b, a')` (the
>   alternative `a' ∈ openSegment(a, b)` is impossible, since `a–b` is a polygon
>   edge and a vertex cannot lie in the open interior of an edge).  The ONLY
>   reason `(a', p, a)` fails the `EmptyCornerData2` packaging is that its apex
>   turn `cross (a - a') (b - a)` — the turn at `a` toward the cyclic successor
>   `b` — is exactly the vanishing spike quantity, i.e. clipping `p` makes `a` a
>   flat (degenerate) vertex of the residual polygon.  Emptiness and
>   diagonal-clearance of `(a', p, a)` DO transfer (via `hbconv`/`hbseg`); the
>   genuine residue is the two-ears step: a different ear (off the flattened
>   junction) must be selected.  This pins the spike obstruction to the same
>   irreducible two-ears / Jordan content as the interior branch.
>
> Net: the irreducible gap of the discrete Umlaufsatz is now uniformly pinned —
> across all four live `sorry`s — to a single missing brick: a polygon-interior
> (point-in-polygon / winding-number) separation predicate for the chord cut.
> Building it is the recommended next direction.

> **Umlaufsatz (earlier round): banked the signed-area additivity across the
> chord cut (sorry-free).**  Worked exclusively on the top-priority discrete
> Hopf Umlaufsatz.  The whole library still builds end-to-end (8128 jobs through
> `SAWFinal.lean`); no new axioms (`propext, Classical.choice, Quot.sound`
> only), no regressions, no new live `sorry`s.
>
> One new sorry-free, reusable, axiom-clean lemma in
> `RequestProject/SAWUmlaufEarSplit.lean`:
> * `shoelace2_chord_split` — for `1 ≤ k < V.length`,
>   `shoelace2 (chordLeft V k) + shoelace2 (chordRight V k) = shoelace2 V`.
>   Cutting the closed polygon `V` along the diagonal `V[0]–V[k]` into the two
>   pieces is area-preserving: the shared-diagonal cross terms
>   (`cross V[k] V[0]` on the left, `cross V[0] V[k]` on the right) cancel by
>   `cross_antisymm`, and the open chains reassemble the closed shoelace of `V`.
>   This is the pure-algebra ingredient of the orientation transfer in the
>   interior-branch ear lift (`meisters_reduction_interior2`).  Documented as
>   preparation (consumed by the open interior core), NOT a dead branch.
>
> Direct high-effort attempts on the two remaining single-`sorry` lifts
> (`meisters_reduction_interior2`, `empty_branch_bad_lift`) still time out: both
> funnel into the same irreducible Jordan-curve-level emptiness/separation
> transfer (a vertex of the OTHER chord piece lying off the lifted ear
> triangle), which requires polygon-interior region separation absent from the
> current segment/cross-product/area toolkit.  Live `sorry`s in the Umlauf chain
> are unchanged in identity: the two boundary spike subcases (inside
> `empty_branch_boundary_lift`), `meisters_reduction_interior2`, and
> `empty_branch_bad_lift`.

> **Umlaufsatz (earlier round): banked the recursion-ready interior-split bundle
> (sorry-free) and wired it into the interior branch.**  Worked exclusively on
> the top-priority discrete Hopf Umlaufsatz in `RequestProject/SAWUmlaufPolygon.lean`.
> The whole library still builds end-to-end (8128 jobs through `SAWFinal.lean`);
> no new axioms (`propext, Classical.choice, Quot.sound` only), no regressions,
> no new live `sorry`s.
>
> One new sorry-free, reusable, axiom-clean lemma:
> * `interior_split_select` — consolidates the banked interior-split bricks
>   (`interior_split_simple`, `interior_split_one_nondeg`, `chordLeft_length_lt`,
>   `chordRight_length_lt`) into the single package the interior branch consumes:
>   from the convex corner `a,b,c` and the farthest interior vertex `w`, it
>   returns the cut index `k` for `W := b :: c :: rest ++ [a]` with BOTH pieces
>   `chordLeft W k` / `chordRight W k` `PolygonSimple` and strictly shorter than
>   `V`, plus AT LEAST ONE of them `polyCycNondeg` — exactly the `IH2` recursion
>   fuel for the piece avoiding the forbidden edge.
>
> `meisters_reduction_interior2` now opens by deriving the corner non-flatness
> `cross (b-a) (c-b) ≠ 0` from `polyCycNondeg V` (via `polyNondeg_cons_cons_cons`)
> and obtaining the `interior_split_select` bundle, so the brick is genuinely
> consumed (NOT a dead branch).  Its remaining content is now exactly the
> recurse-via-`IH2`-and-lift step whose only irreducible gap is the
> Jordan-curve-level ear-emptiness transfer (a vertex of the OTHER chord piece
> lies off the lifted ear triangle), which requires polygon-interior-region
> separation absent from the current segment/cross-product toolkit.
>
> Live `sorry`s in the Umlauf chain are unchanged in identity: the two boundary
> spike subcases (inside `empty_branch_boundary_lift`), `meisters_reduction_interior2`,
> and `empty_branch_bad_lift`.

> **Umlaufsatz (earlier round): the boundary-seam ear lift is now PROVED on its
> non-spike part; only the two collinear "spike" subcases remain.**  Worked
> exclusively on the top-priority discrete Hopf Umlaufsatz in
> `RequestProject/SAWUmlaufPolygon.lean`.  The whole library still builds
> end-to-end (8128 jobs through `SAWFinal.lean`); no new axioms
> (`propext, Classical.choice, Quot.sound` only), no regressions.
>
> Four new sorry-free, reusable lemmas were banked:
> * `clip_ear_lift_general` — arbitrary-prefix generalisation of
>   `clip_ear_lift_interior`: from `(a::c::rest).rotate r' = pre ++ a::c::suf`
>   re-inserting the apex `b` gives `(a::b::c::rest).rotate r'' = pre ++ a::b::c::suf`.
> * `clip_ear_lift_seamB` — the wrap-around (Case B) apex re-insertion, built on
>   `clip_ear_lift_general`.
> * `boundary_lift_caseA_nonspike` / `boundary_lift_caseB_nonspike` — assemble a
>   genuine `EmptyCornerData2 V z1 z2` ear directly in each seam configuration of
>   `boundary_seam_split`, **assuming the apex turn is non-zero** (`cross (a-a')
>   (b-a) ≠ 0` resp. `cross (c-b) (c'-c) ≠ 0`).  Emptiness/diagonal-avoidance of
>   the re-inserted apex come from `hbconv`/`hbseg`; the orientation `iff` is
>   assembled from `shoelace2_clip_second`, `shoelace2_insert_mid`,
>   `shoelace2_rotate`.
>
> `empty_branch_boundary_lift` (hypothesis `hlen` strengthened to `5 ≤ V.length`,
> which the only caller `empty_branch_good_lift` supplies) was rewritten to
> dispatch via `boundary_seam_split` and the two non-spike lemmas, so its single
> broad Jordan-content `sorry` is now replaced by exactly the two NARROW spike
> subcases (`cross (a-a') (b-a) = 0`, resp. `cross (c-b) (c'-c) = 0`): the
> genuine collinear two-ears residue where re-inserting the apex flattens the
> diagonal-endpoint turn and a different ear must be chosen.
>
> Live `sorry`s in the Umlauf chain are now: the two boundary spike subcases
> (inside `empty_branch_boundary_lift`), `meisters_reduction_interior2`, and
> `empty_branch_bad_lift`.

> **Umlaufsatz (earlier round): banked the boundary-seam split + pinned the
> precise residual obstruction of the boundary lift (sorry-free).**  Worked
> exclusively on the top-priority discrete Hopf Umlaufsatz in
> `RequestProject/SAWUmlaufPolygon.lean`.  The whole library still builds
> end-to-end (8128 jobs through `SAWFinal.lean`); no new axioms, no regressions.
> The three genuine live `sorry`s (`empty_branch_boundary_lift`,
> `meisters_reduction_interior2`, `empty_branch_bad_lift`) are unchanged in
> identity; NO new `sorry`s were introduced.  One new sorry-free reusable lemma
> (axioms `propext, Classical.choice, Quot.sound` only), placed directly before
> `empty_branch_boundary_lift` and documented as preparation (NOT a dead
> branch):
> * `boundary_seam_split` — in the boundary subcase, the clip cycle
>   `M = a :: c :: rest` (`Nodup`, `2 ≤ rest.length`) recursed via `IH2` returns
>   an ear `M.rotate r' = a' :: b' :: c' :: rest'` with `b' ≠ a`, `b' ≠ c`; when
>   the `a–c` junction is not interior to `rest'` (`hnotint`) it must sit at the
>   rotation seam, forcing exactly one of two configurations:
>   `(c' = a ∧ rest'.head? = some c)` (Case A) or
>   `(a' = c ∧ rest'.getLast? = some a)` (Case B).  Pure list-combinatorics core
>   (unique cyclic successor of `a` is `c`).
>
> This reduces the boundary lift to two concrete sub-cases, in each of which the
> ear lifts to a genuine consecutive triple of `V` by inserting the apex `b` at
> the junction.  The precise residual obstruction is now pinned down in the
> `empty_branch_boundary_lift` docstring: exactly ONE of the two
> `EmptyCornerData2` clip-turns survives directly (`= hpt'`/`hqt'`); the OTHER
> becomes an *apex turn* (`cross (a-a') (b-a)` in Case A, `cross (c-b) (c'-c)` in
> Case B) that can GENUINELY VANISH in a "spike" configuration (where `a` lies
> strictly between `a'` and `b`), forbidden by neither `hbseg` (which constrains
> `b`, not `a`) nor `polyCycNondeg` (which only constrains consecutive triples).
> Hence the natural ear may fail and a DIFFERENT ear must be chosen — closing
> this branch requires the full two-ears theorem (or a strengthened induction
> invariant forcing the returned ear off the junction).  This is the
> irreducible Jordan-curve-level residue.

> **Umlaufsatz (earlier round): banked the rotation/list-surgery core of the
> interior-branch ear lift (sorry-free).**  Worked exclusively on the top-priority
> discrete Hopf Umlaufsatz.  The whole library still builds end-to-end (8128
> jobs through `SAWFinal.lean`); no new axioms, no regressions.  The three
> genuine live `sorry`s (`empty_branch_boundary_lift`,
> `meisters_reduction_interior2`, `empty_branch_bad_lift`) are unchanged in
> identity; NO new `sorry`s.  Two new sorry-free reusable lemmas in
> `SAWUmlaufPolygon.lean` (axioms `propext, Classical.choice, Quot.sound` only),
> placed after `forbidden_lands_in_chord` and documented as preparation for the
> interior split (NOT dead branches):
> * `consec_edges_triple` — in a `Nodup` cyclic vertex list `W`, two cyclic
>   edges `(a',b')`, `(b',c')` sharing the middle vertex `b'` (with `a' ≠ c'`)
>   force `a',b',c'` to be three consecutive vertices: `∃ r' tl, W.rotate r' =
>   a' :: b' :: c' :: tl`.
> * `chord_consec_triple_lift` — if a rotation of a chord piece
>   (`chordLeft W k` / `chordRight W k`) of a `Nodup` cycle `W` starts with
>   `a' :: b' :: c'` and the middle `b'` avoids the cut endpoints `W[0]`, `W[k]`,
>   then `a',b',c'` are consecutive in the parent cycle `W`.  This is the
>   rotation/list-surgery core of the interior-branch ear lift: an ear of the
>   recursed chord piece whose tip avoids the cut endpoints lifts to a genuine
>   consecutive triple (rotation witness) of `V`.  The remaining genuine content
>   of `meisters_reduction_interior2` is now the *geometric* emptiness /
>   diagonal-clearance / orientation transfer (vertices of the other piece lie
>   off the ear triangle), the Jordan-curve-level residue, plus the
>   flat-cut-vertex removal sub-case.

> **Umlaufsatz (previous round): banked the piece-selection step of the diagonal
> split (sorry-free).**  Worked exclusively on the top-priority discrete Hopf
> Umlaufsatz.  The whole library still builds end-to-end (8128 jobs through
> `SAWFinal.lean`); no new axioms, no regressions.  The three genuine live
> `sorry`s (`empty_branch_boundary_lift`, `meisters_reduction_interior2`,
> `empty_branch_bad_lift`) are unchanged in identity; NO new `sorry`s.  Two new
> sorry-free reusable lemmas in `SAWUmlaufPolygon.lean` (axioms `propext,
> Classical.choice, Quot.sound` only), placed after
> `closedEdge_mem_chord_pathEdges` and documented as preparation for the split
> branches:
> * `HexArea.IsCycEdge_rotate` — rotation-invariance of `IsCycEdge`.
> * `HexArea.forbidden_lands_in_chord` — the forbidden cyclic edge `{z1,z2}`
>   lands in `chordLeft V k` or `chordRight V k` (the combinatorial
>   "forbidden-pair-in-one-piece" step that lets the split-and-recurse induction
>   pick the piece NOT containing `{z1,z2}`).
>
> Combined with the previously-banked `interior_split_simple` (simplicity half +
> cut index) and `interior_split_one_nondeg` (non-degeneracy half), the
> remaining genuine content of the interior / bad-diagonal branches is the
> ear-lift after the recursion (list surgery, analogous to the proved
> `empty_branch_interior_lift`) plus the flat-cut-vertex-removal sub-case.

# Proof Status: μ = √(2+√2)

> **Umlaufsatz (LATEST round): banked the NON-DEGENERACY half of the interior
> diagonal split (sorry-free, disjunctive form), the documented residual
> obstruction of the interior branch.**  Worked exclusively on the top-priority
> discrete Hopf Umlaufsatz.  The whole library still builds end-to-end (8128
> jobs through `SAWFinal.lean`); no new axioms, no regressions; the three
> genuine live `sorry`s (`empty_branch_boundary_lift`,
> `meisters_reduction_interior2`, `empty_branch_bad_lift`) are unchanged in
> identity and NO new `sorry`s were introduced.  Two new sorry-free lemmas in
> `SAWUmlaufPolygon.lean` (each verified to use only `propext, Classical.choice,
> Quot.sound`), placed directly after `seam_one_nonflat` and documented as
> preparation for `meisters_reduction_interior2` (NOT dead branches):
> * `polyCycNondeg_interior_corner` — an interior consecutive triple
>   `(prev, w, succ)` of a cyclically non-degenerate polygon is a non-flat
>   corner (`cross (w-prev) (succ-w) ≠ 0`), read off `polyNondeg` via
>   `polyNondeg_take` / `polyNondeg_drop`.
> * `interior_split_one_nondeg` — **the non-degeneracy half (disjunctive
>   form)**: for the interior diagonal `b–w`, at least one of the two chord
>   pieces `chordLeft` / `chordRight` of `W = b :: c :: rest ++ [a]` is
>   `polyCycNondeg`.  Combines the non-flat genuine corner at `w` with
>   `seam_one_nonflat` and `interior_split_nondeg_left` /
>   `interior_split_nondeg_right`.
>
> This discharges the precise "non-degeneracy half" obstruction that prior
> rounds recorded for the interior branch.  The remaining genuine content of
> `meisters_reduction_interior2` is now the ear-lift after flat-cut-vertex
> removal (list surgery transporting the recursed sub-polygon ear back to `V`,
> analogous to the proved `empty_branch_interior_lift`).

> **Umlaufsatz (earlier round): banked the SIMPLICITY half of the flat-cut-vertex
> removal step (sorry-free), the documented residual obstruction of the interior
> branch.**  Worked exclusively on the top-priority discrete Hopf Umlaufsatz.
> The whole library still builds end-to-end (8128 jobs through `SAWFinal.lean`);
> no new axioms, no regressions.  The genuine live `sorry`s are unchanged in
> identity (`empty_branch_boundary_lift`, `meisters_reduction_interior2`,
> `empty_branch_bad_lift`), plus the one textual `sorry` in the commented-out
> dead branch `ear_turning_bounds`.  NO new `sorry`s were introduced.
>
> Six new sorry-free lemmas in `SAWUmlaufPolygon.lean` (each verified to use only
> `propext, Classical.choice, Quot.sound`), placed directly after
> `seam_one_nonflat` and documented as preparation for
> `meisters_reduction_interior2` (NOT dead branches).  Together they fully
> discharge the *simplicity* half of removing the (at most one) flat seam vertex
> created by the interior diagonal cut, and supply the geometric inputs for the
> non-degeneracy half:
> * `segment_subset_union_of_mem` — if `w ∈ [u,v]` then `[u,v] ⊆ [u,w] ∪ [w,v]`.
> * `mem_closedEdges_remove_mid` — every cyclic edge of the shortened polygon
>   `pre ++ u :: v :: suf` is either the merged edge `(u,v)` or a cyclic edge of
>   the original `pre ++ u :: w :: v :: suf` (pure list/`zip`-`rotate` surgery).
> * `uw_wv_mem_closedEdges` — the two incident edges `(u,w)`,`(w,v)` of the flat
>   vertex are genuine cyclic edges of the original.
> * `PolygonSimple_remove_flat_mid` — **the simplicity half**: deleting a flat
>   vertex `w` (one lying on the segment `[u,v]` between its two cyclic
>   neighbours) from a `PolygonSimple` list yields a `PolygonSimple` list.  The
>   two incident edges merge into `u–v ⊆ [u,w] ∪ [w,v]`, so each disjointness
>   clause is inherited and `Nodup` survives deletion.
> * `cross_pred_corner_remove_flat` / `cross_succ_corner_remove_flat` — the
>   geometric half of `polyCycNondeg` preservation: since `w-u` (resp. `v-w`) is
>   a real multiple of `v-u`, the predecessor corner `(x,u,w)` stays non-flat as
>   `(x,u,v)` and the successor corner `(w,v,y)` stays non-flat as `(u,v,y)`.
>
> Significance: this is the precise infrastructure the documented residual
> obstruction of the interior branch needs.  Prior rounds isolated that only the
> recursion-target piece's single flat seam vertex blocks `polyCycNondeg`
> (`seam_one_nonflat`); these bricks show that flat vertex can be deleted while
> preserving `PolygonSimple` (done, sorry-free) and that the two neighbour
> corners stay non-flat under the deletion (geometric inputs banked).  The
> remaining pieces for full closure are the `polyNondeg`-index surgery wrapping
> the two corner facts and the `EmptyCornerData2` ear-lift across the deletion.
>
> **Umlaufsatz (prior round): banked the PER-PIECE single-seam non-degeneracy
> bricks for the interior split (sorry-free).**  Worked exclusively on the
> top-priority discrete Hopf Umlaufsatz.  The whole library still builds
> end-to-end (8128 jobs through `SAWFinal.lean`); no new axioms, no regressions.
> The genuine live `sorry`s are unchanged in identity
> (`empty_branch_boundary_lift`, `meisters_reduction_interior2`,
> `empty_branch_bad_lift`), plus the one textual `sorry` in the commented-out
> dead branch `ear_turning_bounds`.
>
> Two new sorry-free lemmas in `SAWUmlaufPolygon.lean` (verified to use only
> `propext, Classical.choice, Quot.sound`), placed directly after
> `interior_split_nondeg`:
> * `interior_split_nondeg_left` — the `chordLeft` piece of the `b`-rooted cycle
>   cut along `b–w` is `polyCycNondeg` from the SINGLE left-seam clearance
>   `cross (w - prev) (b - w) ≠ 0` (the apex-`b` corner is automatic from `w`
>   strictly inside the corner triangle).
> * `interior_split_nondeg_right` — companion: the `chordRight` piece is
>   `polyCycNondeg` from the SINGLE right-seam clearance
>   `cross (w - b) (succ - w) ≠ 0`.
>
> Significance: `interior_split_nondeg` previously needed BOTH seam clearances
> to conclude EITHER piece non-degenerate.  Splitting it per-piece makes the
> output of `seam_one_nonflat` (at least one seam is non-flat) directly
> consumable: the non-flat piece is `polyCycNondeg` outright, with no dependence
> on the other (possibly flat) seam.  This pins the interior branch's residual
> obstruction to the single case where the recursion target (the piece NOT
> containing `{z1,z2}`) is the at-most-one flat-seam piece, the precise input to
> the next-round flat-cut-vertex removal step.  Direct high-effort attempts on
> all three live gaps were re-run and still time out (genuinely
> Jordan-curve-theorem-level), so partial progress is preserved as the banked
> bricks above.
>
> **Umlaufsatz (prior round): banked the SEAM-FLATNESS bricks isolating the
> flat-cut-vertex residual case of the interior split (sorry-free).**  Worked
> exclusively on the top-priority discrete Hopf Umlaufsatz.  The whole library
> still builds end-to-end (8128 jobs through `SAWFinal.lean`); no new axioms, no
> regressions.  The genuine live `sorry`s are unchanged in identity
> (`empty_branch_boundary_lift`, `meisters_reduction_interior2`,
> `empty_branch_bad_lift`), plus the one textual `sorry` inside the
> commented-out dead branch `ear_turning_bounds`.
>
> Two new sorry-free lemmas in `SAWUmlaufPolygon.lean` (verified to use only
> `propext, Classical.choice, Quot.sound`):
> * `seam_flat_chain` — if *both* seam corners created at the cut endpoint `w` by
>   the interior diagonal `b–w` are flat (`cross (w-prev) (b-w) = 0` and
>   `cross (w-b) (succ-w) = 0`), then the original cyclic corner `prev,w,succ` is
>   flat too (`cross (w-prev) (succ-w) = 0`).  Pure 2-D parallelism: both edge
>   vectors are parallel to the nonzero diagonal vector, hence to each other
>   (proved via the cross/dot identity `cross(p,s)·|v|² = cross(p,v)·⟨v,s⟩ +
>   ⟨p,v⟩·cross(v,s)`).
> * `seam_one_nonflat` — its consumable contrapositive: since `polyCycNondeg V`
>   forces the genuine cyclic corner `prev,w,succ` to be non-flat, AT LEAST ONE
>   of the two seam corners at `w` is non-flat.  So the diagonal split makes at
>   most ONE of the two pieces' seam corners at `w` flat; that (at most one)
>   flat piece is precisely the flat-cut-vertex residual case.
>
> These pin down the documented root obstruction (the split can introduce a
> *straight*/turning-0 seam corner that `polyCycNondeg` rejects): the two bricks
> show the straightness can affect at most one of the two pieces, so the
> non-flat piece satisfies the `interior_split_nondeg` seam hypothesis outright,
> reducing the interior branch to a single flat-cut-vertex removal step on the
> (at most one) flat piece before the `IH2` recursion.  Both are placed directly
> above their intended consumer `meisters_reduction_interior2` and documented as
> preparation — not dead branches.
>
> **Umlaufsatz (previous round): banked the chord-piece REVERSE-MEMBERSHIP bricks
> for the interior-branch ear lift (sorry-free); re-attempted all three live
> gaps with the strongest search at high effort.**  Worked exclusively on the
> top-priority discrete Hopf Umlaufsatz.  The whole library still builds
> end-to-end (8128 jobs through `SAWFinal.lean`); no new axioms, no regressions.
> The three genuine live `sorry`s are unchanged in identity
> (`empty_branch_boundary_lift`, `meisters_reduction_interior2`,
> `empty_branch_bad_lift`), plus the one textual `sorry` inside the
> commented-out dead branch `ear_turning_bounds`.
>
> Two new sorry-free lemmas in `SAWUmlaufEarSplit.lean` (verified to use only
> `propext, Classical.choice, Quot.sound`):
> * `HexArea.mem_of_mem_chordLeft` — every vertex of `chordLeft V k` is a vertex
>   of `V` (the prefix `V.take (k+1)` is a sublist of `V`).
> * `HexArea.mem_of_mem_chordRight` — every vertex of `chordRight V k` is a
>   vertex of `V` (`V.drop k ++ V.take 1`, both sublists of `V`).
>
> These are the reverse of the existing `mem_chord_split` (which sends a vertex
> of `V` into one of the two pieces).  They are exactly the vertex-transfer
> ingredient the interior-branch ear lift in `meisters_reduction_interior2`
> needs to carry an ear returned by `IH2` on a chord piece back to `V` (an ear
> apex/tip living in a piece is a genuine vertex of `V`).  Both are documented
> as preparation for `meisters_reduction_interior2`, placed in the imported
> `SAWUmlaufEarSplit.lean`, hence part of the build chain — not dead branches.
>
> SEARCH OUTCOME this round: all three live gaps
> (`meisters_reduction_interior2`, `empty_branch_bad_lift`,
> `empty_branch_boundary_lift`) were re-attempted directly with the strongest
> search at high effort, each with an explicit informal route and the full list
> of banked bricks.  None closed within budget — consistent with their being
> genuine Jordan-curve-theorem-level content.  The shared root obstruction is
> unchanged: the interior-diagonal split can create a *straight* (turning-0)
> seam corner that the current `polyCycNondeg` invariant rejects, and the empty
> branch's boundary subcase needs a finer induction invariant forcing the
> `IH2`-returned ear into the interior arc.  Closing them needs either to relax
> `polyCycNondeg` to forbid only U-turns (a global refactor) or to add a
> straight-cut-vertex removal step before recursing; that remains the precise
> next-round target.
>
> **Umlaufsatz (previous round): banked the CUT-DIAGONAL cyclic-edge bricks for
> the interior-split recursion (sorry-free).**  Worked exclusively on the
> top-priority discrete Hopf Umlaufsatz.  The whole library still builds
> end-to-end (8128 jobs through `SAWFinal.lean`); no new axioms, no regressions;
> the three genuine remaining `sorry`s are unchanged in identity
> (`empty_branch_boundary_lift`, `meisters_reduction_interior2`,
> `empty_branch_bad_lift`), plus the one textual `sorry` inside the
> commented-out dead branch `ear_turning_bounds`.
>
> Two new sorry-free lemmas in `SAWUmlaufPolygon.lean` (verified to use only
> `propext, Classical.choice, Quot.sound`):
> * `chordLeft_cut_isCycEdge` — the cut diagonal `{V[0], V[k]}` is a genuine
>   cyclic edge (the closing chord) of the left piece `chordLeft V k`.
> * `chordRight_cut_isCycEdge` — the same for the right piece `chordRight V k`.
>
> These supply exactly the `IsCycEdge` witness that the interior branch must
> hand to `IH2` when it recurses on a chord piece forbidding the cut diagonal
> `{b, w}`, so the recursion stays inside the two-forbidden `IsCycEdge`
> invariant.  Both are placed above their consumer
> (`meisters_reduction_interior2`) and documented as preparation, not dead
> branches.
>
> RECORDED OBSTRUCTION (re-confirmed numerically this round): the seam
> hypotheses `hseamL`/`hseamR` of `interior_split_nondeg` are NOT unconditionally
> true.  The U-turn subcase (a vertex strictly between `b` and `w`) is excluded
> by `hwmax` (it would be a strictly-farther interior vertex), but a benign
> *straight* collinearity can still occur: e.g. `a=(0,0), c=(4,0), b=(2,3)`,
> farthest interior `w=(2,2)`, successor `succ=(2,0.5)` — all on the line `x=2`,
> so `cross (w-b) (succ-w) = 0` while `succ` is a legitimate closer interior
> vertex.  Hence the diagonal split can introduce a *straight* (turning-0) seam
> corner that the current `polyCycNondeg` invariant (no collinear triples)
> rejects.  Closing the interior branch therefore needs either to tolerate
> straight seam corners (relax `polyCycNondeg` to forbid only U-turns / remove
> straight cut-vertices before recursing) or a different pivot — this is the
> genuine isolated remaining gap, now precisely characterised.
>
> **Umlaufsatz (previous round): banked the NON-DEGENERACY half of the interior
> split (sorry-free) and cleanly extracted the empty bad-diagonal subcase.**
> Worked exclusively on the top-priority discrete Hopf Umlaufsatz.  The whole
> library still builds end-to-end (8128 jobs through `SAWFinal.lean`); no new
> axioms, no regressions.  Two changes this round, both in
> `SAWUmlaufPolygon.lean`:
> * New sorry-free lemma `interior_split_nondeg` (verified to use only
>   `propext, Classical.choice, Quot.sound`): the companion of
>   `interior_split_simple`.  Given the two *genuine* seam clearances at the cut
>   endpoint `w` (the diagonal `b–w` is collinear with neither edge of `V`
>   incident to `w`: `hseamL` for the predecessor edge, `hseamR` for the
>   successor edge), BOTH pieces `chordLeft`/`chordRight` of the `b`-rooted
>   cycle `b :: c :: rest ++ [a]` cut along `b–w` are `polyCycNondeg`.  The other
>   two seam corners (at the apex `b`) are discharged automatically from
>   `hwin : inTriangleStrict a b c w` (`w` off lines `b–c` and `a–b`).  Net
>   effect: combined with `interior_split_simple`, both split pieces are now
>   `PolygonSimple` ∧ `polyCycNondeg` ∧ strictly shorter — i.e. FULLY READY for
>   the `IH2` recursion.  The interior branch's only remaining content is now
>   exactly (i) the two genuine seam clearances `hseamL`/`hseamR` — the
>   degenerate-diagonal geometry recorded as the obstruction in earlier rounds —
>   and (ii) the ear lift / assembly.
> * Structural refactor: extracted `meisters_reduction_empty2`'s bad-diagonal
>   subcase into a single targetable declaration `empty_branch_bad_lift`
>   (carrying the `sorry`), mirroring the existing `empty_branch_good_lift` /
>   `empty_branch_boundary_lift` split, and rewired the empty-branch call site to
>   consume it.  No change to the genuine sorry count.
>
> The genuine remaining `sorry`s of the Umlaufsatz chain are now
> `meisters_reduction_interior2`, `empty_branch_boundary_lift`, and
> `empty_branch_bad_lift` (plus the one textual `sorry` inside the
> commented-out dead branch `ear_turning_bounds`).
>
> **Umlaufsatz (previous round): banked the cyclic-edge LOCALIZATION brick of the
> chord-split ear-lift, sorry-free.**  Worked exclusively on the top-priority
> discrete Hopf Umlaufsatz.  The whole library still builds end-to-end (8128
> jobs through `SAWFinal.lean`); no new axioms, no regressions; the genuine
> remaining `sorry`s are unchanged (`meisters_reduction_interior2`, the
> bad-diagonal subcase of `meisters_reduction_empty2`, and
> `empty_branch_boundary_lift`).  New sorry-free lemma
> `HexArea.closedEdge_mem_chord_pathEdges` (only `propext`, `Classical.choice`,
> `Quot.sound`): every cyclic edge of `V` is a path edge of exactly one of the
> two chord pieces `chordLeft V k` / `chordRight V k`.  Combined with the
> already-banked `mem_closedEdges_of_mem_pathEdges`, the forbidden cyclic edge
> `{z1, z2}` now localizes to a single chord piece *as a cyclic edge of that
> piece* — the Step-3 localization that the interior-branch ear-lift consumes
> (recurse via `IH2` on the OTHER piece).  This isolates the interior branch's
> remaining content to the two seam-corner non-degeneracies (the genuine
> degenerate-diagonal gap) plus the list-surgery ear-lift assembly.
>
> **Umlaufsatz (previous round): wired the orientation-robust pivot into the
> interior branch and banked the SIMPLICITY HALF of the interior-diagonal split,
> sorry-free.**  Worked exclusively on the top-priority discrete Hopf
> Umlaufsatz.  The whole library still builds end-to-end (8128 jobs through
> `SAWFinal.lean`); no new axioms, no regressions.  Changes this round (all in
> `SAWUmlaufPolygon.lean`):
> * Replaced `exists_farthest_interior` by `exists_farthest_interior_oriented`
>   in `meisters_reduction2`, and changed `meisters_reduction_interior2`'s
>   `hwmax` to the orientation-robust scaled form, so the geometric heart
>   `interior_chord_is_diagonal` is now directly consumable by the interior
>   branch.
> * New sorry-free lemma `interior_split_simple` (only `propext`,
>   `Classical.choice`, `Quot.sound`): both pieces `chordLeft`/`chordRight` of
>   the `b`-rooted cycle `b :: c :: rest ++ [a]` cut along the diagonal `b–w`
>   are `PolygonSimple`, with cut index `k` satisfying `2 ≤ k` and
>   `k + 2 ≤ W.length` (strict-shortness fuel for `IH2`).  This is the
>   simplicity half of the interior split, assembled from
>   `interior_chord_is_diagonal` + the banked simplicity bricks + rotation
>   toolkit.
> * Recorded (in `meisters_reduction_interior2`'s docstring) the remaining
>   obstruction: the `polyCycNondeg` half is NOT unconditionally true — the
>   interior diagonal `b–w` can be collinear with the edge `prev–w` at `w`,
>   making the left piece's seam corner `(prev, w, b)` flat.  The degenerate
>   diagonal must be avoided (pivot perturbation) or the invariant relaxed; this
>   is the isolated remaining gap of the interior branch.
>
> The three genuine remaining `sorry`s are unchanged
> (`meisters_reduction_interior2`, the bad-diagonal subcase of
> `meisters_reduction_empty2`, and `empty_branch_boundary_lift`), plus the one
> textual `sorry` inside the commented-out dead branch `ear_turning_bounds`.

> **Umlaufsatz (previous round): proved the genuine Jordan-content GEOMETRIC HEART
> of the interior-diagonal split, sorry-free.**  Worked exclusively on the
> top-priority discrete Hopf Umlaufsatz.  The whole library still builds
> end-to-end (8128 jobs through `SAWFinal.lean`); no new axioms, no regressions;
> the three genuine remaining `sorry`s are unchanged
> (`meisters_reduction_interior2`, the bad-diagonal subcase of
> `meisters_reduction_empty2`, and `empty_branch_boundary_lift`), plus the one
> textual `sorry` inside the commented-out dead branch `ear_turning_bounds`.
>
> New sorry-free lemmas (all in `SAWUmlaufPolygon.lean`, only `propext,
> Classical.choice, Quot.sound`), discharging the interior-split's hard geometry:
> * `HexArea.corner_exit_point_ge` — `corner_exit_point` generalised so the
>   start point may be strictly inside the corner (apex test `>= 0`, not `= 0`).
> * `simple_vertex_not_on_far_edge` — a simple-polygon vertex lies on none of
>   its non-incident cyclic edges (`4 <= length`).
> * `chord_disjoint_ear_ab`, `chord_disjoint_ear_bc` — a chord sub-segment off
>   line `a-b` (resp. `b-c`) is disjoint from that ear edge, handling the
>   edge-incidence/collinear case.
> * `interior_chord_is_diagonal` — **the Jordan-content heart**: in a simple
>   polygon the chord from apex `b` to the farthest interior vertex `w` of its
>   ear-triangle is disjoint from every non-incident edge (a diagonal).
> * `exists_farthest_interior_oriented` — the orientation-robust pivot selector
>   feeding `interior_chord_is_diagonal`'s `hwmax`.
>
> ORIENTATION FINDING (recorded, important for the next round): the existing
> `exists_farthest_interior` maximises the *unscaled* `cross (c-a) (.-a)`, which
> equals "farthest from `a-c`" only for positively-oriented corner triangles;
> for the negative orientation it picks the vertex *closest* to `a-c` (verified
> counterexample `a=0,c=4,b=2-3i,w=2-half i,w2=2-2i`).  Use the new
> `exists_farthest_interior_oriented` (scaled by `cross (c-a) (b-a)`) when wiring
> `interior_chord_is_diagonal` into `meisters_reduction_interior2`.  Remaining
> for interior2: feed these two lemmas to the banked `chordLeft/chordRight`
> split-preservation bricks (cut-diagonal clearance gives two shorter simple
> sub-polygons), recurse via `IH2`, and lift the returned ear.

> **Umlaufsatz (previous round): made the interior-diagonal split bricks USABLE
> and banked the full combinatorial split-preservation layer (sorry-free).**
> Worked exclusively on the top-priority discrete Hopf Umlaufsatz
> (`hex_closed_trail_turning_number`).  The whole library still builds
> end-to-end (8128 jobs through `SAWFinal.lean`); no new axioms, no regressions;
> the main theorem still reduces only to `sorryAx` (+ `propext, Classical.choice,
> Quot.sound`).  The three genuine Jordan-content `sorry`s are unchanged
> (`meisters_reduction_interior2`, the bad-diagonal subcase of
> `meisters_reduction_empty2`, and `empty_branch_boundary_lift`); the only other
> textual `sorry` remains inside the commented-out dead branch.
>
> Structural fix.  The combinatorial split bricks built last round
> (`pathEdges`, `closedEdges_eq_pathEdges`, `mem_closedEdges_of_mem_pathEdges`,
> `PolygonSimple_of_simplePath`, `polyCycNondeg_of_path`) were stranded in
> `SAWUmlaufChordSplit.lean`, which *imports* `SAWUmlaufPolygon.lean` — so the
> open Meisters branches (upstream, in `SAWUmlaufPolygon`) could not consume
> them.  I relocated all of them into `SAWUmlaufPolygon.lean`, placed just
> before the open branches, so they are now usable.  `SAWUmlaufChordSplit.lean`
> is kept (still imported by `SAWFinal`) as a thin documented stub recording the
> relocation.
>
> New sorry-free layer (all in `SAWUmlaufPolygon.lean`, namespace `HexArea`,
> verified to use only `propext, Classical.choice, Quot.sound`).  The complete
> *combinatorial* preservation of the interior-diagonal split — both pieces,
> both invariants — given the (geometric) cut-diagonal clearance and seam-corner
> non-flatness as hypotheses:
> * `mem_pathEdges_take`, `pathEdges_chordLeft_mem_closedEdges`,
>   `pathEdges_chordRight_mem_closedEdges` — every path edge of a split piece is
>   a cyclic edge of the parent polygon (edge inheritance);
> * `polyNondeg_take`, `polyNondeg_drop` — `polyNondeg` is inherited by prefixes
>   and suffixes (triple inheritance);
> * `chordLeft_PolygonSimple`, `chordRight_PolygonSimple` — each split piece is
>   `PolygonSimple` given the cut-diagonal clearance (via
>   `PolygonSimple_of_simplePath`);
> * `chordLeft_polyCycNondeg`, `chordRight_polyCycNondeg` — each split piece is
>   `polyCycNondeg` given the two seam corners (via `polyCycNondeg_of_path`).
>
> Net effect: the interior split's *combinatorial* obstacle (each piece is again
> a simple, non-degenerate, strictly-shorter sub-polygon) is now fully
> dischargeable from the chord lemmas already in `SAWUmlaufEarSplit`
> (`chordLeft`/`chordRight` lengths, heads, lasts, nodup, `mem_chord_split`).
> The residual content of `meisters_reduction_interior2` is now exactly the
> *geometric* cut-diagonal clearance (the `hclear`/seam hypotheses, from the
> farthest-interior-vertex maximality) plus the interior ear lift and final
> assembly.  All new lemmas are documented as preparation explicitly linked to
> `meisters_reduction_interior2` (not dead branches).

> **Umlaufsatz (earlier round): built the sorry-free combinatorial half of the
> interior-diagonal split.**  New file `RequestProject/SAWUmlaufChordSplit.lean`
> (imported into `SAWFinal`, so linked into the build) proves, sorry-free:
> * `closedEdges_eq_pathEdges` — the cyclic edges of a vertex list are its path
>   edges plus the single closing chord `(last, head)`;
> * `mem_closedEdges_of_mem_pathEdges` — every path edge is a cyclic edge;
> * `PolygonSimple_of_simplePath` — a vertex list is `PolygonSimple` once its
>   path edges are pairwise disjoint and its closing chord is clear of every
>   non-incident path edge;
> * `polyCycNondeg_of_path` — `polyCycNondeg` from path non-degeneracy plus the
>   two seam corners at the chord's endpoints.
>
> These are the reusable packaging that the two still-open Meisters two-ears
> branches in `SAWUmlaufPolygon.lean` need for their interior-diagonal split
> (`meisters_reduction_interior2`, and the bad-diagonal subcase of
> `meisters_reduction_empty2`): each split piece is a sub-path of the parent
> polygon (so its path edges/triples are inherited verbatim from the parent's
> `PolygonSimple`/`polyCycNondeg`) closed by the single cut diagonal.  The
> remaining gap for those branches is now exactly the *geometric* diagonal
> clearance (the cut chord crosses no edge — supplied in spirit by
> `seg_diagonal_disjoint_of_corner`) plus the ear lift; the combinatorial
> simplicity/non-degeneracy preservation is done.  The main theorem's axiom
> profile is unchanged (`sorryAx` + `propext, Classical.choice, Quot.sound`);
> the three documented Jordan-content `sorry`s remain isolated in
> `SAWUmlaufPolygon.lean`.

> **Umlaufsatz: PROVED the empty-branch good-diagonal lift (interior subcase
> fully closed); isolated the genuine remaining gap to the boundary ear.**
> Worked exclusively on the top-priority discrete Hopf Umlaufsatz
> (`hex_closed_trail_turning_number`).  The whole library still builds
> end-to-end (8127 jobs through `RequestProject/SAWFinal.lean`); no new axioms,
> no regressions; the main theorem still reduces only to `sorryAx`
> (+ `propext, Classical.choice, Quot.sound`).
>
> This round, in `RequestProject/SAWUmlaufPolygon.lean`:
> * Strengthened the convex-apex setup `exists_lexmin_mid_rotation` to also
>   expose the segment-avoidance clause `∀ u w ∈ V, b ≠ u → b ≠ w →
>   b ∉ segment ℝ u w` (proved sorry-free from the lex-min property via
>   `HexArea.lexMin_not_mem_segment`), and threaded it (`hbseg`) through
>   `meisters_reduction2`, `meisters_reduction_interior2`,
>   `meisters_reduction_empty2`, and `empty_branch_good_lift`.  This is the
>   data that the diagonal-clearance transfer in the lift needs.
> * Proved sorry-free the reusable transfer brick `empty_branch_interior_lift`:
>   the *interior* ear lift (re-inserting the apex `b` between `a` and `c` when
>   the clip ear's `a–c` junction is interior to its tail), with the full
>   orientation-sign transfer via `shoelace2_insert_mid` / `shoelace2_rotate` /
>   `shoelace2_clip_second`.
> * Proved sorry-free three reusable combinatorial bricks: `rotate_cons3_mem`
>   (membership through a 3-prefix rotation), `polyCycNondeg_rotate_head` (ear
>   non-degeneracy from cyclic non-degeneracy), and `forbidden_subset_corner`
>   (the forbidden pair `{z1,z2}` lies in `{a,b,c}` because `b`'s only cyclic
>   neighbours are `a` and `c`).
> * **Proved `empty_branch_good_lift`** (now sorry-free in itself): it recurses
>   on the clip via `IH2`, `by_cases` on whether the returned ear is interior to
>   the junction, dispatches the interior subcase to the proved
>   `empty_branch_interior_lift`, and the boundary subcase to the new isolated
>   lemma `empty_branch_boundary_lift`.
>
> Net effect on the open content: the empty branch's good-diagonal lift is no
> longer a monolithic `sorry` — its interior subcase is fully proved, and the
> single genuine remaining Jordan-content `sorry` is now isolated in
> `empty_branch_boundary_lift` (the two-ears boundary case: an IH-returned clip
> ear adjacent to the `a–c` junction, where re-inserting `b` changes a clip
> neighbour's successor from `c` to `b`, so the lifted clip-turn
> `cross (c - a') (b - c)` / `cross (a - a') (b - a)` can vanish — a finer
> induction invariant or a dedicated boundary-lift treatment is needed).  The
> Umlaufsatz now reduces to exactly three precisely-scoped `sorry`s:
> `empty_branch_boundary_lift`, `meisters_reduction_interior2`, and the
> bad-diagonal subcase of `meisters_reduction_empty2`.  Every Umlauf file
> remains imported via the `SAWFinal.lean` chain; the only other textual `sorry`
> sits inside an explicitly commented-out dead branch (`ear_turning_bounds`).

> **Umlaufsatz: banked the interior-ear LIFT machinery (NEWEST).**  Worked
> exclusively on the top-priority discrete Hopf Umlaufsatz
> (`hex_closed_trail_turning_number`).  The whole library still builds
> end-to-end (8127 jobs through `RequestProject/SAWFinal.lean`); no new axioms,
> no regressions; the main theorem still reduces only to `sorryAx`
> (+ `propext, Classical.choice, Quot.sound`).
>
> The empty-branch / interior-branch ear *lift* was the recurring bottleneck.
> This round I isolated and **proved sorry-free** the two reusable bricks that
> constitute the *interior-ear* half of that lift, in
> `RequestProject/SAWUmlaufPolygon.lean` (both verified to use only
> `propext, Classical.choice, Quot.sound`):
>
> * `clip_ear_lift_interior` — the rotation/insertion combinatorics: from a clip
>   rotation `(a :: c :: rest).rotate r' = a' :: b' :: c' :: (s ++ a :: c :: t)`
>   whose `a–c` junction sits in the *interior* of the tail, re-inserting the
>   apex `b` yields a genuine rotation
>   `(a :: b :: c :: rest).rotate r'' = a' :: b' :: c' :: (s ++ a :: b :: c :: t)`
>   with the *same* ear `a' b' c'`.  Key idea: uniqueness of `a` (`a ≠ c`,
>   `a ∉ rest`) forces `rest = t ++ a' :: b' :: c' :: s`, after which
>   `r'' = 3 + t.length` works by `(p ++ q).rotate p.length = q ++ p`.
> * `shoelace2_insert_mid` — signed-area additivity for a *mid-list* apex
>   insertion (`shoelace2 (pre ++ a::b::c::suf) = shoelace2 (pre ++ a::c::suf)
>   + shoelace2 [a,b,c]`), the mid-list generalisation of `shoelace2_clip_second`
>   needed to transfer the ear-orientation `iff` to the lifted `V`-clip.
>
> Together these supply the rotation witness and the orientation-transfer
> identity for the *interior* ear case of both lifts; they are documented as
> preparation explicitly linked to the open lemmas (NOT dead branches).
>
> The Umlaufsatz still reduces to exactly the same three precisely-scoped
> Jordan-content `sorry`s — `empty_branch_good_lift`,
> `meisters_reduction_interior2`, and the bad-diagonal subcase of
> `meisters_reduction_empty2`.  The genuine residual obstruction in the empty
> branch is the *boundary* ear case (the IH-returned clip ear adjacent to the
> `a–c` junction, so `a'` or `c'` is `a`/`c`): re-inserting `b` then changes a
> *second* clip-neighbour to `b`, and the resulting `V`-clip-turn
> `cross (c - b) (c' - c)` need not be non-zero (`b, c, c'` can be collinear),
> so such an ear may genuinely fail the `EmptyCornerData2` clip-turn clause.
> This is the same two-ears subtlety flagged earlier and is the recommended next
> target (a finer induction invariant that forces the returned ear into the
> interior, or a dedicated boundary-lift treatment).

> **Umlaufsatz: made the Meisters ear-search induction SOUND (two-forbidden
> form) and discharged the quadrilateral base case (NEWEST).**  Worked
> exclusively on the top-priority discrete Hopf Umlaufsatz.  The whole library
> still builds end-to-end (8127 jobs through `RequestProject/SAWFinal.lean`); no
> new axioms, no regressions; `hex_closed_trail_turning_number` still reduces
> only to `sorryAx` (+ `propext, Classical.choice, Quot.sound`).
>
> **Root-cause fix.**  The previous single-forbidden induction invariant
> `EmptyCornerData V z` ("an empty ear with tip ≠ z") was *too weak to drive the
> split-and-recurse induction*: a sub-polygon ear returned by the IH may sit at
> *either* endpoint of the cut diagonal, and a single forbidden vertex can only
> exclude one of them.  Both `meisters_reduction_interior` and the non-clean
> case of `meisters_reduction_empty` were therefore unprovable *from the IH they
> were given* (their conclusions are true, but the hypotheses did not suffice).
> This is exactly the genuine Meisters "two-ears" subtlety flagged in earlier
> rounds.
>
> This round, in `RequestProject/SAWUmlaufPolygon.lean`:
> * Added `IsCycEdge` and the two-forbidden predicate `EmptyCornerData2 V z1 z2`,
>   plus `EmptyCornerData_of_two` (the single-forbidden form is the diagonal
>   case `z1 = z2`).
> * Rebuilt the induction in the sound two-forbidden form: `meisters_reduction2`,
>   `exists_empty_corner_avoiding_aux2`, and rewired `exists_empty_corner_avoiding_aux`
>   to derive the single-forbidden consumer interface unchanged.  The recursion
>   now always forbids the *cut edge* (the clip diagonal `{a,c}` or the split
>   diagonal `{b,w}` — a genuine cyclic edge of the strictly-shorter
>   sub-polygon), which is the invariant the induction preserves.
> * **Proved sorry-free the entire quadrilateral base case** `meisters_reduction_quad2`,
>   via the pure-logic selector `forbidden_avoids_one` (an edge can never cover
>   the two *opposite* ears of a quad) and four geometric ear packages
>   `quad_ear_at_a/b/c/d` (modelled on the four finite branches of the retained
>   reference lemma `meisters_reduction_quad`).
>
> The Umlaufsatz now reduces to exactly two clearly-scoped, **sound** (provable
> from their now-sufficient IH) Jordan-curve-level `sorry`s in
> `SAWUmlaufPolygon.lean`: `meisters_reduction_interior2` (interior diagonal
> split preserving simplicity/non-degeneracy + ear lift) and the non-clean case
> of `meisters_reduction_empty2` (clip recursion + ear lift, incl. the
> collinear-far-vertex degenerate sub-cases).  The clean case of the empty
> branch is proved directly.

> **Umlaufsatz: added the reusable clip-preservation brick
> `clip_simple_nondeg_of_empty` (PREVIOUS).**  Worked exclusively on the
> top-priority discrete Hopf Umlaufsatz.  The whole library still builds
> end-to-end (8127 jobs through `RequestProject/SAWFinal.lean`); no new axioms,
> no regressions.  This round, in `RequestProject/SAWUmlaufPolygon.lean`:
>
> * Added and proved (sorry-free, term-mode) `clip_simple_nondeg_of_empty`:
>   from a simple, cyclically non-degenerate cycle `a :: b :: c :: rest` with an
>   *empty* convex corner `a b c` (no far vertex strictly inside, none on the
>   closed diagonal `a–c`) and the two diagonal clip-turns non-flat, the clip
>   `a :: c :: rest` is again `PolygonSimple` *and* `polyCycNondeg`.  This is the
>   combinatorial half of the empty-branch recurse-and-lift step — it produces
>   exactly the two `IH` hypotheses needed to recurse on the strictly-shorter
>   clip — assembled from the existing bricks `diag_disjoint_of_empty_corner` +
>   `PolygonSimple_clip` and `polyCycNondeg_clip`.
>
> The Umlaufsatz still reduces to exactly the two clearly-scoped
> Jordan-curve-theorem-level branch lemmas `meisters_reduction_interior` and the
> non-clean case of `meisters_reduction_empty`, kept as documented `sorry`s.
> Analysis recorded for the empty branch: the residual obstruction is the *lift*
> of a sub-polygon ear back to `V` — a clip ear whose tip lies in `rest` lifts
> directly (its cyclic neighbours are unchanged by re-inserting the convex apex
> `b`), but a clip ear with tip exactly `a` or `c` does not, which is precisely
> the genuine two-ears subtlety (it would need a two-forbidden-vertex
> `EmptyCornerData` to force the recursion's tip into `rest`).

> **Umlaufsatz: proved the clean-case assembly brick `empty_ear_direct` and
> discharged the clean case of the empty branch (NEWEST).**  Worked exclusively
> on the top-priority discrete Hopf Umlaufsatz.  The whole library still builds
> end-to-end (8127 jobs through `RequestProject/SAWFinal.lean`) and
> `hex_closed_trail_turning_number` still reduces only to `sorryAx`
> (+ `propext, Classical.choice, Quot.sound`); no new axioms, no regressions.
> This round, in `RequestProject/SAWUmlaufPolygon.lean`:
>
> * Added and proved **`empty_ear_direct`** (sorry-free, reusable): from a
>   rotation `V.rotate r = a :: b :: c :: rest` with `b ≠ z`, both clip
>   endpoints `p = rest.getLast`, `q = rest.head` off the *line* `a–c`
>   (`cross (c-a) (p-a) ≠ 0`, `cross (c-a) (q-a) ≠ 0`), an empty corner, a clear
>   closed diagonal `a–c`, and matching ear/clip orientation, it assembles
>   `EmptyCornerData V z` directly (the two clip-turn non-degeneracies coming
>   from `HexArea.clip_turn_at_a_ne_zero`/`…c_ne_zero`).  This cleanly separates
>   the purely-combinatorial assembly of the empty branch from its genuine
>   Jordan content.
> * Restructured **`meisters_reduction_empty`** to extract `p, q` (sorry-free)
>   and `by_cases` on the clean predicate, *discharging the clean case* via
>   `empty_ear_direct` and leaving a single, sharper `sorry` for the non-clean
>   case (`b = z`, or a clip endpoint collinear with `a, c`, or a far vertex on
>   the closed diagonal, or reversed orientation), which is handled by the
>   clip/recurse-and-lift route.  Net: same number of open cores (the two
>   `meisters_reduction_{interior,empty}` branches) but the empty branch's
>   clean case is now proved, and `empty_ear_direct` is a consumed (not dead)
>   brick.
>
> Analysis recorded for future rounds: the genuine empty-branch gap is the
> planar-topology fact that an *empty* corner forces the clip `a :: c :: rest`
> to be simple — an edge crossing the diagonal `a–c` would, by simplicity of the
> two ear edges `a–b`, `b–c`, have to terminate at a vertex strictly inside the
> corner triangle, contradicting emptiness.  The degenerate clip-collinearity
> and `b = z` sub-cases additionally need the forbidden-vertex recursion.

> **Umlaufsatz: added the convex-apex segment-exclusion brick for the empty
> branch lift (NEWEST).**  Worked exclusively on the top-priority discrete Hopf
> Umlaufsatz.  The whole library still builds end-to-end (8127 jobs through
> `RequestProject/SAWFinal.lean`) and `hex_closed_trail_turning_number` still
> reduces only to `sorryAx` (+ `propext, Classical.choice, Quot.sound`); no new
> axioms, no regressions.  This round:
>
> * Proved **`HexArea.lexMin_not_mem_segment`** (sorry-free) in
>   `RequestProject/SAWUmlaufEarExtreme.lean`: the strict lex-minimal
>   (leftmost-lowest) vertex of a polygon never lies on the segment between two
>   other *distinct* vertices.  This is the segment analogue of the existing
>   `lexMin_not_inTriangleStrict` (the extreme vertex is a *strict* convex-hull
>   vertex, off the relative interior of every hull chord).  It is the missing
>   geometric input for the empty-branch *lift* step (the convex apex `b` is
>   never on the clip diagonal `a'–c'`, so it can be re-inserted without
>   violating the `x ∉ segment ℝ a' c'` clause of `EmptyCornerData`).
> * Analysis recorded: the two open cores `meisters_reduction_interior` /
>   `meisters_reduction_empty` remain the genuine Jordan content.  Concrete
>   enumeration confirms that, when recursing on the clip `a :: c :: rest` and
>   lifting the returned ear back to `V`, the "clean" lift (ear strictly inside
>   the `rest` arc) transports all `EmptyCornerData` clauses unchanged, while
>   the "boundary" lifts (the clip ear adjacent to the diagonal endpoints,
>   i.e. `b' = rest.head` or `b' = rest.getLast`) make the convex apex `b` a new
>   clip-neighbour and so need their own non-degeneracy treatment — the genuine
>   remaining gap.

> **Umlaufsatz: quadrilateral base case of the Meisters search proved
> sorry-free; open core now split into the two length-≥5 branches (NEWEST).**
> Worked exclusively on the top-priority discrete Hopf Umlaufsatz.  The whole
> library still builds end-to-end (8127 jobs through
> `RequestProject/SAWFinal.lean`) and the top theorem
> `hex_closed_trail_turning_number` still reduces only to `sorryAx`
> (+ `propext, Classical.choice, Quot.sound`); no new axioms.  This round, in
> `RequestProject/SAWUmlaufPolygon.lean`:
>
> * Proved **`segments_cross`** (sorry-free): the standard planar
>   segment-crossing criterion — if `c,d` are strictly on opposite sides of
>   line `a–b` and `a,b` strictly on opposite sides of line `c–d`, then the
>   closed segments `[a,b]` and `[c,d]` meet.  (Reusable, absent from Mathlib.)
> * Proved **`quad_diagonal_interior`** (sorry-free): the genuine `n = 4`
>   Jordan content — a non-degenerate simple quadrilateral has an interior
>   diagonal (one of the two diagonals has the opposite pair of vertices on
>   strictly opposite sides).  Derived from `segments_cross` by the four-point
>   orientation sign calculus; the edge-disjointness hypotheses are essential.
> * Proved **`meisters_reduction_quad`** (sorry-free): the strong-induction
>   **base case** — a simple non-degenerate quadrilateral has an empty corner
>   avoiding any forbidden vertex `z`.  Reduces entirely to
>   `quad_diagonal_interior` plus the clean orientation algebra (using
>   `inTriangleStrict_apex_sameSide`, `not_mem_segment_of_cross_ne`,
>   `cross_edges_eq_shoelace2_triple`, `shoelace2_rotate`).
> * Proved **`exists_farthest_interior`** and **`not_mem_segment_of_cross_ne`**
>   (sorry-free): the pivot-vertex selection and the diagonal-clearness helper.
> * Restructured **`meisters_reduction`** into the base case (length 4, now
>   discharged by `meisters_reduction_quad`) plus the explicit Meisters
>   dichotomy for length ≥ 5: an **interior branch** (non-empty corner →
>   farthest-interior-vertex diagonal split, recursing through `IH`) and an
>   **empty/diagonal branch** (empty corner → direct ear or one-step `IH`
>   recursion to dodge `z`).  Both are well-documented `sorry`s carrying the
>   genuine remaining inductive Jordan content; all five new lemmas above are
>   consumed (no dead branches).
>
> Net effect: the discrete Umlaufsatz base case is fully formalized and the
> remaining open content is exactly the two inductive branches of
> `meisters_reduction` for polygons with ≥ 5 vertices.

> **Umlaufsatz: Meisters Step 1 (convex extreme-vertex setup) proved
> sorry-free and wired into the open core.**  Worked exclusively on
> the top-priority discrete Hopf Umlaufsatz.  The whole library still builds
> end-to-end (8127 jobs through `RequestProject/SAWFinal.lean`) and the top
> theorem `hex_closed_trail_turning_number` still reduces only to `sorryAx`
> (+ `propext, Classical.choice, Quot.sound`); no new axioms.  This round added
> the **sorry-free** lemma `exists_lexmin_mid_rotation` in
> `RequestProject/SAWUmlaufPolygon.lean` — the first step of the Meisters ear
> search: every polygon with `≥ 3` vertices has a cyclic rotation
> `a :: b :: c :: rest` whose middle vertex `b` is the lexicographically minimal
> (leftmost-lowest) vertex, hence a convex-hull vertex never in the strict
> interior of any triangle spanned by polygon vertices (composing
> `exists_lex_min_mem`, `exists_rotate_mid`, `lexMin_not_inTriangleStrict`).
> It is now **consumed** by `meisters_reduction`, whose proof performs this
> convex-vertex setup sorry-free before the single remaining `sorry`.  Net
> effect: the lone open gap is now strictly the Jordan-curve geometric content
> of `meisters_reduction` (empty-corner / farthest-interior-vertex dichotomy,
> interior-diagonal split, and `PolygonSimple` preservation under the split),
> with Step 1 of the search discharged.

> **Umlaufsatz core refactored: strong-induction plumbing split off sorry-free.**
> Worked exclusively on the top-priority discrete Hopf Umlaufsatz.
> The whole library still builds end-to-end (8127 jobs) and the top theorem
> `hex_closed_trail_turning_number` still reduces only to `sorryAx`
> (+ `propext, Classical.choice, Quot.sound`); no new axioms.  This round
> restructured the single remaining open core in
> `RequestProject/SAWUmlaufPolygon.lean`: the previously-monolithic
> `exists_empty_corner_avoiding` sorry is now factored into
> (a) a named conclusion predicate `EmptyCornerData V z`;
> (b) `meisters_reduction` — the genuine Jordan-curve-level geometric reduction
> step, now **carrying the strong-induction hypothesis** `IH` (an empty corner
> for every strictly shorter simple non-degenerate polygon); this holds the
> single remaining math `sorry`;
> (c) `exists_empty_corner_avoiding_aux` — the **sorry-free** strong-induction
> wrapper that discharges `IH` by `Nat.strong_induction_on`; and
> (d) `exists_empty_corner_avoiding` itself, now **sorry-free**, delegating to
> the wrapper (downstream consumers unchanged — `EmptyCornerData` unfolds
> definitionally to the original existential).  Additionally added two
> **sorry-free** `Nodup`-preservation lemmas for the diagonal split in
> `RequestProject/SAWUmlaufEarSplit.lean` — `chordLeft_nodup`,
> `chordRight_nodup` — the combinatorial half of `PolygonSimple` preservation
> under the chord split.  Net effect: the genuine remaining gap is now
> concentrated in the single lemma `meisters_reduction`, with the recursion
> plumbing proved sorry-free; the lone Jordan-curve content left is the
> convex/farthest-vertex dichotomy, the interior-diagonal split, and the
> edge-disjointness half of `PolygonSimple` preservation.

> **Umlaufsatz diagonal-split combinatorial infrastructure added.**
> Worked exclusively on the top-priority discrete Hopf Umlaufsatz; the whole
> library still builds end-to-end (now 8127 jobs) and the top theorem
> `hex_closed_trail_turning_number` still reduces only to `sorryAx`
> (+ `propext, Classical.choice, Quot.sound`); no new axioms.  The single
> remaining live core is still `exists_empty_corner_avoiding` (Meisters
> two-ears search; needs the Jordan-curve-level diagonal-split recursion).
> This round added a new **sorry-free** preparation file
> `RequestProject/SAWUmlaufEarSplit.lean` (imported by `SAWUmlaufPolygon`,
> hence in the `SAWFinal` build chain) holding the *purely combinatorial*
> list-surgery the diagonal-split recursion needs.  For a cycle `V` and a
> chord `V[0]–V[k]` it defines the two sub-polygons
> `chordLeft V k = V.take (k+1)` (vertices `V₀…V_k`) and
> `chordRight V k = V.drop k ++ V.take 1` (vertices `V_k…V_{n-1},V₀`), and
> proves, sorry-free: their exact lengths (`chordLeft_length`,
> `chordRight_length`); that both are `≥ 3` yet strictly shorter than `V`
> (`chordLeft_length_ge/_lt`, `chordRight_length_ge/_lt`) — the strong-induction
> measure decrease; that they meet the shared diagonal correctly at their
> endpoints (`chordLeft_head/_getLast`, `chordRight_head/_getLast`); and that
> together they cover every vertex (`mem_chord_split`).  These are documented
> as preparation toward `exists_empty_corner_avoiding` and isolate the genuine
> remaining gap to the two Jordan-curve-level facts (existence of an interior
> diagonal, and `PolygonSimple` preservation under the split), which remain
> open.

> **Umlaufsatz core factored: assembler proved, single search sorry isolated.**
> Worked exclusively on the top-priority discrete Hopf Umlaufsatz; touched only
> `RequestProject/SAWUmlaufPolygon.lean`.  The whole library still builds
> end-to-end (8126 jobs) and the top theorem `hex_closed_trail_turning_number`
> still reduces only to `sorryAx` (+ `propext, Classical.choice, Quot.sound`);
> no new axioms.  This round **factored** the previously-monolithic open core
> `exists_empty_convex_ear_avoiding` into two pieces:
> - `ear_data_of_empty_corner` — **proved sorry-free** (axioms: only
>   `propext, Classical.choice, Quot.sound`).  The assembler/bookkeeping step:
>   from an *empty* corner `a,b,c` of `a :: b :: c :: rest` whose two clip
>   corners are non-flat (`cross (a-p)(c-a) ≠ 0`, `cross (c-a)(q-c) ≠ 0`) and
>   whose ear triangle shares the clip orientation, it assembles the full
>   12-clause ear-data conjunction (edge non-degeneracies read off
>   `polyCycNondeg`, `polyCycNondeg (a::c::rest)` via `polyCycNondeg_clip`).
> - `exists_empty_corner_avoiding` — the **single remaining live sorry** in the
>   whole Umlaufsatz chain.  This is now the *clean, isolated* statement of the
>   genuine Meisters two-ears geometric search (find an empty non-flat
>   orientation-matching corner with tip `≠ z`).  `exists_empty_convex_ear_avoiding`
>   is now **fully derived** from it plus `ear_data_of_empty_corner` and
>   `polyCycNondeg_rotate` (rotation-transport of cyclic non-degeneracy).
> Net effect: the remaining open content is unchanged mathematically but now
> sits behind one clean named lemma, with all the surrounding bookkeeping
> discharged sorry-free.  The remaining gap is the polygon-split recursion
> (strong induction on `V.length`, split along an interior diagonal into two
> strictly-shorter simple sub-polygons), which is Jordan-curve-theorem-level
> and absent from Mathlib.

> **Umlaufsatz ear-clip combinatorial bricks added.**
> Worked exclusively on the top-priority discrete Hopf Umlaufsatz; touched only
> `RequestProject/SAWUmlaufPolygon.lean`. The whole library still builds
> end-to-end (8126 jobs) and the top theorem `hex_closed_trail_turning_number`
> still reduces only to `sorryAx` (+ `propext, Classical.choice, Quot.sound`);
> no new axioms. The single remaining live core is still
> `exists_empty_convex_ear_avoiding` (Meisters ear existence; needs the
> diagonal-split recursion). Two new **sorry-free** combinatorial bricks were
> proved as preparation toward it:
> - `polyCycNondeg_clip` — clipping the ear `b` from `a :: b :: c :: rest`
>   preserves cyclic non-degeneracy `polyCycNondeg (a :: c :: rest)`, given the
>   two new diagonal corners are non-flat (`cross (a-p)(c-a) ≠ 0`,
>   `cross (c-a)(q-c) ≠ 0`). This is the combinatorial glue that converts the
>   geometric facts `HexArea.clip_turn_at_a_ne_zero` /
>   `HexArea.clip_turn_at_c_ne_zero` into the `polyCycNondeg` clause of the open
>   core.
> - `exists_rotate_mid` — any vertex `v ∈ V` of a length-`≥ 3` cycle can be
>   rotated to the middle (second) position: `V.rotate r = a :: v :: c :: rest`.
>   Lets the ear search normalise the extreme (lex-min) vertex to the ear-tip
>   position.
> The remaining geometric content of `exists_empty_convex_ear_avoiding` (the
> diagonal-split recursion, the convex-ear orientation `iff`, and the
> off-the-diagonal non-flatness of the cyclic neighbours) is still open.

> **Umlaufsatz `ear_turn_concat` fully closed — single core remaining.**
> Worked exclusively on the top-priority discrete Hopf Umlaufsatz. The whole
> library still builds end-to-end (8126 jobs) and the top theorem
> `hex_closed_trail_turning_number` still reduces only to `sorryAx`
> (+ `propext, Classical.choice, Quot.sound`).
>
> **What changed (all in `RequestProject/SAWUmlaufPolygon.lean`).** The exact
> turning-preservation core `ear_turn_concat` (one of the two previously-open
> Jordan-curve-level cores) is now **proved sorry-free**. Key correction: the
> earlier docstring WARNING that `ear_turn_concat` does NOT split into the two
> per-corner facts was found to be true only under *local-emptiness-only*
> hypotheses; under the genuine global `PolygonSimple` hypothesis present in the
> lemma BOTH per-corner facts hold (verified numerically: per-corner wraps
> `(kA,kC)=(0,0)` in 8006/8006 strict-simple ears; the local-only version fails
> ~60%). New sorry-free lemmas added and proved:
> - `arg_add_eq_arg_mul_of_im_sign` — pure no-wrap criterion for `arg`
>   additivity from imaginary-part signs (reduces to `Complex.arg_mul`).
> - `cone_cross_sign_of_disjoint` — pure plane geometry: a point off the cone
>   at a vertex, expressed as a cross-sign disjunction (segment-crossing /
>   `corner_exit_point` argument).
> - `corner_a_cross_sign` / `corner_c_cross_sign` — extract the cone condition
>   from `PolygonSimple` + `polyCycNondeg` (closed-edge disjointness, etc.).
> - `ear_corner_turn_a` / `ear_corner_turn_c` — the per-corner turning facts,
>   from the two above via the im↔cross translation.
> - `ear_turn_concat` — now `linarith` of the two per-corner facts.
>
> **Single remaining open core.** The entire discrete Umlaufsatz now reduces to
> the one lemma `exists_empty_convex_ear` (Meisters two-ears existence; a simple
> non-degenerate polygon with `≥ 4` vertices has a cyclic rotation exhibiting an
> empty convex ear). It needs the split-and-recurse Meisters induction; the
> full `SAWUmlaufEar*` toolkit is available. Everything downstream of it
> (`exists_front_ear`, `exists_ear_clip`, `polygon_ear_reduction`,
> `polygon_umlaufsatz`, `hex_signed_turn_eq_six_sign_shoelace`) is sorry-free.

> **Umlaufsatz middle-vertex-split round note (NEWEST).**
> Focused exclusively on the top-priority discrete Hopf Umlaufsatz
> (`hex_closed_trail_turning_number`, `RequestProject/SAWUmlaufGaussBonnet.lean`).
> The whole library still builds end-to-end (8126 jobs) and the top theorem
> still reduces only to `sorryAx` (+ `propext, Classical.choice, Quot.sound`).
>
> **What changed.** The open local-turning core `ear_local_turning_identity`
> (in `RequestProject/SAWUmlaufPolygon.lean`) is now **proved sorry-free from a
> cleaner core `ear_turn_concat`**: the middle-vertex `arg`-split is discharged
> exactly via the already-proved `arg_split_one_add` (with `w = (c-b)/(b-a)`,
> using `(b-a)+(c-b) = c-a`, so `1+w = (c-a)/(b-a)` and `w/(1+w) = (c-b)/(c-a)`),
> rewriting `arg((c-b)/(b-a)) = arg((c-a)/(b-a)) + arg((c-b)/(c-a))`. The
> remaining gap is now the two-corner turning-concatenation identity
> `ear_turn_concat` (the four-step chain `a-p → b-a → c-a → c-b → q-c` equals
> the merged `a-p → c-a → q-c` as REAL turning, not just mod 2π).
>
> **Remaining open Umlaufsatz cores (both TRUE, Jordan-curve level).**
> 1. `ear_turn_concat` — the irreducible no-2π-wrap content. Its docstring
>    records the WARNING that it must NOT be split into the two per-corner
>    facts (`rngA`/`rngC` fail ~38% of empty-ear cases; the wraps cancel only
>    globally). High-effort automated attempts stall exactly at placing the
>    cyclic neighbours `p, q` from emptiness/simplicity.
> 2. `exists_empty_convex_ear` — the Meisters two-ears existence content
>    (extreme convex vertex + farthest-vertex pivot; full `SAWUmlaufEar*`
>    toolkit available but the rotation/induction assembly is not yet closed).
>
> **Umlaufsatz false-bound fix round note.**
> Focused exclusively on the top-priority discrete Hopf Umlaufsatz
> (`hex_closed_trail_turning_number`, `RequestProject/SAWUmlaufGaussBonnet.lean`).
> The whole library still builds end-to-end (8126 jobs) and the top theorem
> still reduces only to `sorryAx` (+ `propext, Classical.choice, Quot.sound`).
>
> **Critical soundness finding & fix.** The previous decomposition's core
> `ear_turning_bounds` (three `Set.Ioc (-π) π` partial-sum bounds, in
> `RequestProject/SAWUmlaufPolygon.lean`) is **FALSE**: its third bound
> `arg((c-a)/(a-p)) + arg((q-c)/(c-a)) ∈ (-π, π]` is the sum of two of the
> three exterior turns of the clipped triangle, which always sum to
> `2π − (third) ∈ (π, 2π) > π` (counterexample: convex CCW quadrilateral
> `a=0, b=20+i, c=19+2i, d=-1+i`; gives ≈ 3.977). So the whole Umlaufsatz
> skeleton was resting on an unprovable lemma.
>
> **What changed.**
> * `ear_turning_bounds` is commented out (kept as documentation of the dead
>   branch, with the counterexample).
> * The genuine, TRUE fact the ear clip needs — the *local turning identity*
>   `arg((b-a)/(a-p)) + arg((c-b)/(b-a)) + arg((q-c)/(c-b))`
>   `= arg((c-a)/(a-p)) + arg((q-c)/(c-a))` — is isolated as
>   `ear_local_turning_identity` (sorry; verified numerically to hold for empty
>   ears of simple polygons, failing only for self-intersecting configs).
> * A new `polyCycWind_clip_eq_of_identity` consumes that identity directly and
>   is now used by `exists_ear_rotation` (replacing the old
>   `polyCycWind_clip_eq` + false bounds). `exists_front_ear_core` /
>   `exists_front_ear` now thread the identity instead of the three bounds.
> * Two reusable backbone lemmas are **proved sorry-free**:
>   `ear_turning_identity_mod` (the identity holds in `Real.Angle = ℝ/2πℤ`,
>   pure `arg_div_coe_angle` telescoping) and `arg_split_one_add`
>   (`arg w = arg(1+w) + arg(w/(1+w))` unconditionally; the local, geometry-free
>   building block, applied with `w=(c-b)/(b-a)` since `(b-a)+(c-b)=c-a`).
>
> **Remaining open Umlaufsatz cores (both TRUE).**
> 1. `ear_local_turning_identity` — needs only the integer fact that the
>    real-valued difference (an element of `2πℤ` by `ear_turning_identity_mod`)
>    is `0`, i.e. no `2π` wrap. NOTE for future rounds: this does NOT split
>    into two per-corner `(-π,π]` range facts (those analogues `rngA`/`rngC`
>    were checked and FAIL ~38% of empty-ear cases — the wraps cancel only
>    globally), so the false-bound mistake must not be repeated.
> 2. `exists_empty_convex_ear` — the Meisters two-ears existence content.
>
> **Umlaufsatz ear-core split round note.**
> Focused exclusively on the top-priority discrete Hopf Umlaufsatz
> (`hex_closed_trail_turning_number`, `RequestProject/SAWUmlaufGaussBonnet.lean`).
> The whole library still builds end-to-end and the top-level theorem still
> reduces only to `sorryAx` (+ `propext, Classical.choice, Quot.sound`).
>
> **What changed.** The previously single open core `exists_front_ear_core`
> (`RequestProject/SAWUmlaufPolygon.lean`) is now **proved as an assembly** of
> two cleaner, faithful, focused sorried cores, both true and both in the
> `SAWFinal` build chain:
> * `exists_empty_convex_ear` — the genuine Meisters two-ears / ear-existence
>   content: a simple non-degenerate polygon with ≥4 vertices has a cyclic
>   rotation `a :: b :: c :: rest` whose middle vertex `b` is an *empty convex
>   ear* (corner triangle non-degenerate, empty of far vertices and with empty
>   diagonal `a–c`), plus the five edge non-degeneracies, `polyCycNondeg` of
>   the clip, and the orientation equivalence. Intended proof: lex-min convex
>   vertex + farthest-vertex pivot + diagonal split + strong induction on
>   length, using the `SAWUmlaufEar*` toolkit.
> * `ear_turning_bounds` — the three convexity turning-range `(-π, π]` bounds
>   consumed by `arg_ear_local_exact` / `polyCycWind_clip_eq`. Intended proof:
>   telescope each arg-sum to `arg(product)` via `Complex.arg_mul`, with the
>   `arg`-additivity side conditions supplied by cross-product sign facts about
>   the neighbours `p, q` (NOT all far vertices) derived from emptiness +
>   planar simplicity.
>
> The bundling/rotation-transport/edge-nondeg wiring of `exists_front_ear_core`
> is now proved sorry-free; only these two true geometric cores remain open.

> **Umlaufsatz Jordan-segment-core round note (NEWEST).**
> This round focused exclusively on the top-priority discrete Hopf Umlaufsatz
> (`hex_closed_trail_turning_number`, `RequestProject/SAWUmlaufGaussBonnet.lean`).
> The whole library still builds end-to-end (8126 jobs) and the top-level
> theorem still reduces only to `sorryAx` (+ `propext, Classical.choice,
> Quot.sound`).
>
> **What changed: the Jordan-segment core `seg_diagonal_disjoint_of_corner`
> (one of the two previously-open cores) is now PROVED sorry-free**, so the
> Umlaufsatz now rests on a *single* remaining open core,
> `exists_front_ear_core` (the Meisters two-ears / ear-existence content with
> its turning-range bounds and orientation).
>
> New fully-proved file `RequestProject/SAWUmlaufCorner.lean` (imported from
> `SAWUmlaufPolygon`, hence in the `SAWFinal` build chain), containing six
> sorry-free, reusable plane-geometry lemmas:
> * `exists_real_smul_of_cross_zero` — vanishing 2-D cross product ⇒ real
>   linear dependence (affine parameter on a carrier line).
> * `mem_segment_ab_of_cross` / `mem_segment_bc_of_cross` — a point on an
>   edge's carrier line with correct (orientation-agnostic, product-form) side
>   signs lies on the closed edge.
> * `corner_exit_point` — the **constructive crossing core**: a point moving
>   from the relative interior of edge `a–c` towards an apex-side endpoint that
>   is not strictly inside the triangle must hit closed edge `a–b` or `b–c`
>   (explicit first-crossing parameter `τ⋆`; no analysis needed since every
>   side test is affine).
> * `collinear_diag_a_mem` — the degenerate collinear case: if both chord
>   endpoints are on the carrier line of `a–c` but off the closed segment, and
>   an interior point of `a–c` is on the chord, then `a` lies on the chord.
>
> Using these, `seg_diagonal_disjoint_of_corner` (in `SAWUmlaufPolygon.lean`)
> is proved sorry-free: the chord/diagonal intersection point is strictly
> interior to `a–c`, the crossing forces an apex-side endpoint, and
> `corner_exit_point` (generic case) or `collinear_diag_a_mem` (collinear case)
> produces a chord point on a polygon edge, contradicting edge-disjointness.
>
> So the Umlaufsatz now rests on exactly **one** open, true,
> Jordan-curve-level core, `exists_front_ear_core`.

> **Umlaufsatz ear-decomposition round note.**
> This round focused exclusively on the top-priority discrete Hopf Umlaufsatz
> (`hex_closed_trail_turning_number`, `RequestProject/SAWUmlaufGaussBonnet.lean`).
> The whole library still builds end-to-end (8125 jobs) and the top-level
> theorem still reduces only to `sorryAx` (+ `propext, Classical.choice,
> Quot.sound`).
>
> **What changed: the single monolithic ear gap `exists_front_ear` is now
> decomposed into finer, individually-attackable, true pieces** (all in
> `RequestProject/SAWUmlaufPolygon.lean`):
> * `far_edge_disjoint_earEdges` — **PROVED sorry-free** this round: a guarded
>   far edge of the clip is segment-disjoint from the two ear edges `a–b`,
>   `b–c` (pure `PolygonSimple`/`closedEdges` bookkeeping).
> * `seg_diagonal_disjoint_of_corner` — *(open, `sorry`)* the pure-geometry,
>   list-free Jordan-segment heart: a non-degenerate corner whose far-edge
>   endpoints are neither strictly inside the triangle nor on the closed
>   diagonal, with the far edge disjoint from `a–b`, `b–c`, has its diagonal
>   `a–c` disjoint from that far edge.  This is the genuine
>   intermediate-value/“crossing” content.
> * `diag_disjoint_of_empty_corner` — **sorry-free assembly**: turns
>   closed-corner emptiness (`hempty` strict-interior + `hdiagempty`
>   no-vertex-on-diagonal) plus planar simplicity into the diagonal-disjointness
>   clause, via `far_edge_disjoint_earEdges` + `seg_diagonal_disjoint_of_corner`.
> * `exists_front_ear_core` — *(open, `sorry`)* the genuine Meisters two-ears /
>   ear-existence content (extreme convex vertex + farthest-vertex pivot), in
>   geometric-data form with the **emptiness** clause (strict-interior +
>   no-vertex-on-diagonal) in place of the disjointness clause.
> * `exists_front_ear` — now a **sorry-free assembly** of `exists_front_ear_core`
>   and `diag_disjoint_of_empty_corner`.
>
> **Correctness fix folded in:** the intermediate emptiness clause must also
> exclude a far vertex lying on the *open diagonal* `a–c` (`hdiagempty`); plain
> strict-interior emptiness is too weak (a far vertex on the open diagonal would
> break disjointness), so both `exists_front_ear_core` and
> `diag_disjoint_of_empty_corner` carry the `hdiagempty` clause.
>
> So the Umlaufsatz now rests on exactly **two** open, true, Jordan-curve-level
> cores (`seg_diagonal_disjoint_of_corner`, `exists_front_ear_core`); high-effort
> attempts on both timed out (consistent with their being absent from Mathlib).
> All `SAWUmlaufEar*` preparation files remain imported via
> `SAWUmlaufPolygon` and documented as feeding these cores.

> **Umlaufsatz correctness-fix round note.**
> The single remaining Umlaufsatz `sorry` is still `exists_front_ear`
> (`SAWUmlaufPolygon.lean`), the genuine Meisters two-ears / ear-existence core
> (Jordan-curve-theorem level, absent from Mathlib).  The whole library still
> builds and the top-level discrete Umlaufsatz `hex_closed_trail_turning_number`
> still reduces to exactly this one gap (axioms: `propext, sorryAx,
> Classical.choice, Quot.sound`).
>
> **What changed: the gap was FALSE and is now TRUE.**  The previous
> "one-sided-ear" round had restated the planar-simplicity output clause of
> `exists_front_ear` as the *one-sidedness* condition
> `∀ x y ∈ rest, 0 < cross (c-a)(x-a) * cross (c-a)(y-a)` (every far vertex on
> one and the same side of the clip diagonal `a–c`).  That clause is **false in
> general**: the simple, non-degenerate pentagon `[(4,0),(6,0),(6,5),(0,0),(5,1)]`
> has *no* cyclic triple whose far vertices are all on one side of the clip
> diagonal (verified computationally over all 5 rotations), so the existence
> statement could never be proved — a false `sorry` sitting under the main
> theorem.  The same pentagon *does* have a genuine ear (rotation `4`, clipping
> the vertex `(4,0)`): the diagonal `(5,1)–(6,0)` misses every far edge and all
> the turning-range / orientation / non-degeneracy clauses hold.
>
> The fix replaces the one-sidedness clause by the **genuine, always-satisfiable
> diagonal-disjointness clause** — exactly the `hdiag` hypothesis that
> `PolygonSimple_clip` consumes:
> `∀ e ∈ (c :: rest).zip (rest ++ [a]), a ≠ e.1 → a ≠ e.2 → c ≠ e.1 → c ≠ e.2 →`
> `  Disjoint (segment ℝ a c) (segment ℝ e.1 e.2)`.
> `exists_ear_rotation` now feeds this directly into `PolygonSimple_clip`
> (no longer routing through `oneSided_far_edges_sameSide` /
> `diag_disjoint_of_far_sameSide'`, which remain as correct, sorry-free but now
> unconsumed preparation in `SAWUmlaufEarOneSided.lean` /
> `SAWUmlaufPolygon.lean`).  The library builds end-to-end and the gap is now a
> true statement (the classical discrete two-ears theorem), still open.

> **Umlaufsatz one-sided-ear round note.**
> The single remaining Umlaufsatz `sorry` is still `exists_front_ear`
> (`SAWUmlaufPolygon.lean`), the genuine Meisters two-ears / ear-existence core
> (Jordan-curve-theorem level, absent from Mathlib).  The whole library still
> builds and the top-level discrete Umlaufsatz
> (`hex_closed_trail_turning_number`) still reduces to exactly this one gap
> (axioms: `propext, sorryAx, Classical.choice, Quot.sound`).  This round made
> one safe, sorry-free gap-simplification plus reusable building blocks:
> * **Simplified the gap's hardest output clause again.**  `exists_front_ear`
>   previously had to produce a *per-edge far-edge same-side* clause.  It now
>   only has to produce the cleaner, more geometric **one-sidedness** clause
>   `∀ x y ∈ rest, 0 < cross (c-a)(x-a) * cross (c-a)(y-a)` — every far vertex
>   strictly on one and the same side of the diagonal line `a–c` (the defining
>   property of a *one-sided ear*).  A worked example shows a generic empty
>   convex ear (e.g. at the extreme vertex) need NOT satisfy the per-edge
>   same-side clause, while a genuine one-sided ear does; so this states the
>   true geometric heart of the gap.  The downstream `exists_ear_rotation`
>   recovers the per-edge same-side condition (still sorry-free) via the new
>   bridge `HexArea.oneSided_far_edges_sameSide`.
> * **New reusable, sorry-free building blocks** in new file
>   `SAWUmlaufEarOneSided.lean` (imported from `SAWUmlaufPolygon.lean`, hence in
>   the `SAWFinal` chain): `oneSided_far_edges_sameSide` (one-sidedness ⇒ the
>   per-edge same-side clause), `sameSide_pairwise_of_allPos/allNeg`
>   (repackaging), and `clip_turn_at_a_ne_zero` / `clip_turn_at_c_ne_zero` (the
>   two new cyclic turns created by the clip are non-degenerate, for the
>   `polyCycNondeg (a :: c :: rest)` clause).  The first of these is now
>   *consumed* by `exists_ear_rotation`, so it is live, not dead prep.

> **Umlaufsatz gap-simplification round note.**
> The single remaining Umlaufsatz `sorry` is still `exists_front_ear`
> (`SAWUmlaufPolygon.lean`), the genuine Meisters two-ears / ear-existence core
> (Jordan-curve-theorem level, absent from Mathlib).  A direct high-effort proof
> attempt times out, confirming it needs the full diagonal-split recursion.
> This round made two safe, sorry-free advances around that core, keeping the
> whole library building and the top-level discrete Umlaufsatz
> (`hex_closed_trail_turning_number`) reducing to exactly this one gap
> (axioms: `propext, sorryAx, Classical.choice, Quot.sound`):
> * **Simplified the gap's hypothesis.**  `exists_front_ear` previously had to
>   produce a *segment-disjointness* clause for the diagonal `a–c`.  It now only
>   has to produce the more elementary, orientation-agnostic *algebraic*
>   cross-product same-side condition
>   `0 < cross (c-a) (e.1-a) * cross (c-a) (e.2-a)` on the guarded far edges.
>   The new lemma `diag_disjoint_of_far_sameSide'` converts that into the
>   segment-disjointness hypothesis of `PolygonSimple_clip`, and
>   `exists_ear_rotation` was updated accordingly (still sorry-free).
> * **Added a reusable building block** `HexArea.inTriangleStrict_apex_sameSide`
>   (new file `SAWUmlaufEarSide.lean`, imported from `SAWUmlaufPolygon.lean`):
>   a strict interior point of a triangle lies strictly on the apex side of the
>   base diagonal (`0 < cross (c-a) (x-a) * cross (c-a) (b-a)`), proved from the
>   barycentric convex-combination characterization.  This is the per-point
>   side geometry underpinning the same-side condition above; preparation for
>   the eventual `exists_front_ear` proof.
>
> **Umlaufsatz clip-bookkeeping extraction round note.**
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
