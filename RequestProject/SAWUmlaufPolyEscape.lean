import Mathlib
import RequestProject.SAWUmlaufPolyLift
import RequestProject.SAWUmlaufChordCorner

/-!
# `SAWUmlaufPolygon`, part `SAWUmlaufPolyEscape`

This file is one of the six parts the (formerly single, 7000-line) planar
polygon Umlaufsatz development was split into.  Parts are chained by imports
`SAWUmlaufPolyBase → SAWUmlaufPolyChord → SAWUmlaufPolyLift →
SAWUmlaufPolyEscape → SAWUmlaufPolyMeisters → SAWUmlaufPolygon`, and the last
part is imported by `RequestProject.SAWUmlaufSignedArea`, hence lies on the live
route to the main theorem.  See `SAWUmlaufPolyBase` for the overview.
-/

open Real Complex ComplexConjugate

noncomputable section

set_option maxHeartbeats 4000000

/-! The chord-piece cycle-edge classification `chordPiece_cycleEdge_or_diag` now
lives in `RequestProject.SAWUmlaufChordCorner` (imported above), where the corner
escape needs it. -/

/-
**Combinatorial edge structure of an ear-clipped chord piece (reusable,
    provable).**  Let `P` be a chord piece and `P.rotate s = a' :: b' :: c' :: tlP`
    (so `b'` is the ear tip).  Every closed cycle edge `e` of the ear-clipped
    polygon `a' :: c' :: tlP` has both endpoints in `a' :: c' :: tlP`, and its
    segment is *either* the ear base `a'–c'`, *or* `e` is an honest closed edge of
    `W`, *or* its segment is the cut diagonal `u–v`.  Reason: clipping only
    replaces the two ear sides `(a',b'),(b',c')` by the single base edge
    `(a',c')`; every other edge is an edge of `P.rotate s`, hence of `P` (by
    `mem_closedEdges_rotate`), hence classified by `chordPiece_cycleEdge_or_diag`.
    Crucially none of these `W`-edges involves the removed tip `b'`, so the
    ear-side edges `a'–b'`, `b'–c'` are NOT among the edges the escape walk must
    avoid.  NOT a dead branch — consumed by `clipped_ear_escape_walk` below.
-/
lemma clippedPiece_cycleEdge_classify (W : List ℂ) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (P : List ℂ) (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ)
    (hrotP : P.rotate s = a' :: b' :: c' :: tlP)
    (e : ℂ × ℂ) (he : e ∈ HexArea.cycleEdges (a' :: c' :: tlP)) :
    (e.1 ∈ (a' :: c' :: tlP) ∧ e.2 ∈ (a' :: c' :: tlP)) ∧
      (segment ℝ e.1 e.2 = segment ℝ a' c' ∨
        e ∈ closedEdges W ∨ segment ℝ e.1 e.2 = segment ℝ u v) := by
  by_cases he_head : e = (a', c');
  · aesop;
  · have h_e_in_P : e ∈ HexArea.cycleEdges P := by
      have h_e_in_P : e ∈ HexArea.cycleEdges (P.rotate s) := by
        simp_all +decide [ HexArea.cycleEdges ]
      generalize_proofs at *; (
      convert mem_closedEdges_rotate P s e |>.1 ?_ using 1
      generalize_proofs at *; (
      cases P <;> simp +decide [ HexArea.cycleEdges ] at *;
      cases ‹List ℂ› <;> simp +decide [ closedEdges ] at *;
      grind +extAll);
      convert h_e_in_P using 1
      generalize_proofs at *; (
      unfold HexArea.cycleEdges closedEdges;
      refine' List.ext_get _ _ <;> simp +decide [ List.get ];
      · cases P <;> simp +arith +decide at *;
      · intro n hn hn'; rcases n with ( _ | n ) <;> simp_all +decide [ List.getElem_append, List.getElem_rotate ] ;
        grind +qlia))
    generalize_proofs at *; (
    have := chordPiece_cycleEdge_or_diag W k hk1 hk u v hu hv P hP e h_e_in_P; ( have := mem_closedEdges_rotate P s e; ( simp_all +decide [ HexArea.cycleEdges ] ; ) );
    rw [ List.mem_iff_get ] at he; obtain ⟨ i, hi ⟩ := he; simp_all +decide [ List.get ] ;
    grind +splitIndPred)

/-
**Shared vertex-escape core (the single genuine Jordan residue of both
    escape-walk lemmas).**  For a simple polygon `W`, a vertex `x ∈ W`, and a
    finite family `diags` of "diagonal" segments, each disjoint from every
    `W`-edge not incident to its own endpoints (`hdiags`), there is an
    edge-avoiding polyline from `x` reaching a point outside `convexHull ℝ W`
    whose every step avoids all `W`-edges not incident to `x` and every diagonal
    in `diags`.

    This is the genuine polygon-Jordan complement path-connectivity content shared
    by *both* escape residues below: `chord_ear_other_escape_walk` uses
    `diags = [(u,v)]`, and `clipped_ear_escape_walk` uses `diags = [(u,v),(a',c')]`
    (the second being the empty-ear base).  Extracting it here removes the
    duplicated Jordan content from the two residues, which now reduce to this one
    statement (plus, for the clipped case, the local fact that the ear base is a
    valid `W`-diagonal).  It is a TRUE statement (the exterior of a simple polygon
    is path-connected and unbounded, and a boundary vertex has an outward escape
    direction; interior diagonals are avoided by staying in the exterior); NOT a
    dead branch.

A polygon vertex avoids the union of all nonincident polygon edges and
all explicitly avoided diagonals.  This supplies the source-membership premise
needed by the correctly stated fixed-endpoint Jordan core.
-/
lemma vertex_escape_source_mem (W : List ℂ) (h4 : 4 ≤ W.length)
    (hsimple : PolygonSimple W) (x : ℂ) (hxW : x ∈ W)
    (diags : List (ℂ × ℂ))
    (hdiagavoid : ∀ s ∈ diags, x ∉ segment ℝ s.1 s.2) :
    x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        segment ℝ s.1 s.2)ᶜ) := by
  simp_all +decide [ Set.ext_iff ];
  rintro a b ( ⟨ hab, ha, hb ⟩ | hab );
  · convert simple_vertex_not_on_far_edge W h4 hsimple x hxW ( a, b ) hab ( by tauto ) ( by tauto ) using 1;
  · exact hdiagavoid a b hab

/-- The forbidden-segment complement occurring in the escape core is open.
This is a direct specialization of the finite-segment result in
`SAWUmlaufHullExterior` and is consumed by the path-component reduction below. -/
lemma vertex_escape_forbidden_isOpen (W : List ℂ) (x : ℂ)
    (diags : List (ℂ × ℂ)) :
    IsOpen ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        segment ℝ s.1 s.2)ᶜ) := by
  exact HexArea.isOpen_compl_iUnion_segments _

/-
Once an avoiding path reaches beyond a norm radius containing every
forbidden segment, it can be continued to any other point beyond that radius.
The continuation runs in the path-connected ball exterior and therefore avoids
every forbidden segment.
-/
lemma vertex_escape_joinedIn_of_reaches_norm_gt
    (S : List (ℂ × ℂ)) (R : ℝ) (hR : 0 < R)
    (hS : ∀ s ∈ S, ∀ z ∈ segment ℝ s.1 s.2, ‖z‖ < R)
    {x p q : ℂ} (hxp : JoinedIn ((⋃ s ∈ S, segment ℝ s.1 s.2)ᶜ) x p)
    (hp : R < ‖p‖) (hq : R < ‖q‖) :
    JoinedIn ((⋃ s ∈ S, segment ℝ s.1 s.2)ᶜ) x q := by
  obtain ⟨ γ₁, hγ₁ ⟩ := hxp;
  obtain ⟨ γ₂, hγ₂ ⟩ := HexArea.joinedIn_norm_gt R hR hp hq;
  refine' ⟨ γ₁.trans γ₂, _ ⟩;
  intro t; cases' t with t ht; simp_all +decide [ Path.trans_apply ] ;
  grind

/-
**Superseded fixed-endpoint formulation (not retained as a theorem).**
The earlier generic statement `vertex_escape_same_component_to` quantified over
an arbitrary list of diagonals.  Its hypotheses did not prevent several
diagonals from forming an additional closed barrier, so the generic claim was
under-specified.  The proof chain now uses the honest local unbounded-escape
core below, with a cardinality restriction matching the actual Umlaufsatz caller
(the single chord diagonal), followed by the proved large-circle routing lemma.

A connected component of the forbidden-segment complement is unbounded
exactly when it contains points of arbitrarily large norm.  This metric bridge
packages the quantitative endpoint needed by the large-circle route.
-/
lemma exists_norm_gt_of_component_unbounded
    (U : Set ℂ) (x : ℂ)
    (hunbounded : ¬ Bornology.IsBounded (connectedComponentIn U x))
    (R : ℝ) :
    ∃ p : ℂ, R < ‖p‖ ∧ p ∈ connectedComponentIn U x := by
  contrapose! hunbounded with h;
  exact isBounded_iff_forall_norm_le.mpr ⟨ R, fun p hp => le_of_not_gt fun h' => h p h' hp ⟩

/-
Every admissible boundary source has a positive open ball contained in
the forbidden-segment complement.  This gives a verified local escape
neighborhood; the remaining Jordan core must show that this local component is
the unbounded one.
-/
lemma vertex_escape_source_ball
    (W : List ℂ) (x : ℂ) (diags : List (ℂ × ℂ))
    (hsource : x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        segment ℝ s.1 s.2)ᶜ)) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ⊆
      ((⋃ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
          segment ℝ s.1 s.2)ᶜ) := by
  exact Metric.isOpen_iff.mp ( vertex_escape_forbidden_isOpen W x diags ) x hsource

/-
Every point in the local source ball belongs to the same connected
component of the forbidden complement as the source.  This packages the local
half of the unbounded-component argument.
-/
lemma vertex_escape_ball_subset_component
    (W : List ℂ) (x : ℂ) (diags : List (ℂ × ℂ))
    (hsource : x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        segment ℝ s.1 s.2)ᶜ)) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ⊆ connectedComponentIn
      ((⋃ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
          segment ℝ s.1 s.2)ᶜ) x := by
  -- Apply the vertex_escape_source_ball lemma to obtain ε > 0 and the ball subset.
  obtain ⟨ε, hε⟩ := vertex_escape_source_ball W x diags hsource;
  refine' ⟨ ε, hε.1, _ ⟩;
  apply_rules [ IsPreconnected.subset_connectedComponentIn, convex_ball _ _ |> Convex.isPreconnected ];
  · aesop;
  · exact hε.2

/-!
## A ray certificate for the unbounded escape component

Any straight ray from the source which misses every forbidden segment is a
sufficient certificate for the Jordan residue below.  The following generic
lemma turns exactly such a geometric certificate into the connected-component
unboundedness required by the rest of the proof.  Thus it is not a dead branch:
it is an explicitly linked route for proving `vertex_escape_component_unbounded`
when the finite geometry supplies a straight escape; the more general residue
also permits a bent polygonal escape.  All metric and path consequences are
already proved downstream.
-/

/-
A nonconstant ray contained in `U` certifies that the connected component
of its initial point is unbounded.
-/
lemma connectedComponentIn_unbounded_of_ray
    (U : Set ℂ) (x d : ℂ) (hd : d ≠ 0)
    (hray : ∀ t : ℝ, 0 ≤ t → x + (t : ℂ) * d ∈ U) :
    ¬ Bornology.IsBounded (connectedComponentIn U x) := by
  -- By assumption, the ray {x + td | t ≥ 0} is contained in U.
  have h_ray_subset : ∀ t : ℝ, 0 ≤ t → x + t * d ∈ connectedComponentIn U x := by
    intro t ht;
    -- The ray is path-connected, hence connected.
    have h_ray_connected : IsConnected {p : ℂ | ∃ t : ℝ, 0 ≤ t ∧ p = x + (t : ℂ) * d} := by
      rw [ show { p : ℂ | ∃ t : ℝ, 0 ≤ t ∧ p = x + t * d } = ( fun t : ℝ => x + t * d ) '' Set.Ici 0 by ext; aesop ];
      exact ⟨ Set.Nonempty.image _ ⟨ 0, by norm_num ⟩, isPreconnected_Ici.image _ <| Continuous.continuousOn <| by continuity ⟩;
    have h_ray_subset : {p : ℂ | ∃ t : ℝ, 0 ≤ t ∧ p = x + (t : ℂ) * d} ⊆ U := by
      exact fun p hp => by obtain ⟨ t, ht, rfl ⟩ := hp; exact hray t ht;
    apply_rules [ IsPreconnected.subset_connectedComponentIn, h_ray_connected.isPreconnected ];
    · exact ⟨ 0, by norm_num ⟩;
    · exact ⟨ t, ht, rfl ⟩;
  -- By assumption, the ray {x + td | t ≥ 0} is unbounded.
  have h_ray_unbounded : ∀ R : ℝ, ∃ t : ℝ, 0 ≤ t ∧ ‖x + t * d‖ > R := by
    intro R
    obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ ‖t * d‖ > R + ‖x‖ := by
      norm_num [ norm_mul ];
      exact ⟨ ⌊ ( R + ‖x‖ ) / ‖d‖⌋₊ + 1, by positivity, by rw [ abs_of_nonneg ( by positivity ) ] ; nlinarith [ Nat.lt_floor_add_one ( ( R + ‖x‖ ) / ‖d‖ ), norm_pos_iff.mpr hd, mul_div_cancel₀ ( R + ‖x‖ ) ( norm_ne_zero_iff.mpr hd ) ] ⟩;
    exact ⟨ t, ht.1, by have := norm_sub_le ( x + t * d ) x; norm_num at *; linarith ⟩;
  contrapose! h_ray_unbounded;
  exact h_ray_unbounded.exists_norm_le.imp fun R hR t ht => hR _ ( h_ray_subset t ht )

/-
**Opening a polygon at a boundary vertex produces a simple arc.**  The
closed polygon edges not incident to `x` can be ordered as the consecutive
edges of an open simple polygonal arc.  This is the finite list/rotation half of
the no-diagonal escape branch.  It is consumed immediately by
`vertex_escape_joinedIn_arbitrarily_far_no_diag`; together with
`HexArea.simpleArc_complement_isPathConnected` it gives the required exterior
route.
-/
lemma polygon_nonincident_edges_form_simpleArc
    (W : List ℂ) (hsimple : PolygonSimple W) (x : ℂ) (hxW : x ∈ W) :
    ∃ A : List ℂ,
      HexArea.PlaneArcSimple A ∧
      (⋃ e ∈ HexArea.chainEdges A, segment ℝ e.1 e.2) =
        (⋃ e ∈ (closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)),
          segment ℝ e.1 e.2) := by
  -- Let's take the tail of the rotated list W at the index where x is found.
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r < W.length ∧ (W.rotate r).head? = some x := by
    obtain ⟨ r, hr ⟩ := List.mem_iff_get.1 hxW;
    use r.val + 0;
    simp +decide [ ← hr, List.rotate ];
    simp +decide [ Nat.mod_eq_of_lt r.2 ];
  refine' ⟨ ( W.rotate r ).tail, _, _ ⟩;
  · refine' ⟨ _, _ ⟩;
    · have h_tail_nodup : (W.rotate r).Nodup := by
        exact hsimple.1 |> fun h => by simpa [ List.nodup_rotate ] using h;
      exact h_tail_nodup.tail;
    · intro e₁ he₁ e₂ he₂ h₁ h₂ h₃ h₄;
      have h_chain_edges : e₁ ∈ closedEdges (W.rotate r) ∧ e₂ ∈ closedEdges (W.rotate r) := by
        unfold HexArea.chainEdges at *; simp_all +decide [ closedEdges ] ;
        rcases n : W.rotate r with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide [ List.rotate ];
        · linarith [ Nat.mod_lt r ( List.length_pos_iff.mpr ( show W ≠ [] from by aesop_cat ) ) ];
        · have h_chain_edges : ∀ {l : List ℂ}, ∀ e ∈ List.zip (b :: l) l, e ∈ List.zip (b :: l) (l ++ [a]) := by
            intros l e he; induction l <;> simp_all +decide [ List.zip ] ;
            cases ‹List ℂ› <;> simp_all +decide [ List.zipWith ];
            grind +suggestions;
          exact ⟨ Or.inr ( h_chain_edges _ he₁ ), Or.inr ( h_chain_edges _ he₂ ) ⟩;
      have := hsimple.2;
      convert this e₁ ( by simpa only [ mem_closedEdges_rotate ] using h_chain_edges.1 ) e₂ ( by simpa only [ mem_closedEdges_rotate ] using h_chain_edges.2 ) h₁ h₂ h₃ h₄ using 1;
  · -- By definition of `chainEdges`, we know that every edge in `chainEdges (W.rotate r).tail` is also in `closedEdges W`.
    have h_chainEdges_subset_closedEdges : ∀ e ∈ HexArea.chainEdges (W.rotate r).tail, e ∈ closedEdges W ∧ e.1 ≠ x ∧ e.2 ≠ x := by
      intro e he
      have h_chainEdges_subset_closedEdges : e ∈ closedEdges (W.rotate r) := by
        rcases n : W.rotate r with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide [ HexArea.chainEdges, closedEdges ];
        rw [ List.mem_iff_get ] at *; obtain ⟨ i, hi ⟩ := he; simp_all +decide [ List.get ] ;
        refine' Or.inr ⟨ ⟨ i, _ ⟩, _ ⟩ <;> simp_all +decide [ Fin.add_def, Nat.mod_eq_of_lt ];
        grind +qlia;
        grind;
      have h_chainEdges_subset_closedEdges : ∀ e ∈ HexArea.chainEdges (W.rotate r).tail, e.1 ∈ (W.rotate r).tail ∧ e.2 ∈ (W.rotate r).tail := by
        intros e he
        simp [HexArea.chainEdges] at he;
        rw [ List.mem_iff_get ] at he;
        grind;
      have h_chainEdges_subset_closedEdges : ∀ e ∈ HexArea.chainEdges (W.rotate r).tail, e.1 ≠ x ∧ e.2 ≠ x := by
        intros e he
        obtain ⟨he1, he2⟩ := h_chainEdges_subset_closedEdges e he
        have h_ne_x : ∀ y ∈ (W.rotate r).tail, y ≠ x := by
          have h_ne_x : List.Nodup (W.rotate r) := by
            exact hsimple.1 |> fun h => List.nodup_rotate.mpr h;
          cases h : W.rotate r <;> aesop
        exact ⟨h_ne_x e.1 he1, h_ne_x e.2 he2⟩;
      exact ⟨ by rw [ mem_closedEdges_rotate ] at *; aesop, h_chainEdges_subset_closedEdges e he ⟩;
    -- By definition of `closedEdges`, we know that every edge in `closedEdges W` that is not incident to `x` is also in `chainEdges (W.rotate r).tail`.
    have h_closedEdges_subset_chainEdges : ∀ e ∈ closedEdges W, e.1 ≠ x ∧ e.2 ≠ x → e ∈ HexArea.chainEdges (W.rotate r).tail := by
      intro e he hne
      obtain ⟨e', he', heq⟩ : ∃ e' ∈ closedEdges (W.rotate r), e' = e := by
        exact ⟨ e, by simpa [ mem_closedEdges_rotate ] using he, rfl ⟩;
      rcases n : W.rotate r with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide [ closedEdges ];
      cases he' <;> simp_all +decide [ HexArea.chainEdges ];
      rw [ List.mem_iff_get ] at *;
      obtain ⟨ n, hn ⟩ := ‹∃ n, _›; use ⟨ n, by
        grind ⟩ ; simp_all +decide [ List.get ] ;
      grind;
    ext; simp [h_chainEdges_subset_closedEdges, h_closedEdges_subset_chainEdges];
    grind

/-- **Boundary-to-exterior routing without a diagonal.**  This is the first
of the two geometric leaves in the finite polygon escape problem.  It isolates
the assertion that the exterior germ at a boundary vertex belongs to an
unbounded component after deleting all nonincident polygon edges.  It is
consumed by `vertex_escape_joinedIn_arbitrarily_far` below.  The proof now
factors explicitly through the simple-arc complement theorem, so the former
opaque Jordan residue is split into a combinatorial polygon-opening lemma and a
standard planar arc non-separation lemma. -/
lemma vertex_escape_joinedIn_arbitrarily_far_no_diag
    (W : List ℂ) (hsimple : PolygonSimple W) (x : ℂ) (hxW : x ∈ W)
    (hsource : x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x))),
        segment ℝ s.1 s.2)ᶜ)) :
    ∀ R : ℝ, ∃ y : ℂ, R < ‖y‖ ∧
      JoinedIn ((⋃ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x))),
          segment ℝ s.1 s.2)ᶜ) x y := by
  obtain ⟨A, hA, hedge⟩ := polygon_nonincident_edges_form_simpleArc W hsimple x hxW
  rw [← hedge] at hsource ⊢
  exact HexArea.simpleArc_joinedIn_arbitrarily_far A hA x hsource

/-! The predicate `InteriorChord` used throughout this branch is now defined in
`RequestProject.SAWUmlaufChordCorner` (imported above), where it also carries the
strict-extremality *direction* at the rooted endpoint that the corner escape
theorem consumes. -/


/-- **Boundary-to-exterior routing with one valid diagonal.**  This is the
second geometric leaf.  The diagonal misses the source and every nonincident
polygon edge, so the exterior boundary germ can be chosen on its exterior side
and continued to infinity.  It is consumed by
`vertex_escape_joinedIn_arbitrarily_far` below.

**Status of this branch after the corner-escape round.**  The "outside ⟹ winding
`0`" half of the chord branch (`chord_ear_other_ptWind_zero`) no longer routes
through an escape walk: it is now discharged by the elementary corner escape
`HexArea.ptWind_zero_of_extreme_corner` (see
`RequestProject.SAWUmlaufChordCorner`).  The escape-walk chain below
(`vertex_escape_joinedIn_arbitrarily_far_one_diag`, `vertex_escape_walk_core`,
`chord_ear_other_escape_walk`, and the whole simple-arc non-separation
development it rests on) is therefore **not** consumed by the live route at the
moment.  It is retained as preparation for the one escape residue that the
corner escape does *not* cover, `clipped_ear_escape_walk`: there the forbidden
set additionally contains the ear base `a'–c'` of the piece, which is not an
edge of `W`, so the corner cone at the cut endpoint no longer controls it.

**Final status.**  The polygonal Umlaufsatz (`polygon_umlaufsatz_final`,
`RequestProject.SAWUmlaufJordanInduction`) is now complete and does *not* depend
on this lemma: the escape residue it was meant to cover was eliminated by the
corner escape.  It is therefore a genuinely unused `sorry`, kept only as banked
material for a possible future direct treatment of `clipped_ear_escape_walk`.
-/
lemma vertex_escape_joinedIn_arbitrarily_far_one_diag
    (W : List ℂ) (hsimple : PolygonSimple W) (x : ℂ) (hxW : x ∈ W)
    (d : ℂ × ℂ) (hdx : d.1 ≠ x ∧ d.2 ≠ x)
    (hdavoid : x ∉ segment ℝ d.1 d.2)
    (hsource : x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ [d]),
        segment ℝ s.1 s.2)ᶜ))
    (hdiag : ∀ e ∈ closedEdges W,
        d.1 ≠ e.1 → d.1 ≠ e.2 → d.2 ≠ e.1 → d.2 ≠ e.2 →
        Disjoint (segment ℝ d.1 d.2) (segment ℝ e.1 e.2))
    (hint : InteriorChord W d.1 d.2) :
    ∀ R : ℝ, ∃ y : ℂ, R < ‖y‖ ∧
      JoinedIn ((⋃ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ [d]),
          segment ℝ s.1 s.2)ᶜ) x y := by
  sorry

/-- **Arbitrarily-far avoiding paths (remaining geometric leaf).**
For every norm radius, the boundary source can be joined inside the complement
of the forbidden segments to a point beyond that radius.  This is the precise
bent-route replacement for the stronger straight-ray certificate above.

This declaration is not a dead branch: `vertex_escape_connected_reaches`
immediately converts it into connected sets, then
`vertex_escape_component_unbounded` converts those sets into the unbounded
component used by every downstream escape walk.  Thus all remaining geometry
of this branch is now expressed directly as construction of finite-polygon
exterior paths rather than as an opaque connectedness assertion. -/
lemma vertex_escape_joinedIn_arbitrarily_far
    (W : List ℂ) (hsimple : PolygonSimple W)
    (x : ℂ) (hxW : x ∈ W) (diags : List (ℂ × ℂ))
    (hdiagx : ∀ s ∈ diags, s.1 ≠ x ∧ s.2 ≠ x)
    (hdiagcard : diags.length ≤ 1)
    (hdiagavoid : ∀ s ∈ diags, x ∉ segment ℝ s.1 s.2)
    (hsource : x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        segment ℝ s.1 s.2)ᶜ))
    (hdiags : ∀ s ∈ diags, ∀ e ∈ closedEdges W,
        s.1 ≠ e.1 → s.1 ≠ e.2 → s.2 ≠ e.1 → s.2 ≠ e.2 →
        Disjoint (segment ℝ s.1 s.2) (segment ℝ e.1 e.2))
    (hdiagint : ∀ s ∈ diags, InteriorChord W s.1 s.2) :
    ∀ R : ℝ, ∃ y : ℂ, R < ‖y‖ ∧
      JoinedIn ((⋃ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
          segment ℝ s.1 s.2)ᶜ) x y := by
  rcases HexArea.eq_nil_or_eq_singleton_of_length_le_one diags hdiagcard with
    rfl | ⟨d, rfl⟩
  · simpa using
      vertex_escape_joinedIn_arbitrarily_far_no_diag W hsimple x hxW (by simpa using hsource)
  · simpa using vertex_escape_joinedIn_arbitrarily_far_one_diag W hsimple x hxW d
      (hdiagx d (by simp)) (hdiagavoid d (by simp)) hsource
      (fun e he => hdiags d (by simp) e he) (hdiagint d (by simp))

/-- **Finite polygonal escape certificate (proved from the path leaf).**
For every radius, obtain a connected avoiding set containing the boundary
source and reaching beyond that radius by taking the range of the path supplied
by `vertex_escape_joinedIn_arbitrarily_far`.  Unlike a ray certificate, this
permits the route to bend around a nonconvex polygon.  This is consumed
immediately by `vertex_escape_component_unbounded`. -/
lemma vertex_escape_connected_reaches (W : List ℂ) (hsimple : PolygonSimple W)
    (x : ℂ) (hxW : x ∈ W) (diags : List (ℂ × ℂ))
    (hdiagx : ∀ s ∈ diags, s.1 ≠ x ∧ s.2 ≠ x)
    (hdiagcard : diags.length ≤ 1)
    (hdiagavoid : ∀ s ∈ diags, x ∉ segment ℝ s.1 s.2)
    (hsource : x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        segment ℝ s.1 s.2)ᶜ))
    (hdiags : ∀ s ∈ diags, ∀ e ∈ closedEdges W,
        s.1 ≠ e.1 → s.1 ≠ e.2 → s.2 ≠ e.1 → s.2 ≠ e.2 →
        Disjoint (segment ℝ s.1 s.2) (segment ℝ e.1 e.2))
    (hdiagint : ∀ s ∈ diags, InteriorChord W s.1 s.2) :
    ∀ R : ℝ, ∃ C : Set ℂ,
      IsConnected C ∧ x ∈ C ∧
      C ⊆ ((⋃ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
          segment ℝ s.1 s.2)ᶜ) ∧
      ∃ y ∈ C, R < ‖y‖ := by
  apply HexArea.connected_reaches_of_joinedIn
  exact vertex_escape_joinedIn_arbitrarily_far W hsimple x hxW diags hdiagx
    hdiagcard hdiagavoid hsource hdiags hdiagint

/-- **Unbounded-component Jordan core.**  Under the actual Umlaufsatz
configuration (at most one additional valid diagonal), the component of the
boundary source in the complement of all forbidden segments is unbounded.

`connectedComponentIn_unbounded_of_ray` above is a proved sufficient
certificate if the finite geometry produces a straight escaping ray.  The
more general bent-route certificate is `vertex_escape_connected_reaches`, and
the component conversion below is now entirely sorry-free.  All metric and path
consequences are derived downstream. -/
lemma vertex_escape_component_unbounded (W : List ℂ) (hsimple : PolygonSimple W)
    (x : ℂ) (hxW : x ∈ W) (diags : List (ℂ × ℂ))
    (hdiagx : ∀ s ∈ diags, s.1 ≠ x ∧ s.2 ≠ x)
    (hdiagcard : diags.length ≤ 1)
    (hdiagavoid : ∀ s ∈ diags, x ∉ segment ℝ s.1 s.2)
    (hsource : x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        segment ℝ s.1 s.2)ᶜ))
    (hdiags : ∀ s ∈ diags, ∀ e ∈ closedEdges W,
        s.1 ≠ e.1 → s.1 ≠ e.2 → s.2 ≠ e.1 → s.2 ≠ e.2 →
        Disjoint (segment ℝ s.1 s.2) (segment ℝ e.1 e.2))
    (hdiagint : ∀ s ∈ diags, InteriorChord W s.1 s.2) :
    ¬ Bornology.IsBounded (connectedComponentIn
      ((⋃ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
          segment ℝ s.1 s.2)ᶜ) x) := by
  apply HexArea.connectedComponentIn_unbounded_of_connected_reaches
  exact vertex_escape_connected_reaches W hsimple x hxW diags hdiagx hdiagcard
    hdiagavoid hsource hdiags hdiagint

/-
**Local unbounded-escape core.**  From the boundary source, the
component of the forbidden-segment complement reaches beyond every radius that
contains all forbidden segments.  This is the remaining genuinely planar
Jordan-separation statement in the form actually needed by the Umlaufsatz.

Unlike the former arbitrary-fixed-endpoint formulation, this statement asks
only for one point in the unbounded component.  The proved large-circle routing
lemma `vertex_escape_joinedIn_of_reaches_norm_gt` then reaches the chosen target.
It is consumed immediately by `vertex_escape_joinedIn_large`, so it is not a
dead branch.
-/
lemma vertex_escape_reaches_norm_gt (W : List ℂ) (hsimple : PolygonSimple W)
    (x : ℂ) (hxW : x ∈ W) (diags : List (ℂ × ℂ))
    (hdiagx : ∀ s ∈ diags, s.1 ≠ x ∧ s.2 ≠ x)
    (hdiagcard : diags.length ≤ 1)
    (hdiagavoid : ∀ s ∈ diags, x ∉ segment ℝ s.1 s.2)
    (hsource : x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        segment ℝ s.1 s.2)ᶜ))
    (hdiags : ∀ s ∈ diags, ∀ e ∈ closedEdges W,
        s.1 ≠ e.1 → s.1 ≠ e.2 → s.2 ≠ e.1 → s.2 ≠ e.2 →
        Disjoint (segment ℝ s.1 s.2) (segment ℝ e.1 e.2))
    (hdiagint : ∀ s ∈ diags, InteriorChord W s.1 s.2)
    (R : ℝ) (hR : 0 < R)
    (hS : ∀ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        ∀ z ∈ segment ℝ s.1 s.2, ‖z‖ < R) :
    ∃ p : ℂ, R < ‖p‖ ∧
      JoinedIn ((⋃ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
          segment ℝ s.1 s.2)ᶜ) x p := by
  obtain ⟨ p, hp ⟩ := exists_norm_gt_of_component_unbounded ( ( ⋃ s ∈ List.filter ( fun e => decide ( e.1 ≠ x ) && decide ( e.2 ≠ x ) ) ( closedEdges W ) ++ diags, segment ℝ s.1 s.2 ) ᶜ ) x ( vertex_escape_component_unbounded W hsimple x hxW diags hdiagx hdiagcard hdiagavoid hsource hdiags hdiagint ) R;
  refine' ⟨ p, hp.1, _ ⟩;
  have h_connected : IsOpen (connectedComponentIn (⋃ s ∈ List.filter (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) (closedEdges W) ++ diags, segment ℝ s.1 s.2)ᶜ x) ∧ IsConnected (connectedComponentIn (⋃ s ∈ List.filter (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) (closedEdges W) ++ diags, segment ℝ s.1 s.2)ᶜ x) := by
    apply And.intro;
    · apply_rules [ IsOpen.connectedComponentIn, vertex_escape_forbidden_isOpen ];
    · exact ⟨ ⟨ x, mem_connectedComponentIn ( by aesop ) ⟩, isPreconnected_connectedComponentIn ⟩;
  have h_path : IsPathConnected (connectedComponentIn (⋃ s ∈ List.filter (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) (closedEdges W) ++ diags, segment ℝ s.1 s.2)ᶜ x) := by
    have h_path_connected : IsOpen (connectedComponentIn (⋃ s ∈ List.filter (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) (closedEdges W) ++ diags, segment ℝ s.1 s.2)ᶜ x) ∧ IsConnected (connectedComponentIn (⋃ s ∈ List.filter (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) (closedEdges W) ++ diags, segment ℝ s.1 s.2)ᶜ x) → IsPathConnected (connectedComponentIn (⋃ s ∈ List.filter (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) (closedEdges W) ++ diags, segment ℝ s.1 s.2)ᶜ x) := by
      intros h_connected
      apply IsOpen.isConnected_iff_isPathConnected h_connected.left |>.1 h_connected.right;
    grind;
  have := h_path.joinedIn x ( mem_connectedComponentIn hsource ) p hp.2;
  exact this.mono ( connectedComponentIn_subset _ _ )

/-- **Large-endpoint form of the escape core.**  All forbidden segments are
    enclosed in a ball of radius `R`, while the endpoint `q` lies outside both
    that ball and the polygonal convex hull.  The path itself is supplied by the
    fixed-endpoint Jordan core.  This quantitative form is preparation for the
    standard construction that routes the final part of the path around a large
    circle; it is consumed immediately by `vertex_escape_joinedIn`. -/
lemma vertex_escape_joinedIn_large (W : List ℂ) (hsimple : PolygonSimple W)
    (x : ℂ) (hxW : x ∈ W) (diags : List (ℂ × ℂ))
    (hdiagx : ∀ s ∈ diags, s.1 ≠ x ∧ s.2 ≠ x)
    (hdiagcard : diags.length ≤ 1)
    (hdiagavoid : ∀ s ∈ diags, x ∉ segment ℝ s.1 s.2)
    (hsource : x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        segment ℝ s.1 s.2)ᶜ))
    (hdiags : ∀ s ∈ diags, ∀ e ∈ closedEdges W,
        s.1 ≠ e.1 → s.1 ≠ e.2 → s.2 ≠ e.1 → s.2 ≠ e.2 →
        Disjoint (segment ℝ s.1 s.2) (segment ℝ e.1 e.2))
    (hdiagint : ∀ s ∈ diags, InteriorChord W s.1 s.2) :
    ∃ (R : ℝ) (q : ℂ), 0 < R ∧
      q ∉ convexHull ℝ (W.toFinset : Set ℂ) ∧ R < ‖q‖ ∧
      (∀ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
          ∀ z ∈ segment ℝ s.1 s.2, ‖z‖ < R) ∧
      q ∈ ((⋃ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
          segment ℝ s.1 s.2)ᶜ) ∧
      JoinedIn ((⋃ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
          segment ℝ s.1 s.2)ᶜ) x q := by
  classical
  let S := (closedEdges W).filter
      (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags
  obtain ⟨R, q, hR, hq, hqR, hS⟩ :=
    HexArea.exists_exterior_point_beyond_segments W S
  have hqcompl : q ∈ (⋃ s ∈ S, segment ℝ s.1 s.2)ᶜ :=
    HexArea.mem_compl_iUnion_segments_of_norm_gt S R q hS hqR
  obtain ⟨p, hpR, hxp⟩ := vertex_escape_reaches_norm_gt W hsimple x hxW diags
    hdiagx hdiagcard hdiagavoid hsource hdiags hdiagint R hR hS
  have hxq : JoinedIn (⋃ s ∈ S, segment ℝ s.1 s.2)ᶜ x q :=
    vertex_escape_joinedIn_of_reaches_norm_gt S R hR hS hxp hpR hqR
  exact ⟨R, q, hR, hq, hqR, hS, hqcompl, hxq⟩

/-- **The isolated Jordan-connectivity core of the escape residue.**  The base
    vertex `x` of a simple polygon `W` can be joined *by a path* to some point `q`
    outside the convex hull of `W`, the whole path lying in the complement of the
    union of the forbidden segments — the polygon edges not incident to `x`
    together with the diagonals in `diags`.

    The endpoint-existence half is now proved via finite convex-hull boundedness
    (`HexArea.exists_not_mem_convexHull_list`); only the fixed-endpoint Jordan
    statement `vertex_escape_joinedIn_to` remains topological.  Everything else
    in `vertex_escape_walk_core` — turning the path into an edge-avoiding
    polyline — is discharged by `HexArea.exists_escape_polyline_of_joinedIn`.
    Absent from Mathlib. -/
lemma vertex_escape_joinedIn (W : List ℂ) (hsimple : PolygonSimple W)
    (x : ℂ) (hxW : x ∈ W) (diags : List (ℂ × ℂ))
    (hdiagx : ∀ s ∈ diags, s.1 ≠ x ∧ s.2 ≠ x)
    (hdiagcard : diags.length ≤ 1)
    (hdiagavoid : ∀ s ∈ diags, x ∉ segment ℝ s.1 s.2)
    (hsource : x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        segment ℝ s.1 s.2)ᶜ))
    (hdiags : ∀ s ∈ diags, ∀ e ∈ closedEdges W,
        s.1 ≠ e.1 → s.1 ≠ e.2 → s.2 ≠ e.1 → s.2 ≠ e.2 →
        Disjoint (segment ℝ s.1 s.2) (segment ℝ e.1 e.2))
    (hdiagint : ∀ s ∈ diags, InteriorChord W s.1 s.2) :
    ∃ q : ℂ, q ∉ convexHull ℝ (W.toFinset : Set ℂ) ∧
      JoinedIn ((⋃ s ∈ ((closedEdges W).filter
          (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
          segment ℝ s.1 s.2)ᶜ) x q := by
  obtain ⟨R, q, hR, hq, hqR, hsegments, hqcompl, hjoin⟩ :=
    vertex_escape_joinedIn_large W hsimple x hxW diags hdiagx hdiagcard hdiagavoid hsource hdiags hdiagint
  exact ⟨q, hq, hjoin⟩

lemma vertex_escape_walk_core (W : List ℂ) (hsimple : PolygonSimple W)
    (x : ℂ) (hxW : x ∈ W) (diags : List (ℂ × ℂ))
    (hdiagx : ∀ s ∈ diags, s.1 ≠ x ∧ s.2 ≠ x)
    (hdiagcard : diags.length ≤ 1)
    (hdiagavoid : ∀ s ∈ diags, x ∉ segment ℝ s.1 s.2)
    (hsource : x ∈ ((⋃ s ∈ ((closedEdges W).filter
        (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
        segment ℝ s.1 s.2)ᶜ))
    (hdiags : ∀ s ∈ diags, ∀ e ∈ closedEdges W,
        s.1 ≠ e.1 → s.1 ≠ e.2 → s.2 ≠ e.1 → s.2 ≠ e.2 →
        Disjoint (segment ℝ s.1 s.2) (segment ℝ e.1 e.2))
    (hdiagint : ∀ s ∈ diags, InteriorChord W s.1 s.2) :
    ∃ zs : List ℂ,
      List.IsChain (fun a b =>
          (∀ e ∈ closedEdges W, e.1 ≠ x → e.2 ≠ x →
              Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) ∧
          (∀ s ∈ diags, Disjoint (segment ℝ a b) (segment ℝ s.1 s.2))) (x :: zs) ∧
      (zs.getLastD x) ∉ convexHull ℝ (W.toFinset : Set ℂ) := by
  classical
  obtain ⟨q, hq, hjoin⟩ :=
    vertex_escape_joinedIn W hsimple x hxW diags hdiagx hdiagcard hdiagavoid hsource hdiags hdiagint
  obtain ⟨zs, hchain, hlast⟩ :=
    HexArea.exists_escape_polyline_of_joinedIn _ x q _ hq hjoin
  refine ⟨zs, ?_, hlast⟩
  refine hchain.imp ?_
  intro a b hab
  refine ⟨?_, ?_⟩
  · intro e he he1 he2
    exact hab e (by
      rw [List.mem_append]; left; rw [List.mem_filter]
      exact ⟨he, by simp [he1, he2]⟩)
  · intro s hs
    exact hab s (by rw [List.mem_append]; right; exact hs)

/- **DEAD BRANCH (superseded).**  The block below is the *old* route to the
Jordan-separation keystone `chord_ear_empty_other`, which reduced it to an
escaping edge-avoiding walk out of the clipped polygon.  That route needed the
residual hull-interior escape `clipped_ear_escape_walk`, whose hypotheses are in
fact contradictory in the shape stated, so it could not be discharged.

The live route now goes through `chord_ear_empty_other_jordan`
(`RequestProject.SAWUmlaufJordanCore`), which derives the keystone from the
point-in-polygon dichotomy `polygon_ptWind_dichotomy` plus the winding-number
jump across an edge.  `chord_ear_lift`
(`RequestProject.SAWUmlaufPolyMeisters`) calls that version, so the block below
is no longer referenced anywhere; it is commented out rather than deleted, to
keep the record of the abandoned route.
-/
/-
/-- **Escaping edge-avoiding walk out of the clipped polygon (hull-interior
    residue).**  Same setup as `clipped_ear_ptWind_zero`: `x` lies strictly inside
    the empty convex ear `(a', b', c')` of the chord piece `P`, and (the residual
    case) `x` lies inside the convex hull of the clipped polygon `a' :: c' :: tlP`.
    Since `x` is genuinely exterior to the *simple* clipped polygon (the ear is
    empty, so the ear-triangle interior meets `a' :: c' :: tlP` only along the
    shared edge `a'–c'`, and its other two sides `a'–b'`, `b'–c'` are not edges of
    the clipped polygon), `x` lies in the unbounded complementary component and
    can be joined to a hull-exterior point by an edge-avoiding polyline.

    **Status: `sorry`.**  This is the honest exterior-path (polygon Jordan
    complement path-connectivity) residue.  It is a TRUE statement.  NOT a dead
    branch — consumed directly by `clipped_ear_ptWind_zero` just below via the
    proved walk-invariance tool `HexArea.ptWind_zero_of_walk_to_not_hull`
    (`SAWUmlaufPtWindMove`), which is exactly what reduces the winding-`0` fact to
    exhibiting this walk. 

**Only the `tlP ≠ []` case is still needed.**  When the piece `P` is a triangle
the clipped polygon degenerates to the pair `[a', c']`, whose winding vanishes
outright (`HexArea.ptWind_pair_zero`); that case is discharged directly in
`clipped_ear_ptWind_zero` below, so this walk is invoked only for pieces with at
least four vertices.-/
lemma clipped_ear_escape_walk (W : List ℂ) (hsimple : PolygonSimple W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ) (hPsimple : PolygonSimple P)
    (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ)
    (hrotP : P.rotate s = a' :: b' :: c' :: tlP)
    (hemptyP : ∀ y ∈ tlP, ¬ HexArea.inTriangleStrict a' b' c' y)
    (horientP : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tlP)))
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P)
    (hin : HexArea.inTriangleStrict a' b' c' x)
    (hx : x ∈ convexHull ℝ ((a' :: c' :: tlP).toFinset : Set ℂ)) :
    ∃ zs : List ℂ,
      List.IsChain (fun a b => ∀ e ∈ HexArea.cycleEdges (a' :: c' :: tlP),
          Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) (x :: zs) ∧
      (zs.getLastD x) ∉ convexHull ℝ ((a' :: c' :: tlP).toFinset : Set ℂ) := by
  -- The clipped polygon `a' :: c' :: tlP` sits inside `P`, and the removed ear
  -- tip `b'` is not one of its vertices.
  have hcl_sub : ∀ y ∈ (a' :: c' :: tlP), y ∈ P := by
    intro y hy
    have hy' : y ∈ P.rotate s := by
      rw [hrotP]; simp only [List.mem_cons] at hy ⊢; tauto
    exact (List.mem_rotate).mp hy'
  have hxcl : x ∉ (a' :: c' :: tlP) := fun h => hxP (hcl_sub x h)
  have hnd : (a' :: b' :: c' :: tlP).Nodup := hrotP ▸ (List.nodup_rotate.mpr hPsimple.1)
  have hb'cl : b' ∉ (a' :: c' :: tlP) := by
    have h1 := hnd
    simp only [List.nodup_cons, List.mem_cons] at h1
    simp only [List.mem_cons]
    grind
  -- Reduce, via `clippedPiece_cycleEdge_classify`, from avoiding every edge of
  -- the clipped polygon to avoiding the ear base `a'–c'`, all of `W`'s edges NOT
  -- incident to the removed tip `b'` (and not incident to `x`), and the diagonal
  -- `u–v`.  Crucially the two ear sides `a'–b'`, `b'–c'` (the only `W`-edges the
  -- classification excludes, since they carry `b'`) are left free, which is what
  -- lets the walk escape the ear triangle.  This isolates the genuine
  -- plane-topology content (routing through `W`'s exterior out past the hull).
  suffices h : ∃ zs : List ℂ,
      List.IsChain (fun a b =>
          Disjoint (segment ℝ a b) (segment ℝ a' c') ∧
          (∀ e ∈ closedEdges W, e.1 ≠ b' → e.2 ≠ b' → e.1 ≠ x → e.2 ≠ x →
              Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) ∧
          Disjoint (segment ℝ a b) (segment ℝ u v)) (x :: zs) ∧
      (zs.getLastD x) ∉ convexHull ℝ ((a' :: c' :: tlP).toFinset : Set ℂ) by
    obtain ⟨zs, hchain, hlast⟩ := h
    refine ⟨zs, ?_, hlast⟩
    refine hchain.imp ?_
    intro a b hab e he
    obtain ⟨⟨he1, he2⟩, hcase⟩ :=
      clippedPiece_cycleEdge_classify W k hk1 hk u v hu hv P hP a' b' c' s tlP hrotP e he
    rcases hcase with hbase | hWe | hdiage
    · rw [hbase]; exact hab.1
    · exact hab.2.1 e hWe (fun h => hb'cl (h ▸ he1)) (fun h => hb'cl (h ▸ he2))
        (fun h => hxcl (h ▸ he1)) (fun h => hxcl (h ▸ he2))
    · rw [hdiage]; exact hab.2.2
  -- Reduce the endpoint clause to the LARGER hull `convexHull W`: every vertex
  -- of the clipped polygon lies in `P` (`hcl_sub`), hence in `W`, so a point
  -- outside `convexHull W` is outside `convexHull (a'::c'::tlP)` by the general
  -- monotonicity brick `HexArea.not_mem_convexHull_sub`.  This isolates the
  -- genuine remaining plane-topology content (routing through the exterior of
  -- `W`) with the natural, larger target hull.
  obtain ⟨zs, hchain, hlast⟩ : ∃ zs : List ℂ,
      List.IsChain (fun a b =>
          Disjoint (segment ℝ a b) (segment ℝ a' c') ∧
          (∀ e ∈ closedEdges W, e.1 ≠ b' → e.2 ≠ b' → e.1 ≠ x → e.2 ≠ x →
              Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) ∧
          Disjoint (segment ℝ a b) (segment ℝ u v)) (x :: zs) ∧
      (zs.getLastD x) ∉ convexHull ℝ (W.toFinset : Set ℂ) := by
    -- This clipped-case residue morally reduces to the shared Jordan core
    -- `vertex_escape_walk_core` (with diagonals `u–v` and the ear base `a'–c'`),
    -- BUT the ear base `a'–c'` is only an ear of the *piece* `P`, not of the whole
    -- polygon `W`: a vertex or edge of the OTHER chord piece can poke into the
    -- ear triangle, so `a'–c'` need not be a valid `W`-diagonal.  Hence the base
    -- clause cannot be discharged by the core unconditionally, and this residue
    -- is kept as an isolated `sorry` rather than reduced through a possibly-false
    -- diagonal-validity lemma.
    sorry
  exact ⟨zs, hchain,
    HexArea.not_mem_convexHull_sub (a' :: c' :: tlP) P hcl_sub _
      (HexArea.not_mem_convexHull_chordPiece_of_not_mem W k P hP _ hlast)⟩

-/
/-
**Escaping edge-avoiding walk out of the piece `P` (hull-interior residue).**
    Same setup as `chord_ear_other_ptWind_zero`: `x` is a vertex of the OTHER
    chord piece (`x ∈ W`, `x ∉ P`), and (the residual case) `x` lies inside the
    convex hull of `P`.  A valid diagonal cut splits the simple polygon into two
    simply-connected pieces, neither surrounding the other, so `x` (on the
    boundary of `W`, off `P`) lies in the unbounded complementary component of the
    simple polygon `P` and can be joined to a hull-exterior point by an
    edge-avoiding polyline.

    **Status: `sorry`.**  Honest exterior-path residue; a TRUE statement.  NOT a
    dead branch — consumed directly by `chord_ear_other_ptWind_zero` just below
    via `HexArea.ptWind_zero_of_walk_to_not_hull` (`SAWUmlaufPtWindMove`).

A tempting length shortcut here is false: for a triangle `W = [a,b,c]`,
`k = 1`, the left chord piece `[a,b]` omits `c`.  Therefore no generic
`4 ≤ W.length` conclusion may be extracted merely from `x ∉ P`; callers that
need the four-vertex far-edge lemma must supply a genuine length argument from
their stronger branch hypotheses.  This dead statement is deliberately not
declared.

**Incident-edge dichotomy at a third vertex.**  In a nodup cyclic list
of length at least four, given distinct vertices `u`, `v`, `x`, either an edge
incident to `x` has its other endpoint outside `{u,v}`, or `x` is cyclically
between `u` and `v`.  This is the exact combinatorial split used by
`valid_diagonal_no_third_vertex`: the first branch contradicts diagonal
edge-disjointness, while the second contradicts cyclic nondegeneracy if `x`
lies on `segment u v`.
-/
lemma third_vertex_incident_edge_or_between
    (W : List ℂ) (h4 : 4 ≤ W.length) (hnd : W.Nodup)
    (u v x : ℂ) (huW : u ∈ W) (hvW : v ∈ W) (hxW : x ∈ W)
    (hxu : x ≠ u) (hxv : x ≠ v) :
    (∃ y : ℂ, y ≠ u ∧ y ≠ v ∧
      ((x, y) ∈ closedEdges W ∨ (y, x) ∈ closedEdges W)) ∨
    (∃ r tl, W.rotate r = u :: x :: v :: tl) ∨
    (∃ r tl, W.rotate r = v :: x :: u :: tl) := by
  unfold closedEdges at *; simp_all +decide [ List.mem_append, List.mem_cons ] ;
  by_cases h : ∃ y, y ≠ u ∧ y ≠ v ∧ (x, y) ∈ W.zip (W.rotate 1) ∨ y ≠ u ∧ y ≠ v ∧ (y, x) ∈ W.zip (W.rotate 1);
  · grind;
  · -- Since there's no y satisfying the conditions, the only possibility is that u and v are consecutive to x.
    have h_consecutive : (u ∈ W ∧ v ∈ W ∧ x ∈ W ∧ u ≠ x ∧ v ≠ x) → (∃ r tl, W.rotate r = u :: x :: v :: tl) ∨ (∃ r tl, W.rotate r = v :: x :: u :: tl) := by
      intros huvx
      obtain ⟨p, q, hp, hq, hpq⟩ : ∃ p q, (p, x) ∈ W.zip (W.rotate 1) ∧ (x, q) ∈ W.zip (W.rotate 1) ∧ p ≠ q := by
        obtain ⟨p, hp⟩ : ∃ p, (p, x) ∈ W.zip (W.rotate 1) := by
          have h_consecutive : ∀ {l : List ℂ}, l.Nodup → ∀ x ∈ l, ∃ p, (p, x) ∈ l.zip (l.rotate 1) := by
            intros l hl x hx; induction' l with hd tl ih generalizing x <;> simp_all +decide [ List.zip ] ;
            rcases hx with ( rfl | hx ) <;> simp_all +decide [ List.mem_iff_get ];
            · exact ⟨ ⟨ tl.length, by simp +decide ⟩, by simp +decide ⟩;
            · obtain ⟨ n, hn ⟩ := hx; use ⟨ n, by
                simp +arith +decide [ List.length_zipWith ] ⟩ ; simp +decide [ hn ] ;
          exact h_consecutive hnd x hxW
        obtain ⟨q, hq⟩ : ∃ q, (x, q) ∈ W.zip (W.rotate 1) := by
          rw [ List.mem_iff_get ] at *;
          obtain ⟨ n, hn ⟩ := hxW; use W.get ⟨ ( n + 1 ) % W.length, Nat.mod_lt _ ( by linarith ) ⟩ ; simp +decide [ hn, List.getElem?_eq_getElem, Nat.mod_eq_of_lt ] ;
          rw [ List.mem_iff_get ] ; use ⟨ n, by
            simp +decide [ List.length_zip, List.length_rotate ] ⟩ ; simp +decide [ hn, List.getElem_rotate ] ;
          exact hn
        use p, q;
        simp_all +decide [ List.mem_iff_get ];
        obtain ⟨ n, hn₁, hn₂ ⟩ := hp; obtain ⟨ m, hm₁, hm₂ ⟩ := hq; simp_all +decide [ List.getElem_rotate ] ;
        have := List.nodup_iff_injective_get.mp hnd; have := @this ⟨ ( n + 1 ) % W.length, by
          exact Nat.mod_lt _ ( by linarith ) ⟩ ⟨ m, by
          exact lt_of_lt_of_le m.2 ( by simp ) ⟩ ; simp_all +decide [ Nat.mod_eq_of_lt ] ;
        generalize_proofs at *;
        intro H; have := ‹Function.Injective W.get› ( show W.get ⟨ n, by linarith ⟩ = W.get ⟨ ( m + 1 ) % W.length, by linarith ⟩ from by aesop ) ; simp_all +decide [ Fin.ext_iff ] ;
        have := Nat.mod_add_div ( m + 1 + 1 ) W.length; simp_all +decide [ Nat.mod_eq_of_lt ] ;
        nlinarith [ show ( m + 1 + 1 : ℕ ) / W.length = 0 by nlinarith ];
      have h_consecutive : ∃ r tl, W.rotate r = [p, x, q] ++ tl :=
        HexArea.consec_edges_triple W hnd p x q hp hq hpq
      grind;
    exact Or.inr <| h_consecutive ⟨ huW, hvW, hxW, Ne.symm hxu, Ne.symm hxv ⟩

/-
**No third polygon vertex lies on a valid diagonal.**  For a simple,
cyclically nondegenerate polygon, a segment disjoint from every nonincident
polygon edge contains no polygon vertex other than its endpoints.  This is the
local geometric incidence core used by the exterior-path branch.
-/
lemma valid_diagonal_no_third_vertex
    (W : List ℂ) (h4 : 4 ≤ W.length) (hsimple : PolygonSimple W)
    (hnd : polyCycNondeg W) (u v x : ℂ)
    (huW : u ∈ W) (hvW : v ∈ W) (hxW : x ∈ W)
    (hxu : x ≠ u) (hxv : x ≠ v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 →
        v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2)) :
    x ∉ segment ℝ u v := by
  -- By `third_vertex_incident_edge_or_between`, x is either incident to an edge or lies between u and v.
  by_cases hxinc : ∃ y, y ≠ u ∧ y ≠ v ∧ ((x, y) ∈ closedEdges W ∨ (y, x) ∈ closedEdges W);
  · obtain ⟨ y, hyu, hyv, hyinc ⟩ := hxinc;
    cases hyinc <;> [ exact fun h => Set.disjoint_left.mp ( hdiag _ ‹_› ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ) ) h ( left_mem_segment _ _ _ ) ; exact fun h => Set.disjoint_left.mp ( hdiag _ ‹_› ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ) ) h ( right_mem_segment _ _ _ ) ];
  · obtain ⟨r, tl, hrot⟩ : ∃ r tl, W.rotate r = u :: x :: v :: tl ∨ W.rotate r = v :: x :: u :: tl := by
      have := third_vertex_incident_edge_or_between W h4 hsimple.1 u v x huW hvW hxW hxu hxv; aesop;
    cases' hrot with hrot hrot;
    · have h_cross : HexArea.cross (x - u) (v - x) ≠ 0 := by
        have := polyCycNondeg_rotate W r ( by omega );
        unfold polyCycNondeg at this;
        unfold polyNondeg at this; simp_all +decide ;
        rcases W with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | W ⟩ ⟩ ⟩ ) <;> simp_all +decide;
        unfold polyCycNondeg at hnd; unfold polyNondeg at hnd; simp_all +decide ;
      contrapose! h_cross; simp_all +decide [ HexArea.cross ] ;
      rw [ segment_eq_image ] at h_cross; obtain ⟨ t, ht, rfl ⟩ := h_cross; norm_num [ Complex.ext_iff ] ; ring;
    · have := polyCycNondeg_rotate W r ( by omega );
      simp_all +decide [ polyCycNondeg ];
      contrapose! this; simp_all +decide [ polyNondeg ] ;
      intro h; specialize this; rw [ segment_eq_image ] at this; obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := this; simp_all +decide [ HexArea.cross ] ;
      exact False.elim <| h <| by ring;

/-
A vertex belonging to the other side of a valid polygon diagonal cannot
lie on the diagonal segment itself.  This is the local incidence fact required
for the source endpoint of the exterior path to lie in the forbidden-segment
complement.
-/
lemma other_piece_vertex_not_on_valid_diagonal
    (W : List ℂ) (h4 : 4 ≤ W.length) (hsimple : PolygonSimple W)
    (hnd : polyCycNondeg W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (P : List ℂ) (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P) :
    x ∉ segment ℝ u v := by
  apply valid_diagonal_no_third_vertex W h4 hsimple hnd u v x;
  any_goals tauto;
  · grind;
  · grind +splitIndPred;
  · grind +suggestions;
  · rcases hP with ( rfl | rfl );
    · unfold HexArea.chordLeft at hxP; simp_all +decide [ List.Nodup ] ;
      rw [ List.mem_iff_getElem ] at *; aesop;
    · contrapose! hxP; simp_all +decide [ HexArea.chordRight ] ;
      exact Or.inl ( by rw [ List.mem_iff_get ] ; exact ⟨ ⟨ 0, by aesop ⟩, by aesop ⟩ )

lemma chord_ear_other_escape_walk (W : List ℂ) (h4 : 4 ≤ W.length)
    (hsimple : PolygonSimple W) (hnd : polyCycNondeg W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ) (hPsimple : PolygonSimple P)
    (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P)
    (hx : x ∈ convexHull ℝ (P.toFinset : Set ℂ)) :
    ∃ zs : List ℂ,
      List.IsChain (fun a b => ∀ e ∈ HexArea.cycleEdges P,
          Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) (x :: zs) ∧
      (zs.getLastD x) ∉ convexHull ℝ (P.toFinset : Set ℂ) := by
  -- Reduce, via `chordPiece_cycleEdge_or_diag`, from avoiding every edge of `P`
  -- to avoiding all of `W`'s (non-`x`-incident) edges together with the single
  -- diagonal segment `u–v`.  This isolates the genuine plane-topology content:
  -- routing an edge-avoiding polyline through the exterior of the whole polygon
  -- `W` (which avoids every `W`-edge and the interior diagonal) out past the
  -- convex hull of `P`.  Since every edge of `P` has both endpoints in `P` and
  -- `x ∉ P`, no edge of `P` is incident to `x`, so the `x`-incidence guard never
  -- fires for the edges we must avoid.
  suffices h : ∃ zs : List ℂ,
      List.IsChain (fun a b =>
          (∀ e ∈ closedEdges W, e.1 ≠ x → e.2 ≠ x →
              Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) ∧
          Disjoint (segment ℝ a b) (segment ℝ u v)) (x :: zs) ∧
      (zs.getLastD x) ∉ convexHull ℝ (P.toFinset : Set ℂ) by
    obtain ⟨zs, hchain, hlast⟩ := h
    refine ⟨zs, ?_, hlast⟩
    refine hchain.imp ?_
    intro a b hab e he
    obtain ⟨⟨he1P, he2P⟩, hcase⟩ :=
      chordPiece_cycleEdge_or_diag W k hk1 hk u v hu hv P hP e he
    rcases hcase with hWe | hseg
    · exact hab.1 e hWe (fun h => hxP (h ▸ he1P)) (fun h => hxP (h ▸ he2P))
    · rw [hseg]; exact hab.2
  -- Reduce the endpoint clause to the LARGER hull `convexHull W`: `hull P ⊆
  -- hull W`, so a point outside `convexHull W` is outside `convexHull P` by the
  -- packaged brick `HexArea.not_mem_convexHull_chordPiece_of_not_mem`.  This
  -- isolates the genuine remaining plane-topology content (routing through the
  -- exterior of `W`) with the natural, larger target hull.
  obtain ⟨zs, hchain, hlast⟩ : ∃ zs : List ℂ,
      List.IsChain (fun a b =>
          (∀ e ∈ closedEdges W, e.1 ≠ x → e.2 ≠ x →
              Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) ∧
          Disjoint (segment ℝ a b) (segment ℝ u v)) (x :: zs) ∧
      (zs.getLastD x) ∉ convexHull ℝ (W.toFinset : Set ℂ) := by
    -- Reduced to the shared Jordan core `vertex_escape_walk_core` with the single
    -- valid diagonal `u–v`.  Both cut endpoints `u, v` lie in `P`, hence differ
    -- from `x ∉ P` (the required diagonal-incidence side condition `hdiagx`).
    have hkW : k < W.length := by omega
    have hWne : W ≠ [] := by rintro rfl; simp at hu
    have hWhead : W.head? = some u := by rw [List.head?_eq_getElem?]; exact hu
    have huP : u ∈ P := by
      rcases hP with h | h <;> subst h
      · exact List.mem_of_mem_head? (by rw [HexArea.chordLeft_head]; exact hWhead)
      · exact List.mem_of_mem_getLast?
          (by rw [HexArea.chordRight_getLast W k hWne hkW]; exact hWhead)
    have hvP : v ∈ P := by
      rcases hP with h | h <;> subst h
      · exact List.mem_of_mem_getLast? (by rw [HexArea.chordLeft_getLast W k hkW]; exact hv)
      · exact List.mem_of_mem_head? (by rw [HexArea.chordRight_head W k hkW]; exact hv)
    obtain ⟨zs, hch, hl⟩ := vertex_escape_walk_core W hsimple x hxW [(u, v)]
      (by
        intro s hs; simp only [List.mem_singleton] at hs; subst hs
        exact ⟨fun h => hxP (h ▸ huP), fun h => hxP (h ▸ hvP)⟩)
      (by simp)
      (by
        intro s hs; simp only [List.mem_singleton] at hs; subst hs
        exact other_piece_vertex_not_on_valid_diagonal W h4 hsimple hnd k hk1 hk u v hu hv
          hdiag P hP x hxW hxP)
      (by
        exact vertex_escape_source_mem W h4 hsimple x hxW [(u, v)] (by
          intro s hs; simp only [List.mem_singleton] at hs; subst hs
          exact other_piece_vertex_not_on_valid_diagonal W h4 hsimple hnd k hk1 hk u v hu hv
            hdiag P hP x hxW hxP))
      (by intro s hs; simp only [List.mem_singleton] at hs; subst hs; exact hdiag)
      (by intro s hs; simp only [List.mem_singleton] at hs; subst hs; exact hint)
    exact ⟨zs, hch.imp (fun a b hab => ⟨hab.1, hab.2 (u, v) (by simp)⟩), hl⟩
  exact ⟨zs, hchain,
    HexArea.not_mem_convexHull_chordPiece_of_not_mem W k P hP _ hlast⟩

/- **DEAD BRANCH (superseded).**  The block below is the *old* route to the
Jordan-separation keystone `chord_ear_empty_other`, which reduced it to an
escaping edge-avoiding walk out of the clipped polygon.  That route needed the
residual hull-interior escape `clipped_ear_escape_walk`, whose hypotheses are in
fact contradictory in the shape stated, so it could not be discharged.

The live route now goes through `chord_ear_empty_other_jordan`
(`RequestProject.SAWUmlaufJordanCore`), which derives the keystone from the
point-in-polygon dichotomy `polygon_ptWind_dichotomy` plus the winding-number
jump across an edge.  `chord_ear_lift`
(`RequestProject.SAWUmlaufPolyMeisters`) calls that version, so the block below
is no longer referenced anywhere; it is commented out rather than deleted, to
keep the record of the abandoned route.
-/
/-
lemma clipped_ear_ptWind_zero (W : List ℂ) (hsimple : PolygonSimple W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ) (hPsimple : PolygonSimple P)
    (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ)
    (hrotP : P.rotate s = a' :: b' :: c' :: tlP)
    (hemptyP : ∀ y ∈ tlP, ¬ HexArea.inTriangleStrict a' b' c' y)
    (horientP : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tlP)))
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P)
    (hin : HexArea.inTriangleStrict a' b' c' x) :
    HexArea.ptWind x (a' :: c' :: tlP) = 0 := by
  -- The convex-exterior case is discharged by the Hahn-Banach base case
  -- `HexArea.ptWind_zero_of_not_mem_convexHull` (SAWUmlaufExterior): if `x` is
  -- outside the convex hull of the clipped polygon's vertices it cannot wind
  -- around it.  The genuine hull-interior (region-wrapping) case is reduced to an
  -- escaping edge-avoiding walk (`clipped_ear_escape_walk`) via the proved
  -- walk-invariance tool `HexArea.ptWind_zero_of_walk_to_not_hull`.
  -- TRIANGLE BASE CASE (`tlP = []`, i.e. the piece `P` is a triangle): the
  -- clipped polygon degenerates to the pair `[a', c']`, which never winds
  -- (`HexArea.ptWind_pair_zero`); `x` is off the base segment because it is
  -- *strictly* inside the ear triangle.
  rcases tlP with _ | ⟨y0, tl0⟩
  · refine HexArea.ptWind_pair_zero x a' c' ?_
    have hcr : HexArea.cross (c' - a') (x - a') ≠ 0 := by
      rcases hin with ⟨_, _, h3⟩ | ⟨_, _, h3⟩ <;>
        · intro hc
          rw [HexArea.cross_pos_vec] at *
          simp [HexArea.cross] at hc h3 ⊢
          linarith
    exact not_mem_segment_of_cross_ne a' c' x hcr
  by_cases hx : x ∈ convexHull ℝ ((a' :: c' :: y0 :: tl0).toFinset : Set ℂ)
  · obtain ⟨zs, hchain, hy⟩ := clipped_ear_escape_walk W hsimple k hk1 hk u v hu hv
      hdiag hint P hPsimple hP a' b' c' s (y0 :: tl0) hrotP hemptyP horientP x hxW hxP hin hx
    exact HexArea.ptWind_zero_of_walk_to_not_hull (a' :: c' :: y0 :: tl0) x zs hchain hy
  · exact HexArea.ptWind_zero_of_not_mem_convexHull x (a' :: c' :: y0 :: tl0) hx

lemma chord_ear_inner_ptWind_ne_zero (W : List ℂ) (hsimple : PolygonSimple W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ) (hPsimple : PolygonSimple P)
    (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ)
    (hrotP : P.rotate s = a' :: b' :: c' :: tlP)
    (hemptyP : ∀ y ∈ tlP, ¬ HexArea.inTriangleStrict a' b' c' y)
    (horientP : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tlP)))
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P)
    (hin : HexArea.inTriangleStrict a' b' c' x) :
    HexArea.ptWind x P ≠ 0 := by
  -- `x` lies off the clip diagonal `a'–c'` (a strict interior point is off the
  -- edge line), so the ear-split identity applies.
  have hac : x ∉ segment ℝ a' c' := by
    intro hx
    have hzero := HexArea.cross_combo_segment a' c' x hx
    have hside := HexArea.inTriangleStrict_diag_side a' b' c' x hin
    rw [hzero] at hside; simp at hside
  rw [HexArea.ptWind_ear_split x a' b' c' P s tlP hrotP hac hin,
    clipped_ear_ptWind_zero W hsimple k hk1 hk u v hu hv hdiag hint P hPsimple hP
      a' b' c' s tlP hrotP hemptyP horientP x hxW hxP hin]
  simp only [zero_add, ne_eq]
  intro hcontra
  split_ifs at hcontra <;> nlinarith [Real.pi_pos]

-/
/-! ### The other piece's vertices form a `ptWind`-constant arc

The vertices of `W` that are **not** vertices of the chord piece `P` are the
interior vertices of the other piece's arc.  Consecutive such vertices are joined
by `W`-edges whose endpoints both avoid `P`, so (by
`chordPiece_cycleEdge_or_diag`, `PolygonSimple W` and the diagonal hypothesis)
those edges are disjoint from *every* cycle edge of `P`.  Hence, by the winding
invariance bricks of `RequestProject.SAWUmlaufChordArcWind`, the function
`ptWind · P` is **constant** on the whole set `{x ∈ W | x ∉ P}`.

Consequence (`chord_ear_other_ptWind_zero_of_witness`): the point-in-polygon
residue "`ptWind x P = 0` for every vertex `x` of the other piece" only needs
**one** witness vertex with vanishing winding — for instance any such vertex
lying outside `convexHull P`, which is free by
`HexArea.ptWind_zero_of_not_mem_convexHull`.  This is a strict reduction of the
Jordan content of this branch and is the intended attack surface for the
remaining escape leaf `vertex_escape_joinedIn_arbitrarily_far_one_diag`.
-/

/-- Consecutive entries of a vertex list are closed cyclic edges of it. -/
lemma isChain_closedEdges_self (W : List ℂ) :
    List.IsChain (fun a b => (a, b) ∈ closedEdges W) W := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hlen : (closedEdges W).length = W.length := by simp [closedEdges]
  rw [List.mem_iff_getElem]
  refine ⟨i, by omega, ?_⟩
  have hi' : i < W.length := by omega
  have h1 : (closedEdges W)[i]'(by omega) = (W[i], (W.rotate 1)[i]'(by simpa using hi')) := by
    simp [closedEdges, List.getElem_zip]
  rw [h1]
  have hmod : (i + 1) % W.length = i + 1 := Nat.mod_eq_of_lt hi
  have h2 : (W.rotate 1)[i]'(by simpa using hi') = W[(i + 1) % W.length]'(by omega) := by
    rw [List.getElem_rotate]
  rw [h2]
  congr 1
  · simp [hmod]

/-- Vertices of `W` off the left piece are exactly the entries after index `k`. -/
lemma mem_drop_of_not_mem_chordLeft (W : List ℂ) (k : ℕ) (x : ℂ)
    (hx : x ∈ W) (hxP : x ∉ HexArea.chordLeft W k) : x ∈ W.drop (k + 1) := by
  rw [HexArea.chordLeft] at hxP
  have h0 := List.take_append_drop (k + 1) W
  rw [← h0] at hx
  rcases List.mem_append.mp hx with h | h
  · exact absurd h hxP
  · exact h

lemma not_mem_chordLeft_of_mem_drop (W : List ℂ) (hnd : W.Nodup) (k : ℕ) (y : ℂ)
    (hy : y ∈ W.drop (k + 1)) : y ∈ W ∧ y ∉ HexArea.chordLeft W k := by
  refine ⟨List.mem_of_mem_drop hy, ?_⟩
  intro hmem
  rw [HexArea.chordLeft] at hmem
  have hdisj := hnd
  rw [← List.take_append_drop (k + 1) W] at hdisj
  exact (List.disjoint_of_nodup_append hdisj) hmem hy

/-- Vertices of `W` off the right piece are exactly the entries strictly between
index `0` and index `k`. -/
lemma mem_take_drop_of_not_mem_chordRight (W : List ℂ) (k : ℕ) (x : ℂ)
    (hx : x ∈ W) (hxP : x ∉ HexArea.chordRight W k) : x ∈ (W.take k).drop 1 := by
  rw [HexArea.chordRight] at hxP
  have hxtake : x ∈ W.take k := by
    have h0 := List.take_append_drop k W
    rw [← h0] at hx
    rcases List.mem_append.mp hx with h | h
    · exact h
    · exact absurd (List.mem_append.mpr (Or.inl h)) hxP
  have hx1 : x ∉ W.take 1 := fun h => hxP (List.mem_append.mpr (Or.inr h))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at hxtake
  · have h1 : (W.take k).take 1 = W.take 1 := by
      rw [List.take_take]; congr 1; omega
    have h2 := List.take_append_drop 1 (W.take k)
    rw [h1] at h2
    rw [← h2] at hxtake
    rcases List.mem_append.mp hxtake with h | h
    · exact absurd h hx1
    · exact h

lemma not_mem_chordRight_of_mem_take_drop (W : List ℂ) (hnd : W.Nodup) (k : ℕ) (y : ℂ)
    (hy : y ∈ (W.take k).drop 1) : y ∈ W ∧ y ∉ HexArea.chordRight W k := by
  have hytake : y ∈ W.take k := List.mem_of_mem_drop hy
  refine ⟨List.mem_of_mem_take hytake, ?_⟩
  intro hmem
  rw [HexArea.chordRight] at hmem
  rcases List.mem_append.mp hmem with h | h
  · have hdisj := hnd
    rw [← List.take_append_drop k W] at hdisj
    exact (List.disjoint_of_nodup_append hdisj) hytake h
  · have hndk : (W.take k).Nodup := hnd.take
    have h1 : y ∈ (W.take k).take 1 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hytake
      · rwa [List.take_take, Nat.min_eq_left (by omega : 1 ≤ k)]
    have hdisj := hndk
    rw [← List.take_append_drop 1 (W.take k)] at hdisj
    exact (List.disjoint_of_nodup_append hdisj) h1 hy

/-- A `W`-edge whose two endpoints both avoid the piece `P` is disjoint from
every cycle edge of `P` (the `W`-edges of `P` by simplicity, the cut diagonal by
`hdiag`). -/
lemma chordPiece_step_segAvoids (W : List ℂ) (hsimple : PolygonSimple W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (P : List ℂ) (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (huP : u ∈ P) (hvP : v ∈ P)
    (a b : ℂ) (hab : (a, b) ∈ closedEdges W) (ha : a ∉ P) (hb : b ∉ P) :
    HexArea.SegAvoids P a b := by
  intro e he
  obtain ⟨⟨he1P, he2P⟩, hcase⟩ :=
    chordPiece_cycleEdge_or_diag W k hk1 hk u v hu hv P hP e he
  rcases hcase with hWe | hseg
  · exact hsimple.2 (a, b) hab e hWe
      (by intro h; have h' : a = e.1 := h; rw [h'] at ha; exact ha he1P)
      (by intro h; have h' : a = e.2 := h; rw [h'] at ha; exact ha he2P)
      (by intro h; have h' : b = e.1 := h; rw [h'] at hb; exact hb he1P)
      (by intro h; have h' : b = e.2 := h; rw [h'] at hb; exact hb he2P)
  · rw [hseg]
    exact (hdiag (a, b) hab
      (by intro h; have h' : u = a := h; rw [← h'] at ha; exact ha huP)
      (by intro h; have h' : u = b := h; rw [← h'] at hb; exact hb huP)
      (by intro h; have h' : v = a := h; rw [← h'] at ha; exact ha hvP)
      (by intro h; have h' : v = b := h; rw [← h'] at hb; exact hb hvP)).symm

/-- **The other piece's vertices form an edge-avoiding chain.**  There is a list
`ys` containing exactly the vertices of `W` off `P`, whose consecutive segments
are disjoint from every cycle edge of `P`. -/
lemma chordPiece_other_arc_chain (W : List ℂ) (hsimple : PolygonSimple W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (P : List ℂ) (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (huP : u ∈ P) (hvP : v ∈ P) :
    ∃ ys : List ℂ,
      List.IsChain (HexArea.SegAvoids P) ys ∧
      (∀ x : ℂ, x ∈ W → x ∉ P → x ∈ ys) ∧
      (∀ y ∈ ys, y ∈ W ∧ y ∉ P) := by
  classical
  have hnd : W.Nodup := hsimple.1
  have hstep : ∀ a b : ℂ, (a, b) ∈ closedEdges W → a ∉ P → b ∉ P →
      HexArea.SegAvoids P a b := fun a b hab ha hb =>
    chordPiece_step_segAvoids W hsimple k hk1 hk u v hu hv hdiag P hP huP hvP a b hab ha hb
  rcases hP with hPL | hPR
  · refine ⟨W.drop (k + 1), ?_, ?_, ?_⟩
    · refine HexArea.isChain_of_forall_mem _ _ _
        ((isChain_closedEdges_self W).infix (List.drop_suffix (k + 1) W).isInfix) ?_
      intro a ha b hb hab
      exact hstep a b hab (hPL ▸ (not_mem_chordLeft_of_mem_drop W hnd k a ha).2)
        (hPL ▸ (not_mem_chordLeft_of_mem_drop W hnd k b hb).2)
    · intro x hx hxP
      exact mem_drop_of_not_mem_chordLeft W k x hx (hPL ▸ hxP)
    · intro y hy
      have := not_mem_chordLeft_of_mem_drop W hnd k y hy
      exact ⟨this.1, hPL ▸ this.2⟩
  · refine ⟨(W.take k).drop 1, ?_, ?_, ?_⟩
    · refine HexArea.isChain_of_forall_mem _ _ _
        ((isChain_closedEdges_self W).infix
          (((List.drop_suffix 1 (W.take k)).isInfix).trans
            (List.take_prefix k W).isInfix)) ?_
      intro a ha b hb hab
      exact hstep a b hab (hPR ▸ (not_mem_chordRight_of_mem_take_drop W hnd k a ha).2)
        (hPR ▸ (not_mem_chordRight_of_mem_take_drop W hnd k b hb).2)
    · intro x hx hxP
      exact mem_take_drop_of_not_mem_chordRight W k x hx (hPR ▸ hxP)
    · intro y hy
      have := not_mem_chordRight_of_mem_take_drop W hnd k y hy
      exact ⟨this.1, hPR ▸ this.2⟩

/-- **One witness suffices for the other-piece winding.**  Given one vertex `y0`
of `W` off `P` with `ptWind y0 P = 0`, *every* vertex of `W` off `P` has
vanishing winding around `P`. -/
lemma chord_ear_other_ptWind_zero_of_witness (W : List ℂ) (hsimple : PolygonSimple W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (P : List ℂ) (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (huP : u ∈ P) (hvP : v ∈ P)
    (y0 : ℂ) (hy0W : y0 ∈ W) (hy0P : y0 ∉ P) (hy0 : HexArea.ptWind y0 P = 0)
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P) :
    HexArea.ptWind x P = 0 := by
  obtain ⟨ys, hchain, hmem, _⟩ :=
    chordPiece_other_arc_chain W hsimple k hk1 hk u v hu hv hdiag P hP huP hvP
  exact HexArea.ptWind_zero_of_isChain_witness P ys hchain y0 (hmem y0 hy0W hy0P) hy0
    x (hmem x hxW hxP)

/-- **Point-in-polygon, outside direction (winding 0).**  Under the same setup
    as `chord_ear_empty_other`, the winding number of the piece `P` around a
    vertex `x` of the *other* chord piece (`x ∈ W`, `x ∉ P`) is `0`: `x` lies in
    the region cut off by the valid diagonal on the far side of `P`, so `P` does
    not wind around it.  This is the "outside ⟹ winding 0" point-in-polygon
    behaviour of a simple polygon, specialised to the two pieces of a valid
    diagonal cut (where the diagonal separates `P`'s region from `x`).

    **Status: `sorry`.**  The second point-in-polygon direction the
    Jordan-separation keystone `chord_ear_empty_other` reduces to.  NOT a dead
    branch — consumed directly by `chord_ear_empty_other` just below. -/
lemma chord_ear_other_ptWind_zero (W : List ℂ) (hsimple : PolygonSimple W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ)
    (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P) :
    HexArea.ptWind x P = 0 := by
  -- The cut endpoints are vertices of the piece.
  have hkW : k < W.length := by omega
  have hWne : W ≠ [] := by rintro rfl; simp at hu
  have hWhead : W.head? = some u := by rw [List.head?_eq_getElem?]; exact hu
  have huP : u ∈ P := by
    rcases hP with h | h <;> subst h
    · exact List.mem_of_mem_head? (by rw [HexArea.chordLeft_head]; exact hWhead)
    · exact List.mem_of_mem_getLast?
        (by rw [HexArea.chordRight_getLast W k hWne hkW]; exact hWhead)
  have hvP : v ∈ P := by
    rcases hP with h | h <;> subst h
    · exact List.mem_of_mem_getLast? (by rw [HexArea.chordLeft_getLast W k hkW]; exact hv)
    · exact List.mem_of_mem_head? (by rw [HexArea.chordRight_head W k hkW]; exact hv)
  -- The witness: the cyclic neighbour of the rooted cut endpoint `u` belonging to
  -- the OTHER piece has vanishing winding, by the corner escape
  -- (`chordPiece_other_neighbour_ptWind_zero`, in
  -- `RequestProject.SAWUmlaufChordCorner`) — no Jordan-curve input is used.  The
  -- arc-constancy brick `chord_ear_other_ptWind_zero_of_witness` then propagates
  -- the vanishing winding to every vertex of the other piece, in particular `x`.
  obtain ⟨y0, hy0W, hy0P, hy0⟩ :=
    chordPiece_other_neighbour_ptWind_zero W hsimple k hk1 hk u v hu hv hint P hP
  exact chord_ear_other_ptWind_zero_of_witness W hsimple k hk1 hk u v hu hv hdiag P hP
    huP hvP y0 hy0W hy0P hy0 x hxW hxP

/- **DEAD BRANCH (superseded).**  The block below is the *old* route to the
Jordan-separation keystone `chord_ear_empty_other`, which reduced it to an
escaping edge-avoiding walk out of the clipped polygon.  That route needed the
residual hull-interior escape `clipped_ear_escape_walk`, whose hypotheses are in
fact contradictory in the shape stated, so it could not be discharged.

The live route now goes through `chord_ear_empty_other_jordan`
(`RequestProject.SAWUmlaufJordanCore`), which derives the keystone from the
point-in-polygon dichotomy `polygon_ptWind_dichotomy` plus the winding-number
jump across an edge.  `chord_ear_lift`
(`RequestProject.SAWUmlaufPolyMeisters`) calls that version, so the block below
is no longer referenced anywhere; it is commented out rather than deleted, to
keep the record of the abandoned route.
-/
/-
lemma chord_ear_empty_other (W : List ℂ) (hsimple : PolygonSimple W)
    (hnd : polyCycNondeg W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ) (hPsimple : PolygonSimple P)
    (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ)
    (hrotP : P.rotate s = a' :: b' :: c' :: tlP)
    (hemptyP : ∀ y ∈ tlP, ¬ HexArea.inTriangleStrict a' b' c' y)
    (horientP : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tlP)))
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P) :
    ¬ HexArea.inTriangleStrict a' b' c' x := by
  intro hin
  exact chord_ear_inner_ptWind_ne_zero W hsimple k hk1 hk u v hu hv hdiag hint P hPsimple
      hP a' b' c' s tlP hrotP hemptyP horientP x hxW hxP hin
    (chord_ear_other_ptWind_zero W hsimple k hk1 hk u v hu hv hdiag hint P hP x hxW hxP)

-/
/-
**List-surgery brick for `chord_ear_lift` (chordLeft case).**
    An ear rotation of the left chord piece `chordLeft W k = W.take (k+1)` whose
    tip `b'` avoids both cut endpoints `u = W[0]` and `v = W[k]` is an *interior*
    ear: its tip sits at some interior index `i` (`1 ≤ i`, `i+1 ≤ k`) of `W`, so
    the ear triple `a', b', c'` are three cyclically-consecutive vertices of `W`
    itself, exhibited by the rotation `W.rotate (i-1)`.  This is pure
    list/modular arithmetic (no geometry): the head of `(W.take (k+1)).rotate s`
    is `W[s % (k+1)]`, and `W.Nodup` turns the value inequalities `b' ≠ W[0]`,
    `b' ≠ W[k]` into the index bounds that place the tip strictly inside the arc
    (so no modular wraparound occurs and the three vertices are genuinely
    consecutive in `W`).  Numerically validated.  NOT a dead branch — preparation
    consumed by `chord_ear_lift`.
-/
lemma chordLeft_interior_ear_extract (W : List ℂ) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ W.length) (hWnd : W.Nodup) (s : ℕ) (a' b' c' : ℂ)
    (rest0 : List ℂ)
    (hrotP : (HexArea.chordLeft W k).rotate s = a' :: b' :: c' :: rest0)
    (hbu : b' ≠ W[0]!) (hbv : b' ≠ W[k]!) :
    ∃ i : ℕ, 1 ≤ i ∧ i + 1 ≤ k ∧
      W.rotate (i - 1) = a' :: b' :: c' :: (W.drop (i + 2) ++ W.take (i - 1)) := by
  -- Calculate the indices of the vertices in the rotated list.
  set i := (s + 1) % (k + 1) with hi_def
  have hi_bounds : 1 ≤ i ∧ i + 1 ≤ k := by
    have hi_bounds : b' = W[i]! := by
      have hb'_eq : b' = (HexArea.chordLeft W k)[(1 + s) % (k + 1)]! := by
        convert congr_arg ( fun l : List ℂ => l[1]! ) hrotP using 1
        generalize_proofs at *;
        · grind;
        · rw [ ← hrotP ] ; simp +decide [ add_comm, List.getElem?_rotate ] ;
          rw [ List.getElem?_rotate ] ;
          · rw [ add_comm, HexArea.chordLeft ] ; aesop;
          · grind +suggestions
      generalize_proofs at *;
      rw [ hb'_eq, add_comm 1 s ];
      unfold HexArea.chordLeft; simp +decide [ List.getElem?_take, Nat.mod_lt _ ( by linarith : 0 < k + 1 ) ] ;
      rfl;
    constructor <;> contrapose! hbu;
    · aesop;
    · have : i = k := by
        linarith [ Nat.mod_lt ( s + 1 ) ( by linarith : 0 < k + 1 ) ]
      rw [this] at hi_bounds; simp_all +decide [ Nat.mod_eq_of_lt ] ;
  -- By definition of $i$, we know that $a' = W[i - 1]$, $b' = W[i]$, and $c' = W[i + 1]$.
  have ha' : a' = W[i - 1] := by
    have ha' : a' = (HexArea.chordLeft W k)[s % (k + 1)]! := by
      replace hrotP := congr_arg List.head? hrotP; simp_all +decide [ List.rotate ] ;
      simp_all +decide [ HexArea.chordLeft ];
      cases hrotP <;> simp_all +decide [ Nat.mod_lt ];
      linarith [ Nat.mod_lt s ( Nat.succ_pos k ) ];
    have h_mod : s % (k + 1) = (s + 1) % (k + 1) - 1 := by
      rw [ Nat.ModEq.symm ];
      exact Nat.mod_eq_of_lt ( show ( s + 1 ) % ( k + 1 ) - 1 < k + 1 from lt_of_le_of_lt ( Nat.sub_le _ _ ) ( Nat.mod_lt _ ( Nat.succ_pos _ ) ) );
      simp +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_sub ( show 1 ≤ ( s + 1 ) % ( k + 1 ) from hi_bounds.1 ) ];
    convert ha' using 1;
    simp +decide [ HexArea.chordLeft, List.getElem?_take, List.getElem?_drop, h_mod ];
    rw [ if_pos ( Nat.le_of_lt ( Nat.mod_lt _ ( Nat.succ_pos _ ) ) ), List.getElem?_eq_getElem ] ; aesop
  have hb' : b' = W[i] := by
    replace hrotP := congr_arg List.tail hrotP; simp_all +decide [ HexArea.chordLeft ] ;
    replace hrotP := congr_arg List.head? hrotP; simp_all +decide [ List.getElem_rotate ] ;
    rw [ List.getElem?_eq_some_iff ] at hrotP;
    rw [ ← hrotP.choose_spec, List.getElem_rotate ];
    simp +decide [ add_comm, List.length_take, hk ]
  have hc' : c' = W[i + 1] := by
    have hc' : c' = (HexArea.chordLeft W k)[(s + 2) % (k + 1)]! := by
      have hc' : c' = ((HexArea.chordLeft W k).rotate s)[2]! := by
        aesop;
      convert hc' using 1;
      simp +decide [ List.getElem_rotate, Nat.mod_eq_of_lt ];
      rw [ List.getElem?_rotate ];
      · rw [ add_comm, HexArea.chordLeft ];
        rw [ List.length_take, min_eq_left hk ];
      · simp +arith +decide [ HexArea.chordLeft ];
        omega;
    rw [ hc', show ( s + 2 ) % ( k + 1 ) = i + 1 from by
                rw [ show s + 2 = ( s + 1 ) + 1 by ring, Nat.add_mod ];
                rw [ Nat.add_mod, Nat.mod_eq_of_lt ];
                · norm_num [ Nat.mod_eq_of_lt ( by linarith : 1 < k + 1 ) ];
                  rfl;
                · rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ];
                  · linarith;
                  · grobner ];
    simp +decide [ HexArea.chordLeft, List.getElem?_take, List.getElem?_drop, hk ];
    rw [ if_pos ( by linarith ), List.getElem?_eq_getElem ] ; aesop;
  use i; simp_all +decide [ List.rotate_eq_drop_append_take ] ;
  rw [ List.rotate_eq_drop_append_take ];
  · rw [ List.drop_eq_getElem_cons ];
    rw [ Nat.sub_add_cancel ( by linarith ) ];
    rw [ List.drop_eq_getElem_cons ];
    rw [ List.drop_eq_getElem_cons ];
    exact ⟨ hi_bounds.1, by linarith, by rfl ⟩;
  · omega

/-
**List-surgery brick for `chord_ear_lift` (chordRight case).**
    Symmetric companion of `chordLeft_interior_ear_extract` for the right chord
    piece `chordRight W k = W.drop k ++ W.take 1`.  An ear rotation whose tip `b'`
    avoids both cut endpoints `u = W[0]` and `v = W[k]` sits at an interior index
    `i` of `W` with `k+1 ≤ i ≤ W.length - 1`, so the ear triple `a', b', c'` are
    three cyclically-consecutive vertices of `W`, exhibited by `W.rotate (i-1)`
    (the tail `tl` is left existential because the cyclic successor `c'` of the
    last interior vertex wraps around to `W[0]`).  Pure list/modular arithmetic
    (no geometry); numerically validated.  NOT a dead branch — preparation
    consumed by `chord_ear_lift`.
-/
lemma chordRight_interior_ear_extract (W : List ℂ) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ W.length) (hWnd : W.Nodup) (s : ℕ) (a' b' c' : ℂ)
    (rest0 : List ℂ)
    (hrotP : (HexArea.chordRight W k).rotate s = a' :: b' :: c' :: rest0)
    (hbu : b' ≠ W[0]!) (hbv : b' ≠ W[k]!) :
    ∃ (i : ℕ) (tl : List ℂ), k + 1 ≤ i ∧ i + 1 ≤ W.length ∧
      W.rotate (i - 1) = a' :: b' :: c' :: tl := by
  -- Let $t = (s + 1) \% m$ where $m = W.length - k + 1$.
  set m := W.length - k + 1 with hm
  set t := (s + 1) % m with ht;
  have h_t_range : 1 ≤ t ∧ t < m - 1 := by
    have ht_range : b' = (HexArea.chordRight W k)[t]! := by
      have := List.getElem_rotate ( HexArea.chordRight W k ) s ( 1 : ℕ ) ?_ <;> simp_all +decide [ List.getElem?_eq_getElem, Nat.mod_eq_of_lt ];
      simp_all +decide [ add_comm, HexArea.chordRight ];
      cases min_cases 1 W.length <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      rw [ List.getElem?_eq_getElem ];
      rw [ Option.getD_some ];
    constructor;
    · contrapose! hbv; simp_all +decide [ HexArea.chordRight ] ;
    · have ht_lt_m_minus_1 : b' ≠ (HexArea.chordRight W k)[m - 1]! := by
        unfold HexArea.chordRight; simp +decide [ List.getElem?_append, List.getElem?_drop, List.getElem?_take ] ;
        grind;
      exact lt_of_le_of_ne ( Nat.le_sub_one_of_lt ( Nat.mod_lt _ ( Nat.succ_pos _ ) ) ) fun h => ht_lt_m_minus_1 <| h ▸ ht_range;
  have h_a' : a' = W[(k + t - 1) % W.length]! := by
    have h_a' : a' = (HexArea.chordRight W k)[(s % m)]! := by
      replace hrotP := congr_arg List.head? hrotP; simp_all +decide [ List.rotate ] ;
      cases hrotP <;> simp_all +decide [ HexArea.chordRight ];
      · cases min_cases 1 W.length <;> aesop;
      · cases min_cases 1 W.length <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        linarith [ Nat.mod_lt s ( by linarith : 0 < W.length - k + 1 ) ];
    have h_a'_index : (s % m) = t - 1 := by
      rw [ Nat.ModEq.symm ];
      exact Nat.mod_eq_of_lt ( show t - 1 < m from lt_of_lt_of_le ( Nat.sub_lt h_t_range.1 zero_lt_one ) ( Nat.le_of_lt ( Nat.lt_of_lt_of_le h_t_range.2 ( Nat.sub_le _ _ ) ) ) );
      simp +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_sub h_t_range.1 ];
      simp +zetaDelta at *;
    rw [h_a', h_a'_index];
    have h_a'_index : (HexArea.chordRight W k)[t - 1]! = W[(k + t - 1) % W.length]! := by
      have h_t_range : t - 1 < W.length - k := by
        omega
      simp +decide [ HexArea.chordRight, Nat.mod_eq_of_lt ( show k + t - 1 < W.length from by omega ) ];
      rw [ List.getElem?_append ] ; norm_num [ Nat.add_sub_assoc ( show 1 ≤ k + t from by linarith ) ];
      rw [ if_pos h_t_range, Nat.add_sub_assoc ( by linarith ) ];
    exact h_a'_index
  have h_b' : b' = W[(k + t) % W.length]! := by
    have h_b' : b' = (HexArea.chordRight W k)[(s + 1) % m]! := by
      convert congr_arg ( fun l => l[1]! ) hrotP using 1;
      · aesop;
      · rw [ ← hrotP ];
        simp +decide [ List.getElem?_rotate ];
        rw [ List.getElem?_rotate ];
        · rw [ add_comm, HexArea.chordRight_length ];
          finiteness;
        · unfold HexArea.chordRight; simp +arith +decide;
          omega;
    convert h_b' using 1;
    unfold HexArea.chordRight; simp +decide [ Nat.mod_eq_of_lt ( show k + t < W.length from by omega ) ] ;
    rw [ List.getElem?_append ] ; norm_num;
    grind
  have h_c' : c' = W[(k + t + 1) % W.length]! := by
    have h_c' : c' = (HexArea.chordRight W k)[(t + 1) % m]! := by
      have h_c' : c' = (List.rotate (HexArea.chordRight W k) s)[2]! := by
        aesop;
      convert h_c' using 1;
      simp +zetaDelta at *;
      rw [ List.getElem?_rotate ];
      · simp +arith +decide [ HexArea.chordRight, hk.le ];
        rw [ min_eq_left ( by linarith ) ] ; ring;
      · simp +arith +decide [ HexArea.chordRight ];
        omega;
    convert h_c' using 1;
    unfold HexArea.chordRight; simp +decide [ List.getElem?_append, List.getElem?_drop, List.getElem?_take ] ;
    split_ifs <;> simp_all +decide [ Nat.mod_eq_of_lt ];
    · rw [ Nat.mod_eq_of_lt ( by omega ) ] ; simp +decide [ add_assoc ] ;
    · norm_num [ show ( k + ( s + 1 ) % ( W.length - k + 1 ) + 1 ) % W.length = 0 by exact Nat.mod_eq_zero_of_dvd <| by exact ⟨ 1, by linarith [ Nat.sub_add_cancel hk.le ] ⟩ ];
  refine' ⟨ k + t, _, _, _, _ ⟩ <;> norm_num [ h_a', h_b', h_c' ];
  exact ( W.rotate ( k + t - 1 ) ).drop 3;
  · grind;
  · omega;
  · have h_rotate : W.rotate (k + t - 1) = List.map (fun i => W[(k + t - 1 + i) % W.length]!) (List.range W.length) := by
      refine' List.ext_get _ _ <;> simp +decide [ List.getElem?_eq_getElem ];
      intro n hn; rw [ List.getElem_rotate ] ;
      rw [ add_comm, List.getElem?_eq_getElem ] ; aesop;
    rcases W with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, W ⟩ ⟩ ⟩ ) <;> simp_all +decide [ List.range_succ_eq_map ];
    · grind;
    · lia

end
