import Mathlib
import RequestProject.SAWUmlaufPolyBase

/-!
# `SAWUmlaufPolygon`, part `SAWUmlaufPolyChord`

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

/-! ### Interior-diagonal split: reusable simplicity/non-degeneracy bricks

These were previously stranded in `SAWUmlaufChordSplit` (which imports this
file), so they were unusable by the open Meisters branches below.  They are
moved here, before the branches, so the interior-diagonal split can consume
them.  They are purely combinatorial packaging: a split piece is a sub-path of
the parent polygon closed by the single cut diagonal. -/

namespace HexArea

/-- The **non-cyclic** (path) edges of a vertex list `P`: the consecutive pairs
    `(P₀,P₁), …, (P_{n-1},P_n)`, omitting the wrap-around edge.  The cyclic edges
    are `pathEdges P ++ [(last, head)]` (`closedEdges_eq_pathEdges`). -/
def pathEdges (P : List ℂ) : List (ℂ × ℂ) := P.zip P.tail

@[simp] lemma pathEdges_nil : pathEdges ([] : List ℂ) = [] := rfl
@[simp] lemma pathEdges_singleton (a : ℂ) : pathEdges [a] = [] := rfl

lemma pathEdges_cons_cons (a b : ℂ) (rest : List ℂ) :
    pathEdges (a :: b :: rest) = (a, b) :: pathEdges (b :: rest) := by
  simp [pathEdges]

/-- `(p :: rest).rotate 1 = rest ++ [p]`. -/
lemma rotate_one_cons (p : ℂ) (rest : List ℂ) :
    (p :: rest).rotate 1 = rest ++ [p] := by
  rw [List.rotate_cons_succ]; simp

/-- **Cyclic edges = path edges plus the closing chord.** -/
lemma closedEdges_eq_pathEdges (P : List ℂ) (u v : ℂ)
    (hhead : P.head? = some u) (hlast : P.getLast? = some v) :
    closedEdges P = pathEdges P ++ [(v, u)] := by
  rcases P with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide [ pathEdges ];
  · unfold closedEdges; aesop;
  · induction l generalizing u y <;> simp_all +decide [ closedEdges ]

/-- **Membership in path edges implies membership in cyclic edges.** -/
lemma mem_closedEdges_of_mem_pathEdges (P : List ℂ) (e : ℂ × ℂ)
    (he : e ∈ pathEdges P) : e ∈ closedEdges P := by
  rcases P with ( _ | ⟨ a, _ | ⟨ b, P ⟩ ⟩ ) <;> simp_all +decide [ pathEdges, closedEdges ];
  have h_zip_append : ∀ (l r1 r2 : List ℂ), List.zip l (r1 ++ r2) = List.zip l r1 ++ List.zip (List.drop r1.length l) r2 := by
    intros l r1 r2; induction' l with hd tl hl generalizing r1 r2 <;> cases r1 <;> cases r2 <;> simp +decide [ * ] ;
  grind

/-- **Simplicity from a simple path plus a clear closing chord.** -/
lemma PolygonSimple_of_simplePath (P : List ℂ) (u v : ℂ)
    (hhead : P.head? = some u) (hlast : P.getLast? = some v)
    (hnodup : P.Nodup)
    (hpath : ∀ e₁ ∈ pathEdges P, ∀ e₂ ∈ pathEdges P,
        e₁.1 ≠ e₂.1 → e₁.1 ≠ e₂.2 → e₁.2 ≠ e₂.1 → e₁.2 ≠ e₂.2 →
        Disjoint (segment ℝ e₁.1 e₁.2) (segment ℝ e₂.1 e₂.2))
    (hdiag : ∀ e ∈ pathEdges P,
        v ≠ e.1 → v ≠ e.2 → u ≠ e.1 → u ≠ e.2 →
        Disjoint (segment ℝ v u) (segment ℝ e.1 e.2)) :
    PolygonSimple P := by
  refine' ⟨ hnodup, _ ⟩;
  rw [ closedEdges_eq_pathEdges P u v hhead hlast ];
  grind

/-- **Cyclic non-degeneracy from path non-degeneracy plus two seam corners.** -/
lemma polyCycNondeg_of_path (P : List ℂ) (u u2 v vp : ℂ)
    (h3 : 3 ≤ P.length)
    (hu : P.head? = some u) (hu2 : P[1]? = some u2)
    (hv : P.getLast? = some v) (hvp : P.dropLast.getLast? = some vp)
    (hpath : polyNondeg P)
    (hseam1 : HexArea.cross (v - vp) (u - v) ≠ 0)
    (hseam2 : HexArea.cross (u - v) (u2 - u) ≠ 0) :
    polyCycNondeg P := by
  obtain ⟨a, b, c, rest, hP⟩ : ∃ a b c : ℂ, ∃ rest : List ℂ, P = a :: b :: c :: rest := by
    rcases P with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | P ⟩ ⟩ ⟩ ) <;> simp_all +decide;
  simp_all +decide [ polyCycNondeg ];
  have h_polyNondeg : ∀ (L : List ℂ), polyNondeg L → ∀ (x y : ℂ), HexArea.cross (L.getLast! - L.dropLast.getLast!) (x - L.getLast!) ≠ 0 → HexArea.cross (x - L.getLast!) (y - x) ≠ 0 → polyNondeg (L ++ [x, y]) := by
    intros L hL x y hx hy; induction' L with a L ih generalizing x y <;> simp_all +decide [ polyNondeg_cons_cons_cons ] ;
    rcases L with ( _ | ⟨ b, _ | ⟨ c, L ⟩ ⟩ ) <;> simp_all +decide [ polyNondeg_cons_cons_cons ];
  convert h_polyNondeg ( u :: u2 :: c :: rest ) hpath u u2 _ _ using 1 <;> simp_all +decide [ List.getLast? ]

/-! #### Edge inheritance for the chord-split pieces (preparation for
`meisters_reduction_interior2`).  Each split piece's path edges are cyclic edges
of the parent polygon, so the piece inherits `PolygonSimple`'s edge-disjointness
verbatim.  These bricks plus the geometric diagonal clearance feed
`PolygonSimple_of_simplePath`. -/

/-
A path edge of a prefix `V.take m` is a path edge of `V`.
-/
lemma mem_pathEdges_take (V : List ℂ) (m : ℕ) (e : ℂ × ℂ)
    (he : e ∈ pathEdges (V.take m)) : e ∈ pathEdges V := by
  induction' m with m ih generalizing V;
  · cases he;
  · rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ pathEdges_cons_cons ];
    cases m <;> simp_all +decide [ pathEdges_cons_cons ];
    cases he <;> simp_all +decide [ pathEdges_cons_cons ]

/-
Every path edge of the left split piece `chordLeft V k` is a cyclic edge of
    the whole polygon `V`.
-/
lemma pathEdges_chordLeft_mem_closedEdges (V : List ℂ) (k : ℕ) (e : ℂ × ℂ)
    (he : e ∈ pathEdges (chordLeft V k)) : e ∈ closedEdges V := by
  apply mem_closedEdges_of_mem_pathEdges;
  apply mem_pathEdges_take;
  convert he using 1

/-
Every path edge of the right split piece `chordRight V k` is a cyclic edge of
    the whole polygon `V`.
-/
lemma pathEdges_chordRight_mem_closedEdges (V : List ℂ) (k : ℕ) (hk : k < V.length)
    (e : ℂ × ℂ) (he : e ∈ pathEdges (chordRight V k)) : e ∈ closedEdges V := by
  induction' k with k ih generalizing V;
  · rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ chordRight ];
    · cases he;
      · simp +decide [ closedEdges ];
      · contradiction;
    · induction' V with V ih generalizing a b;
      · unfold pathEdges closedEdges at * ; aesop;
      · cases ih <;> simp_all +decide [ pathEdges, closedEdges ];
        grind;
  · rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ chordRight ];
    grind +suggestions

/-
**Left split piece is simple** given the cut-diagonal clearance.  Preparation
    for `meisters_reduction_interior2`: combined with the geometric clearance of
    the cut diagonal `V[k]–V[0]`, the left piece `V₀,…,V_k` is a `PolygonSimple`
    sub-polygon.
-/
lemma chordLeft_PolygonSimple (V : List ℂ) (k : ℕ) (v0 vk : ℂ)
    (hk2 : 2 ≤ k) (hk : k + 1 ≤ V.length)
    (hsimple : PolygonSimple V)
    (hv0 : V.head? = some v0) (hvk : V[k]? = some vk)
    (hclear : ∀ e ∈ pathEdges (chordLeft V k),
        vk ≠ e.1 → vk ≠ e.2 → v0 ≠ e.1 → v0 ≠ e.2 →
        Disjoint (segment ℝ vk v0) (segment ℝ e.1 e.2)) :
    PolygonSimple (chordLeft V k) := by
  apply PolygonSimple_of_simplePath (chordLeft V k) v0 vk;
  · convert hv0 using 1;
    convert chordLeft_head V k;
  · grind +suggestions;
  · exact List.Nodup.sublist ( List.take_sublist _ _ ) hsimple.1;
  · exact fun e₁ he₁ e₂ he₂ h₁ h₂ h₃ h₄ => hsimple.2 e₁ ( pathEdges_chordLeft_mem_closedEdges V k e₁ he₁ ) e₂ ( pathEdges_chordLeft_mem_closedEdges V k e₂ he₂ ) h₁ h₂ h₃ h₄;
  · assumption

/-
**Right split piece is simple** given the cut-diagonal clearance.  Preparation
    for `meisters_reduction_interior2`.
-/
lemma chordRight_PolygonSimple (V : List ℂ) (k : ℕ) (v0 vk : ℂ)
    (hk1 : 1 ≤ k) (hk : k < V.length)
    (hsimple : PolygonSimple V)
    (hv0 : V.head? = some v0) (hvk : V[k]? = some vk)
    (hclear : ∀ e ∈ pathEdges (chordRight V k),
        v0 ≠ e.1 → v0 ≠ e.2 → vk ≠ e.1 → vk ≠ e.2 →
        Disjoint (segment ℝ v0 vk) (segment ℝ e.1 e.2)) :
    PolygonSimple (chordRight V k) := by
  apply PolygonSimple_of_simplePath;
  rotate_left;
  rotate_left;
  exact chordRight_nodup V k hk1 hk hsimple.1;
  rotate_left;
  convert hclear using 1;
  · unfold chordRight; aesop;
  · grind +suggestions;
  · intros e₁ he₁ e₂ he₂ hne₁ hne₂ hne₃ hne₄;
    apply hsimple.2 e₁ (pathEdges_chordRight_mem_closedEdges V k hk e₁ he₁) e₂ (pathEdges_chordRight_mem_closedEdges V k hk e₂ he₂) hne₁ hne₂ hne₃ hne₄

/-! #### Non-degeneracy inheritance for the chord-split pieces (companion to the
simplicity bricks; preparation for `meisters_reduction_interior2`).  A contiguous
infix of a path keeps all its consecutive-triple non-flatness, so each split
piece's path triples are inherited; the only new corners are the two seams at the
cut diagonal's endpoints. -/

/-
`polyNondeg` is inherited by any prefix.
-/
lemma polyNondeg_take (V : List ℂ) (m : ℕ) (h : polyNondeg V) :
    polyNondeg (V.take m) := by
  induction' n : V.length with n ih generalizing V m;
  · cases V <;> aesop;
  · rcases m with ( _ | _ | _ | m ) <;> rcases V with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, V ⟩ ⟩ ⟩ ) <;> simp_all +decide [ polyNondeg_cons_cons_cons ];
    convert ih ( b :: c :: V ) ( m + 2 ) h.2 ( by simp +arith +decide [ n.symm ] ) using 1

/-
`polyNondeg` is inherited by any suffix.
-/
lemma polyNondeg_drop (V : List ℂ) (k : ℕ) (h : polyNondeg V) :
    polyNondeg (V.drop k) := by
  induction' k with k ih generalizing V;
  · simpa;
  · rcases V with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, V ⟩ ⟩ ⟩ ) <;> simp_all +decide [ polyNondeg_cons_cons_cons ]

/-
**Left split piece is cyclically non-degenerate** given the two seam corners
    at the cut-diagonal endpoints.  Preparation for
    `meisters_reduction_interior2`.
-/
lemma chordLeft_polyCycNondeg (V : List ℂ) (k : ℕ) (v0 v1 vk vkm1 : ℂ)
    (hk2 : 2 ≤ k) (hk : k + 1 ≤ V.length)
    (hnd : polyCycNondeg V)
    (hv0 : V.head? = some v0) (hv1 : V[1]? = some v1)
    (hvk : V[k]? = some vk) (hvkm1 : V[k-1]? = some vkm1)
    (hseam1 : HexArea.cross (vk - vkm1) (v0 - vk) ≠ 0)
    (hseam2 : HexArea.cross (v0 - vk) (v1 - v0) ≠ 0) :
    polyCycNondeg (chordLeft V k) := by
  convert polyCycNondeg_of_path ( chordLeft V k ) v0 v1 vk vkm1 _ _ _ _ _ _ using 1;
  grind +splitIndPred;
  all_goals norm_num [ chordLeft ];
  grind;
  · cases V <;> aesop;
  · grind;
  · grind;
  · grind +splitImp;
  · convert polyNondeg_take _ _ hnd using 1;
    rw [ List.take_append_of_le_length ] ; omega

/-
**Right split piece is cyclically non-degenerate** given the two seam corners
    at the cut-diagonal endpoints.  Preparation for
    `meisters_reduction_interior2`.
-/
lemma chordRight_polyCycNondeg (V : List ℂ) (k : ℕ) (v0 vk vk1 vlast : ℂ)
    (hk1 : 1 ≤ k) (hk : k + 2 ≤ V.length)
    (hnd : polyCycNondeg V)
    (hv0 : V.head? = some v0) (hvk : V[k]? = some vk)
    (hvk1 : V[k+1]? = some vk1) (hvlast : V[V.length-1]? = some vlast)
    (hseam1 : HexArea.cross (v0 - vlast) (vk - v0) ≠ 0)
    (hseam2 : HexArea.cross (vk - v0) (vk1 - vk) ≠ 0) :
    polyCycNondeg (chordRight V k) := by
  convert polyCycNondeg_of_path ( chordRight V k ) vk vk1 v0 vlast _ _ _ _ _ _ _ using 1;
  all_goals norm_num [ chordRight, List.drop_append, List.take_append, hk1, hk ];
  any_goals omega;
  exact Or.inl hseam2;
  · exact Or.inl hvk;
  · grind;
  · cases V <;> aesop;
  · grind;
  · convert polyNondeg_take ( V.drop k ++ V.take 2 ) ( V.length - k + 1 ) _ using 1;
    · rcases V with ( _ | ⟨ x, _ | ⟨ y, V ⟩ ⟩ ) <;> simp_all +decide [ List.take_append ];
    · convert polyNondeg_drop ( V ++ V.take 2 ) k _ using 1;
      · simp +arith +decide [ List.drop_append, List.take_append ];
        rw [ Nat.sub_eq_zero_of_le ( by linarith ) ] ; norm_num;
      · exact hnd

/-
**Cyclic-edge localization to a chord piece (combinatorial brick).**
    Every cyclic edge `e` of the polygon `V` is a *path edge* of exactly one of
    the two chord pieces `chordLeft V k` / `chordRight V k` of the diagonal
    `V[0]–V[k]`.  Indeed the closed edges of `V` are the consecutive pairs
    `(V[i], V[i+1])` for `i < n-1` together with the wrap edge `(V[n-1], V[0])`;
    the left piece's path edges are the pairs with `i < k`, and the right piece's
    path edges are the pairs with `k ≤ i < n-1` together with the wrap edge.
    Pure list surgery; preparation for the ear-lift step of
    `meisters_reduction_interior2` (the forbidden cyclic edge `{z1, z2}` lands
    entirely inside one chord piece, so the recursion runs on the other piece).
    Not yet consumed by another declaration only because the lift it feeds is
    still open — recorded partial progress, not a dead branch.
-/
lemma closedEdge_mem_chord_pathEdges (V : List ℂ) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ V.length)
    (e : ℂ × ℂ) (he : e ∈ closedEdges V) :
    e ∈ pathEdges (HexArea.chordLeft V k)
      ∨ e ∈ pathEdges (HexArea.chordRight V k) := by
  -- By definition of closedEdges, e is either a pair (V[i], V[(i+1) % V.length]) for some i < V.length.
  obtain ⟨i, hi⟩ : ∃ i < V.length, e = (V[i]!, V[(i + 1) % V.length]!) := by
    have h_zip : e ∈ List.zip V (V.rotate 1) := by
      exact he;
    rw [ List.mem_iff_get ] at h_zip;
    rcases h_zip with ⟨ n, rfl ⟩ ; use n; rcases n with ( _ | n ) <;> simp_all +decide [ List.get ] ;
    · rcases V with ( _ | ⟨ x, _ | ⟨ y, V ⟩ ⟩ ) <;> simp_all +decide [ List.rotate ];
    · grind +suggestions;
  by_cases h : i < k <;> simp_all +decide [ chordLeft, chordRight ];
  · left; simp [pathEdges, List.take] at *; (
    rw [ List.mem_iff_getElem ] ; simp_all +decide [ List.getElem?_take ] ;
    simp_all +decide [ Nat.mod_eq_of_lt ( by linarith : i + 1 < V.length ) ];
    exact ⟨ i, h, rfl, by rw [ List.getElem?_eq_getElem ( by linarith ) ] ; rfl ⟩);
  · have h_pair : (V[i], V[(i + 1) % V.length]?.getD default) ∈ pathEdges (List.drop k V ++ List.take 1 V) := by
      have h_pair : ∃ j < (List.drop k V ++ List.take 1 V).length - 1, (V[i], V[(i + 1) % V.length]?.getD default) = ((List.drop k V ++ List.take 1 V)[j]!, (List.drop k V ++ List.take 1 V)[j + 1]!) := by
        by_cases h : i + 1 < V.length <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        · refine' ⟨ i - k, _, _, _ ⟩ <;> norm_num [ List.getElem?_append, List.getElem?_drop, List.getElem?_take ];
          · omega;
          · grind;
          · grind;
        · cases h.eq_or_lt <;> first | linarith | simp_all +decide [ Nat.mod_eq_of_lt ] ;
          use i - k;
          grind
      obtain ⟨ j, hj₁, hj₂ ⟩ := h_pair; rw [ hj₂ ] ; simp +decide [ pathEdges ] ;
      rw [ List.mem_iff_getElem ] ; simp +decide [ List.getElem_zip ] ;
      grind;
    exact Or.inr h_pair

/-- **`IsCycEdge` is rotation invariant.**  A pair `{x, y}` is a cyclic edge of
    `V.rotate n` iff it is a cyclic edge of `V`.  Immediate from
    `mem_closedEdges_rotate` applied to both orderings.  Reusable preparation for
    `meisters_reduction_interior2` / `empty_branch_bad_lift`: it transports the
    forbidden cyclic edge `{z1, z2}` of `V` across the rotation
    `V.rotate r = a :: b :: c :: rest`. -/
lemma IsCycEdge_rotate (V : List ℂ) (n : ℕ) (x y : ℂ) :
    IsCycEdge (V.rotate n) x y ↔ IsCycEdge V x y := by
  unfold IsCycEdge
  rw [mem_closedEdges_rotate, mem_closedEdges_rotate]

/-- **Endpoints of a cyclic edge are vertices.**  If `{x, y}` is a cyclic edge
    of `V` then both `x` and `y` are vertices of `V`.  Pure combinatorial
    bookkeeping (a closed edge `V.zip (V.rotate 1)` has both coordinates in `V`).
    Sorry-free, reusable preparation for the diagonal-split recursion
    (`meisters_reduction_interior2` / `empty_branch_bad_lift`): the forbidden
    pair handed to `IH2` must be shown to be genuine vertices of the cycle. -/
lemma IsCycEdge_mem (V : List ℂ) (x y : ℂ) (h : IsCycEdge V x y) :
    x ∈ V ∧ y ∈ V := by
  have hsub : ∀ p : ℂ × ℂ, p ∈ closedEdges V → p.1 ∈ V ∧ p.2 ∈ V := by
    intro p hp
    rw [closedEdges] at hp
    have h1 := List.of_mem_zip hp
    refine ⟨h1.1, ?_⟩
    have := h1.2
    rwa [List.mem_rotate] at this
  rcases h with h | h
  · exact hsub _ h
  · exact (hsub _ h).symm

/-- **Rotating the corner-rooted cycle by one step.**  From
    `V.rotate r = a :: b :: c :: rest` we get
    `V.rotate (r + 1) = b :: c :: rest ++ [a]`, the `b`-rooted cycle `W` used by
    the interior diagonal split.  Sorry-free, reusable preparation for
    `meisters_reduction_interior2`: it is the rotation identity
    `W = V.rotate (r+1)` that lets `IsCycEdge_rotate` and `forbidden_lands_in_chord`
    transfer the forbidden edge from `V` to `W`. -/
lemma rotate_corner_succ (V : List ℂ) (r : ℕ) (a b c : ℂ) (rest : List ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest) :
    V.rotate (r + 1) = b :: c :: rest ++ [a] := by
  rw [← List.rotate_rotate, hrot]
  simp [List.rotate_cons_succ]

/-- **The forbidden cyclic edge lands in one of the two chord pieces.**  Given a
    cyclic edge `{z1, z2}` of `V` and a chord cut index `k` (with `1 ≤ k` and
    `k + 1 ≤ V.length`), the pair `{z1, z2}` is a cyclic edge of the left piece
    `chordLeft V k` or of the right piece `chordRight V k`.  This is the
    combinatorial "forbidden pair lies in one piece" step of the interior /
    bad-diagonal split branches: it lets the split-and-recurse induction choose
    the piece **not** containing `{z1, z2}` to recurse on.  Assembled from
    `closedEdge_mem_chord_pathEdges` (every closed edge of `V` is a path edge of
    a piece) and `mem_closedEdges_of_mem_pathEdges` (a path edge is a closed
    edge), handling both orderings of the pair.  Sorry-free; reusable
    preparation for `meisters_reduction_interior2` / `empty_branch_bad_lift`. -/
lemma forbidden_lands_in_chord (V : List ℂ) (k : ℕ) (z1 z2 : ℂ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ V.length) (he : IsCycEdge V z1 z2) :
    IsCycEdge (HexArea.chordLeft V k) z1 z2 ∨
      IsCycEdge (HexArea.chordRight V k) z1 z2 := by
  unfold IsCycEdge at he ⊢
  rcases he with he | he
  · rcases closedEdge_mem_chord_pathEdges V k hk1 hk (z1, z2) he with hL | hR
    · exact Or.inl (Or.inl (mem_closedEdges_of_mem_pathEdges _ _ hL))
    · exact Or.inr (Or.inl (mem_closedEdges_of_mem_pathEdges _ _ hR))
  · rcases closedEdge_mem_chord_pathEdges V k hk1 hk (z2, z1) he with hL | hR
    · exact Or.inl (Or.inr (mem_closedEdges_of_mem_pathEdges _ _ hL))
    · exact Or.inr (Or.inr (mem_closedEdges_of_mem_pathEdges _ _ hR))

/-
**Consecutive cyclic edges determine the triple in a nodup cycle.**  In a
    `Nodup` cyclic vertex list `W`, if `(a', b')` and `(b', c')` are both cyclic
    edges of `W` (sharing the middle vertex `b'`) and `a' ≠ c'`, then
    `a', b', c'` are three *consecutive* vertices of `W`: some rotation of `W`
    has them as its first three entries.  Reason: in a `Nodup` cycle every
    vertex occurs once, so its predecessor and successor (read off the two
    incident closed edges) are uniquely determined; the rotation bringing `a'`
    to the front then exhibits `a' :: b' :: c'`.  Sorry-free preparation for the
    chord-piece ear lift of `meisters_reduction_interior2`.
-/
lemma consec_edges_triple (W : List ℂ) (hnodup : W.Nodup) (a' b' c' : ℂ)
    (hab : (a', b') ∈ closedEdges W) (hbc : (b', c') ∈ closedEdges W)
    (hac : a' ≠ c') :
    ∃ r' tl, W.rotate r' = a' :: b' :: c' :: tl := by
  -- From `(a', b') ∈ closedEdges W`, obtain `i < n` (where `n = W.length`) with `W[i]? = some a'` and `W[(i+1) % n]? = some b'`.
  obtain ⟨i, hi, hia', hib'⟩ : ∃ i < W.length, W[i]? = some a' ∧ W[(i + 1) % W.length]? = some b' := by
    have h_zip : (a', b') ∈ W.zip (W.rotate 1) := by
      exact hab;
    obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 h_zip; simp_all +decide [ List.getElem_rotate ] ;
    exact ⟨ i, Nat.lt_of_lt_of_le i.2 ( by simp ), by aesop ⟩;
  -- From `(b',c') ∈ closedEdges W`, obtain `j < n` with `W[j]? = some b'` and `W[(j+1) % n]? = some c'`.
  obtain ⟨j, hj, hjb', hjc'⟩ : ∃ j < W.length, W[j]? = some b' ∧ W[(j + 1) % W.length]? = some c' := by
    unfold closedEdges at hbc;
    rw [ List.mem_iff_get ] at hbc;
    rcases hbc with ⟨ n, hn ⟩ ; use n; simp_all +decide [ List.get ] ;
    grind +suggestions;
  -- Since `W` is `Nodup` and `W[(i+1)%n]? = some b' = W[j]?`, index-uniqueness gives `(i+1) % n = j`.
  have hmod : (i + 1) % W.length = j := by
    grind +suggestions;
  -- The list `W.rotate i` has length `n`; its `m`-th entry (for `m < n`) is `W[(i+m) % n]`.
  -- In particular its first three entries are `W[i] = a'`, `W[(i+1)%n] = b'`, `W[(i+2)%n] = c'`.
  have hrotate : W.rotate i = List.map (fun m => W[(i + m) % W.length]!) (List.range W.length) := by
    refine' List.ext_get _ _ <;> simp +decide [ List.getElem_rotate ];
    exact fun n hn => by rw [ add_comm, List.getElem?_eq_getElem ( Nat.mod_lt _ ( by linarith ) ) ] ; rfl;
  rcases n : W.length with ( _ | _ | _ | n ) <;> simp_all +decide [ List.range_succ_eq_map ];
  · interval_cases i <;> interval_cases j <;> simp_all +decide;
  · simp_all +decide [ Nat.mod_eq_of_lt ];
    aesop

/-
**Chord-piece consecutive-triple lift.**  If a rotation of a chord piece
    `P` (either `chordLeft W k` or `chordRight W k`) of a `Nodup` cycle `W`
    starts with `a' :: b' :: c'`, and the shared middle vertex `b'` is *not* one
    of the two cut endpoints `W[0]`, `W[k]`, then `a', b', c'` are three
    consecutive vertices of the *parent* cycle `W`.  Both ear edges `(a',b')`,
    `(b',c')` of the piece avoid its single closing (cut) edge — whose endpoints
    are exactly `W[0]` and `W[k]` — hence are genuine path edges of the piece,
    therefore cyclic edges of `W` (`pathEdges_chordLeft_mem_closedEdges` /
    `pathEdges_chordRight_mem_closedEdges`); `consec_edges_triple` then assembles
    the consecutive triple.  This is the rotation/list-surgery core of the
    interior-branch ear lift; sorry-free preparation for
    `meisters_reduction_interior2`.
-/
lemma chord_consec_triple_lift (W : List ℂ) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ W.length) (hnodup : W.Nodup) {P : List ℂ}
    (hP : P = chordLeft W k ∨ P = chordRight W k)
    {a' b' c' : ℂ} {s : ℕ} {tl : List ℂ}
    (hrot : P.rotate s = a' :: b' :: c' :: tl)
    (hb0 : W[0]? ≠ some b') (hbk : W[k]? ≠ some b') :
    ∃ r' tl', W.rotate r' = a' :: b' :: c' :: tl' := by
  have h_mem_closedEdges : (a', b') ∈ closedEdges W ∧ (b', c') ∈ closedEdges W := by
    have h_mem_closedEdges : (a', b') ∈ closedEdges P ∧ (b', c') ∈ closedEdges P := by
      have h_edges : (a', b') ∈ closedEdges (a' :: b' :: c' :: tl) ∧ (b', c') ∈ closedEdges (a' :: b' :: c' :: tl) := by
        simp +decide [ closedEdges ];
      rw [ ← hrot ] at h_edges; exact mem_closedEdges_rotate _ _ _ |>.1 h_edges.1 |> fun h => ⟨ h, mem_closedEdges_rotate _ _ _ |>.1 h_edges.2 |> fun h => h ⟩ ;
    rcases hP with ( rfl | rfl ) <;> simp_all +decide [ pathEdges_chordLeft_mem_closedEdges, pathEdges_chordRight_mem_closedEdges ];
    · have h_mem_closedEdges : (a', b') ∈ pathEdges (chordLeft W k) ∧ (b', c') ∈ pathEdges (chordLeft W k) := by
        have h_closedEdges : closedEdges (chordLeft W k) = pathEdges (chordLeft W k) ++ [(W[k]!, W[0]!)] := by
          convert closedEdges_eq_pathEdges ( chordLeft W k ) ( W[0]! ) ( W[k]! ) _ _ using 1 <;> simp +decide [ chordLeft ];
          · cases W <;> aesop;
          · rw [ List.getLast?_take ] ; aesop
        grind;
      exact ⟨ pathEdges_chordLeft_mem_closedEdges _ _ _ h_mem_closedEdges.1, pathEdges_chordLeft_mem_closedEdges _ _ _ h_mem_closedEdges.2 ⟩;
    · have h_mem_closedEdges : (a', b') ∈ pathEdges (chordRight W k) ∧ (b', c') ∈ pathEdges (chordRight W k) := by
        have h_closedEdges : closedEdges (chordRight W k) = pathEdges (chordRight W k) ++ [(W[0], W[k])] := by
          convert closedEdges_eq_pathEdges _ _ _ _ _ using 1;
          · unfold chordRight; aesop;
          · convert chordRight_getLast W k ( by aesop ) hk using 1;
            cases W <;> aesop
        grind +splitImp;
      exact ⟨ pathEdges_chordRight_mem_closedEdges W k hk _ h_mem_closedEdges.1, pathEdges_chordRight_mem_closedEdges W k hk _ h_mem_closedEdges.2 ⟩;
  apply consec_edges_triple W hnodup a' b' c' h_mem_closedEdges.left h_mem_closedEdges.right;
  have h_nodup : (a' :: b' :: c' :: tl).Nodup := by
    have h_nodup : P.Nodup := by
      rcases hP with ( rfl | rfl ) <;> [ exact chordLeft_nodup _ _ hnodup; exact chordRight_nodup _ _ hk1 ( by linarith ) hnodup ];
    exact hrot ▸ List.nodup_rotate.mpr h_nodup;
  grind

/-- **Generalised corner-exit lemma (start point need not be on the base
    line).**  This is `corner_exit_point` with its `hzac : cross (a-c)(z-c) = 0`
    weakened to `0 ≤ cross (a-c)(z-c) * O`: the start point `z` is allowed to be
    strictly on the apex side (`PC(z) ≥ 0`) rather than exactly on the base line.
    The same affine first-crossing argument applies: along `z → u` the apex test
    `PC` is `(1-τ)·PC(z) + τ·PC(u) ≥ τ·PC(u) > 0` for `τ > 0`, so the moving point
    leaves the wedge through `a–b` or `b–c`.  Reusable preparation for
    `interior_chord_is_diagonal` (where the chord-crossing point is *strictly
    inside* the corner triangle, never on the base line). -/
lemma corner_exit_point_ge (a b c z u : ℂ)
    (hO : cross (b - a) (c - b) ≠ 0)
    (hzab : 0 < cross (b - a) (z - a) * cross (b - a) (c - b))
    (hzbc : 0 < cross (c - b) (z - b) * cross (b - a) (c - b))
    (hzac : 0 ≤ cross (a - c) (z - c) * cross (b - a) (c - b))
    (huac : 0 < cross (a - c) (u - c) * cross (b - a) (c - b))
    (hunot : ¬ inTriangleStrict a b c u) :
    (∃ y ∈ segment ℝ z u, y ∈ segment ℝ a b) ∨
    (∃ y ∈ segment ℝ z u, y ∈ segment ℝ b c) := by
  set O := cross (b - a) (c - b) with hO_def
  have hPA : ∀ τ : ℝ, cross (b - a) (z + τ • (u - z) - a) * O
      = (1 - τ) * cross (b - a) (z - a) * O + τ * cross (b - a) (u - a) * O := by
    unfold cross; norm_num [ Complex.ext_iff ] ; intros; ring
  have hPB : ∀ τ : ℝ, cross (c - b) (z + τ • (u - z) - b) * O
      = (1 - τ) * cross (c - b) (z - b) * O + τ * cross (c - b) (u - b) * O := by
    unfold cross; norm_num [ Complex.ext_iff ] ; intros; ring
  have hPC : ∀ τ : ℝ, cross (a - c) (z + τ • (u - z) - c) * O
      = (1 - τ) * cross (a - c) (z - c) * O + τ * cross (a - c) (u - c) * O := by
    unfold cross; norm_num [ Complex.ext_iff ] ; intros; ring
  by_cases hPAu : cross (b - a) (u - a) * O ≤ 0
  · set t := cross (b - a) (z - a) * O / (cross (b - a) (z - a) * O - cross (b - a) (u - a) * O) with ht_def
    have ht_bounds : 0 < t ∧ t ≤ 1 :=
      ⟨ div_pos hzab ( by linarith ), div_le_one_of_le₀ ( by linarith ) ( by linarith ) ⟩
    have ht_PA : cross (b - a) (z + t • (u - z) - a) * O = 0 := by grind
    have ht_PC : 0 < cross (a - c) (z + t • (u - z) - c) * O := by
      rw [ hPC ] ; nlinarith [ mul_pos ht_bounds.1 huac,
        mul_nonneg ( by linarith [ ht_bounds.2 ] : (0:ℝ) ≤ 1 - t ) hzac ]
    by_cases hPBu : cross (c - b) (u - b) * O ≥ 0
    · refine Or.inl ⟨ z + t • ( u - z ), ?_, ?_ ⟩
      · rw [ segment_eq_image ]
        exact ⟨ t, ⟨ by linarith, by linarith ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩
      · apply mem_segment_ab_of_cross a b c (z + t • (u - z)) hO
        · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO ht_PA
        · nlinarith [ hPB t ]
        · exact le_of_lt ht_PC
    · set s := cross (c - b) (z - b) * O / (cross (c - b) (z - b) * O - cross (c - b) (u - b) * O) with hs_def
      have hs_bounds : 0 < s ∧ s ≤ 1 :=
        ⟨ div_pos hzbc ( by linarith ), div_le_one_of_le₀ ( by linarith ) ( by linarith ) ⟩
      have hs_PB : cross (c - b) (z + s • (u - z) - b) * O = 0 := by grind
      have hs_PC : 0 < cross (a - c) (z + s • (u - z) - c) * O := by
        rw [ hPC ] ; nlinarith [ mul_pos hs_bounds.1 huac,
          mul_nonneg ( by linarith [ hs_bounds.2 ] : (0:ℝ) ≤ 1 - s ) hzac ]
      by_cases hts : t ≤ s
      · have ht_PB_nonneg : 0 ≤ cross (c - b) (z + t • (u - z) - b) * O := by
          rw [ hPB ] ; rw [ le_div_iff₀ ] at hts <;> nlinarith
        refine Or.inl ⟨ z + t • ( u - z ), ?_, ?_ ⟩
        · rw [ segment_eq_image ]
          exact ⟨ t, ⟨ by linarith, by linarith ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩
        · apply mem_segment_ab_of_cross a b c (z + t • (u - z)) hO
          · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO ht_PA
          · exact ht_PB_nonneg
          · exact le_of_lt ht_PC
      · have hs_PA : cross (b - a) (z + s • (u - z) - a) * O ≥ 0 := by
          rw [ hPA ] ; rw [ div_le_iff₀ ] at hts <;> nlinarith
        refine Or.inr ⟨ z + s • ( u - z ), ?_, ?_ ⟩
        · rw [ segment_eq_image ]
          exact ⟨ s, ⟨ by linarith, by linarith ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩
        · apply mem_segment_bc_of_cross a b c (z + s • (u - z)) hO
          · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO hs_PB
          · exact hs_PA
          · exact le_of_lt hs_PC
  · have hPBu : cross (c - b) (u - b) * O ≤ 0 := by
      contrapose! hunot; simp_all +decide [ inTriangleStrict ]
      cases lt_or_gt_of_ne hO <;>
        first
          | exact Or.inl ⟨ by nlinarith, by nlinarith, by nlinarith ⟩
          | exact Or.inr ⟨ by nlinarith, by nlinarith, by nlinarith ⟩
    set s := cross (c - b) (z - b) * O / (cross (c - b) (z - b) * O - cross (c - b) (u - b) * O) with hs_def
    have hs_pos : 0 < s := div_pos hzbc ( by linarith )
    have hs_le_one : s ≤ 1 := div_le_one_of_le₀ ( by linarith ) ( by linarith )
    have hPB_s : cross (c - b) (z + s • (u - z) - b) * O = 0 := by
      rw [ hPB, hs_def ] ; nlinarith [ mul_div_cancel₀ ( cross ( c - b ) ( z - b ) * O )
        ( by linarith : ( cross ( c - b ) ( z - b ) * O - cross ( c - b ) ( u - b ) * O ) ≠ 0 ) ]
    have hPC_s : 0 ≤ cross (a - c) (z + s • (u - z) - c) * O := by
      rw [ hPC ] ; nlinarith [ mul_nonneg hs_pos.le huac.le,
        mul_nonneg ( by linarith : (0:ℝ) ≤ 1 - s ) hzac ]
    refine Or.inr ⟨ z + s • ( u - z ), ?_, ?_ ⟩
    · rw [ segment_eq_image ]
      exact ⟨ s, ⟨ hs_pos.le, hs_le_one ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩
    · apply mem_segment_bc_of_cross a b c (z + s • (u - z)) hO
      · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO hPB_s
      · nlinarith [ hPA s ]
      · exact hPC_s

end HexArea

/-
**A simple-polygon vertex lies on none of its non-incident edges.**  If
    `V` is a simple polygon (`4 ≤ V.length`), `w` is a vertex of `V`, and `e` is
    a cyclic edge of `V` with neither endpoint equal to `w`, then `w` does not
    lie on the closed segment `e`.

    Proof: `w = V[i]`; its two incident cyclic edges `(V[i-1], w)` and
    `(w, V[i+1])` both contain `w`.  Since `n ≥ 4`, the two neighbours `V[i-1]`,
    `V[i+1]` are not cyclically adjacent, so `e` (whose endpoints avoid `w`)
    shares an endpoint with at most one of the two incident edges; the other
    incident edge is non-adjacent to `e`, hence `Disjoint` from it by
    `PolygonSimple` — but both contain `w` if `w ∈ e`, a contradiction.
    Combinatorial preparation for `interior_chord_is_diagonal` (the `z = w`
    boundary case, where the chord meets a far edge exactly at the pivot `w`).
-/
lemma simple_vertex_not_on_far_edge (V : List ℂ) (h4 : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (w : ℂ) (hw : w ∈ V)
    (e : ℂ × ℂ) (he : e ∈ closedEdges V) (hne1 : w ≠ e.1) (hne2 : w ≠ e.2) :
    w ∉ segment ℝ e.1 e.2 := by
  obtain ⟨ i, hi ⟩ := List.mem_iff_getElem.mp hw;
  obtain ⟨ hi, rfl ⟩ := hi;
  -- By definition of `closedEdges`, there exists some `j` such that `e = (V[j], V[(j+1)%n])`.
  obtain ⟨ j, hj ⟩ : ∃ j, j < V.length ∧ e = (V[j]!, V[(j + 1) % V.length]!) := by
    have h_closedEdges : closedEdges V = List.map (fun j => (V[j]!, V[(j + 1) % V.length]!)) (List.range V.length) := by
      refine' List.ext_get _ _ <;> simp +decide [ closedEdges ];
      grind +suggestions;
    grind;
  have h_incident : V[(i + V.length - 1) % V.length]! ≠ e.1 ∧ V[(i + V.length - 1) % V.length]! ≠ e.2 ∨ V[(i + 1) % V.length]! ≠ e.1 ∧ V[(i + 1) % V.length]! ≠ e.2 := by
    by_cases h_cases : j = (i + V.length - 1) % V.length ∨ (j + 1) % V.length = (i + V.length - 1) % V.length;
    · rcases h_cases with ( rfl | h_cases ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · rcases i with ( _ | i ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · have h_distinct : (i + 1) % V.length ≠ j ∧ (i + 1) % V.length ≠ (i + V.length - 1) % V.length := by
          constructor <;> intro h <;> have := Nat.mod_add_div ( i + 1 ) V.length <;> have := Nat.mod_add_div ( i + V.length - 1 ) V.length <;> simp_all +decide [ Nat.mod_eq_of_lt ];
          · rcases k : ( i + 1 ) / V.length with ( _ | _ | k ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
            · have := Nat.modEq_iff_dvd.mp h_cases.symm; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
              obtain ⟨ a, ha ⟩ := this; rw [ Nat.cast_sub ( by linarith ) ] at ha; norm_num at ha; nlinarith [ show a = 0 by nlinarith ] ;
            · norm_num [ show i = V.length - 1 by omega ] at *;
              norm_num [ show j = 0 by omega ] at *;
              rcases V with ( _ | ⟨ _, _ | V ⟩ ) <;> norm_num at *;
              norm_num [ ( by ring : ( List.length ‹_› + 1 + ( List.length ‹_› + 1 ) ) = ( List.length ‹_› + 1 + 1 ) + ( List.length ‹_› ) ) ] at *;
              norm_num [ Nat.mod_eq_of_lt ] at *;
              grind +qlia;
            · nlinarith;
          · rcases V with ( _ | ⟨ _, _ | V ⟩ ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ];
            nlinarith [ show ( i + 1 ) / ( List.length ‹_› + 2 ) = ( i + List.length ‹_› + 1 ) / ( List.length ‹_› + 2 ) by nlinarith ];
        have := hsimple.1;
        rw [ List.nodup_iff_injective_get ] at this;
        exact ⟨ by rw [ List.getElem?_eq_getElem ( by linarith [ Nat.mod_lt ( i + 1 ) ( by linarith : 0 < V.length ) ] ) ] ; exact fun h => h_distinct.1 <| by have := @this ⟨ ( i + 1 ) % V.length, by linarith [ Nat.mod_lt ( i + 1 ) ( by linarith : 0 < V.length ) ] ⟩ ⟨ j, by linarith ⟩ ; aesop, by rw [ List.getElem?_eq_getElem ( by linarith [ Nat.mod_lt ( i + 1 ) ( by linarith : 0 < V.length ) ] ), List.getElem?_eq_getElem ( by linarith [ Nat.mod_lt ( i + V.length - 1 ) ( by linarith : 0 < V.length ) ] ) ] ; exact fun h => h_distinct.2 <| by have := @this ⟨ ( i + 1 ) % V.length, by linarith [ Nat.mod_lt ( i + 1 ) ( by linarith : 0 < V.length ) ] ⟩ ⟨ ( i + V.length - 1 ) % V.length, by linarith [ Nat.mod_lt ( i + V.length - 1 ) ( by linarith : 0 < V.length ) ] ⟩ ; aesop ⟩;
    · have h_distinct : V.Nodup := by
        exact hsimple.1;
      have h_distinct : ∀ (k l : ℕ), k < V.length → l < V.length → k ≠ l → V[k]! ≠ V[l]! := by
        intros k l hk hl hkl; have := List.nodup_iff_injective_get.mp h_distinct; simp_all +decide [ Function.Injective ] ;
        exact fun h => hkl <| by simpa [ Fin.ext_iff ] using @this ⟨ k, hk ⟩ ⟨ l, hl ⟩ h;
      exact Or.inl ⟨ by specialize h_distinct ( ( i + V.length - 1 ) % V.length ) j ( Nat.mod_lt _ ( by linarith ) ) hj.1; aesop, by specialize h_distinct ( ( i + V.length - 1 ) % V.length ) ( ( j + 1 ) % V.length ) ( Nat.mod_lt _ ( by linarith ) ) ( Nat.mod_lt _ ( by linarith ) ) ; aesop ⟩;
  have h_disjoint : Disjoint (segment ℝ (V[(i + V.length - 1) % V.length]!) (V[i])) (segment ℝ e.1 e.2) ∨ Disjoint (segment ℝ (V[i]) (V[(i + 1) % V.length]!)) (segment ℝ e.1 e.2) := by
    cases h_incident <;> simp_all +decide [ PolygonSimple ];
    · have h_disjoint : (V[(i + V.length - 1) % V.length]!, V[i]) ∈ closedEdges V := by
        convert List.mem_iff_getElem.mpr _ using 1;
        use (i + V.length - 1) % V.length;
        simp +decide [ closedEdges, List.getElem_zip ];
        simp +decide [ List.getElem_rotate, Nat.mod_lt ];
        simp +decide [ Nat.sub_add_cancel ( by linarith : 1 ≤ i + V.length ), Nat.mod_eq_of_lt hi ];
        exact ⟨ Nat.mod_lt _ ( by linarith ), by rw [ List.getElem?_eq_getElem ( Nat.mod_lt _ ( by linarith ) ) ] ; rfl ⟩;
      grind;
    · refine Or.inr <| hsimple.2 _ _ ?_ _ _ ?_ ?_ ?_ ?_ ?_ <;> simp_all +decide [ closedEdges ];
      rw [ List.mem_iff_getElem ];
      use i; simp [List.getElem_zip, List.getElem_rotate];
      exact ⟨ hi, by rw [ List.getElem?_eq_getElem ( Nat.mod_lt _ ( by linarith ) ) ] ; rfl ⟩;
  cases h_disjoint <;> simp_all +decide [ Set.disjoint_left ];
  · rename_i h;
    exact fun h' => h ( right_mem_segment _ _ _ ) h';
  · exact fun h => ‹∀ a ∈ segment ℝ V[i] ( V[(i + 1) % V.length]?.getD default ), a ∉ segment ℝ V[j] ( V[(j + 1) % V.length]?.getD default ) › _ ( left_mem_segment _ _ _ ) h

/-
**A chord sub-segment lying off the line `a–b` avoids the ear edge `a–b`.**
    If `z, y` lie on a cyclic edge `e` of the simple polygon `a::b::c::rest`
    (with `b` not on `e`), `a` is not on the sub-segment `z–y`, and `z` is
    strictly off the line `a–b` (`cross (b-a)(z-a) ≠ 0`), then `segment z y` is
    disjoint from the ear edge `segment a b`.

    Proof: a common point `p` lies on `e` (convexity), is `≠ a` (`a ∉ z–y`) and
    `≠ b` (`b ∉ e`).  If `e` shares no endpoint with `a`, `PolygonSimple` makes
    `e` and the edge `a–b` disjoint — contradiction.  If `e` is incident to `a`,
    then `e` and `a–b` share the endpoint `a` and the common point `p ≠ a`, so
    both are collinear through `a`; hence `z` (on `e`) lies on the line `a–b`,
    forcing `cross (b-a)(z-a) = 0`, contradicting the hypothesis.  Preparation
    for `interior_chord_is_diagonal`.
-/
lemma chord_disjoint_ear_ab (a b c : ℂ) (rest : List ℂ) (z y : ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (e : ℂ × ℂ) (he : e ∈ closedEdges (a :: b :: c :: rest))
    (hb1 : b ≠ e.1) (hb2 : b ≠ e.2)
    (hz : z ∈ segment ℝ e.1 e.2) (hy : y ∈ segment ℝ e.1 e.2)
    (hbe : b ∉ segment ℝ e.1 e.2) (hazy : a ∉ segment ℝ z y)
    (hzab : HexArea.cross (b - a) (z - a) ≠ 0) :
    Disjoint (segment ℝ z y) (segment ℝ a b) := by
  simp_all +decide [ Set.disjoint_left, segment_eq_image ];
  intro p x hx₁ hx₂ rfl y hy₁ hy₂
  by_cases ha : a = e.1 ∨ a = e.2;
  · rcases ha with ( rfl | rfl ) <;> simp_all +decide [ HexArea.cross ];
    · obtain ⟨ u, hu₁, hu₂ ⟩ := hz; obtain ⟨ v, hv₁, hv₂ ⟩ := hy; simp_all +decide [ Complex.ext_iff ] ;
      grind;
    · obtain ⟨ u, hu₁, hu₂ ⟩ := hz; obtain ⟨ v, hv₁, hv₂ ⟩ := hy; simp_all +decide [ Complex.ext_iff ] ;
      grind +splitImp;
  · have := hsimple.2 ( a, b ) ( by
      simp +decide [ closedEdges ] ) e he
    generalize_proofs at *;
    contrapose! this;
    simp_all +decide [ Set.disjoint_left, segment_eq_image ];
    obtain ⟨ u, hu₁, hu₂ ⟩ := hz; obtain ⟨ v, hv₁, hv₂ ⟩ := hy; use y; use hy₁, hy₂; use ( 1 - x ) * u + x * v; simp_all +decide [ Complex.ext_iff ] ;
    exact ⟨ by nlinarith, by nlinarith, by rw [ ← hu₂.1, ← hv₂.1 ] ; ring, by rw [ ← hu₂.2, ← hv₂.2 ] ; ring ⟩

/-
**A chord sub-segment lying off the line `b–c` avoids the ear edge `b–c`.**
    The `b–c` analogue of `chord_disjoint_ear_ab`.  Preparation for
    `interior_chord_is_diagonal`.
-/
lemma chord_disjoint_ear_bc (a b c : ℂ) (rest : List ℂ) (z y : ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (e : ℂ × ℂ) (he : e ∈ closedEdges (a :: b :: c :: rest))
    (hb1 : b ≠ e.1) (hb2 : b ≠ e.2)
    (hz : z ∈ segment ℝ e.1 e.2) (hy : y ∈ segment ℝ e.1 e.2)
    (hbe : b ∉ segment ℝ e.1 e.2) (hczy : c ∉ segment ℝ z y)
    (hzbc : HexArea.cross (c - b) (z - b) ≠ 0) :
    Disjoint (segment ℝ z y) (segment ℝ b c) := by
  -- Suppose there exists a point `p` in both segments.
  by_contra h_contra;
  obtain ⟨p, hp⟩ : ∃ p, p ∈ segment ℝ z y ∧ p ∈ segment ℝ b c := by
    exact Set.not_disjoint_iff.mp h_contra;
  have h_cases : c = e.1 ∨ c = e.2 := by
    contrapose! h_contra;
    have h_disjoint : Disjoint (segment ℝ e.1 e.2) (segment ℝ b c) := by
      have := hsimple.2 ( b, c ) ?_ e ?_ <;> simp_all +decide [ closedEdges ];
      exact this.symm;
    exact Set.disjoint_left.mpr fun x hxz hxz' => h_disjoint.le_bot ⟨ by exact convex_segment _ _ |> fun h => h.segment_subset hz hy hxz, hxz' ⟩;
  rcases h_cases with ( rfl | rfl ) <;> simp_all +decide [ segment_eq_image ];
  · obtain ⟨ ⟨ x, hx, rfl ⟩, ⟨ y, hy, hy' ⟩ ⟩ := hp; simp_all +decide [ Complex.ext_iff ] ;
    obtain ⟨ u, hu, hu', hu'' ⟩ := hz; obtain ⟨ v, hv, hv', hv'' ⟩ := ‹∃ x : ℝ, ( 0 ≤ x ∧ x ≤ 1 ) ∧ ( 1 - x ) * e.1.re + x * e.2.re = _ ∧ ( 1 - x ) * e.1.im + x * e.2.im = _›; simp_all +decide [ HexArea.cross ] ;
    grind;
  · obtain ⟨ ⟨ x, hx, rfl ⟩, ⟨ y, hy, hy' ⟩ ⟩ := hp; simp_all +decide [ Complex.ext_iff ] ;
    obtain ⟨ u, hu, hu' ⟩ := hz; obtain ⟨ v, hv, hv' ⟩ := ‹∃ x : ℝ, ( 0 ≤ x ∧ x ≤ 1 ) ∧ ( 1 - x ) * e.1.re + x * e.2.re = _ ∧ ( 1 - x ) * e.1.im + x * e.2.im = _›; simp_all +decide [ HexArea.cross ] ;
    grind

/-
**The Meisters interior diagonal is clear (genuine geometric core).**
    In a simple polygon `a :: b :: c :: rest` whose corner triangle `a, b, c`
    is non-degenerate, let `w ∈ rest` be a vertex strictly inside the triangle
    that is *farthest from the base line* `a–c`.  Then the chord `b–w` is
    disjoint, as a segment, from every cyclic edge of the polygon not incident
    to `b` or `w` — i.e. `b–w` is a diagonal.

    **Orientation note (important).**  Every interior vertex `x` of the corner
    triangle satisfies `cross (c-a) (x-a) = β · cross (c-a) (b-a)` for some
    `β ∈ (0,1)` (barycentric `b`-weight), so all interior vertices share the
    sign of `cross (c-a) (b-a)` and "farthest from `a–c`" means "largest `β`".
    Maximising the *signed* quantity `cross (c-a) (·-a)` is "farthest" only for
    positively-oriented triangles; for the negative orientation it picks the
    vertex *closest* to `a–c` and the chord can then run through a farther
    interior vertex (verified counterexample:
    `a=0, c=4, b=2-3i, w=2-½i, w₂=2-2i`).  Hence the correct, orientation-robust
    "farthest" hypothesis used here is `hwmax`, scaled by `cross (c-a) (b-a)`:
    `cross (c-a) (y-a) * cross (c-a) (b-a) ≤ cross (c-a) (w-a) * cross (c-a) (b-a)`,
    i.e. `w` maximises the `b`-weight `β`.

    Proof idea (Meisters' farthest-vertex argument).  The chord `b–w` lies in
    the closed corner triangle `a,b,c`, and every point of it has `b`-weight
    `≥ β(w)` (it interpolates between the apex `b`, with `β = 1`, and `w`).  A far
    edge meeting `b–w` at an interior point `z` cannot cross the two corner
    edges `a–b`, `b–c` (`far_edge_disjoint_earEdges`), and a segment crosses the
    base line `a–c` at most once; hence it has an endpoint strictly inside the
    smaller sub-triangle cut off by the line through `w` parallel to `a–c`, i.e.
    an interior vertex `y ∈ rest` with `β(y) > β(w)` — contradicting `hwmax`.

    This is the genuine Jordan-content heart of `meisters_reduction_interior2`:
    combined with the banked combinatorial split-preservation bricks
    (`HexArea.chordLeft_PolygonSimple` / `chordRight_PolygonSimple` etc.) it
    yields the two strictly-shorter simple sub-polygons of the interior split.
    NOTE: the existing `exists_farthest_interior` supplies the *unscaled*
    `hwmax` (correct only up to orientation); aligning that pivot selection to
    this orientation-robust form is the remaining bridge before this lemma can
    be consumed by `meisters_reduction_interior2`.  Recorded preparation.
-/
lemma interior_chord_is_diagonal (a b c w : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hwrest : w ∈ rest)
    (hwin : HexArea.inTriangleStrict a b c w)
    (hwmax : ∀ y ∈ rest, HexArea.inTriangleStrict a b c y →
        HexArea.cross (c - a) (y - a) * HexArea.cross (c - a) (b - a)
          ≤ HexArea.cross (c - a) (w - a) * HexArea.cross (c - a) (b - a)) :
    ∀ e ∈ closedEdges (a :: b :: c :: rest),
      b ≠ e.1 → b ≠ e.2 → w ≠ e.1 → w ≠ e.2 →
      Disjoint (segment ℝ b w) (segment ℝ e.1 e.2) := by
  intro e he hb1 hb2 hw1 hw2;
  by_contra h_contra;
  -- Choose the endpoint `y ∈ {e.1, e.2}` of `e` maximising `g`: since `g` is affine on `segment ℝ e.1 e.2` and `z` lies on it, `g z ≤ max (g e.1) (g e.2)`; let `y` be the maximiser, so `g y ≥ g z > g w` and `g y > 0`.
  obtain ⟨z, hz⟩ : ∃ z ∈ segment ℝ b w, z ∈ segment ℝ e.1 e.2 := by
    grind +splitImp
  obtain ⟨y, hy⟩ : ∃ y ∈ ({e.1, e.2} : Set ℂ), HexArea.cross (a - c) (y - c) * HexArea.cross (b - a) (c - b) ≥ HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) := by
    have h_affine : ∀ t : ℝ, t ∈ Set.Icc 0 1 → HexArea.cross (a - c) ((1 - t) • e.1 + t • e.2 - c) * HexArea.cross (b - a) (c - b) = (1 - t) * (HexArea.cross (a - c) (e.1 - c) * HexArea.cross (b - a) (c - b)) + t * (HexArea.cross (a - c) (e.2 - c) * HexArea.cross (b - a) (c - b)) := by
      unfold HexArea.cross; norm_num [ Complex.ext_iff ] ; intros; ring;
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ z = (1 - t) • e.1 + t • e.2 := by
      rcases hz.2 with ⟨ u, v, hu, hv, huv, rfl ⟩ ; exact ⟨ v, ⟨ by linarith, by linarith ⟩, by simp +decide [ huv.symm ] ⟩ ;
    simp_all +decide [ segment_eq_image ];
    cases le_total ( HexArea.cross ( a - c ) ( e.1 - c ) * HexArea.cross ( b - a ) ( c - b ) ) ( HexArea.cross ( a - c ) ( e.2 - c ) * HexArea.cross ( b - a ) ( c - b ) ) <;> first | left; nlinarith | right; nlinarith;
  -- From `inTriangleStrict a b c w` (`cases hwin`) and `t ∈ (0,1)`, derive (each by `nlinarith` after `unfold HexArea.cross` / using the three corner tests at `w`):
  -- - `cross (b-a)(z-a) * O > 0`  [hence `cross (b-a)(z-a) ≠ 0`],
  -- - `cross (c-b)(z-b) * O > 0`  [hence `cross (c-b)(z-b) ≠ 0`],
  -- - `g z > g w` and `g z > 0`  (`g z = (1-t)*(cross (c-a)(b-a))^2 + t*g w`, and `(cross (c-a)(b-a))^2 > g w` for interior `w`).
  have hz_pos : HexArea.cross (b - a) (z - a) * HexArea.cross (b - a) (c - b) > 0 ∧ HexArea.cross (c - b) (z - b) * HexArea.cross (b - a) (c - b) > 0 ∧ HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) > HexArea.cross (a - c) (w - c) * HexArea.cross (b - a) (c - b) ∧ HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) > 0 := by
    obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, z = (1 - t) • b + t • w := by
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, z = (1 - t) • b + t • w := by
        rw [ segment_eq_image ] at hz ; aesop;
      refine' ⟨ t, ⟨ lt_of_le_of_ne ht.1.1 _, lt_of_le_of_ne ht.1.2 _ ⟩, ht.2 ⟩ <;> rintro rfl <;> simp_all +decide [ segment_eq_image ];
      · obtain ⟨ x, hx, hx' ⟩ := hz.2;
        have := simple_vertex_not_on_far_edge ( a :: b :: c :: rest ) ( by
          grind +splitImp ) hsimple b ( by
          simp +decide ) e he hb1 hb2;
        exact this ⟨ 1 - x, x, by aesop ⟩;
      · have := simple_vertex_not_on_far_edge ( a :: b :: c :: rest ) ( by
          grind ) hsimple w ( by
          grind ) e he hw1 hw2; simp_all +decide [ segment_eq_image ] ;
    rcases hwin with ( hwin | hwin ) <;> simp_all +decide [ HexArea.cross ];
    · refine' ⟨ _, _, _, _ ⟩;
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.mpr ht.1.2 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.1 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.2.2 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.1 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.2.1 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.2.2 ) ];
    · refine' ⟨ _, _, _, _ ⟩;
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.mpr ht.1.2 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.1 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.2.2 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.1 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.2.1 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.2 ) ];
  -- From `hy`, `hz_pos`, and `hwmax`, we get `y ∈ rest` and `¬ inTriangleStrict a b c y`.
  have hy_rest : y ∈ rest := by
    have hy_rest : y ∈ a :: b :: c :: rest := by
      have := List.of_mem_zip he; simp_all +decide [ List.mem_rotate ] ;
      grind +ring;
    by_cases hya : y = a <;> by_cases hyc : y = c <;> simp_all +decide;
    · unfold HexArea.cross at * ; aesop;
    · linarith;
    · simp_all +decide [ HexArea.cross ];
      linarith;
    · grind
  have hy_not_in_triangle : ¬ HexArea.inTriangleStrict a b c y := by
    intro hy_in_triangle
    have := hwmax y hy_rest hy_in_triangle
    simp_all +decide [ HexArea.cross ];
    linarith [ hwmax y hy_rest hy_in_triangle ];
  -- From `hy`, `hz_pos`, and `hwmax`, we get `b ∉ segment ℝ e.1 e.2` and `a ∉ segment ℝ z y` and `c ∉ segment ℝ z y`.
  have hb_not_in_segment : b ∉ segment ℝ e.1 e.2 := by
    apply simple_vertex_not_on_far_edge (a :: b :: c :: rest) (by
    grind) hsimple b (by
    simp +decide) e he hb1 hb2
  have ha_not_in_segment : a ∉ segment ℝ z y := by
    intro ha_in_segment
    have h_cross_zero : HexArea.cross (a - c) (a - c) * HexArea.cross (b - a) (c - b) = 0 := by
      unfold HexArea.cross; ring;
    have h_cross_zero : ∀ t : ℝ, t ∈ Set.Icc 0 1 → HexArea.cross (a - c) ((1 - t) • z + t • y - c) * HexArea.cross (b - a) (c - b) = (1 - t) * HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) + t * HexArea.cross (a - c) (y - c) * HexArea.cross (b - a) (c - b) := by
      intros t ht
      simp [HexArea.cross]
      ring;
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ a = (1 - t) • z + t • y := by
      rw [ segment_eq_image ] at ha_in_segment;
      rcases ha_in_segment with ⟨ t, ht, rfl ⟩ ; exact ⟨ t, ht, rfl ⟩ ;
    norm_num [ ht.2 ] at *;
    specialize h_cross_zero t ht.1 ht.2 ; norm_num at h_cross_zero ; nlinarith
  have hc_not_in_segment : c ∉ segment ℝ z y := by
    intro hc_in_segment
    have h_cross_zero : HexArea.cross (a - c) (c - c) * HexArea.cross (b - a) (c - b) = 0 := by
      unfold HexArea.cross; norm_num;
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ c = (1 - t) • z + t • y := by
      rw [ segment_eq_image ] at hc_in_segment; obtain ⟨ t, ht, rfl ⟩ := hc_in_segment; exact ⟨ t, ht, rfl ⟩ ;
    have h_cross_zero : HexArea.cross (a - c) (c - c) * HexArea.cross (b - a) (c - b) = (1 - t) * HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) + t * HexArea.cross (a - c) (y - c) * HexArea.cross (b - a) (c - b) := by
      rw [ht.right];
      unfold HexArea.cross; norm_num; ring;
    nlinarith [ ht.1.1, ht.1.2 ];
  have := HexArea.corner_exit_point_ge a b c z y hndtri hz_pos.1 hz_pos.2.1 hz_pos.2.2.2.le (by
  linarith) hy_not_in_triangle;
  rcases this with ( ⟨ p, hp₁, hp₂ ⟩ | ⟨ p, hp₁, hp₂ ⟩ );
  · have := chord_disjoint_ear_ab a b c rest z y hsimple e he hb1 hb2 hz.2 (by
    rcases hy.1 with ( rfl | rfl ) <;> [ exact left_mem_segment _ _ _; exact right_mem_segment _ _ _ ]) hb_not_in_segment ha_not_in_segment (by
    exact fun h => by simp_all +decide [ HexArea.cross ] ;);
    exact this.le_bot ⟨ hp₁, hp₂ ⟩;
  · have := chord_disjoint_ear_bc a b c rest z y hsimple e he hb1 hb2 hz.2 (by
    rcases hy.1 with ( rfl | rfl ) <;> [ exact left_mem_segment _ _ _; exact right_mem_segment _ _ _ ]) hb_not_in_segment hc_not_in_segment (by
    exact fun h => by simp_all +decide [ HexArea.cross ] ;);
    exact this.le_bot ⟨ hp₁, hp₂ ⟩

/-
**Boundary-seam split (sorry-free combinatorial brick).**  In the boundary
    subcase of the empty-branch lift, the clip cycle `M = a :: c :: rest`
    (a `Nodup` list) is recursed on and `IH2` returns an ear
    `M.rotate r' = a' :: b' :: c' :: rest'` whose middle vertex avoids the cut
    endpoints (`b' ≠ a`, `b' ≠ c`).  When the `a–c` junction does NOT sit
    strictly inside the returned tail (`hnotint`), it must sit at the rotation
    seam, and the directed junction edge `a → c` (the unique cyclic successor of
    `a` is `c`) pins down exactly two configurations:
    * `c' = a` with `rest'.head? = some c` (ear immediately *before* the
      junction), or
    * `a' = c` with `rest'.getLast? = some a` (ear immediately *after* the
      junction).

    This is the pure list-combinatorics core that reduces the boundary lift to
    two concrete sub-cases; explicitly NOT a dead branch — it is preparation
    consumed by `empty_branch_boundary_lift`.
-/
lemma boundary_seam_split (a c : ℂ) (rest : List ℂ) (a' b' c' : ℂ)
    (rest' : List ℂ) (r' : ℕ) (hnodup : (a :: c :: rest).Nodup)
    (hrest : 2 ≤ rest.length)
    (hrot' : (a :: c :: rest).rotate r' = a' :: b' :: c' :: rest')
    (hb'a : b' ≠ a) (hb'c : b' ≠ c)
    (hnotint : ¬ ∃ s t, rest' = s ++ a :: c :: t) :
    (c' = a ∧ rest'.head? = some c) ∨ (a' = c ∧ rest'.getLast? = some a) := by
  rcases r' with ( _ | _ | r' ) <;> simp_all +decide [ List.rotate ];
  · rcases rest with ( _ | ⟨ a, rest ⟩ ) <;> simp_all +decide [ List.append ];
    induction rest <;> aesop;
  · rcases n : ( r' + 1 + 1 ) % ( rest.length + 1 + 1 ) with ( _ | _ | n ) <;> simp_all +decide [ List.drop, List.take ];
    · rcases rest' with ( _ | ⟨ x, _ | ⟨ y, rest' ⟩ ⟩ ) <;> simp_all +decide [ List.append_assoc ];
      · rcases rest with ( _ | ⟨ x, _ | ⟨ y, rest ⟩ ⟩ ) <;> simp_all +decide [ List.append_assoc ];
      · rcases rest with ( _ | ⟨ y, _ | ⟨ z, rest ⟩ ⟩ ) <;> simp_all +decide [ List.append_eq_cons_iff ];
      · replace hrot' := congr_arg List.reverse hrot'.2 ; simp_all +decide [ List.reverse_append ];
        replace hrot' := congr_arg List.reverse hrot'; simp_all +decide [ List.reverse_append ] ;
        replace hrot' := congr_arg List.getLast? hrot'; simp_all +decide [ List.getLast?_append ] ;
    · rcases x : List.drop ‹_› rest with ( _ | ⟨ a', _ | ⟨ b', _ | ⟨ c', rest' ⟩ ⟩ ⟩ ) <;> simp_all +decide [ List.drop ];
      · aesop;
      · grind

/-
**Boundary-seam lift, Case A, non-spike subcase (PROVED).**  In Case A of
    `boundary_seam_split` the returned clip ear is `a' :: b' :: a :: c :: rest''`
    (its diagonal endpoint `c'` coincides with the junction vertex `a`, and the
    junction continues with `c`).  Re-inserting the convex apex `b` between `a`
    and `c` (via `clip_ear_lift_general` with `pre = [a', b']`) yields the genuine
    `V`-rotation `a' :: b' :: a :: b :: c :: rest''`.  The ear `(a', b', a)` is
    then an `EmptyCornerData2` ear of `V`: the surviving clip turn `hpt'` gives
    the turn at `a'`, while the turn at the new neighbour `b` of the diagonal
    endpoint `a` is the apex turn `cross (a - a') (b - a)`, supplied non-zero by
    `hturnA` (the non-spike hypothesis).  Emptiness/diagonal-avoidance of the
    inserted `b` come from `hbconv`/`hbseg`; the orientation `iff` is assembled
    from `horient`, `horient'`, `shoelace2_clip_second`, `shoelace2_insert_mid`,
    `shoelace2_rotate`.  The genuinely open content is only the spike case
    (`cross (a - a') (b - a) = 0`), left in `empty_branch_boundary_lift`.
-/
lemma boundary_lift_caseA_nonspike (V : List ℂ) (z1 z2 : ℂ)
    (a b c : ℂ) (rest : List ℂ) (r : ℕ)
    (hrot : V.rotate r = a :: b :: c :: rest)
    (hac : a ≠ c) (hanr : a ∉ rest) (hba : b ≠ a)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (horient : ((0:ℝ) < HexArea.shoelace2 [a, b, c]
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)))
    (hzrest : ∀ y ∈ rest, y ≠ z1 ∧ y ≠ z2)
    (a' b' p' : ℂ) (rest'' : List ℂ) (r' : ℕ)
    (hrot' : (a :: c :: rest).rotate r' = a' :: b' :: a :: c :: rest'')
    (hb'rest : b' ∈ rest) (ha'V : a' ∈ V) (hb'V : b' ∈ V) (ha'b : b ≠ a')
    (hp' : (c :: rest'').getLast? = some p')
    (hpt' : HexArea.cross (a' - p') (a - a') ≠ 0)
    (hempty' : ∀ x ∈ (c :: rest''), ¬ HexArea.inTriangleStrict a' b' a x)
    (hdiag' : ∀ x ∈ (c :: rest''), x ∉ segment ℝ a' a)
    (horient' : ((0:ℝ) < HexArea.shoelace2 [a', b', a]
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: a :: c :: rest'')))
    (hturnA : HexArea.cross (a - a') (b - a) ≠ 0) :
    EmptyCornerData2 V z1 z2 := by
  -- Apply `clip_ear_lift_general` to get the required rotation.
  obtain ⟨r'', hr''⟩ : ∃ r'', (a :: b :: c :: rest).rotate r'' = a' :: b' :: a :: b :: c :: rest'' := by
    apply clip_ear_lift_general a b c rest [a', b'] rest'' r' hac hanr hrot';
  refine' ⟨ r + r'', a', b', a, p', b, b :: c :: rest'', _, _, _, _, _ ⟩ <;> simp_all +decide [ List.rotate_rotate ];
  · rw [ ← hr'', ← hrot, List.rotate_rotate ];
  · refine' ⟨ _, _, _ ⟩;
    · replace hrot := congr_arg List.toFinset hrot; rw [ Finset.ext_iff ] at hrot; specialize hrot a; aesop;
    · have haV : a ∈ V := by
        have hmem : a ∈ V.rotate r := by rw [hrot]; simp
        exact List.mem_rotate.mp hmem
      grind +suggestions;
    · have hshoelace : HexArea.shoelace2 (a' :: a :: b :: c :: rest'') = HexArea.shoelace2 (a' :: a :: c :: rest'') + HexArea.shoelace2 [a, b, c] := by
        convert shoelace2_insert_mid [ a' ] rest'' a b c using 1;
      have hshoelace : HexArea.shoelace2 (a :: c :: rest) = HexArea.shoelace2 (a' :: a :: c :: rest'') + HexArea.shoelace2 [a', b', a] := by
        have hshoelace : HexArea.shoelace2 (a :: c :: rest) = HexArea.shoelace2 ((a :: c :: rest).rotate r') := by
          exact?;
        rw [hshoelace, hrot'];
        convert shoelace2_insert_mid [ a' ] ( c :: rest'' ) a' b' a using 1; all_goals simp +decide [ HexArea.shoelace2 ];
      grind

/-
**Seam-B apex re-insertion (pure list surgery).**  In Case B of
    `boundary_seam_split` the junction `a → c` wraps the rotation seam.  Rotating
    `hrot'` by one makes `a :: c` internal as `(b' :: c' :: s') ++ a :: c :: []`,
    so `clip_ear_lift_general` (with `pre = b' :: c' :: s'`, `suf = []`) inserts
    the apex `b`, and a further rotation returns the head to `c`, exhibiting the
    lifted `V`-rotation `c :: b' :: c' :: (s' ++ [a, b])`.  Consumed by
    `boundary_lift_caseB_nonspike`.
-/
lemma clip_ear_lift_seamB (a b c c' b' : ℂ) (rest s' : List ℂ) (r' : ℕ)
    (hac : a ≠ c) (hanr : a ∉ rest)
    (hrot' : (a :: c :: rest).rotate r' = c :: b' :: c' :: (s' ++ [a])) :
    ∃ ρ, (a :: b :: c :: rest).rotate ρ = c :: b' :: c' :: (s' ++ [a, b]) := by
  have hrot1 : (a :: c :: rest).rotate (r' + 1) = (b' :: c' :: s') ++ a :: c :: [] := by
    -- Apply the lemma that rotating a list by n+1 is the same as rotating by n and then rotating by 1.
    have hrotate_step : (a :: c :: rest).rotate (r' + 1) = ((a :: c :: rest).rotate r').rotate 1 := by
      simp +decide [ List.rotate_rotate ];
    simp_all +decide [ List.rotate ]
  generalize_proofs at *; (
  obtain ⟨r'', hr''⟩ : ∃ r'', (a :: b :: c :: rest).rotate r'' = b' :: c' :: (s' ++ [a, b, c]) := by
    apply clip_ear_lift_general a b c rest (b' :: c' :: s') [] (r' + 1) hac hanr hrot1
  generalize_proofs at *; (
  use r'' + (b' :: c' :: (s' ++ [a, b])).length
  simp_all +decide [ List.rotate_rotate ];
  convert congr_arg ( fun l => l.rotate ( l.length - 1 ) ) hr'' using 1;
  · rw [ ← List.rotate_rotate ] ; simp +arith +decide [ hr'' ] ;
  · simp +decide [ List.rotate ];
    simp +arith +decide [ List.take_append ]))

/-
**Boundary-seam lift, Case B, non-spike subcase (PROVED).**  In Case B of
    `boundary_seam_split` the returned clip ear is `c :: b' :: c' :: (s' ++ [a])`
    (its diagonal endpoint `a'` coincides with the junction vertex `c`, and the
    tail ends with `a`).  Re-inserting the convex apex `b` between `a` and `c`
    (via `clip_ear_lift_general`, after rotating the junction internal) yields
    the genuine `V`-rotation `c :: b' :: c' :: (s' ++ [a, b])`.  The ear
    `(c, b', c')` is then an `EmptyCornerData2` ear of `V`: the surviving clip
    turn `hqt'` gives the turn at `c'`, while the turn at the new neighbour `b`
    of the diagonal endpoint `c` is the apex turn `cross (c - b) (c' - c)`,
    supplied non-zero by `hturnB` (the non-spike hypothesis).  Mirrors
    `boundary_lift_caseA_nonspike`.  The genuinely open content is only the spike
    case (`cross (c - b) (c' - c) = 0`), left in `empty_branch_boundary_lift`.
-/
lemma boundary_lift_caseB_nonspike (V : List ℂ) (z1 z2 : ℂ)
    (a b c : ℂ) (rest : List ℂ) (r : ℕ)
    (hrot : V.rotate r = a :: b :: c :: rest)
    (hac : a ≠ c) (hanr : a ∉ rest) (hba : b ≠ a) (hbc : b ≠ c)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (horient : ((0:ℝ) < HexArea.shoelace2 [a, b, c]
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)))
    (hzrest : ∀ y ∈ rest, y ≠ z1 ∧ y ≠ z2)
    (b' c' q' : ℂ) (s' : List ℂ) (r' : ℕ)
    (hrot' : (a :: c :: rest).rotate r' = c :: b' :: c' :: (s' ++ [a]))
    (hb'rest : b' ∈ rest) (hc'V : c' ∈ V) (hb'V : b' ∈ V) (hb'c : b ≠ c')
    (hq' : (s' ++ [a]).head? = some q')
    (hqt' : HexArea.cross (c' - c) (q' - c') ≠ 0)
    (hempty' : ∀ x ∈ (s' ++ [a]), ¬ HexArea.inTriangleStrict c b' c' x)
    (hdiag' : ∀ x ∈ (s' ++ [a]), x ∉ segment ℝ c c')
    (horient' : ((0:ℝ) < HexArea.shoelace2 [c, b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (c :: c' :: (s' ++ [a]))))
    (hturnB : HexArea.cross (c - b) (c' - c) ≠ 0) :
    EmptyCornerData2 V z1 z2 := by
  obtain ⟨ ρ, hρ ⟩ := clip_ear_lift_seamB a b c c' b' rest s' r' hac hanr hrot';
  refine' ⟨ r + ρ, c, b', c', b, q', s' ++ [ a, b ], _, _, _, _, _ ⟩ <;> simp_all +decide [ List.rotate_rotate ];
  · rw [ ← hρ, ← hrot, List.rotate_rotate ];
  · have hrotate : HexArea.shoelace2 (c :: c' :: (s' ++ [a, b])) = HexArea.shoelace2 (a :: b :: c :: c' :: s') := by
      have hrotate : ∃ n : ℕ, (c :: c' :: (s' ++ [a, b])).rotate n = a :: b :: c :: c' :: s' := by
        use 2 + s'.length;
        simp +arith +decide [ Nat.mod_eq_of_lt ];
      obtain ⟨ n, hn ⟩ := hrotate;
      rw [ ← hn, shoelace2_rotate ];
    have hrotate : HexArea.shoelace2 (a :: b :: c :: c' :: s') = HexArea.shoelace2 (a :: c :: c' :: s') + HexArea.shoelace2 [a, b, c] := by
      grind +suggestions;
    have hrotate : HexArea.shoelace2 (a :: c :: rest) = HexArea.shoelace2 (c :: c' :: (s' ++ [a])) + HexArea.shoelace2 [c, b', c'] := by
      have hrotate : HexArea.shoelace2 (a :: c :: rest) = HexArea.shoelace2 (c :: b' :: c' :: (s' ++ [a])) := by
        rw [ ← hrot', shoelace2_rotate ];
      convert shoelace2_insert_mid [] ( s' ++ [ a ] ) c b' c' using 1;
    have hrotate : HexArea.shoelace2 (a :: c :: c' :: s') = HexArea.shoelace2 (c :: c' :: (s' ++ [a])) := by
      have hrotate : ∀ (L : List ℂ), HexArea.shoelace2 (L ++ [a]) = HexArea.shoelace2 (a :: L) := by
        intro L; induction L <;> simp_all +decide [ HexArea.shoelace2 ] ;
        cases ‹List ℂ› <;> simp_all +decide [ HexArea.shoelaceOpen ] ; ring;
        grind +qlia;
      convert hrotate ( c :: c' :: s' ) |> Eq.symm using 1;
    refine' ⟨ _, _, _ ⟩;
    · replace hrot := congr_arg List.toFinset hrot; rw [ Finset.ext_iff ] at hrot; specialize hrot c; aesop;
    · replace hrot := congr_arg List.toFinset hrot; rw [ Finset.ext_iff ] at hrot; specialize hrot c; aesop;
    · grind +splitIndPred

/-
**Segment split at an interior point.**  If `w` lies on the closed segment
    `[u, v]`, then `[u, v]` is covered by the two sub-segments `[u, w]` and
    `[w, v]`.  Sorry-free preparation (with `PolygonSimple_remove_flat_mid`) for
    the flat-cut-vertex removal of `meisters_reduction_interior2`.
-/
lemma segment_subset_union_of_mem (u v w : ℂ) (hw : w ∈ segment ℝ u v) :
    segment ℝ u v ⊆ segment ℝ u w ∪ segment ℝ w v := by
  intro p hp;
  simp_all +decide [ segment_eq_image ];
  rcases hw with ⟨ x, hx, rfl ⟩ ; rcases hp with ⟨ y, hy, rfl ⟩ ; (rcases lt_trichotomy y x with h | rfl | h );
  · refine Or.inl ⟨ y / x, ⟨ by rw [ le_div_iff₀ ] <;> linarith, by rw [ div_le_iff₀ ] <;> linarith ⟩, ?_ ⟩ ; ring;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < x from lt_of_le_of_lt hy.1 h ) ] ; ring;
    simp +decide [ mul_assoc, mul_comm ( x : ℂ ), show x ≠ 0 by linarith ];
  · exact Or.inr ⟨ 0, by norm_num, by norm_num ⟩;
  · refine' Or.inr ⟨ ( y - x ) / ( 1 - x ), ⟨ _, _ ⟩, _ ⟩;
    · exact div_nonneg ( by linarith ) ( by linarith );
    · rw [ div_le_iff₀ ] <;> linarith;
    · norm_num [ Complex.ext_iff, hx, hy, h.ne', sub_ne_zero.mpr ( by linarith : ( 1 : ℝ ) ≠ x ) ] ; ring;
      norm_cast; norm_num [ show ( 1 - x ) ≠ 0 by linarith ] ; ring_nf ;
      grind

/-
**Edge surgery for flat-vertex removal: every cyclic edge of the shortened
    polygon is either the merged edge or a cyclic edge of the original.**  Pure
    list combinatorics over `closedEdges = zip with rotate 1`.  Sorry-free
    preparation for `PolygonSimple_remove_flat_mid`.
-/
lemma mem_closedEdges_remove_mid (pre suf : List ℂ) (u w v : ℂ) (e : ℂ × ℂ)
    (he : e ∈ closedEdges (pre ++ u :: v :: suf)) :
    e = (u, v) ∨ e ∈ closedEdges (pre ++ u :: w :: v :: suf) := by
  induction' pre with pre_head pre_tail pre_ih generalizing u w v e <;> simp_all +decide [ List.rotate ];
  · rcases suf with ( _ | ⟨ x, _ | ⟨ y, suf ⟩ ⟩ ) <;> simp_all +decide [ closedEdges ]; all_goals grind;
  · unfold closedEdges at *; simp_all +decide [ List.zip ] ;
    rw [ List.mem_iff_get ] at he; rcases he with ⟨ i, hi ⟩ ; rcases i with ( _ | i ) <;> simp_all +decide [ List.get ] ;
    · cases pre_tail <;> aesop;
    · rcases le_or_gt ( List.length pre_tail ) i with hi' | hi' <;> simp_all +decide [ List.getElem_append, List.getElem?_append ];
      · rcases i' : i - pre_tail.length with ( _ | _ | i' ) <;> simp_all +decide [ List.get ];
        · rw [ Nat.sub_eq_iff_eq_add ] at i' <;> aesop;
        · rw [ Nat.sub_eq_iff_eq_add ] at i' <;> try linarith;
          rw [ ← hi ];
          simp +arith +decide [ i', List.getElem_append ];
          rcases suf with ( _ | ⟨ x, suf ⟩ ) <;> simp +arith +decide [ List.get ] at *;
          · rw [ List.mem_iff_get ] ; simp +arith +decide [ List.get ];
            exact Or.inr ⟨ ⟨ pre_tail.length + 3, by simp +arith +decide ⟩, by simp +arith +decide, by simp +arith +decide ⟩;
          · rw [ List.mem_iff_get ] ; simp +arith +decide [ List.get ];
            refine' Or.inr ⟨ ⟨ pre_tail.length + 3, _ ⟩, _, _ ⟩ <;> simp +arith +decide [ List.get ];
        · rw [ ← hi ] ; simp +decide [ List.getElem_append, List.getElem?_append, i' ] ;
          rw [ List.mem_iff_get ] ; simp +decide [ List.getElem_append, List.getElem?_append, i' ] ;
          refine' Or.inr ⟨ ⟨ i + 1 - pre_tail.length + pre_tail.length + 1, _ ⟩, _, _ ⟩ <;> simp +decide [ List.getElem_append, List.getElem?_append, i' ];
          grind; all_goals grind;
      · refine' Or.inr _;
        rw [ List.mem_iff_get ] ; use ⟨ i + 1, by
          grind ⟩ ; simp +decide [ List.get ];
        grind

/-
**The two incident edges of the flat vertex are genuine cyclic edges.**
    Sorry-free preparation for `PolygonSimple_remove_flat_mid`.
-/
lemma uw_wv_mem_closedEdges (pre suf : List ℂ) (u w v : ℂ) :
    (u, w) ∈ closedEdges (pre ++ u :: w :: v :: suf) ∧
    (w, v) ∈ closedEdges (pre ++ u :: w :: v :: suf) := by
  unfold closedEdges;
  constructor <;> rw [ List.mem_iff_get ];
  · use ⟨ pre.length, by simp +arith +decide ⟩ ; simp +decide [ List.get ] ;
    simp +decide [ List.rotate ];
    simp +arith +decide [ List.getElem_append ];
  · use ⟨ pre.length + 1, by simp +arith +decide ⟩ ; simp +arith +decide [ List.get ] ;
    simp +arith +decide [ List.rotate ]

/-
**Flat-vertex removal preserves simplicity (middle form).**  In a simple
    polygon `pre ++ u :: w :: v :: suf`, if the vertex `w` is *flat* — it lies on
    the closed segment `[u, v]` between its two cyclic neighbours — then deleting
    it yields the still-simple polygon `pre ++ u :: v :: suf`.  The two incident
    edges `u–w`, `w–v` merge into `u–v ⊆ [u,w] ∪ [w,v]`, so every disjointness
    clause of `PolygonSimple` is inherited and `Nodup` survives deletion.
    Reusable preparation for the flat-cut-vertex removal step of
    `meisters_reduction_interior2` (rotate the flat seam vertex into the middle,
    remove, rotate back).  NOT a dead branch.
-/
lemma PolygonSimple_remove_flat_mid (pre suf : List ℂ) (u w v : ℂ)
    (hsimple : PolygonSimple (pre ++ u :: w :: v :: suf))
    (hflat : w ∈ segment ℝ u v) :
    PolygonSimple (pre ++ u :: v :: suf) := by
  refine' ⟨ _, _ ⟩;
  · have := hsimple.1; simp_all +decide [ List.nodup_append ] ;
  · intro e₁ he₁ e₂ he₂ h₁ h₂ h₃ h₄
    by_cases he₁uv : e₁ = (u, v)
    by_cases he₂uv : e₂ = (u, v);
    · aesop;
    · have hseam : e₂ ∈ closedEdges (pre ++ u :: w :: v :: suf) := by
        exact mem_closedEdges_remove_mid _ _ _ _ _ _ he₂ |> Or.resolve_left <| by aesop;
      have hseam : e₂.1 ≠ w ∧ e₂.2 ≠ w := by
        have hseam : ∀ x ∈ pre ++ u :: v :: suf, x ≠ w := by
          have := hsimple.1; simp_all +decide [ List.nodup_append ] ;
          grind +ring;
        unfold closedEdges at he₂; simp_all +decide [ List.mem_iff_get ] ;
        rcases he₂ with ⟨ n, rfl ⟩ ; simp_all +decide [ List.getElem_rotate ] ;
        exact ⟨ by rename_i h; exact h ⟨ n, by simpa using n.2 ⟩, by rename_i h; exact h ⟨ ( n + 1 ) % ( pre.length + ( suf.length + 1 + 1 ) ), by simpa using Nat.mod_lt _ ( by simp +arith +decide ) ⟩ ⟩;
      have hseam : Disjoint (segment ℝ u w) (segment ℝ e₂.1 e₂.2) ∧ Disjoint (segment ℝ w v) (segment ℝ e₂.1 e₂.2) := by
        have := hsimple.2 ( u, w ) ( uw_wv_mem_closedEdges pre suf u w v |>.1 ) e₂ ‹_›; have := hsimple.2 ( w, v ) ( uw_wv_mem_closedEdges pre suf u w v |>.2 ) e₂ ‹_›; simp_all +decide [ Set.disjoint_left ] ;
        grind;
      intro a ha; specialize hseam; have := segment_subset_union_of_mem u v w hflat; simp_all +decide [ Set.subset_def ] ;
      grind;
    · by_cases he₂uv : e₂ = (u, v);
      · have h_disjoint_uw : Disjoint (segment ℝ e₁.1 e₁.2) (segment ℝ u w) := by
          have h_disjoint_uw : e₁ ∈ closedEdges (pre ++ u :: w :: v :: suf) := by
            exact mem_closedEdges_remove_mid _ _ _ _ _ _ he₁ |> Or.resolve_left <| by aesop;
          apply hsimple.2 e₁ h_disjoint_uw (u, w) (uw_wv_mem_closedEdges pre suf u w v).left;
          · grind;
          · have := hsimple.1;
            contrapose! h₁; have := hsimple.2; simp_all +decide [ closedEdges ] ;
            rw [ List.mem_iff_get ] at he₁; obtain ⟨ i, hi ⟩ := he₁; simp_all +decide [ List.get ] ;
            grind;
          · grind +ring;
          · have h_mem : ∀ e ∈ closedEdges (pre ++ u :: v :: suf), e.1 ∈ pre ++ u :: v :: suf ∧ e.2 ∈ pre ++ u :: v :: suf := by
              intros e he; exact (by
              unfold closedEdges at he; simp_all +decide [ List.mem_iff_get ] ;
              rcases he with ⟨ n, rfl ⟩ ; simp +decide [ List.getElem_rotate ] ;
              exact ⟨ ⟨ ⟨ n, by simpa using n.2 ⟩, rfl ⟩, ⟨ ⟨ ( n + 1 ) % ( pre.length + ( suf.length + 1 + 1 ) ), by
                exact lt_of_lt_of_le ( Nat.mod_lt _ ( by simp +arith +decide ) ) ( by simp +arith +decide ) ⟩, rfl ⟩ ⟩);
            have := hsimple.1; simp_all +decide [ List.nodup_append ] ;
            grind
        have h_disjoint_wv : Disjoint (segment ℝ e₁.1 e₁.2) (segment ℝ w v) := by
          have h_disjoint_wv : (w, v) ∈ closedEdges (pre ++ u :: w :: v :: suf) := by
            exact uw_wv_mem_closedEdges pre suf u w v |>.2;
          apply hsimple.2 e₁ (by
          exact mem_closedEdges_remove_mid _ _ _ _ _ _ he₁ |> Or.resolve_left <| by aesop;) (w, v) h_disjoint_wv (by
          contrapose! h_disjoint_uw; simp_all +decide [ segment_same ] ;
          rw [ Set.not_disjoint_iff ];
          exact ⟨ w, left_mem_segment _ _ _, right_mem_segment _ _ _ ⟩) (by
          grobner) (by
          contrapose! h_disjoint_uw; simp_all +decide [ segment_same ] ;
          exact Set.not_disjoint_iff_nonempty_inter.mpr ⟨ w, right_mem_segment _ _ _, right_mem_segment _ _ _ ⟩) (by
          grind +ring);
        have h_subset : segment ℝ u v ⊆ segment ℝ u w ∪ segment ℝ w v := by
          exact segment_subset_union_of_mem u v w hflat;
        grind;
      · have h₁' : e₁ ∈ closedEdges (pre ++ u :: w :: v :: suf) := by
          exact Or.resolve_left ( mem_closedEdges_remove_mid _ _ _ _ _ _ he₁ ) he₁uv
        have h₂' : e₂ ∈ closedEdges (pre ++ u :: w :: v :: suf) := by
          exact mem_closedEdges_remove_mid _ _ _ _ _ _ he₂ |> Or.resolve_left <| by aesop;
        exact hsimple.2 e₁ h₁' e₂ h₂' h₁ h₂ h₃ h₄

/-
**Flat-vertex removal preserves the predecessor corner (geometric half).**
    If `w` lies on `[u, v]`, then `w - u` is a (nonnegative) real multiple of
    `v - u`, so the corner turn `cross (u - x) (· - u)` at `u` cannot become flat
    by replacing the neighbour `w` with `v`: a non-flat corner `(x, u, w)` stays
    non-flat as `(x, u, v)`.  Sorry-free preparation for the `polyCycNondeg` half
    of the flat-cut-vertex removal in `meisters_reduction_interior2`.
-/
lemma cross_pred_corner_remove_flat (x u v w : ℂ) (hw : w ∈ segment ℝ u v)
    (h : HexArea.cross (u - x) (w - u) ≠ 0) :
    HexArea.cross (u - x) (v - u) ≠ 0 := by
  obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hw;
  contrapose! h; simp_all +decide [ HexArea.cross ] ; ring;
  grind

/-
**Flat-vertex removal preserves the successor corner (geometric half).**
    If `w` lies on `[u, v]`, then `v - w` is a (nonnegative) real multiple of
    `v - u`, so the corner turn at `v` cannot become flat by replacing the
    neighbour `w` with `u`: a non-flat corner `(w, v, y)` stays non-flat as
    `(u, v, y)`.  Sorry-free preparation for the `polyCycNondeg` half of the
    flat-cut-vertex removal in `meisters_reduction_interior2`.
-/
lemma cross_succ_corner_remove_flat (y u v w : ℂ) (hw : w ∈ segment ℝ u v)
    (h : HexArea.cross (v - w) (y - v) ≠ 0) :
    HexArea.cross (v - u) (y - v) ≠ 0 := by
  simp_all +decide [ segment_eq_image, HexArea.cross ];
  obtain ⟨ x, hx, rfl ⟩ := hw; ring_nf at h ⊢;
  cases lt_or_gt_of_ne h <;> norm_num [ Complex.ext_iff ] at * <;> nlinarith

end
