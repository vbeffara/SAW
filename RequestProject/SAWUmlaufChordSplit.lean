import RequestProject.SAWUmlaufPolygon

/-!
# Interior-diagonal split: reusable simplicity brick

This file develops reusable infrastructure for the **interior-diagonal split**
of a simple polygon — the combinatorial half of the Jordan-curve content that
the Meisters two-ears induction needs in
`RequestProject.SAWUmlaufPolygon` (the open branches
`meisters_reduction_interior2` and the bad-diagonal subcase of
`meisters_reduction_empty2`).

The geometric heart (a diagonal of a simple polygon does not cross any edge) is
already available as `seg_diagonal_disjoint_of_corner`.  What is missing is the
*list-combinatorial* packaging: given a simple **path** `P` (a Hamiltonian-ish
arc of the polygon) whose consecutive edges are pairwise disjoint and whose
closing chord `last–head` is clear of every non-incident path edge, the closed
polygon `P` is `PolygonSimple`.  This is exactly what each split piece needs:
its path edges are inherited (verbatim) from the parent polygon's simplicity,
and its single new edge is the cut diagonal.

These lemmas are **preparation for future use** (the interior-split branch); the
file is imported into `RequestProject.SAWFinal` so it is part of the build and
logically linked to the main development, even though the open branches do not
yet consume it.
-/

namespace HexArea

/-- The **non-cyclic** (path) edges of a vertex list `P`: the consecutive pairs
    `(P₀,P₁), (P₁,P₂), …, (P_{n-1},P_n)`, omitting the wrap-around edge.  Built as
    `P.zip P.tail`.  The cyclic edges are `pathEdges P ++ [(last, head)]`
    (`closedEdges_eq_pathEdges`). -/
def pathEdges (P : List ℂ) : List (ℂ × ℂ) := P.zip P.tail

@[simp] lemma pathEdges_nil : pathEdges ([] : List ℂ) = [] := rfl
@[simp] lemma pathEdges_singleton (a : ℂ) : pathEdges [a] = [] := rfl

lemma pathEdges_cons_cons (a b : ℂ) (rest : List ℂ) :
    pathEdges (a :: b :: rest) = (a, b) :: pathEdges (b :: rest) := by
  simp [pathEdges]

/-- `(p :: rest).rotate 1 = rest ++ [p]`: a single cyclic shift moves the head
    to the back. -/
lemma rotate_one_cons (p : ℂ) (rest : List ℂ) :
    (p :: rest).rotate 1 = rest ++ [p] := by
  rw [List.rotate_cons_succ]; simp

/-
**Cyclic edges = path edges plus the closing chord.**  For a vertex list `P`
    with head `u` and last `v`, the closed-polygon edges decompose as the path
    edges followed by the single wrap-around edge `(v, u)`.
-/
lemma closedEdges_eq_pathEdges (P : List ℂ) (u v : ℂ)
    (hhead : P.head? = some u) (hlast : P.getLast? = some v) :
    closedEdges P = pathEdges P ++ [(v, u)] := by
  rcases P with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide [ pathEdges ];
  · unfold closedEdges; aesop;
  · induction l generalizing u y <;> simp_all +decide [ closedEdges ]

/-
**Membership in path edges implies membership in cyclic edges.**  Every path
    edge of `P` is also a closed edge.  Used to inherit the pairwise edge
    disjointness of a split piece from the parent polygon.
-/
lemma mem_closedEdges_of_mem_pathEdges (P : List ℂ) (e : ℂ × ℂ)
    (he : e ∈ pathEdges P) : e ∈ closedEdges P := by
  rcases P with ( _ | ⟨ a, _ | ⟨ b, P ⟩ ⟩ ) <;> simp_all +decide [ pathEdges, closedEdges ];
  have h_zip_append : ∀ (l r1 r2 : List ℂ), List.zip l (r1 ++ r2) = List.zip l r1 ++ List.zip (List.drop r1.length l) r2 := by
    intros l r1 r2; induction' l with hd tl hl generalizing r1 r2 <;> cases r1 <;> cases r2 <;> simp +decide [ * ] ;
  grind

/-
**Simplicity from a simple path plus a clear closing chord.**  If `P` is
    `Nodup` with head `u ≠ v = last`, its path edges are pairwise disjoint
    (`hpath`, for edges sharing no endpoint), and the closing chord `v–u` is
    disjoint from every non-incident path edge (`hdiag`), then `P` is a
    `PolygonSimple` closed polygon.

    This is the reusable combinatorial brick of the interior-diagonal split:
    each split piece is a sub-path of the parent polygon (so `hpath` is
    inherited from the parent's `PolygonSimple` via
    `mem_closedEdges_of_mem_pathEdges`) closed by the single cut diagonal (so
    `hdiag` is the diagonal-clearance fact, supplied by
    `seg_diagonal_disjoint_of_corner`-style geometry).
-/
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

/-
**Cyclic non-degeneracy from path non-degeneracy plus two seam corners.**
    The closed polygon `P` (length `≥ 3`, head `u`, second `u2`, last `v`,
    penultimate `vp`) is cyclically non-degenerate provided all its *path*
    triples are non-flat (`hpath : polyNondeg P`) and the two wrap-around
    ("seam") corners — the corner `vp → v → u` (`hseam1`) and the corner
    `v → u → u2` (`hseam2`) — are non-flat.  This is the non-degeneracy companion
    to `PolygonSimple_of_simplePath`: in the interior-diagonal split each piece
    inherits its path triples verbatim from the parent's `polyCycNondeg`, and the
    two seam corners are exactly the two new corners at the cut diagonal's
    endpoints, supplied by the diagonal-non-flatness facts.
-/
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
  -- By definition of `polyNondeg`, we need to show that all consecutive triples in the list are non-flat.
  have h_polyNondeg : ∀ (L : List ℂ), polyNondeg L → ∀ (x y : ℂ), HexArea.cross (L.getLast! - L.dropLast.getLast!) (x - L.getLast!) ≠ 0 → HexArea.cross (x - L.getLast!) (y - x) ≠ 0 → polyNondeg (L ++ [x, y]) := by
    intros L hL x y hx hy; induction' L with a L ih generalizing x y <;> simp_all +decide [ polyNondeg_cons_cons_cons ] ;
    rcases L with ( _ | ⟨ b, _ | ⟨ c, L ⟩ ⟩ ) <;> simp_all +decide [ polyNondeg_cons_cons_cons ];
  convert h_polyNondeg ( u :: u2 :: c :: rest ) hpath u u2 _ _ using 1 <;> simp_all +decide [ List.getLast? ]

end HexArea