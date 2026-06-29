/-
# Diagonal-split combinatorial infrastructure for the Meisters ear search

This file collects the **purely combinatorial list-surgery** facts needed by the
diagonal-split recursion at the heart of the discrete Hopf Umlaufsatz
(`exists_empty_corner_avoiding` in `RequestProject.SAWUmlaufPolygon`).

The Meisters "two-ears" proof proceeds by strong induction on the number of
vertices: a simple polygon with `≥ 4` vertices has an interior diagonal joining
two non-adjacent vertices; rotating so the diagonal joins `V[0]` and `V[k]`
(`2 ≤ k ≤ V.length - 2`), the diagonal cuts the cycle into two strictly shorter
sub-polygons that share exactly the diagonal:

* `chordLeft  V k = V₀, V₁, …, V_k`              (`= V.take (k+1)`)
* `chordRight V k = V_k, V_{k+1}, …, V_{n-1}, V₀` (`= V.drop k ++ V.take 1`)

The genuinely *topological* facts (that such a diagonal exists, and that each
sub-polygon is again `PolygonSimple`) are the Jordan-curve-theorem-level content
and live with the open core.  Everything in **this** file is the elementary
bookkeeping that surrounds them: the lengths of the two pieces, that they are
both strictly shorter than `V` yet still have `≥ 3` vertices, that together they
cover every vertex of `V`, and that they meet the shared diagonal correctly at
their endpoints (`head?`/`getLast?`).

This file is **preparation**: it is imported by `RequestProject.SAWUmlaufPolygon`
(hence transitively from `RequestProject.SAWFinal`), so it is part of the build
chain.  Its lemmas are designed to be consumed by the eventual proof of
`exists_empty_corner_avoiding`; they are not yet referenced by another
declaration only because the core they feed is still open.  This is intentional,
recorded partial progress, not a dead branch.
-/

import Mathlib
import RequestProject.SAWUmlaufEar

open Complex

noncomputable section

namespace HexArea

/-- Left sub-polygon of the chord `V[0]–V[k]`: the vertices `V₀, V₁, …, V_k`. -/
def chordLeft (V : List ℂ) (k : ℕ) : List ℂ := V.take (k + 1)

/-- Right sub-polygon of the chord `V[0]–V[k]`: the vertices
    `V_k, V_{k+1}, …, V_{n-1}, V₀`. -/
def chordRight (V : List ℂ) (k : ℕ) : List ℂ := V.drop k ++ V.take 1

/-- The left piece has exactly `k + 1` vertices when the chord index is in range. -/
lemma chordLeft_length (V : List ℂ) (k : ℕ) (hk : k + 1 ≤ V.length) :
    (chordLeft V k).length = k + 1 := by
  simp [chordLeft, Nat.min_eq_left hk]

/-- The right piece has exactly `n - k + 1` vertices when the chord index is in
    range (`k < n`). -/
lemma chordRight_length (V : List ℂ) (k : ℕ) (hk : k < V.length) :
    (chordRight V k).length = V.length - k + 1 := by
  simp [chordRight]; omega

/-- The left piece has at least three vertices when `2 ≤ k`. -/
lemma chordLeft_length_ge (V : List ℂ) (k : ℕ) (hk2 : 2 ≤ k)
    (hk : k + 1 ≤ V.length) : 3 ≤ (chordLeft V k).length := by
  rw [chordLeft_length V k hk]; omega

/-- The right piece has at least three vertices when `k ≤ n - 2`. -/
lemma chordRight_length_ge (V : List ℂ) (k : ℕ) (hk : k + 2 ≤ V.length) :
    3 ≤ (chordRight V k).length := by
  rw [chordRight_length V k (by omega)]; omega

/-- The left piece is strictly shorter than the whole cycle when `k ≤ n - 2`. -/
lemma chordLeft_length_lt (V : List ℂ) (k : ℕ) (hk : k + 2 ≤ V.length) :
    (chordLeft V k).length < V.length := by
  rw [chordLeft_length V k (by omega)]; omega

/-- The right piece is strictly shorter than the whole cycle when `2 ≤ k`
    (and `k < n`). -/
lemma chordRight_length_lt (V : List ℂ) (k : ℕ) (hk2 : 2 ≤ k)
    (hk : k < V.length) : (chordRight V k).length < V.length := by
  rw [chordRight_length V k hk]; omega

/-- The left piece starts at `V₀`. -/
lemma chordLeft_head (V : List ℂ) (k : ℕ) :
    (chordLeft V k).head? = V.head? := by
  cases V <;> simp [chordLeft]

/-- The right piece ends at `V₀` (closing the diagonal back to the start). -/
lemma chordRight_getLast (V : List ℂ) (k : ℕ) (hV : V ≠ []) (hk : k < V.length) :
    (chordRight V k).getLast? = V.head? := by
  rw [chordRight, List.getLast?_append]
  cases V with
  | nil => simp
  | cons a t => simp

/-- The left piece ends at `V_k`. -/
lemma chordLeft_getLast (V : List ℂ) (k : ℕ) (hk : k < V.length) :
    (chordLeft V k).getLast? = V[k]? := by
  rw [chordLeft, List.getLast?_eq_getElem?, List.getElem?_take]
  simp [Nat.min_eq_left (by omega : k + 1 ≤ V.length)]

/-- The right piece starts at `V_k`. -/
lemma chordRight_head (V : List ℂ) (k : ℕ) (hk : k < V.length) :
    (chordRight V k).head? = V[k]? := by
  have h : (V.drop k).head? = V[k]? := by
    simp [List.head?_drop, List.getElem?_eq_getElem hk]
  rw [chordRight, List.head?_append, h, List.getElem?_eq_getElem hk]
  rfl

/-- Together the two pieces cover every vertex of the cycle: any vertex of `V`
    lies in the left piece or the right piece. -/
lemma mem_chord_split (V : List ℂ) (k : ℕ) (hk : k < V.length) (x : ℂ)
    (hx : x ∈ V) : x ∈ chordLeft V k ∨ x ∈ chordRight V k := by
  rw [← List.take_append_drop (k + 1) V] at hx
  rcases List.mem_append.mp hx with h | h
  · exact Or.inl h
  · right
    rw [chordRight, List.mem_append]
    left
    have h2 : x ∈ (V.drop k).drop 1 := by
      rw [List.drop_drop]; convert h using 2
    exact List.mem_of_mem_drop h2

/-- The left split piece `V₀,…,V_k` inherits `Nodup` from the whole cycle: it is
    a prefix of `V`, hence a sublist.  This is the `Nodup` half of
    `PolygonSimple` preservation under the diagonal split. -/
lemma chordLeft_nodup (V : List ℂ) (k : ℕ) (hV : V.Nodup) :
    (chordLeft V k).Nodup :=
  hV.sublist (List.take_sublist _ _)

/-
The right split piece `V_k,…,V_{n-1},V₀` inherits `Nodup` from the whole
    cycle (for a chord with `1 ≤ k`): the suffix `V.drop k` is a sublist of `V`
    (hence `Nodup`), the singleton `V.take 1 = [V₀]` is trivially `Nodup`, and
    they are disjoint because `V₀` occurs in the `Nodup` cycle only at index `0`,
    which is dropped when `1 ≤ k`.  This is the `Nodup` half of `PolygonSimple`
    preservation under the diagonal split.
-/
lemma chordRight_nodup (V : List ℂ) (k : ℕ) (hk1 : 1 ≤ k) (hk : k < V.length)
    (hV : V.Nodup) : (chordRight V k).Nodup := by
  convert List.Nodup.append ?_ ?_ ?_ using 1;
  · exact hV.sublist ( List.drop_sublist _ _ );
  · exact hV.sublist ( List.take_sublist _ _ );
  · cases V <;> simp_all +decide [ List.disjoint_left ];
    rw [ List.mem_iff_getElem ];
    grind

/-- **Reverse membership for the left piece.**  Every vertex of `chordLeft V k`
    is a vertex of `V` (it is the prefix `V.take (k+1)`, hence a sublist).
    Preparation for the interior-branch ear lift in
    `meisters_reduction_interior2`: transferring vertex data from a chord piece
    back to `V`.  Sorry-free; not a dead branch. -/
lemma mem_of_mem_chordLeft (V : List ℂ) (k : ℕ) {x : ℂ}
    (hx : x ∈ chordLeft V k) : x ∈ V :=
  (List.take_sublist _ _).subset hx

/-- **Reverse membership for the right piece.**  Every vertex of `chordRight V k`
    is a vertex of `V` (it is `V.drop k ++ V.take 1`, both sublists of `V`).
    Preparation for the interior-branch ear lift in
    `meisters_reduction_interior2`.  Sorry-free; not a dead branch. -/
lemma mem_of_mem_chordRight (V : List ℂ) (k : ℕ) {x : ℂ}
    (hx : x ∈ chordRight V k) : x ∈ V := by
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_of_mem_drop h
  · exact List.mem_of_mem_take h

/-
**Signed-area additivity across the chord cut (sorry-free, reusable).**
    Cutting the closed polygon `V` along the diagonal `V[0]–V[k]`
    (`1 ≤ k < V.length`) into the two pieces `chordLeft V k` and
    `chordRight V k` is *area-preserving*: the (twice-)signed areas of the two
    pieces add up to that of `V`.  The shared diagonal contributes
    `cross V[k] V[0]` to the left piece and `cross V[0] V[k]` to the right
    piece, and these cancel (`cross_antisymm`); the remaining open chains
    reassemble the closed shoelace of `V`.

    This is the pure-algebra ingredient of the orientation transfer in the
    interior-branch ear lift (`meisters_reduction_interior2`): a chord piece
    has the *same* orientation sign as `V` exactly when the OTHER piece's area
    has the same sign, which the Jordan-interior diagonal guarantees.  Recorded
    preparation; not a dead branch.
-/
lemma shoelace2_chord_split (V : List ℂ) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k < V.length) :
    shoelace2 (chordLeft V k) + shoelace2 (chordRight V k) = shoelace2 V := by
  rcases V with ( _ | ⟨ v, _ | ⟨ w, V ⟩ ⟩ ) <;> norm_num at *;
  · grind;
  · induction' k with k ih generalizing v w V <;> simp_all +decide [ List.take, List.drop ];
    rcases k with ( _ | k ) <;> simp_all +decide [ chordLeft, chordRight ];
    · unfold shoelace2;
      induction V <;> simp_all +decide [ List.getLast? ];
      · unfold cross; ring;
      · cases ‹List ℂ› <;> simp_all +decide [ shoelaceOpen ] ; ring;
        · linear_combination' ‹cross w v + cross v w = 0›;
        · linarith [ cross_antisymm v w ];
    · cases V <;> simp_all +decide [ List.take, List.drop ];
      grind +suggestions

/-
**The two chord pieces share only the two cut vertices.**  For a `Nodup`
    cycle `V` cut at `1 ≤ k < V.length`, a vertex lying in BOTH `chordLeft V k`
    and `chordRight V k` must be one of the two diagonal endpoints `V[0]` or
    `V[k]`.  This is the vertex-disjointness needed for *piece selection* in the
    split branches (`meisters_reduction_interior2`, `empty_branch_bad_lift`): a
    forbidden cyclic edge `{z1,z2}` that lands in one piece cannot have an
    interior vertex of the other piece equal to `z1` or `z2`, so the ear tip
    returned by recursion on the other piece avoids the forbidden pair.
    Sorry-free, reusable; not a dead branch.
-/
lemma chord_pieces_inter (V : List ℂ) (k : ℕ) (hk1 : 1 ≤ k) (hk : k < V.length)
    (hV : V.Nodup) {x : ℂ} (hL : x ∈ chordLeft V k) (hR : x ∈ chordRight V k) :
    x = V[0]! ∨ x = V[k]! := by
  simp_all +decide [ chordLeft, chordRight ];
  rcases hR with ( hR | hR ) <;> rw [ List.mem_iff_getElem ] at * <;> simp_all +decide [ List.getElem?_take, List.getElem?_drop ];
  · grind +suggestions;
  · grind

end HexArea

end