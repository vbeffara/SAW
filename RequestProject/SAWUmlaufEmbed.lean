/-
# Injectivity of the hex lattice embedding (Umlaufsatz preparation)

For *any* route to the discrete Hopf Umlaufsatz `umlaufsatz_pm_one`
(in `RequestProject.SAWTurningNumber`) one needs to know that the planar
polygon obtained by embedding a *simple* closed honeycomb trail has genuinely
distinct vertices in `ℂ`.  The basic fact making this work is that the
embedding `correctHexEmbed : HexVertex → ℂ` is **injective**: distinct lattice
vertices map to distinct points of the plane.

This file develops, fully sorry-free, the **simplicity transfer** needed for the
signed-area / ear-clipping route to the Umlaufsatz: it turns the weak
combinatorial hypothesis `h_simple : L.tail.dropLast.Nodup` (only the *interior*
vertices are distinct) into the genuine "distinct points in the plane" statement
about the embedded polygon.  The development has three layers:

* **Embedding injectivity:** `correctHexEmbed_injective`, `correctHexEmbed_ne`,
  `correctHexEmbed_map_nodup`.
* **3-regularity (pigeonhole):** `hexGraph_adj_mem_three` (each vertex has at
  most three explicit neighbours) and `hex_four_neighbours_not_nodup` (four
  common neighbours of a vertex cannot be pairwise distinct).
* **Index-level trail structure:** `hexTrailList_adj_get`,
  `hexTrailList_nobacktrack_get`, `hex_interior_getElem_ne`.

These combine to give the main combinatorial results:

* `hex_closed_trail_start_not_interior` — the start vertex of a simple closed
  hex trail never recurs among the interior vertices (degree-3 + no-backtrack);
* `hex_closed_trail_dropLast_nodup` — hence the full vertex cycle `L.dropLast`
  is `Nodup` (a genuinely simple polygon); and
* `hex_closed_trail_embed_nodup` — therefore the embedded polygon
  `L.dropLast.map correctHexEmbed` has pairwise distinct points in `ℂ`, exactly
  the "simple polygon" hypothesis the topological (signed-area / Jordan) half of
  `umlaufsatz_pm_one` consumes.

This file is imported from `RequestProject.SAWFinal`; it is **preparation** for
the Umlaufsatz (`umlaufsatz_pm_one` in `RequestProject.SAWTurningNumber`) and is
not yet consumed by another declaration.
-/

import Mathlib
import RequestProject.SAWTurningNumber

open Complex

noncomputable section

/-
The hex lattice embedding `correctHexEmbed` is injective: distinct lattice
    vertices have distinct images in `ℂ`.
-/
lemma correctHexEmbed_injective : Function.Injective correctHexEmbed := by
  intro v w h;
  rcases v with ⟨x, y, b⟩; rcases w with ⟨x', y', b'⟩; simp_all +decide [ correctHexEmbed ];
  cases b <;> cases b' <;> norm_num [ Complex.ext_iff ] at h;
  · exact ⟨ by norm_cast at h; linarith, by norm_cast at h; linarith, rfl ⟩;
  · rw [ div_add_one, div_eq_div_iff ] at h <;> norm_cast at * ; omega;
  · rw [ div_add_one, div_eq_div_iff ] at h <;> norm_cast at * ; omega;
  · exact ⟨ by norm_cast at h; linarith, by norm_cast at h; linarith, rfl ⟩

/-- Convenience contrapositive form of `correctHexEmbed_injective`. -/
lemma correctHexEmbed_ne {v w : HexVertex} (h : v ≠ w) :
    correctHexEmbed v ≠ correctHexEmbed w :=
  fun heq => h (correctHexEmbed_injective heq)

/-- The embedded vertices of a list with distinct entries are themselves
    distinct as points of `ℂ`: `Nodup` is preserved by the embedding. -/
lemma correctHexEmbed_map_nodup {L : List HexVertex} (h : L.Nodup) :
    (L.map correctHexEmbed).Nodup :=
  h.map correctHexEmbed_injective

/-! ## The hex lattice is 3-regular: at most three neighbours per vertex

The explicit neighbour structure of `hexGraph` gives that any vertex has at
most three neighbours.  We package the consequence we need for the simplicity
argument: four vertices all adjacent to a common vertex cannot be pairwise
distinct. -/

/-
Every neighbour of a vertex `v` in `hexGraph` is one of three explicit
    vertices (depending only on the sublattice bit of `v`).
-/
lemma hexGraph_adj_mem_three (v w : HexVertex) (h : hexGraph.Adj v w) :
    w = (v.1, v.2.1, !v.2.2) ∨
    w = (v.1 + (if v.2.2 then -1 else 1), v.2.1, !v.2.2) ∨
    w = (v.1, v.2.1 + (if v.2.2 then -1 else 1), !v.2.2) := by
  obtain ⟨a, b, c⟩ := v; obtain ⟨d, e, f⟩ := w; simp [hexGraph] at h;
  grind

/-
The hex lattice is (at most) 3-regular: four common neighbours of a vertex
    `v` cannot be pairwise distinct.  This is the pigeonhole fact underlying the
    simplicity argument for closed hex trails.
-/
lemma hex_four_neighbours_not_nodup (v a b c d : HexVertex)
    (ha : hexGraph.Adj v a) (hb : hexGraph.Adj v b)
    (hc : hexGraph.Adj v c) (hd : hexGraph.Adj v d) :
    ¬ ([a, b, c, d].Nodup) := by
  obtain ⟨N1, N2, N3, hN⟩ : ∃ N1 N2 N3 : HexVertex, ∀ w : HexVertex, hexGraph.Adj v w → w = N1 ∨ w = N2 ∨ w = N3 := by
    exact ⟨ _, _, _, fun w hw => hexGraph_adj_mem_three v w hw ⟩;
  grind

/-! ## Index-level adjacency / no-backtrack extraction from `HexTrailList` -/

/-
A `HexTrailList` of length `≥ 3` is adjacent at every consecutive index
    pair.  (Length `≥ 3` is needed: a 2-element `HexTrailList` is `True` and
    stores no adjacency.)
-/
lemma hexTrailList_adj_get (L : List HexVertex) (h : HexTrailList L)
    (hlen : 3 ≤ L.length) (k : ℕ) (hk : k + 1 < L.length) :
    hexGraph.Adj (L.get ⟨k, by omega⟩) (L.get ⟨k + 1, by omega⟩) := by
  induction' k with k ih generalizing L;
  · rcases L with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | L ⟩ ⟩ ⟩ ) <;> simp_all +decide [ HexTrailList ];
  · rcases L with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, L ⟩ ⟩ ⟩ ) <;> norm_num at *;
    rcases h with ⟨ hab, hbc, hne, hL ⟩ ; simp_all +arith +decide ;
    grind

/-
A `HexTrailList` never immediately backtracks: consecutive edges differ.
-/
lemma hexTrailList_nobacktrack_get (L : List HexVertex) (h : HexTrailList L)
    (k : ℕ) (hk : k + 2 < L.length) :
    s(L.get ⟨k, by omega⟩, L.get ⟨k + 1, by omega⟩) ≠
      s(L.get ⟨k + 1, by omega⟩, L.get ⟨k + 2, by omega⟩) := by
  induction' k with k ih generalizing L;
  · rcases L with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | L ⟩ ⟩ ⟩ ) <;> norm_num at *;
    · contradiction;
    · contradiction;
    · contradiction;
    · cases h ; aesop;
    · cases h ; aesop;
  · rcases L with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | L ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
    · contradiction;
    · contradiction;
    · contradiction;
    · grind;
    · convert ih ( b :: c :: L :: ‹_› ) ( by cases h ; tauto ) ( by simp +arith +decide at hk ⊢; linarith ) using 1

/-! ## A simple closed hex trail has a `Nodup` full vertex cycle

The simplicity hypothesis in `umlaufsatz_pm_one` (`h_simple`) only asserts that
the *interior* vertices `L.tail.dropLast` are distinct.  The honeycomb's
degree-3 structure plus the no-immediate-backtrack condition forces the start
vertex never to recur among the interior vertices, so the whole vertex cycle
`L.dropLast` is automatically `Nodup` — a genuinely simple polygon.  This is
the purely-combinatorial half of the simplicity transfer needed for the
signed-area route to the Umlaufsatz.

Proof idea: write `L.dropLast = L.head :: L.tail.dropLast`.  If the start
vertex `v₀ = L.head` occurred at an interior index `i`, then `v₀`'s successor
`L[1]`, the predecessor `L[i-1]` and successor `L[i+1]` of the interior
occurrence, and the predecessor `L[m-1]` of the closing occurrence would all be
neighbours of `v₀`.  The endpoints `i = 1`, `i = 2`, `i = m-2`, `i = m-1` are
excluded by `hexGraph` looplessness and the no-backtrack condition; the
remaining genuinely-interior case gives four *distinct* neighbours of `v₀`
(distinct by `h_simple`), contradicting `hex_four_neighbours_not_nodup`. -/

/-
Distinct *interior* indices (in `[1, L.length-2]`) of a list whose interior
    `L.tail.dropLast` is `Nodup` give distinct elements.  Here `p, q` are indices
    into `L` itself with `1 ≤ p, q ≤ L.length - 2`.
-/
lemma hex_interior_getElem_ne (L : List HexVertex)
    (h_simple : L.tail.dropLast.Nodup)
    {p q : ℕ} (hp1 : 1 ≤ p) (hq1 : 1 ≤ q)
    (hp2 : p < L.length - 1) (hq2 : q < L.length - 1) (hpq : p ≠ q) :
    L[p]'(by omega) ≠ L[q]'(by omega) := by
  -- By definition of `Nodup`, if `L.tail.dropLast` is `Nodup`, then any two distinct indices `j` and `m` in `L.tail.dropLast` correspond to distinct elements in `L`.
  have h_nodup : ∀ (j m : ℕ), j < (L.tail.dropLast).length → m < (L.tail.dropLast).length → j ≠ m → (L.tail.dropLast)[j]! ≠ (L.tail.dropLast)[m]! := by
    intro j m hj hm hne; have := List.nodup_iff_injective_get.mp h_simple; simp_all +decide [ Function.Injective ] ;
    exact fun h => hne <| by simpa [ Fin.ext_iff ] using @this ⟨ j, by omega ⟩ ⟨ m, by omega ⟩ h;
  convert h_nodup ( p - 1 ) ( q - 1 ) _ _ _ using 1 <;> norm_num [ List.getElem?_eq_getElem, hp1, hq1, hp2, hq2 ];
  · grind +extAll;
  · grind;
  · omega;
  · omega;
  · omega

/-- For a simple closed hex trail, the start vertex does not recur among the
    interior vertices. -/
lemma hex_closed_trail_start_not_interior (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    L.headI ∉ L.tail.dropLast := by
  intro h
  obtain ⟨j, hj⟩ : ∃ j, j < L.tail.dropLast.length ∧ L.tail.dropLast[j]! = L.headI := by
    obtain ⟨ j, hj ⟩ := List.mem_iff_get.mp h
    exact ⟨ j.val, j.isLt, by
      rw [← hj]
      simp [List.getElem!_eq_getElem?_getD, List.get_eq_getElem,
        List.getElem?_eq_getElem j.isLt] ⟩
  obtain ⟨i, hi1, hi2, hiv⟩ : ∃ i, 1 ≤ i ∧ i < L.length - 1 ∧ L[i]! = L.headI := by
    have hjlt : j < L.tail.dropLast.length := hj.1
    have h2 : j + 1 < L.length := by
      rw [List.length_dropLast, List.length_tail] at hjlt; omega
    refine ⟨ j + 1, by omega, by
      rw [List.length_dropLast, List.length_tail] at hjlt; omega, ?_ ⟩
    rw [← hj.2]
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem hjlt]
    rw [List.getElem_dropLast, List.getElem_tail]
    rw [List.getElem?_eq_getElem h2]
  have hlast : L[L.length - 1]! = L.headI := by
    have := list_get_last_eq_get_zero_of_closed L (by omega) h_closed
    rcases L with ( _ | ⟨ x, rest ⟩ )
    · simp at hL
    · simp only [List.get_eq_getElem] at this
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
      simpa using this
  have hAdj : ∀ k : ℕ, k + 1 < L.length → hexGraph.Adj (L[k]!) (L[k+1]!) := by
    intro k hk
    have := hexTrailList_adj_get L h_trail (by omega) k hk
    simpa [List.get_eq_getElem, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (show k < L.length by omega)] using this
  have hNB : ∀ k : ℕ, k + 2 < L.length →
      s(L[k]!, L[k+1]!) ≠ s(L[k+1]!, L[k+2]!) := by
    intro k hk
    have := hexTrailList_nobacktrack_get L h_trail k hk
    simpa [List.get_eq_getElem, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (show k + 1 < L.length by omega),
      List.getElem?_eq_getElem (show k < L.length by omega)] using this
  have hA : hexGraph.Adj (L.headI) (L[1]!) := by
    have := hAdj 0 (by omega)
    simpa [show L[0]! = L.headI by
      rcases L with _ | ⟨x, rest⟩; · simp at hL
      · simp] using this
  have hB : hexGraph.Adj (L.headI) (L[i-1]!) := by
    have := hAdj (i-1) (by omega)
    rw [show i - 1 + 1 = i by omega, hiv] at this
    exact this.symm
  have hC : hexGraph.Adj (L.headI) (L[i+1]!) := by
    have := hAdj i (by omega)
    rw [hiv] at this
    exact this
  have hD : hexGraph.Adj (L.headI) (L[L.length-2]!) := by
    have := hAdj (L.length - 2) (by omega)
    rw [show L.length - 2 + 1 = L.length - 1 by omega, hlast] at this
    exact this.symm
  have hL0 : L[0]! = L.headI := by
    rcases L with _ | ⟨x, rest⟩
    · simp at hL
    · simp
  by_cases hcase : i = 1 ∨ i = 2 ∨ i = L.length - 3 ∨ i = L.length - 2
  · rcases hcase with rfl | rfl | rfl | rfl
    · rw [hiv] at hA; exact hexGraph.irrefl hA
    · -- i = 2: s(L0,L1) = s(L1,L2) since L2 = headI = L0
      refine hNB 0 (by omega) ?_
      rw [show (0:ℕ)+1 = 1 by rfl, show (0:ℕ)+2 = 2 by rfl, hiv, ← hL0, Sym2.eq_swap]
    · -- i = L.length - 3
      refine hNB (L.length - 3) (by omega) ?_
      rw [show L.length - 3 + 1 = L.length - 2 by omega,
          show L.length - 3 + 2 = L.length - 1 by omega, hiv, hlast, Sym2.eq_swap]
    · -- i = L.length - 2
      have hci : L[(L.length - 2) + 1]! = L.headI := by
        rw [show (L.length - 2) + 1 = L.length - 1 by omega]; exact hlast
      rw [hci] at hC
      exact hexGraph.irrefl hC
  · push_neg at hcase
    obtain ⟨hc1, hc2, hc3, hc4⟩ := hcase
    obtain ⟨hilo, hihi⟩ : 3 ≤ i ∧ i ≤ L.length - 4 := by omega
    refine hex_four_neighbours_not_nodup (L.headI) (L[1]!) (L[i-1]!) (L[i+1]!) (L[L.length-2]!) hA hB hC hD ?_
    have e1 : L[1]! = L[1]'(by omega) := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show 1 < L.length by omega)]
    have e2 : L[i-1]! = L[i-1]'(by omega) := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show i-1 < L.length by omega)]
    have e3 : L[i+1]! = L[i+1]'(by omega) := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show i+1 < L.length by omega)]
    have e4 : L[L.length-2]! = L[L.length-2]'(by omega) := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show L.length-2 < L.length by omega)]
    rw [e1, e2, e3, e4]
    rw [List.nodup_cons, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, ?_, List.nodup_singleton _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_, ?_⟩
      · exact hex_interior_getElem_ne L h_simple (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hex_interior_getElem_ne L h_simple (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hex_interior_getElem_ne L h_simple (by omega) (by omega) (by omega) (by omega) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_⟩
      · exact hex_interior_getElem_ne L h_simple (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hex_interior_getElem_ne L h_simple (by omega) (by omega) (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton]
      exact hex_interior_getElem_ne L h_simple (by omega) (by omega) (by omega) (by omega) (by omega)

/-
For a simple closed hex trail, the full vertex cycle `L.dropLast` is
    `Nodup`: the embedded polygon is genuinely simple.
-/
lemma hex_closed_trail_dropLast_nodup (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    L.dropLast.Nodup := by
  obtain ⟨a, rest, hL⟩ : ∃ a rest, L = a :: rest ∧ rest ≠ [] := by
    rcases L with ( _ | ⟨ a, _ | ⟨ b, L ⟩ ⟩ ) <;> aesop_cat;
  have h_dropLast : L.dropLast = a :: L.tail.dropLast := by
    cases rest <;> aesop;
  convert List.nodup_cons.mpr ⟨ hex_closed_trail_start_not_interior L ‹_› ‹_› ‹_› ‹_›, h_simple ⟩ using 1;
  aesop

/-- **Simplicity transfer for the signed-area route.** For a simple closed hex
    trail, the embedded polygon `L.dropLast.map correctHexEmbed` has pairwise
    distinct vertices in `ℂ`.  This combines `hex_closed_trail_dropLast_nodup`
    (the combinatorial simplicity of the full vertex cycle) with
    `correctHexEmbed_map_nodup` (injectivity of the embedding), giving exactly
    the "simple polygon in the plane" hypothesis that the signed-area / Jordan
    half of the Umlaufsatz `umlaufsatz_pm_one` consumes. -/
lemma hex_closed_trail_embed_nodup (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    (L.dropLast.map correctHexEmbed).Nodup :=
  correctHexEmbed_map_nodup
    (hex_closed_trail_dropLast_nodup L hL h_trail h_closed h_simple)

end