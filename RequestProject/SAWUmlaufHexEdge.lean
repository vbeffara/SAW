/-
# Honeycomb edge geometry (Umlaufsatz planarity preparation)

This file isolates the **single genuinely geometric fact** behind honeycomb
planarity, the second remaining core of the discrete Hopf Umlaufsatz: two
distinct honeycomb lattice edges, embedded in `ℂ` by `correctHexEmbed`, meet
only at a shared vertex.  Concretely, if `(v,w)` and `(v',w')` are two
`hexGraph` adjacencies whose four endpoints are pairwise distinct (the two edges
share no vertex), then the embedded unit segments are disjoint.

The point of factoring this out as a *general* statement about honeycomb edges
(rather than about polygon edges) is twofold:

* it decouples the geometry (unit segments in three lattice directions cannot
  cross) from the combinatorics of `closedEdges (hexEmbeddedPolygon L)`; and
* it is reusable: the honeycomb-specific Umlaufsatz planarity lemma
  `hexEmbeddedPolygon_edges_disjoint` (in `RequestProject.SAWUmlaufPolygon`)
  follows from it by translating polygon-edge endpoints into `hexGraph`
  adjacencies (consecutive trail vertices) and the four point-inequalities into
  vertex-inequalities via `correctHexEmbed_injective`.

## Geometry of honeycomb edges

Every `hexGraph` edge joins a `false`-sublattice vertex to a `true`-sublattice
one.  Writing `F = correctHexEmbed (x, y, false) = (-3(x+y)/2, (x-y)√3/2)`, the
three edge types out of a `false` vertex have embedding differences

  `(x,y,true) - F = (1, 0)`,
  `(x+1,y,true) - F = (-1/2, √3/2)`,
  `(x,y+1,true) - F = (-1/2, -√3/2)`,

i.e. unit vectors at angles `0, 120°, 240°`.  Two such unit segments at lattice
positions either share an endpoint or are disjoint; that finite case analysis,
together with the irrationality of `√3` separating the lattice coordinates, is
the content of `hexEdge_dir`, `hexEdge_segments_disjoint` below.

This file is **preparation** for the Umlaufsatz: it is imported by
`RequestProject.SAWUmlaufPolygon` (hence transitively from
`RequestProject.SAWFinal`) and consumed there by
`hexEmbeddedPolygon_edges_disjoint`.
-/

import Mathlib
import RequestProject.SAWUmlaufEmbed

open Real Complex ComplexConjugate

noncomputable section

set_option maxHeartbeats 1000000

/-- **Direction of an oriented honeycomb edge.**  If `v` (a `false`-vertex) is
    adjacent to `w` (a `true`-vertex), the embedding difference
    `correctHexEmbed w - correctHexEmbed v` is one of the three unit vectors
    `1`, `-1/2 + (√3/2)·I`, `-1/2 - (√3/2)·I`.  This pins the geometry of a
    single honeycomb edge to three explicit directions, the input to the
    segment-disjointness case analysis. -/
lemma hexEdge_dir (v w : HexVertex) (hv : v.2.2 = false) (hadj : hexGraph.Adj v w) :
    correctHexEmbed w - correctHexEmbed v = 1 ∨
    correctHexEmbed w - correctHexEmbed v = ⟨-1/2, Real.sqrt 3 / 2⟩ ∨
    correctHexEmbed w - correctHexEmbed v = ⟨-1/2, -(Real.sqrt 3 / 2)⟩ := by
  obtain ⟨x, y, b⟩ := v
  obtain ⟨x', y', b'⟩ := w
  simp only at hv; subst hv
  -- `hadj` is the `false → true` clause of `hexGraph.Adj`.
  rcases hadj with ⟨_, hw2, h3 | h3 | h3⟩ | ⟨hcontra, _, _⟩
  · -- (x,y,false) → (x,y,true)
    obtain ⟨e1, e2⟩ := h3
    simp only at hw2; subst hw2
    left
    simp only [correctHexEmbed, Complex.ext_iff]
    constructor <;> simp_all
  · -- (x,y,false) → (x+1,y,true)
    obtain ⟨e1, e2⟩ := h3
    simp only at hw2; subst hw2
    right; left
    simp only [correctHexEmbed, Complex.ext_iff]
    have hx' : (x' : ℝ) = (x : ℝ) + 1 := by exact_mod_cast e1.symm
    have hy' : (y' : ℝ) = (y : ℝ) := by exact_mod_cast e2.symm
    constructor <;> simp_all <;> ring
  · -- (x,y,false) → (x,y+1,true)
    obtain ⟨e1, e2⟩ := h3
    simp only at hw2; subst hw2
    right; right
    simp only [correctHexEmbed, Complex.ext_iff]
    have hx' : (x' : ℝ) = (x : ℝ) := by exact_mod_cast e1.symm
    have hy' : (y' : ℝ) = (y : ℝ) + 1 := by exact_mod_cast e2.symm
    constructor <;> simp_all <;> ring
  · simp at hcontra

/-- Every honeycomb edge joins a `false`-sublattice vertex to a `true`-sublattice
    one: an adjacency `v ~ w` has `v` false and `w` true, or vice versa.  Used to
    orient an edge so that `hexEdge_dir` applies (its base must be `false`). -/
lemma hexEdge_false_or (v w : HexVertex) (h : hexGraph.Adj v w) :
    (v.2.2 = false ∧ w.2.2 = true) ∨ (v.2.2 = true ∧ w.2.2 = false) := by
  rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> simp_all

/- **Oriented honeycomb edge-disjointness (geometric core).**  `hexEdge_dir`
    applies directly to each oriented edge (`correctHexEmbed w - correctHexEmbed v`
    is one of the three unit directions `1, -1/2 ± (√3/2)·I`).  A common point of
    the two segments gives `embed v + t•d = embed v' + s•d'` with `t,s ∈ [0,1]`;
    real and imaginary parts (clearing `√3`) give linear relations among the
    integer lattice coordinates forcing `v = v'` or `w = w'`.  The proof is
    split into the three first-edge directions `hexEdge_disjoint_d1/d2/d3`. -/

/-! ### Nine direction-pair leaf cases

Each `hexEdge_disjoint_leaf_ij` fixes BOTH edge directions to specific unit
vectors (`D1 = 1`, `D2 = ⟨-1/2,√3/2⟩`, `D3 = ⟨-1/2,-√3/2⟩`), reducing to a
single concrete real-arithmetic disjointness goal: a common point
`embed v + t•Dᵢ = embed v' + s•Dⱼ` with `t,s ∈ [0,1]` forces `v=v'` or `w=w'`.
Only `hvv` (`v ≠ v'`) and `hww` (`w ≠ w'`) are load-bearing (`v ≠ w'`, `w ≠ v'`
are automatic by `false`/`true` parity). -/

lemma hexEdge_disjoint_leaf_11 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (hd : correctHexEmbed w - correctHexEmbed v = 1)
    (hd' : correctHexEmbed w' - correctHexEmbed v' = 1)
    (hvv : v ≠ v') (_hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) := by
  simp_all +decide [ sub_eq_iff_eq_add, segment_eq_image' ];
  simp_all +decide [ Set.disjoint_left ];
  rintro a x hx₁ hx₂ rfl y hy₁ hy₂ H; simp_all +decide [ Complex.ext_iff ] ;
  unfold correctHexEmbed at *;
  rcases v with ⟨ x, y, z ⟩ ; rcases v' with ⟨ x', y', z' ⟩ ; simp_all +decide ;
  -- From the equality of the real parts, we get $x' + y' = x + y$.
  have h_sum : x' + y' = x + y := by
    exact Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ] ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ] );
  exact hvv ( by norm_cast at *; linarith ) ( by norm_cast at *; linarith )

lemma hexEdge_disjoint_leaf_12 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (hd : correctHexEmbed w - correctHexEmbed v = 1)
    (hd' : correctHexEmbed w' - correctHexEmbed v' = ⟨-1/2, Real.sqrt 3 / 2⟩)
    (hvv : v ≠ v') (hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) := by
  apply Set.disjoint_left.mpr;
  intro a ha hb
  obtain ⟨t, ht⟩ := (segment_eq_image' ℝ (correctHexEmbed v) (correctHexEmbed w)).subset ha
  obtain ⟨s, hs⟩ := (segment_eq_image' ℝ (correctHexEmbed v') (correctHexEmbed w')).subset hb;
  obtain ⟨x, y, hx⟩ : ∃ x y : ℤ, v = (x, y, false) := by
    exact ⟨ v.1, v.2.1, Prod.ext rfl ( Prod.ext rfl hv ) ⟩
  obtain ⟨x', y', hx'⟩ : ∃ x' y' : ℤ, v' = (x', y', false) := by
    exact ⟨ _, _, Prod.ext rfl ( Prod.ext rfl hv' ) ⟩;
  -- By equating the real and imaginary parts from the two expressions for `a`, we get two equations:
  have h_eq1 : -3 * (x + y - x' - y') = -s - 2 * t := by
    simp_all +decide [ Complex.ext_iff ];
    unfold correctHexEmbed at * ; norm_num at * ; linarith
  have h_eq2 : (x - y) - (x' - y') = s := by
    simp_all +decide [ Complex.ext_iff, correctHexEmbed ];
    nlinarith [ Real.sqrt_pos.mpr zero_lt_three ];
  -- From the equations $-3 * (x + y - x' - y') = -s - 2 * t$ and $(x - y) - (x' - y') = s$, we can solve for $s$ and $t$.
  have h_solve : s = 0 ∧ t = 0 ∨ s = 1 ∧ t = 1 := by
    have h_solve : ∃ k : ℤ, s = k := by
      exact ⟨ x - y - ( x' - y' ), by push_cast; linarith ⟩;
    rcases h_solve with ⟨ k, rfl ⟩ ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at * <;> try linarith;
    · norm_num [ show t = 0 by exact le_antisymm ( by linarith [ show ( x + y - x' - y' : ℝ ) = 0 by exact_mod_cast Int.le_antisymm ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith } ) ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith } ) ] ) ht.1.1 ] at *;
    · norm_num [ show t = 1 by linarith [ show ( x + y - x' - y' : ℝ ) = 1 by exact_mod_cast Int.le_antisymm ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith } ) ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith } ) ] ] at *;
  cases h_solve <;> simp_all +decide;
  · exact hvv ( by norm_cast at h_eq1 h_eq2; linarith ) ( by norm_cast at h_eq1 h_eq2; linarith );
  · grind +suggestions

lemma hexEdge_disjoint_leaf_13 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (hd : correctHexEmbed w - correctHexEmbed v = 1)
    (hd' : correctHexEmbed w' - correctHexEmbed v' = ⟨-1/2, -(Real.sqrt 3 / 2)⟩)
    (hvv : v ≠ v') (hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) := by
  obtain ⟨x, y, hx⟩ : ∃ x y : ℤ, v = (x, y, false) := by
    exact ⟨ v.1, v.2.1, Prod.ext rfl ( Prod.ext rfl hv ) ⟩
  obtain ⟨x', y', hx'⟩ : ∃ x' y' : ℤ, v' = (x', y', false) := by
    exact ⟨ _, _, Prod.ext rfl ( Prod.ext rfl hv' ) ⟩;
  simp_all +decide [ segment_eq_image' ];
  rw [ Set.disjoint_left ];
  simp_all +decide [ Complex.ext_iff, correctHexEmbed ];
  intro a t ht₁ ht₂ ht₃ ht₄ u hu₁ hu₂ hu₃ hu₄;
  -- By simplifying, we can see that the only solution is $t = 0$ and $u = 0$.
  have h_sol : t = 0 ∧ u = 0 ∨ t = 1 ∧ u = 1 := by
    have h_sol : ∃ k : ℤ, u = k := by
      exact ⟨ x' - y' - ( x - y ), by push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] ⟩;
    rcases h_sol with ⟨ k, rfl ⟩ ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at * <;> try (left; constructor <;> linarith);
    · exact False.elim <| hvv ( Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] ) ) ( Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] ) );
    · by_contra h_contra;
      exact h_contra <| by nlinarith [ Real.sqrt_pos.mpr zero_lt_three, show ( x : ℝ ) + y = x' + y' + 1 by exact_mod_cast Int.le_antisymm ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] } ) ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] } ) ] ;
  rcases h_sol with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num at *;
  · exact hvv ( by exact_mod_cast ( by nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] : ( x : ℝ ) = x' ) ) ( by exact_mod_cast ( by nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] : ( y : ℝ ) = y' ) );
  · rcases w with ⟨ x, y, z ⟩ ; rcases w' with ⟨ x', y', z' ⟩ ; norm_num at *;
    cases z <;> cases z' <;> norm_num at *;
    · field_simp at *;
      norm_cast at * ; omega;
    · field_simp at *;
      norm_cast at * ; omega;
    · field_simp at *;
      norm_cast at * ; omega;
    · exact hww ( by exact_mod_cast ( by nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] : ( x : ℝ ) = x' ) ) ( by exact_mod_cast ( by nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] : ( y : ℝ ) = y' ) )

lemma hexEdge_disjoint_leaf_21 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (hd : correctHexEmbed w - correctHexEmbed v = ⟨-1/2, Real.sqrt 3 / 2⟩)
    (hd' : correctHexEmbed w' - correctHexEmbed v' = 1)
    (hvv : v ≠ v') (hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) :=
  -- swap the two edges and use `leaf_12`
  (hexEdge_disjoint_leaf_12 v' w' v w hv' hv hd' hd hvv.symm hww.symm).symm

lemma hexEdge_disjoint_leaf_22 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (hd : correctHexEmbed w - correctHexEmbed v = ⟨-1/2, Real.sqrt 3 / 2⟩)
    (hd' : correctHexEmbed w' - correctHexEmbed v' = ⟨-1/2, Real.sqrt 3 / 2⟩)
    (hvv : v ≠ v') (_hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) := by
  simp_all +decide [ sub_eq_iff_eq_add, segment_eq_image' ];
  simp +decide [ Set.disjoint_left, Set.mem_image ];
  rintro _ x hx₁ hx₂ rfl y hy₁ hy₂; contrapose! hvv;
  rcases v with ⟨ x, y, z ⟩ ; rcases v' with ⟨ x', y', z' ⟩ ; simp_all +decide [ Complex.ext_iff ];
  unfold correctHexEmbed at * ; norm_num at *;
  -- By simplifying, we can see that the only solution is $x = x'$ and $y = y'$.
  have h_eq : x = x' ∧ y = y' := by
    have h_x : x = x' := by
      exact Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] )
    have h_y : y = y' := by
      exact Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] )
    exact ⟨h_x, h_y⟩;
  exact h_eq

lemma hexEdge_disjoint_leaf_23 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (hd : correctHexEmbed w - correctHexEmbed v = ⟨-1/2, Real.sqrt 3 / 2⟩)
    (hd' : correctHexEmbed w' - correctHexEmbed v' = ⟨-1/2, -(Real.sqrt 3 / 2)⟩)
    (hvv : v ≠ v') (hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) := by
  contrapose! hvv; contrapose! hww; simp_all +decide [ sub_eq_iff_eq_add ] ;
  simp_all +decide [ Set.not_disjoint_iff, segment_eq_image' ];
  simp_all +decide [ Complex.ext_iff ];
  obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, b, ⟨ hb₁, hb₂ ⟩, hab₁, hab₂ ⟩ := hvv; rcases v with ⟨ x, y, z ⟩ ; rcases v' with ⟨ x', y', z' ⟩ ; simp_all +decide [ correctHexEmbed ] ;
  -- By simplifying, we can see that the only solution is $a = 0$ and $b = 0$, or $a = 1$ and $b = 1$.
  have h_solutions : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
    have h_solutions : ∃ k : ℤ, a - b = 3 * k := by
      exact ⟨ x' + y' - x - y, by push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] ⟩;
    obtain ⟨ k, hk ⟩ := h_solutions; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> try (left; constructor <;> linarith);
    -- By simplifying, we can see that the only solution is $b = 0$ or $b = 1$, contradicting our assumption.
    have h_contra : ∃ k : ℤ, b = k := by
      exact ⟨ x' - x, by push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] ⟩;
    rcases h_contra with ⟨ k, rfl ⟩ ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at * <;> linarith;
  rcases h_solutions with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num at *;
  · norm_cast at *; omega;
  · rcases w with ⟨ a, b, c ⟩ ; rcases w' with ⟨ a', b', c' ⟩ ; norm_num at * ;
    cases c <;> cases c' <;> norm_num at *;
    · field_simp at *;
      norm_cast at *; omega;
    · field_simp at *;
      norm_cast at *; omega;
    · field_simp at *;
      norm_cast at * ; omega;
    · -- By simplifying, we can see that the only solution is $a = a'$ and $b = b'$.
      field_simp at *
      ring_nf at *;
      norm_cast at *; omega;

lemma hexEdge_disjoint_leaf_31 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (hd : correctHexEmbed w - correctHexEmbed v = ⟨-1/2, -(Real.sqrt 3 / 2)⟩)
    (hd' : correctHexEmbed w' - correctHexEmbed v' = 1)
    (hvv : v ≠ v') (hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) :=
  -- swap the two edges and use `leaf_13`
  (hexEdge_disjoint_leaf_13 v' w' v w hv' hv hd' hd hvv.symm hww.symm).symm

lemma hexEdge_disjoint_leaf_32 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (hd : correctHexEmbed w - correctHexEmbed v = ⟨-1/2, -(Real.sqrt 3 / 2)⟩)
    (hd' : correctHexEmbed w' - correctHexEmbed v' = ⟨-1/2, Real.sqrt 3 / 2⟩)
    (hvv : v ≠ v') (hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) :=
  -- swap the two edges and use `leaf_23`
  (hexEdge_disjoint_leaf_23 v' w' v w hv' hv hd' hd hvv.symm hww.symm).symm

lemma hexEdge_disjoint_leaf_33 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (hd : correctHexEmbed w - correctHexEmbed v = ⟨-1/2, -(Real.sqrt 3 / 2)⟩)
    (hd' : correctHexEmbed w' - correctHexEmbed v' = ⟨-1/2, -(Real.sqrt 3 / 2)⟩)
    (hvv : v ≠ v') (_hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) := by
  refine' Set.disjoint_left.mpr _;
  intros a ha hb; rw [ segment_eq_image' ] at ha hb; obtain ⟨ t, ht, rfl ⟩ := ha; obtain ⟨ s, hs, hs' ⟩ := hb; simp_all +decide [ Complex.ext_iff ] ;
  -- Extract integer coordinates from `v` and `v'` using the definitions of `correctHexEmbed` and `hv`, `hv'`.
  obtain ⟨x, y, hx⟩ : ∃ x y : ℤ, v = (x, y, false) := by
    exact ⟨ v.1, v.2.1, Prod.ext rfl ( Prod.ext rfl hv ) ⟩
  obtain ⟨x', y', hx'⟩ : ∃ x' y' : ℤ, v' = (x', y', false) := by
    exact ⟨ _, _, Prod.ext rfl ( Prod.ext rfl hv' ) ⟩;
  simp_all +decide [ correctHexEmbed ];
  -- From the imaginary part equation, we get $t = s$.
  have hts : t = s := by
    by_contra hts_ne;
    exact hts_ne <| by nlinarith [ Real.sqrt_pos.mpr zero_lt_three, show ( x : ℝ ) + y = x' + y' by exact_mod_cast Int.le_antisymm ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] } ) ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] } ) ] ;
  -- From the imaginary part equation, we get $x' - y' = x - y$.
  have hxy : x' - y' = x - y := by
    exact_mod_cast ( by nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] : ( x' : ℝ ) - y' = x - y );
  -- From the real part equation, we get $x' = x$.
  have hx'x : x' = x := by
    exact_mod_cast ( by nlinarith [ Real.sqrt_pos.mpr zero_lt_three ] : ( x' : ℝ ) = x );
  exact hvv hx'x.symm ( by linarith )

/-- Oriented edge-disjointness with the first edge's direction fixed to `1`;
    dispatches on the second edge's direction to the leaf lemmas. -/
lemma hexEdge_disjoint_d1 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (h2 : hexGraph.Adj v' w')
    (hd : correctHexEmbed w - correctHexEmbed v = 1)
    (hvv : v ≠ v') (hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) := by
  rcases hexEdge_dir v' w' hv' h2 with hd' | hd' | hd'
  · exact hexEdge_disjoint_leaf_11 v w v' w' hv hv' hd hd' hvv hww
  · exact hexEdge_disjoint_leaf_12 v w v' w' hv hv' hd hd' hvv hww
  · exact hexEdge_disjoint_leaf_13 v w v' w' hv hv' hd hd' hvv hww

/-- Oriented edge-disjointness with the first edge's direction fixed to
    `⟨-1/2, √3/2⟩`; dispatches on the second edge's direction. -/
lemma hexEdge_disjoint_d2 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (h2 : hexGraph.Adj v' w')
    (hd : correctHexEmbed w - correctHexEmbed v = ⟨-1/2, Real.sqrt 3 / 2⟩)
    (hvv : v ≠ v') (hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) := by
  rcases hexEdge_dir v' w' hv' h2 with hd' | hd' | hd'
  · exact hexEdge_disjoint_leaf_21 v w v' w' hv hv' hd hd' hvv hww
  · exact hexEdge_disjoint_leaf_22 v w v' w' hv hv' hd hd' hvv hww
  · exact hexEdge_disjoint_leaf_23 v w v' w' hv hv' hd hd' hvv hww

/-- Oriented edge-disjointness with the first edge's direction fixed to
    `⟨-1/2, -√3/2⟩`; dispatches on the second edge's direction. -/
lemma hexEdge_disjoint_d3 (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (h2 : hexGraph.Adj v' w')
    (hd : correctHexEmbed w - correctHexEmbed v = ⟨-1/2, -(Real.sqrt 3 / 2)⟩)
    (hvv : v ≠ v') (hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) := by
  rcases hexEdge_dir v' w' hv' h2 with hd' | hd' | hd'
  · exact hexEdge_disjoint_leaf_31 v w v' w' hv hv' hd hd' hvv hww
  · exact hexEdge_disjoint_leaf_32 v w v' w' hv hv' hd hd' hvv hww
  · exact hexEdge_disjoint_leaf_33 v w v' w' hv hv' hd hd' hvv hww

/-- **Oriented honeycomb edge-disjointness (geometric core).**  Two honeycomb
    edges oriented so their first endpoints `v, v'` are the `false` vertices,
    sharing no vertex, embed to disjoint segments.  (Only `v ≠ v'` and `w ≠ w'`
    are needed: `v ≠ w'` and `w ≠ v'` are automatic by false/true parity.)
    Dispatches on the first edge's direction to `hexEdge_disjoint_d1/d2/d3`. -/
lemma hexEdge_segments_disjoint_oriented
    (v w v' w' : HexVertex)
    (hv : v.2.2 = false) (hv' : v'.2.2 = false)
    (h1 : hexGraph.Adj v w) (h2 : hexGraph.Adj v' w')
    (hvv : v ≠ v') (hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) := by
  rcases hexEdge_dir v w hv h1 with hd | hd | hd
  · exact hexEdge_disjoint_d1 v w v' w' hv hv' h2 hd hvv hww
  · exact hexEdge_disjoint_d2 v w v' w' hv hv' h2 hd hvv hww
  · exact hexEdge_disjoint_d3 v w v' w' hv hv' h2 hd hvv hww

/-- **Honeycomb edge-disjointness (general geometric core).**  Two honeycomb
    graph edges `(v,w)`, `(v',w')` whose four endpoints are pairwise distinct
    (the edges share no vertex) embed to disjoint segments in `ℂ`.

    This is the only genuinely geometric content of honeycomb planarity (two
    unit honeycomb edges meet only at a shared vertex); it is consumed by
    `hexEmbeddedPolygon_edges_disjoint` to discharge the Umlaufsatz planarity
    hypothesis.  Absent from Mathlib.

    Reduced to the oriented core `hexEdge_segments_disjoint_oriented` by
    orienting each edge (via `hexEdge_false_or` and `segment_symm`) so its first
    endpoint is the `false` vertex. -/
lemma hexEdge_segments_disjoint
    (v w v' w' : HexVertex)
    (h1 : hexGraph.Adj v w) (h2 : hexGraph.Adj v' w')
    (hvv : v ≠ v') (hvw : v ≠ w') (hwv : w ≠ v') (hww : w ≠ w') :
    Disjoint (segment ℝ (correctHexEmbed v) (correctHexEmbed w))
             (segment ℝ (correctHexEmbed v') (correctHexEmbed w')) := by
  rcases hexEdge_false_or v w h1 with ⟨hvf, hwt⟩ | ⟨hvt, hwf⟩ <;>
    rcases hexEdge_false_or v' w' h2 with ⟨hv'f, hw't⟩ | ⟨hv't, hw'f⟩
  · exact hexEdge_segments_disjoint_oriented v w v' w' hvf hv'f h1 h2 hvv hww
  · rw [segment_symm ℝ (correctHexEmbed v') (correctHexEmbed w')]
    exact hexEdge_segments_disjoint_oriented v w w' v' hvf hw'f h1 h2.symm hvw hwv
  · rw [segment_symm ℝ (correctHexEmbed v) (correctHexEmbed w)]
    exact hexEdge_segments_disjoint_oriented w v v' w' hwf hv'f h1.symm h2 hwv hvw
  · rw [segment_symm ℝ (correctHexEmbed v) (correctHexEmbed w),
        segment_symm ℝ (correctHexEmbed v') (correctHexEmbed w')]
    exact hexEdge_segments_disjoint_oriented w v w' v' hwf hw'f h1.symm h2.symm hww hvv

end