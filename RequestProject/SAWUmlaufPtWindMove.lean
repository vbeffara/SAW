/-
# Locally-constant behaviour of the point-winding along an edge-avoiding segment

This file develops the **homotopy invariance backbone** of the point-winding
number `HexArea.ptWind` (defined in `RequestProject.SAWUmlaufPtWind`): as the
base point `x` moves along a straight segment that avoids every (closed) edge of
the polygon `V`, the winding number `ptWind x V` does not change.

This is the honest, self-contained plane-topology brick behind the two remaining
point-in-polygon residues of the discrete Hopf Umlaufsatz
(`RequestProject.SAWUmlaufPolygon`): `clipped_ear_ptWind_zero` and
`chord_ear_other_ptWind_zero`.  Both say "`ptWind x V = 0` for a point `x`
outside the enclosed region".  The winding number is
  * **continuous** in `x` off the polygon (each edge's sweep angle
    `arg ((b - x)/(a - x))` is continuous in `x` as long as `x` stays off the
    closed segment `[a, b]`, because the ratio then stays in the slit plane), and
  * **integer-valued** (a multiple of `2π`, via `ptWind_int`).
A continuous, `2π·ℤ`-valued function on the connected segment `[x, y]` is
constant (elementary intermediate-value / parity argument), giving
`ptWind x V = ptWind y V`.  Chaining this with the convex base case
`ptWind_zero_of_not_mem_convexHull` (`RequestProject.SAWUmlaufExterior`) yields
the packaged consumer `ptWind_zero_of_segment_to_not_hull`: if `x` can be joined
to a point `y` outside the convex hull of the vertices by an edge-avoiding
segment, then `ptWind x V = 0`.

## Downstream use (NOT a dead branch)

This file is imported by `RequestProject.SAWUmlaufPolygon`.  The consumer
`ptWind_zero_of_segment_to_not_hull` reduces each hull-interior residue of the
two point-in-polygon atoms to the strictly more concrete obligation of
*exhibiting a single edge-avoiding segment from the forbidden point to the
convex-hull exterior* — a local geometric fact, rather than the full Jordan
separation theorem.
-/

import Mathlib
import RequestProject.SAWUmlaufPtWind
import RequestProject.SAWUmlaufPtWindJordan
import RequestProject.SAWUmlaufExterior

open Real Complex

noncomputable section

namespace HexArea

set_option maxHeartbeats 4000000

/-- The list of directed edges of the *closed* cycle on `V`: consecutive pairs of
    `V ++ V.take 1` (so the last edge closes the loop back to the first vertex).
    This is exactly the index set summed over in `ptWind x V = ptTurn x (V ++ V.take 1)`. -/
def cycleEdges (V : List ℂ) : List (ℂ × ℂ) :=
  (V ++ V.take 1).zip ((V ++ V.take 1).drop 1)

/-
**The sweep ratio of an edge lies in the slit plane when the base point is
    off the closed edge segment.**  If `w ∉ segment ℝ a b`, then
    `(b - w)/(a - w) ∈ Complex.slitPlane` (i.e. its real part is positive or its
    imaginary part is nonzero).  Indeed the ratio is a non-positive real exactly
    when `w` is a convex combination of `a` and `b` (equivalently `w ∈ segment`),
    which is excluded.
-/
lemma ratio_mem_slitPlane (a b w : ℂ) (h : w ∉ segment ℝ a b) :
    (b - w) / (a - w) ∈ Complex.slitPlane := by
  contrapose! h;
  -- If $(b - w) / (a - w)$ is not in the slit plane, then it must be a non-positive real number.
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r ≤ 0 ∧ (b - w) / (a - w) = r := by
    simp_all +decide [ Complex.ext_iff, slitPlane ]
  generalize_proofs at *; (
  by_cases ha : a = w <;> simp_all +decide [ sub_eq_iff_eq_add, div_eq_iff ];
  · exact left_mem_segment _ _ _;
  · rw [ segment_eq_image ];
    refine' ⟨ 1 / ( 1 - r ), _, _ ⟩ <;> norm_num [ ha, hr ];
    · exact ⟨ by linarith, inv_le_one_of_one_le₀ <| by linarith ⟩;
    · by_cases h : ( 1 - r : ℂ ) = 0 <;> simp_all +decide [ sub_eq_iff_eq_add, mul_assoc, mul_left_comm ];
      · norm_cast at h; linarith;
      · grind)

/-
**Continuity of a single edge's sweep angle in the base point.**  For fixed
    endpoints `a, b`, the map `w ↦ arg ((b - w)/(a - w))` is continuous at every
    `w₀` off the closed segment `[a, b]` (the ratio stays in the slit plane, where
    `arg` is continuous).
-/
lemma continuousAt_arg_ratio (a b w₀ : ℂ) (h : w₀ ∉ segment ℝ a b) :
    ContinuousAt (fun w : ℂ => Complex.arg ((b - w) / (a - w))) w₀ := by
  convert Complex.continuousAt_arg _ |> ContinuousAt.comp <| show ContinuousAt ( fun w => ( ( b - w ) / ( a - w ) ) ) w₀ from ?_ using 1
  generalize_proofs at *;
  · grind +suggestions;
  · exact ContinuousAt.div ( continuousAt_const.sub continuousAt_id ) ( continuousAt_const.sub continuousAt_id ) ( sub_ne_zero_of_ne <| by rintro rfl; exact h <| left_mem_segment _ _ _ )

/-
**Continuity of the open-chain sweep sum `ptTurn` in the base point.**  If
    `w₀` lies off every consecutive-edge segment of the chain `L`, then
    `w ↦ ptTurn w L` is continuous at `w₀`.
-/
lemma continuousAt_ptTurn (L : List ℂ) (w₀ : ℂ)
    (h : ∀ p ∈ L.zip (L.drop 1), w₀ ∉ segment ℝ p.1 p.2) :
    ContinuousAt (fun w : ℂ => ptTurn w L) w₀ := by
  induction' L with a L ih generalizing w₀;
  · exact continuousAt_const;
  · rcases L with ( _ | ⟨ b, L ⟩ ) <;> simp_all +decide [ List.zip ];
    convert ContinuousAt.add ( continuousAt_arg_ratio a b w₀ h.1 ) ( ih w₀ h.2 ) using 1

/-
**Continuity of the closed-cycle winding `ptWind` in the base point.**  If
    `w₀` lies off every edge segment of the closed cycle on `V`, then
    `w ↦ ptWind w V` is continuous at `w₀`.
-/
lemma continuousAt_ptWind (V : List ℂ) (w₀ : ℂ)
    (h : ∀ p ∈ cycleEdges V, w₀ ∉ segment ℝ p.1 p.2) :
    ContinuousAt (fun w : ℂ => ptWind w V) w₀ := by
  exact continuousAt_ptTurn (V ++ V.take 1) w₀ h

/-
**Off every edge segment ⟹ off every vertex.**  A base point avoiding all
    closed-cycle edge segments in particular avoids every vertex of `V` (each
    vertex is an endpoint of an edge, hence lies in that edge's segment).
-/
lemma vertices_ne_of_avoids_cycleEdges (V : List ℂ) (w : ℂ)
    (h : ∀ p ∈ cycleEdges V, w ∉ segment ℝ p.1 p.2) :
    ∀ v ∈ V, v ≠ w := by
  contrapose! h;
  rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ cycleEdges ];
  rcases h with ( rfl | rfl | h );
  · exact Or.inl <| left_mem_segment _ _ _;
  · exact Or.inl <| right_mem_segment _ _ _;
  · obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp h;
    refine' Or.inr ⟨ _, _, _, _ ⟩;
    exact if k = ⟨ 0, by linarith [ Fin.is_lt k ] ⟩ then b else V.get ⟨ k - 1, by
      exact lt_of_le_of_lt ( Nat.pred_le _ ) k.2 ⟩
    exact w
    all_goals generalize_proofs at *;
    · rcases k with ⟨ _ | k, hk ⟩ <;> simp_all +decide [ List.get ];
      · cases V <;> aesop;
      · rw [ List.mem_iff_get ];
        use ⟨ k + 1, by
          grind ⟩
        generalize_proofs at *;
        grind;
    · exact right_mem_segment _ _ _

/-
**Locally-constant along an edge-avoiding segment.**  If the whole straight
    segment `[x, y]` is disjoint from every closed-cycle edge of `V`, then
    `ptWind x V = ptWind y V`.

    Proof: the map `t ↦ ptWind (x + t·(y-x)) V` on `[0,1]` is continuous
    (`continuousAt_ptWind`, each interior point avoids all edges) and takes values
    in `2π·ℤ` (`ptWind_int`, each interior point avoids all vertices).  Two
    distinct `2π·ℤ`-values differ by at least `2π`, so if the endpoints differed
    the intermediate value theorem would force the function to hit `2π·(m)+π`, a
    non-multiple of `2π` — contradiction.
-/
lemma ptWind_eq_of_segment_avoids (V : List ℂ) (x y : ℂ)
    (havoid : ∀ p ∈ cycleEdges V, Disjoint (segment ℝ x y) (segment ℝ p.1 p.2)) :
    ptWind x V = ptWind y V := by
  -- By the intermediate value theorem, since ptWind is continuous on the segment [x, y] and takes integer values at the endpoints, it must be constant on the segment.
  have h_const : ∀ t ∈ Set.Icc (0 : ℝ) 1, ptWind ((1 - t) • x + t • y) V ∈ Set.range (fun n : ℤ => 2 * Real.pi * n) := by
    intro t ht
    have h_cont : ∀ p ∈ cycleEdges V, (1 - t) • x + t • y ∉ segment ℝ p.1 p.2 := by
      intro p hp; specialize havoid p hp; simp_all +decide [ Set.disjoint_left ] ;
      exact havoid <| by rw [ segment_eq_image ] ; exact ⟨ t, ⟨ by linarith, by linarith ⟩, by simp +decide [ add_comm ] ⟩ ;
    obtain ⟨ n, hn ⟩ := ptWind_int ( ( 1 - t ) • x + t • y ) V ( fun v hv => vertices_ne_of_avoids_cycleEdges V ( ( 1 - t ) • x + t • y ) h_cont v hv ) ; use n; aesop;
  have h_const : ContinuousOn (fun t : ℝ => ptWind ((1 - t) • x + t • y) V) (Set.Icc 0 1) := by
    refine' ContinuousOn.comp ( show ContinuousOn ( fun w => ptWind w V ) ( Set.image ( fun t : ℝ => ( 1 - t ) • x + t • y ) ( Set.Icc 0 1 ) ) from _ ) _ _;
    · intro w hw
      obtain ⟨t, ht, rfl⟩ := hw
      have h_cont : ContinuousAt (fun w => ptWind w V) ((1 - t) • x + t • y) := by
        apply continuousAt_ptWind;
        grind +suggestions
      exact h_cont.continuousWithinAt;
    · fun_prop;
    · exact fun t ht => Set.mem_image_of_mem _ ht;
  have h_const : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ n : ℤ, ptWind ((1 - t) • x + t • y) V = 2 * Real.pi * n := by
    grind;
  choose! n hn using h_const;
  have h_const : ContinuousOn (fun t : ℝ => n t : ℝ → ℤ) (Set.Icc 0 1) := by
    have h_const : ContinuousOn (fun t : ℝ => (n t : ℝ)) (Set.Icc 0 1) := by
      have h_const : ContinuousOn (fun t : ℝ => ptWind ((1 - t) • x + t • y) V / (2 * Real.pi)) (Set.Icc 0 1) := by
        exact h_const.div_const _;
      exact h_const.congr fun t ht => by rw [ hn t ht, mul_div_cancel_left₀ _ ( by positivity ) ] ;
    rw [ Metric.continuousOn_iff ] at *;
    exact fun b hb ε hε => by rcases h_const b hb ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, fun a ha hab => by simpa [ ← @Int.cast_lt ℝ ] using H a ha hab ⟩ ;
  have h_const : ∀ t ∈ Set.Icc (0 : ℝ) 1, n t = n 0 := by
    have h_const : IsConnected (Set.image (fun t : ℝ => n t) (Set.Icc 0 1)) := by
      exact ⟨ Set.Nonempty.image _ ⟨ 0, Set.left_mem_Icc.mpr zero_le_one ⟩, isPreconnected_Icc.image _ h_const ⟩;
    have := h_const.isPreconnected.subsingleton;
    exact fun t ht => this ⟨ t, ht, rfl ⟩ ⟨ 0, by norm_num, rfl ⟩;
  have := hn 0; have := hn 1; aesop;

/-- **Packaged consumer: an edge-avoiding segment to a hull-exterior point kills
    the winding.**  If `x` is joined to a point `y` outside the convex hull of the
    vertices of `V` by a segment disjoint from every closed-cycle edge, then
    `ptWind x V = 0`.  Combines `ptWind_eq_of_segment_avoids` with the convex base
    case `ptWind_zero_of_not_mem_convexHull`.

    This is the reusable tool for the hull-interior residues of the two
    point-in-polygon atoms in `SAWUmlaufPolygon`: it reduces "the winding is `0`"
    to the concrete geometric task of exhibiting one escaping edge-avoiding
    segment from the forbidden point. -/
lemma ptWind_zero_of_segment_to_not_hull (V : List ℂ) (x y : ℂ)
    (havoid : ∀ p ∈ cycleEdges V, Disjoint (segment ℝ x y) (segment ℝ p.1 p.2))
    (hy : y ∉ convexHull ℝ (V.toFinset : Set ℂ)) :
    ptWind x V = 0 := by
  rw [ptWind_eq_of_segment_avoids V x y havoid]
  exact ptWind_zero_of_not_mem_convexHull y V hy

/-- **Locally-constant along an edge-avoiding polyline (walk).**  A single
    segment from `x` may cross an edge even when `x` is exterior; but if `x` can be
    joined to a point by a *walk* (polyline `x, zs`) all of whose consecutive
    segments avoid every closed-cycle edge, then the winding is unchanged along
    it.  Here the walk is encoded as `List.Chain` of the segment-avoidance
    relation, and its endpoint is `zs.getLastD x` (the last vertex, or `x` if the
    walk is trivial).  Proved by list induction, stepping with
    `ptWind_eq_of_segment_avoids`.  The walk `x :: zs` is encoded via
    `List.IsChain` of the segment-avoidance relation. -/
lemma ptWind_eq_of_walk (V : List ℂ) :
    ∀ (zs : List ℂ) (x : ℂ),
      List.IsChain (fun a b => ∀ e ∈ cycleEdges V,
          Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) (x :: zs) →
      ptWind x V = ptWind (zs.getLastD x) V := by
  intro zs
  induction zs with
  | nil => intro x _; simp
  | cons a t ih =>
      intro x hchain
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hrest⟩ := hchain
      rw [ptWind_eq_of_segment_avoids V x a hstep, ih a hrest, List.getLastD_cons]

/-- **Packaged consumer: an edge-avoiding walk to a hull-exterior point kills the
    winding.**  If `x` is joined by an edge-avoiding polyline (walk `x, zs`) to a
    point `zs.getLastD x` lying outside the convex hull of the vertices of `V`,
    then `ptWind x V = 0`.  This is the honest reduction of the two hull-interior
    point-in-polygon residues of `SAWUmlaufPolygon` to the concrete geometric task
    of routing a single edge-avoiding polyline from the forbidden point out to the
    convex-hull exterior. -/
lemma ptWind_zero_of_walk_to_not_hull (V : List ℂ) (x : ℂ) (zs : List ℂ)
    (hchain : List.IsChain (fun a b => ∀ e ∈ cycleEdges V,
        Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) (x :: zs))
    (hy : (zs.getLastD x) ∉ convexHull ℝ (V.toFinset : Set ℂ)) :
    ptWind x V = 0 := by
  rw [ptWind_eq_of_walk V zs x hchain]
  exact ptWind_zero_of_not_mem_convexHull (zs.getLastD x) V hy

end HexArea

end