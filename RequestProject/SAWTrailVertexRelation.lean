/-
# Trail Vertex Relation (Lemma 1) — Infrastructure

Infrastructure for proving the cancellation identity:
  trailVertexSum T L v = 0

## Key results (sorry-free)
* `incoming_sum_split` — incoming trails split by v-edge count (0 or 2)
* `outgoing_sum_split` — outgoing trails split by v-edge count (1 or 3)
* `extensionMap` — bijection from IncomingRoot to OutgoingExt
* `root_triplet_zero` — each root's triplet contribution vanishes
* `outgoing_ext_by_root_index` — decomposes outgoing ext sum by root index

## Architecture
The vertex sum decomposes as (IncomingRoot + OutgoingExt) + (IncomingPair + OutgoingPairMem).
For StripTrails (no freshness), the "triplet part" (IncomingRoot + OutgoingExt) is NOT
independently zero because the outgoing sum at k includes self-extensions from roots at k.
The correct decomposition uses FreshTrails (see SAWVertexRelationProof.lean) where freshness
excludes self-extensions, making the triplet part independently zero.

## Remaining gaps
* `triplet_part_zero` — needs corrected decomposition (see note above)
* `pair_part_zero` — requires loop-reversal involution
-/

import Mathlib
import RequestProject.SAWWindingGeneral

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Splitting StripTrail sums by v-edge count

Since StripTrail is Finite, tsum = sum over finite type. We split into
subtypes by vEdgeCount. -/

/-- Incoming trail with 0 v-edges. -/
def IncomingRoot (T L : ℕ) (v : HexVertex) (ji : Fin 3) :=
  {γ : StripTrail T L (hexNeighbors3 v ji) v // vEdgeCount v γ.walk = 0}

/-- Incoming trail with 2 v-edges. -/
def IncomingPair (T L : ℕ) (v : HexVertex) (ji : Fin 3) :=
  {γ : StripTrail T L (hexNeighbors3 v ji) v // vEdgeCount v γ.walk = 2}

/-- Outgoing trail with 1 v-edge. -/
def OutgoingExt (T L : ℕ) (v : HexVertex) (k : Fin 3) :=
  {γ : StripTrail T L v (hexNeighbors3 v k) // vEdgeCount v γ.walk = 1}

/-- Outgoing trail with 3 v-edges. -/
def OutgoingPairMem (T L : ℕ) (v : HexVertex) (k : Fin 3) :=
  {γ : StripTrail T L v (hexNeighbors3 v k) // vEdgeCount v γ.walk = 3}

instance (T L : ℕ) (v : HexVertex) (ji : Fin 3) : Finite (IncomingRoot T L v ji) :=
  Subtype.finite
instance (T L : ℕ) (v : HexVertex) (ji : Fin 3) : Finite (IncomingPair T L v ji) :=
  Subtype.finite
instance (T L : ℕ) (v : HexVertex) (k : Fin 3) : Finite (OutgoingExt T L v k) :=
  Subtype.finite
instance (T L : ℕ) (v : HexVertex) (k : Fin 3) : Finite (OutgoingPairMem T L v k) :=
  Subtype.finite

/-! ## Sum decomposition by v-edge count -/

/-
Incoming trails split into 0-v-edge and 2-v-edge.
-/
lemma incoming_sum_split (T L : ℕ) (v : HexVertex) (ji : Fin 3)
    (hv_ne_start : v ≠ paperStart) :
    ∑' (γ : StripTrail T L (hexNeighbors3 v ji) v), γ.weight =
    ∑' (γ : IncomingRoot T L v ji), γ.1.weight +
    ∑' (γ : IncomingPair T L v ji), γ.1.weight := by
  have h_split : ∀ (γ : StripTrail T L (hexNeighbors3 v ji) v), γ.weight = (if vEdgeCount v γ.walk = 0 then γ.weight else 0) + (if vEdgeCount v γ.walk = 2 then γ.weight else 0) := by
    intro γ; specialize hv_ne_start; have := incoming_trail_vEdge_classify v ji γ hv_ne_start; aesop;
  convert ( tsum_congr h_split ) using 1;
  rw [ Summable.tsum_add ];
  · congr! 1;
    · convert ( tsum_subtype _ _ ) using 1;
      simp +decide [ Set.indicator ];
      congr! 3;
    · convert ( tsum_subtype _ _ ) using 1;
      simp +decide [ Set.indicator ];
      congr! 3;
  · haveI := Fintype.ofFinite ( StripTrail T L ( hexNeighbors3 v ji ) v ) ; exact ⟨ _, hasSum_fintype _ ⟩ ;
  · haveI := Fintype.ofFinite ( StripTrail T L ( hexNeighbors3 v ji ) v ) ; exact ⟨ _, hasSum_fintype _ ⟩ ;

/-
Outgoing trails split into 1-v-edge and 3-v-edge (for nonempty walks).
-/
lemma outgoing_sum_split (T L : ℕ) (v : HexVertex) (k : Fin 3)
    (hv_ne_start : v ≠ paperStart) :
    ∑' (γ : StripTrail T L v (hexNeighbors3 v k)), γ.weight =
    ∑' (γ : OutgoingExt T L v k), γ.1.weight +
    ∑' (γ : OutgoingPairMem T L v k), γ.1.weight := by
  rw [ ← Summable.tsum_subtype_add_tsum_subtype_compl ];
  congr! 1;
  · -- Since the complement of 1 is 3, the two sets are equal.
    have h_compl : {γ : StripTrail T L v (hexNeighbors3 v k) | vEdgeCount v γ.walk = 1}ᶜ = {γ : StripTrail T L v (hexNeighbors3 v k) | vEdgeCount v γ.walk = 3} := by
      ext γ; simp [hv_ne_start];
      have := outgoing_trail_vEdge_classify v k γ hv_ne_start (by
      contrapose! hv_ne_start; induction γ; simp_all +decide [ StripTrail ] ;
      cases ‹hexGraph.Walk paperStart v› <;> aesop);
      grind;
    congr! 2;
    · convert congr_arg _ h_compl using 1;
    · congr! 1;
      congr! 1;
  · exact?

/-! ## The extension map: IncomingRoot → OutgoingExt -/

/-- The extension map: a 0-v-edge incoming root at ji maps to a 1-v-edge outgoing at k. -/
def extensionMap {T L : ℕ} {v : HexVertex} {ji : Fin 3} (k : Fin 3)
    (hv : PaperFinStrip T L v)
    (γ : IncomingRoot T L v ji) : OutgoingExt T L v k :=
  ⟨tripletExtendStrip v ji k γ.1 γ.2 hv,
   tripletExtendStrip_vEdge v ji k γ.1 γ.2 hv⟩

/-- The extension preserves weights according to the triplet formula. -/
lemma extensionMap_weight_k {T L : ℕ} {v : HexVertex} {ji : Fin 3}
    (hv : PaperFinStrip T L v) (γ : IncomingRoot T L v ji) :
    (extensionMap (fin3_other ji).1 hv γ).1.weight =
    walkWeight (γ.1.winding - Real.pi / 3) (γ.1.len + 1) xc sigma := by
  unfold extensionMap StripTrail.weight
  rw [triplet_winding_general_k, tripletExtendStrip_len]

lemma extensionMap_weight_l {T L : ℕ} {v : HexVertex} {ji : Fin 3}
    (hv : PaperFinStrip T L v) (γ : IncomingRoot T L v ji) :
    (extensionMap (fin3_other ji).2 hv γ).1.weight =
    walkWeight (γ.1.winding + Real.pi / 3) (γ.1.len + 1) xc sigma := by
  unfold extensionMap StripTrail.weight
  rw [triplet_winding_general_l, tripletExtendStrip_len]

/-! ## Triplet sum over IncomingRoot

For each incoming root γ at index ji, the triplet contribution is:
  midEdgeDir v ji * γ.weight
  + midEdgeDir v k * ext_k(γ).weight
  + midEdgeDir v l * ext_l(γ).weight = 0

The key step: summing over all roots and all their extensions gives zero. -/

/-- The triplet contribution of a single root vanishes. -/
lemma root_triplet_zero {T L : ℕ} (v : HexVertex) (ji : Fin 3)
    (hv : PaperFinStrip T L v) (γ : IncomingRoot T L v ji) :
    midEdgeDir v ji * γ.1.weight +
    midEdgeDir v (fin3_other ji).1 * (extensionMap (fin3_other ji).1 hv γ).1.weight +
    midEdgeDir v (fin3_other ji).2 * (extensionMap (fin3_other ji).2 hv γ).1.weight = 0 := by
  rw [extensionMap_weight_k, extensionMap_weight_l]
  have := strip_triplet_zero v ji γ.1.winding γ.1.len
  unfold stripTrailContrib at this; unfold StripTrail.weight
  fin_cases ji <;> simpa [fin3_other] using this

/-! ## The vertex relation: triplet-only case

For vertex-SAWs (paths), only 0-v-edge incoming and 1-v-edge outgoing
trails arise (no pairs). The vertex relation follows from the triplet
cancellation alone.

For general trails, we also need pair cancellation. -/

/-! ## Extension map is injective -/

/-
The extension map is injective on IncomingRoot.
-/
lemma extensionMap_injective {T L : ℕ} {v : HexVertex} {ji : Fin 3} (k : Fin 3)
    (hv : PaperFinStrip T L v) :
    Function.Injective (extensionMap k hv : IncomingRoot T L v ji → OutgoingExt T L v k) := by
  intro x y;
  intro hxy
  have h_walk : x.1.walk = y.1.walk := by
    injection hxy;
    injection ‹_›;
    grind +suggestions
  exact Subtype.ext (by
  cases h : x.val ; cases h' : y.val ; aesop)

/-
Every 1-v-edge outgoing trail is an extension of some 0-v-edge incoming root.
-/
lemma outgoingExt_from_root {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v)
    (hv_ne_start : v ≠ paperStart)
    (γ : OutgoingExt T L v k) :
    ∃ (ji : Fin 3) (root : IncomingRoot T L v ji),
      extensionMap k hv root = γ := by
  obtain ⟨j, prefix_trail, h_prefix_trail, h_len, h_no_v⟩ : ∃ j : Fin 3, ∃ prefix_trail : hexGraph.Walk paperStart (hexNeighbors3 v j), prefix_trail.IsTrail ∧ γ.1.walk = prefix_trail.append (.cons (hexNeighbors3_adj v j).symm .nil) ∧ vEdgeCount v prefix_trail = 0 := by
    have := γ.2;
    obtain ⟨u, prefix_trail, hadj, h_walk⟩ : ∃ u : HexVertex, ∃ prefix_trail : hexGraph.Walk paperStart u, ∃ hadj : hexGraph.Adj u v, γ.1.walk = prefix_trail.append (.cons hadj .nil) ∧ prefix_trail.IsTrail ∧ s(u, v) ∉ prefix_trail.edges := by
      have := walk_decompose_last_trail γ.1.walk γ.1.is_trail (by
      contrapose! this; simp_all +decide [ vEdgeCount ] ;
      grind);
      exact this;
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, u = hexNeighbors3 v j := by
      have := hexNeighbors3_complete v u hadj.symm; aesop;
    have h_no_v : vEdgeCount v (prefix_trail.append (.cons hadj .nil)) = vEdgeCount v prefix_trail + (if v ∈ s(u, v) then 1 else 0) := by
      convert vEdgeCount_append_edge v prefix_trail hadj using 1;
    aesop;
  unfold extensionMap;
  use j, ⟨⟨prefix_trail, h_prefix_trail, hexNeighbors3_adj v j |> SimpleGraph.Adj.symm, fun u hu => ?_⟩, h_no_v⟩;
  all_goals norm_num [ tripletExtendStrip ];
  congr;
  · exact h_len.symm;
  · exact γ.1.in_strip u ( by aesop )

/-
The combined extension map is injective.
-/
lemma sigma_extensionMap_injective {T L : ℕ} {v : HexVertex} (k : Fin 3)
    (hv : PaperFinStrip T L v) :
    Function.Injective (fun (p : Σ (ji : Fin 3), IncomingRoot T L v ji) =>
      extensionMap k hv p.2 : _ → OutgoingExt T L v k) := by
  intro p₁ p₂ h_eq
  have h_support : p₁.2.1.walk.support = p₂.2.1.walk.support := by
    have h_walk_eq : (p₁.2.1.walk.append (.cons (hexNeighbors3_adj v p₁.1).symm .nil)).support = (p₂.2.1.walk.append (.cons (hexNeighbors3_adj v p₂.1).symm .nil)).support := by
      convert congr_arg ( fun x : OutgoingExt T L v k => x.1.walk.support ) h_eq using 1;
    simp_all +decide [ SimpleGraph.Walk.support_append ];
  have h_last : p₁.2.1.walk.support.getLast? = some (hexNeighbors3 v p₁.1) ∧ p₂.2.1.walk.support.getLast? = some (hexNeighbors3 v p₂.1) := by
    have h_last : ∀ (ji : Fin 3) (γ : IncomingRoot T L v ji), γ.1.walk.support.getLast? = some (hexNeighbors3 v ji) := by
      intros ji γ
      have h_last : γ.1.walk.support.getLast? = some (γ.1.walk.support.getLast!) := by
        cases h : γ.val.walk.support <;> aesop;
      rw [ h_last, List.getLast!_eq_getElem! ];
      simp +decide [ StripTrail.walk ];
    grind;
  have h_last_eq : hexNeighbors3 v p₁.1 = hexNeighbors3 v p₂.1 := by
    grind +qlia;
  have h_last_eq : p₁.1 = p₂.1 := by
    exact hexNeighbors3_injective v h_last_eq;
  have h_inj : Function.Injective (extensionMap k hv : IncomingRoot T L v p₁.1 → OutgoingExt T L v k) := by
    grind +suggestions;
  cases p₁ ; cases p₂ ; aesop

/-- The combined extension map is surjective. -/
lemma sigma_extensionMap_surjective {T L : ℕ} {v : HexVertex} (k : Fin 3)
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart) :
    Function.Surjective (fun (p : Σ (ji : Fin 3), IncomingRoot T L v ji) =>
      extensionMap k hv p.2 : _ → OutgoingExt T L v k) := by
  intro γ; exact outgoingExt_from_root hv hv_ne_start γ |>.elim fun ji h => h.elim fun root hr => ⟨⟨ji, root⟩, hr⟩

/-- Rewrite outgoing ext tsum via bijection. -/
lemma outgoing_ext_tsum_rewrite {T L : ℕ} {v : HexVertex} (k : Fin 3)
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart) :
    ∑' (γ : OutgoingExt T L v k), γ.1.weight =
    ∑' (p : Σ (ji : Fin 3), IncomingRoot T L v ji),
      (extensionMap k hv p.2).1.weight := by
  have hbij : Function.Bijective (fun (p : Σ (ji : Fin 3), IncomingRoot T L v ji) =>
    extensionMap k hv p.2 : _ → OutgoingExt T L v k) :=
    ⟨sigma_extensionMap_injective k hv, sigma_extensionMap_surjective k hv hv_ne_start⟩
  rw [← Equiv.tsum_eq (Equiv.ofBijective _ hbij)]
  simp [Equiv.ofBijective_apply]

/-- Decompose outgoing ext tsum by root index. -/
lemma outgoing_ext_by_root_index {T L : ℕ} {v : HexVertex} (k : Fin 3)
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart) :
    ∑' (γ : OutgoingExt T L v k), γ.1.weight =
    ∑ ji : Fin 3, ∑' (γ : IncomingRoot T L v ji), (extensionMap k hv γ).1.weight := by
  rw [outgoing_ext_tsum_rewrite k hv hv_ne_start]
  rw [Summable.tsum_sigma' (fun ji => Summable.of_finite) Summable.of_finite]
  simp only [tsum_fintype]

/-- The triplet part of the vertex sum vanishes. -/
theorem triplet_part_zero (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v)
    (hv_ne_start : v ≠ paperStart) :
    ∑ ji : Fin 3, midEdgeDir v ji * ∑' (γ : IncomingRoot T L v ji), γ.1.weight +
    ∑ k : Fin 3, midEdgeDir v k * ∑' (γ : OutgoingExt T L v k), γ.1.weight = 0 := by
  /- Note: For StripTrails (no freshness), the triplet part is NOT independently zero
     because the outgoing sum at k includes self-extensions from roots at k.
     The correct decomposition uses FreshTrails (see SAWVertexRelationProof.lean). -/
  sorry

/-- The pair part of the vertex sum vanishes. -/
theorem pair_part_zero (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v)
    (hv_ne_start : v ≠ paperStart) :
    ∑ ji : Fin 3, midEdgeDir v ji * ∑' (γ : IncomingPair T L v ji), γ.1.weight +
    ∑ k : Fin 3, midEdgeDir v k * ∑' (γ : OutgoingPairMem T L v k), γ.1.weight = 0 := by
  sorry

/-
The vertex sum decomposes into triplet + pair parts.
-/
theorem vertex_sum_decompose (T L : ℕ) (v : HexVertex)
    (hv_ne_start : v ≠ paperStart) :
    trailVertexSum T L v =
    (∑ ji : Fin 3, midEdgeDir v ji * ∑' (γ : IncomingRoot T L v ji), γ.1.weight +
     ∑ k : Fin 3, midEdgeDir v k * ∑' (γ : OutgoingExt T L v k), γ.1.weight) +
    (∑ ji : Fin 3, midEdgeDir v ji * ∑' (γ : IncomingPair T L v ji), γ.1.weight +
     ∑ k : Fin 3, midEdgeDir v k * ∑' (γ : OutgoingPairMem T L v k), γ.1.weight) := by
  unfold trailVertexSum trailObs; simp +decide [ Finset.sum_add_distrib, mul_add ] ;
  simp +decide only [outgoing_sum_split T L v _ hv_ne_start, mul_add, Finset.sum_add_distrib] ; ring;
  simp +decide only [incoming_sum_split T L v _ hv_ne_start, mul_add, Finset.sum_add_distrib];
  ring

/-- **Lemma 1**: The trail vertex relation. -/
theorem trail_vertex_relation' (T L : ℕ) (v : HexVertex)
    (hv_strip : PaperFinStrip T L v)
    (hv_ne_start : v ≠ paperStart)
    (h_nbrs_strip : ∀ i : Fin 3, PaperFinStrip T L (hexNeighbors3 v i)) :
    trailVertexSum T L v = 0 := by
  rw [vertex_sum_decompose T L v hv_ne_start]
  have h1 := triplet_part_zero T L v hv_strip hv_ne_start
  have h2 := pair_part_zero T L v hv_strip hv_ne_start
  linear_combination h1 + h2

end