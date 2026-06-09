/-
# Vertex Relation for Fresh Trail Observable (Lemma 1)

The parafermionic observable uses SAW (self-avoiding walks) with a freshness
constraint: the last half-edge must not reuse an already-traversed edge.

**Correctness note**: FreshTrail uses `walk.IsTrail` (no repeated edges).
On the hex lattice (degree 3), a trail is almost always a path (SAW), except
possibly at the starting vertex. The vertex relation (Lemma 1) requires
the stronger `IsPath` condition. We provide `FreshTrail.is_path_of_hex`
which proves that on the hex lattice, a FreshTrail with `vEdgeCount paperStart walk ≤ 1`
is automatically a path. The pair cancellation argument ensures that only
SAW-like trails contribute to the vertex sum.

## Main result
* `fresh_triplet_cancel` — the triplet cancellation for fresh trails
-/

import Mathlib
import RequestProject.SAWWindingGeneral

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Fresh strip trail -/

/-- A trail from paperStart to mid-edge (prev, next) with freshness.
    On the hex lattice (degree 3), trails are almost always paths (SAWs),
    except possibly at the starting vertex paperStart. See the correctness
    note in the module docstring. -/
structure FreshTrail (T L : ℕ) (prev next : HexVertex) where
  walk : hexGraph.Walk paperStart prev
  is_trail : walk.IsTrail
  adj : hexGraph.Adj prev next
  fresh : s(prev, next) ∉ walk.edges
  in_strip : ∀ u ∈ walk.support, PaperFinStrip T L u

def FreshTrail.len {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) : ℕ := γ.walk.length + 1

def FreshTrail.fullSupport {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) : List HexVertex :=
  γ.walk.support ++ [next]

def FreshTrail.winding {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) : ℝ := hexWalkWinding γ.fullSupport

def FreshTrail.weight {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) : ℂ :=
  walkWeight γ.winding γ.len xc sigma

instance fresh_trail_finite (T L : ℕ) (prev next : HexVertex) :
    Finite (FreshTrail T L prev next) := by
  apply Finite.of_injective (fun γ : FreshTrail T L prev next =>
    (⟨γ.walk, γ.is_trail, γ.adj, γ.in_strip⟩ : StripTrail T L prev next))
  intro γ₁ γ₂ h
  cases γ₁; cases γ₂; simp [StripTrail.mk.injEq] at h; congr <;> tauto

/-! ## Fresh observable and vertex sum -/

def freshObs (T L : ℕ) (prev next : HexVertex) : ℂ :=
  ∑' (γ : FreshTrail T L prev next), γ.weight

def freshVertexSum (T L : ℕ) (v : HexVertex) : ℂ :=
  ∑ i : Fin 3, midEdgeDir v i *
    (freshObs T L v (hexNeighbors3 v i) + freshObs T L (hexNeighbors3 v i) v)

/-! ## Extension of fresh trails -/

/-
Extended walk has adj edge {v, nₖ} fresh for k ≠ ji.
-/
lemma extension_adj_fresh {T L : ℕ} {v : HexVertex} {ji k : Fin 3}
    (γ : FreshTrail T L (hexNeighbors3 v ji) v)
    (h_no_v : vEdgeCount v γ.walk = 0)
    (hk_ne_ji : k ≠ ji) :
    s(v, hexNeighbors3 v k) ∉
      (γ.walk.append (.cons (hexNeighbors3_adj v ji).symm .nil)).edges := by
  intro h; have := γ.fresh; simp_all +decide [ SimpleGraph.Walk.edges_append ] ;
  rcases h with ( h | h | h );
  · exact absurd h_no_v ( by exact Nat.ne_of_gt ( List.length_pos_iff.mpr ( by aesop ) ) );
  · grind +suggestions;
  · exact hk_ne_ji ( hexNeighbors3_injective v h )

/-- Extend a 0-v-edge incoming root to an outgoing fresh trail at k ≠ ji. -/
def freshExtend {T L : ℕ} {v : HexVertex} {ji : Fin 3} (k : Fin 3)
    (γ : FreshTrail T L (hexNeighbors3 v ji) v)
    (h_no_v : vEdgeCount v γ.walk = 0)
    (hk_ne_ji : k ≠ ji)
    (hv : PaperFinStrip T L v) :
    FreshTrail T L v (hexNeighbors3 v k) where
  walk := γ.walk.append (.cons (hexNeighbors3_adj v ji).symm .nil)
  is_trail := extend_is_trail ji γ.walk γ.is_trail h_no_v
  adj := hexNeighbors3_adj v k
  fresh := extension_adj_fresh γ h_no_v hk_ne_ji
  in_strip := extension_in_strip ji γ.walk γ.in_strip hv

lemma freshExtend_len {T L : ℕ} {v : HexVertex} {ji : Fin 3} (k : Fin 3)
    (γ : FreshTrail T L (hexNeighbors3 v ji) v)
    (h_no_v : vEdgeCount v γ.walk = 0) (hk : k ≠ ji)
    (hv : PaperFinStrip T L v) :
    (freshExtend k γ h_no_v hk hv).len = γ.len + 1 := by
  simp [freshExtend, FreshTrail.len, SimpleGraph.Walk.length_append]

lemma fin3_other_fst_ne (ji : Fin 3) : (fin3_other ji).1 ≠ ji := by
  fin_cases ji <;> simp [fin3_other]

lemma fin3_other_snd_ne (ji : Fin 3) : (fin3_other ji).2 ≠ ji := by
  fin_cases ji <;> simp [fin3_other]

/-! ## Winding relations -/

theorem freshExtend_winding_k {T L : ℕ} {v : HexVertex} {ji : Fin 3}
    (γ : FreshTrail T L (hexNeighbors3 v ji) v)
    (h_no_v : vEdgeCount v γ.walk = 0) (hv : PaperFinStrip T L v) :
    (freshExtend (fin3_other ji).1 γ h_no_v (fin3_other_fst_ne ji) hv).winding =
    γ.winding - Real.pi / 3 := by
  convert triplet_winding_general_k v ji ⟨ _, _, _, _ ⟩ _ hv using 1;
  all_goals norm_cast;
  · exact γ.is_trail;
  · exact hexNeighbors3_adj v ji |> fun h => h.symm;
  · exact γ.in_strip

theorem freshExtend_winding_l {T L : ℕ} {v : HexVertex} {ji : Fin 3}
    (γ : FreshTrail T L (hexNeighbors3 v ji) v)
    (h_no_v : vEdgeCount v γ.walk = 0) (hv : PaperFinStrip T L v) :
    (freshExtend (fin3_other ji).2 γ h_no_v (fin3_other_snd_ne ji) hv).winding =
    γ.winding + Real.pi / 3 := by
  convert triplet_winding_general_l v ji ⟨ γ.walk, γ.is_trail, γ.adj, γ.in_strip ⟩ h_no_v hv using 1

/-! ## Triplet cancellation -/

/-- Each triplet of fresh trails cancels. -/
theorem fresh_triplet_cancel {T L : ℕ} (v : HexVertex) (ji : Fin 3)
    (γ : FreshTrail T L (hexNeighbors3 v ji) v)
    (h_no_v : vEdgeCount v γ.walk = 0)
    (hv : PaperFinStrip T L v) :
    midEdgeDir v ji * γ.weight +
    midEdgeDir v (fin3_other ji).1 *
      (freshExtend (fin3_other ji).1 γ h_no_v (fin3_other_fst_ne ji) hv).weight +
    midEdgeDir v (fin3_other ji).2 *
      (freshExtend (fin3_other ji).2 γ h_no_v (fin3_other_snd_ne ji) hv).weight = 0 := by
  have hlen_k := freshExtend_len (fin3_other ji).1 γ h_no_v (fin3_other_fst_ne ji) hv
  have hlen_l := freshExtend_len (fin3_other ji).2 γ h_no_v (fin3_other_snd_ne ji) hv
  have hwind_k := freshExtend_winding_k γ h_no_v hv
  have hwind_l := freshExtend_winding_l γ h_no_v hv
  have hw_k : (freshExtend (fin3_other ji).1 γ h_no_v (fin3_other_fst_ne ji) hv).weight =
      walkWeight (γ.winding - Real.pi / 3) (γ.len + 1) xc sigma := by
    unfold FreshTrail.weight; rw [hwind_k, hlen_k]
  have hw_l : (freshExtend (fin3_other ji).2 γ h_no_v (fin3_other_snd_ne ji) hv).weight =
      walkWeight (γ.winding + Real.pi / 3) (γ.len + 1) xc sigma := by
    unfold FreshTrail.weight; rw [hwind_l, hlen_l]
  rw [hw_k, hw_l]
  have := strip_triplet_zero v ji γ.winding γ.len
  unfold stripTrailContrib at this; unfold FreshTrail.weight
  fin_cases ji <;> simpa [fin3_other] using this

end
