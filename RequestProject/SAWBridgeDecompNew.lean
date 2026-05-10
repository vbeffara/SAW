/-
# Bridge decomposition helpers for Hammersley-Welsh bound

Key helper lemmas for the bridge decomposition injection:
paper_bridge_decomp_injection.

The Hammersley-Welsh decomposition maps each SAW to a pair of
bridge sequences. Key steps:
1. Find the first vertex with maximum diagCoord
2. Split the walk there
3. Each half decomposes into bridges
4. The decomposition is at most 2-to-1
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWHWDecompHelper

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Maximum diagCoord infrastructure -/

/-- The maximum diagCoord in a walk's support. -/
def walk_max_dc {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map diagCoordHW).foldl max (diagCoordHW v)

/-
walk_max_dc is at least the diagCoord of any vertex in the support.
-/
lemma le_walk_max_dc {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    diagCoordHW u ≤ walk_max_dc p := by
  have h_foldl : ∀ {l : List ℤ} {x : ℤ}, x ∈ l → x ≤ List.foldl max (diagCoordHW v) l := by
    intros l x hx; induction' l using List.reverseRecOn with l IH <;> aesop;
  exact h_foldl ( List.mem_map.mpr ⟨ u, hu, rfl ⟩ )

/-
walk_max_dc is achieved by some vertex.
-/
lemma walk_max_dc_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, diagCoordHW u = walk_max_dc p := by
  -- The maximum of a finite set of integers is achieved by some element in the set.
  have h_max_achieved : ∀ (S : List ℤ), S ≠ [] → ∃ u ∈ S, u = S.foldl max (S.head!) := by
    intros S hS_nonempty; induction' S using List.reverseRecOn with S ih <;> simp_all +decide [ List.foldl ] ;
    cases S <;> simp_all +decide [ List.foldl_append ];
    grind;
  -- Apply the hypothesis `h_max_achieved` to the list of diagonal coordinates of the support of `p`.
  have h_support_nonempty : p.support.map diagCoordHW ≠ [] := by
    cases p <;> aesop;
  convert h_max_achieved _ h_support_nonempty using 1;
  simp +decide [ walk_max_dc ];
  cases p <;> aesop

/-- walk_max_dc ≥ diagCoordHW v (the starting vertex). -/
lemma walk_max_dc_ge_start {v w : HexVertex} (p : hexGraph.Walk v w) :
    diagCoordHW v ≤ walk_max_dc p := by
  exact le_walk_max_dc p v p.start_mem_support

/-- walk_max_dc ≥ diagCoordHW w (the ending vertex). -/
lemma walk_max_dc_ge_end {v w : HexVertex} (p : hexGraph.Walk v w) :
    diagCoordHW w ≤ walk_max_dc p := by
  exact le_walk_max_dc p w p.end_mem_support

/-
walk_max_dc ≤ diagCoordHW v + walk length.
-/
lemma walk_max_dc_le_start_add_length {v w : HexVertex} (p : hexGraph.Walk v w) :
    walk_max_dc p ≤ diagCoordHW v + p.length := by
  -- By definition of $walk_max_dc$, we know that there exists some vertex $u$ in the support of $p$ such that $walk_max_dc p = diagCoordHW u$.
  obtain ⟨u, hu_support, hu_max⟩ : ∃ u ∈ p.support, walk_max_dc p = diagCoordHW u := by
    exact walk_max_dc_achieved p |> fun ⟨ u, hu, hu' ⟩ => ⟨ u, hu, hu'.symm ⟩;
  -- By definition of $diagCoordHW$, we know that $diagCoordHW u - diagCoordHW v \leq p.length$.
  have h_diff : diagCoordHW u - diagCoordHW v ≤ p.length := by
    have h_diff : ∀ {v w : HexVertex} (p : hexGraph.Walk v w), ∀ u ∈ p.support, diagCoordHW u - diagCoordHW v ≤ p.length := by
      intros v w p u hu_support
      have h_diff : diagCoordHW u - diagCoordHW v ≤ (p.takeUntil u hu_support).length := by
        convert hexGraph_walk_sum_bound_pos ( p.takeUntil u hu_support ) using 1;
      grind +suggestions;
    exact h_diff p u hu_support;
  linarith

/-
The powerset product identity:
    ∑_{S ⊆ F} ∏_{i ∈ S} a_i = ∏_{i ∈ F} (1 + a_i).
-/
lemma Finset.sum_powerset_prod_eq_prod_add_one {α : Type*} [CommSemiring α]
    (F : Finset ι) (a : ι → α) :
    ∑ S ∈ F.powerset, ∏ i ∈ S, a i = ∏ i ∈ F, (1 + a i) := by
  rw [Finset.prod_one_add]

end