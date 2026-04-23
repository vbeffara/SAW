/-
# Hammersley-Welsh bridge decomposition infrastructure

Additional helper lemmas for the HW decomposition.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWHWCore

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk max diagCoord -/

/-- The maximum diagCoord achieved in a walk. -/
def walkMaxDiagCoord {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  p.support.foldl (fun m u => max m (diagCoordZ u)) (diagCoordZ v)

/-
The max is ≥ every vertex's diagCoord.
-/
lemma walkMaxDiagCoord_ge {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    diagCoordZ u ≤ walkMaxDiagCoord p := by
      -- By definition of `walkMaxDiagCoord`, the maximum of a set of numbers is each of those numbers.
      have h_max_le : ∀ (l : List HexVertex), ∀ (u : HexVertex), u ∈ l → diagCoordZ u ≤ List.foldl (fun m u => max m (diagCoordZ u)) (diagCoordZ (l.head!)) l := by
        intro l u hu;
        induction' l using List.reverseRecOn with l ih;
        · contradiction;
        · cases l <;> aesop;
      convert h_max_le p.support u hu using 1;
      unfold walkMaxDiagCoord; cases p <;> aesop;

/-
The max is achieved.
-/
lemma walkMaxDiagCoord_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, diagCoordZ u = walkMaxDiagCoord p := by
      -- By definition of `walkMaxDiagCoord`, it is the maximum of the diagonal coordinates of the vertices in the support of the walk.
      have h_max_def : walkMaxDiagCoord p = Finset.max (p.support.toFinset.image diagCoordZ) := by
        -- By induction on the list, we can show that the foldl of max over the support is equal to the maximum of the image of diagCoordZ over the support.
        have h_ind : ∀ (l : List HexVertex) (a : ℤ), List.foldl (fun m u => max m (diagCoordZ u)) a l = Finset.max (insert a (Finset.image diagCoordZ l.toFinset)) := by
          intro l a;
          induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ Finset.max ];
          grind;
        convert h_ind p.support ( diagCoordZ v ) using 1;
        cases p <;> aesop;
      have := Finset.mem_of_max h_max_def.symm; aesop;

end