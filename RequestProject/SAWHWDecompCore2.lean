/-
# Hammersley-Welsh Decomposition: Walk Peak Splitting

This file formalizes the first step of the Hammersley-Welsh bridge
decomposition: splitting a SAW at its vertex of minimal diagonal coordinate.

## Reference

Section 3 of Duminil-Copin & Smirnov (2012):
"If γ is a self-avoiding walk in the plane, one can cut the trajectory
into two pieces γ₁ and γ₂: the vertices of γ up to the first vertex
of maximal real part, and the remaining vertices."

In our formalization, "maximal real part" corresponds to "minimal
diagonal coordinate" (diagCoord = x + y), since Re(embed(v)) decreases
as diagCoord increases.
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Diagonal coordinate -/

/-- The diagonal coordinate of a hex vertex. -/
def diagCoord' (v : HexVertex) : ℤ := v.1 + v.2.1

/-- paperStart has diagCoord 0. -/
@[simp] lemma diagCoord'_paperStart : diagCoord' paperStart = 0 := by
  simp [diagCoord', paperStart]

/-! ## Minimum diagonal coordinate on a walk -/

/-- The minimum diagonal coordinate visited by a walk. -/
def walkMinDC' {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map diagCoord').foldl min (diagCoord' v)

/-
The minimum is at most the diagonal coordinate of any vertex on the walk.
-/
lemma walkMinDC'_le_of_mem {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    walkMinDC' p ≤ diagCoord' u := by
  induction' p with v w p ih generalizing u;
  · unfold walkMinDC' diagCoord'; aesop;
  · cases hu;
    · unfold walkMinDC';
      induction' ( SimpleGraph.Walk.cons ‹_› ‹_› ).support using List.reverseRecOn with u hu ih <;> aesop;
    · unfold walkMinDC' at *;
      simp_all +decide [ SimpleGraph.Walk.support ];
      rename_i h₁ h₂ h₃;
      have h_foldl_min : ∀ {l : List ℤ} {x : ℤ}, x ∈ l → List.foldl min (diagCoord' w) l ≤ x := by
        intros l x hx; induction' l using List.reverseRecOn with l IH <;> aesop;
      exact h_foldl_min ( List.mem_map.mpr ⟨ u, h₃, rfl ⟩ )

/-- The minimum is at most the diagonal coordinate of the start. -/
lemma walkMinDC'_le_start {v w : HexVertex} (p : hexGraph.Walk v w) :
    walkMinDC' p ≤ diagCoord' v :=
  walkMinDC'_le_of_mem p v (SimpleGraph.Walk.start_mem_support p)

/-
The minimum is attained by some vertex on the walk.
-/
lemma walkMinDC'_attained {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, diagCoord' u = walkMinDC' p := by
  unfold walkMinDC';
  have h_min_exists : ∀ {l : List ℤ}, l ≠ [] → ∃ u ∈ l, u = List.foldl min (l.head!) l := by
    intros l hl_nonempty
    induction' l using List.reverseRecOn with l ih;
    · contradiction;
    · cases l <;> simp_all +decide [ List.foldl_append ];
      grind;
  specialize @h_min_exists ( List.map diagCoord' p.support );
  cases p <;> aesop

/-! ## Walk width -/

/-- The diagonal width of a walk: diagCoord(start) - min diagCoord. -/
def walkDiagWidth' {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  diagCoord' v - walkMinDC' p

/-- Width is non-negative. -/
lemma walkDiagWidth'_nonneg {v w : HexVertex} (p : hexGraph.Walk v w) :
    0 ≤ walkDiagWidth' p := by
  unfold walkDiagWidth'
  linarith [walkMinDC'_le_start p]

end