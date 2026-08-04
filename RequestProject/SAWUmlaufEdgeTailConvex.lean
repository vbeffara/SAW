import Mathlib
import RequestProject.SAWUmlaufArcBasics

/-!
# The old tail meets the new edge in a convex terminal piece

This file is preparation for `SAWUmlaufCorridorSelect` and hence lies on the
live route to the Umlaufsatz.

`PlaneArcSimple` permits adjacent collinear overlap, so the new edge `[a,b]` may
meet the old tail `chainCarrier (b :: L)` in more than the attachment point `b`.
What is nevertheless always true is that the intersection is **convex**: only the
adjacent tail edge `[b, c]` can meet `[a,b]` at all, and the intersection of two
segments is convex.

Convexity is exactly what the corridor construction needs: since the tail
intersection is a convex subset of `[a,b]` containing `b`, every point of the
edge that is *not* in the tail is separated from `b` by points that are also not
in the tail.  Hence the initial piece `[a, a + s₀ (b-a)]` reaching the deepest
crossing is entirely free of the tail, and a corridor around it is tail-free.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- Both endpoints of a chain edge are vertices of the chain. -/
lemma chainEdges_endpoints_mem (L : List ℂ) {e : ℂ × ℂ} (he : e ∈ chainEdges L) :
    e.1 ∈ L ∧ e.2 ∈ L := by
  have he' : (e.1, e.2) ∈ L.zip L.tail := by
    simpa [chainEdges] using he
  obtain ⟨h1, h2⟩ := List.of_mem_zip he'
  exact ⟨h1, (List.tail_sublist L).subset h2⟩

/-- Edges of the second tail of a chain are edges of the chain. -/
lemma chainEdges_mem_of_tail_tail (a b : ℂ) (M : List ℂ) {e : ℂ × ℂ}
    (he : e ∈ chainEdges M) : e ∈ chainEdges (a :: b :: M) := by
  rcases M with _ | ⟨c, M'⟩
  · simp [chainEdges] at he
  · rw [chainEdges_cons_cons, chainEdges_cons_cons]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)

/-- The new edge is disjoint from every non-adjacent tail edge. -/
lemma segment_disjoint_chainCarrier_drop2 (a b c : ℂ) (L' : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: c :: L')) :
    Disjoint (segment ℝ a b) (chainCarrier (c :: L')) := by
  obtain ⟨hnodup, hdisj⟩ := hsimple
  have hane : a ∉ c :: L' := by
    intro h
    simp only [List.nodup_cons] at hnodup
    exact hnodup.1 (List.mem_cons_of_mem _ h)
  have hbne : b ∉ c :: L' := by
    intro h
    simp only [List.nodup_cons] at hnodup
    exact hnodup.2.1 h
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [chainCarrier] at hz'
  simp only [Set.mem_iUnion] at hz'
  obtain ⟨e, he, hze⟩ := hz'
  obtain ⟨h1, h2⟩ := chainEdges_endpoints_mem (c :: L') he
  have hab : ((a, b) : ℂ × ℂ) ∈ chainEdges (a :: b :: c :: L') := by
    rw [chainEdges_cons_cons]; exact List.mem_cons_self
  have heL : e ∈ chainEdges (a :: b :: c :: L') :=
    chainEdges_mem_of_tail_tail a b (c :: L') he
  have hd := hdisj (a, b) hab e heL
    (by rintro rfl; exact hane h1) (by rintro rfl; exact hane h2)
    (by rintro rfl; exact hbne h1) (by rintro rfl; exact hbne h2)
  exact Set.disjoint_left.mp hd hz hze

/-- **The tail meets the new edge in a convex set.**  Only the adjacent tail
edge can meet `[a,b]`, so the intersection is an intersection of two
segments. -/
lemma segment_inter_tail_convex (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L)) :
    Convex ℝ (segment ℝ a b ∩ chainCarrier (b :: L)) := by
  rcases L with _ | ⟨c, L'⟩
  · simp only [chainCarrier_singleton, Set.inter_empty]
    exact convex_empty
  · have hdisj := segment_disjoint_chainCarrier_drop2 a b c L' hsimple
    have hrw : segment ℝ a b ∩ chainCarrier (b :: c :: L')
        = segment ℝ a b ∩ segment ℝ b c := by
      rw [chainCarrier_cons_cons, Set.inter_union_distrib_left,
        Set.disjoint_iff_inter_eq_empty.mp hdisj, Set.union_empty]
    rw [hrw]
    exact (convex_segment a b).inter (convex_segment b c)

/-- The attachment endpoint lies in the tail whenever the tail is nonempty. -/
lemma terminal_mem_chainCarrier (b c : ℂ) (L' : List ℂ) :
    b ∈ chainCarrier (b :: c :: L') := by
  rw [chainCarrier_cons_cons]
  exact Or.inl (left_mem_segment ℝ b c)

end HexArea
