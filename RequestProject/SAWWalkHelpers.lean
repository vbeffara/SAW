/-
# Walk helper lemmas for the cutting argument and bridge decomposition

Helper lemmas about paths on hexGraph:
- hexGraph neighbor enumeration
- Interior vertex neighbors in paths
- Walk reaches strip boundary
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

/-! ## hexGraph neighbor enumeration -/

/-- hexGraph is bipartite: adjacent vertices have different sublattice types. -/
lemma hexGraph_bip {v w : HexVertex} (h : hexGraph.Adj v w) :
    v.2.2 ≠ w.2.2 := by
  unfold hexGraph at h; rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> simp_all

/-- Neighbors of TRUE(x,y): FALSE(x,y), FALSE(x-1,y), FALSE(x,y-1). -/
lemma adj_true_iff {x y : ℤ} {w : HexVertex} :
    hexGraph.Adj (x, y, true) w ↔
      w = (x, y, false) ∨ w = (x - 1, y, false) ∨ w = (x, y - 1, false) := by
  constructor <;> intro h
  · unfold hexGraph at h; grind
  · cases h <;> unfold hexGraph <;> aesop

/-! ## Walk successor/predecessor -/

/-- A vertex u ≠ w in a walk v → w has a successor in the walk's support. -/
lemma walk_has_succ {v w : HexVertex}
    (p : hexGraph.Walk v w) (u : HexVertex)
    (hu : u ∈ p.support) (huw : u ≠ w) :
    ∃ z ∈ p.support, hexGraph.Adj u z := by
  revert u
  induction p <;> simp_all +decide
  rename_i u v w h₁ h₂ h₃
  cases u; cases v; cases w; simp_all +decide [hexGraph]
  cases h₂ <;> simp_all +decide [hexGraph] <;> grind

/-- A vertex u ≠ v in a walk v → w has a predecessor in the walk's support. -/
lemma walk_has_pred {v w : HexVertex}
    (p : hexGraph.Walk v w) (u : HexVertex)
    (hu : u ∈ p.support) (huv : u ≠ v) :
    ∃ z ∈ p.support, hexGraph.Adj z u := by
  contrapose! huv with huv
  induction p <;> aesop

/-! ## Interior vertex of a PATH has two distinct neighbors -/

/-
An interior vertex (u ≠ start, u ≠ end) of a PATH has two DISTINCT
    neighbors in the support.

    Proof: split the path at u using takeUntil/dropUntil. Both pieces
    are non-nil (since u ≠ start and u ≠ end), so each has a step
    adjacent to u. The predecessor z₂ is in takeUntil.support and
    the successor z₁ is in dropUntil.support \ {u}. Since the path
    is self-avoiding, these two sets are disjoint, so z₁ ≠ z₂.
-/
lemma path_interior_two_distinct_neighbors
    {v w u : HexVertex} (p : hexGraph.Walk v w) (hp : p.IsPath)
    (hu : u ∈ p.support) (huv : u ≠ v) (huw : u ≠ w) :
    ∃ z₁ z₂ : HexVertex, z₁ ≠ z₂ ∧
      hexGraph.Adj u z₁ ∧ hexGraph.Adj z₂ u ∧
      z₁ ∈ p.support ∧ z₂ ∈ p.support := by
  -- By definition of `IsPath`, since `p.IsPath`, `p.support` contains no duplicates.
  have h_no_dup : p.support.Nodup := by
    exact?;
  obtain ⟨q₁, q₂, hq₁, hq₂, huq₁, huq₂⟩ : ∃ q₁ q₂ : hexGraph.Walk v u × hexGraph.Walk u w, p = q₁.1.append q₂.2 ∧ q₁.1.IsPath ∧ q₂.2.IsPath := by
    have h_split : ∃ q₁ : hexGraph.Walk v u, ∃ q₂ : hexGraph.Walk u w, p = q₁.append q₂ := by
      exact ⟨ p.takeUntil u hu, p.dropUntil u hu, by rw [ SimpleGraph.Walk.take_spec ] ⟩;
    obtain ⟨q₁, q₂, hq₁, hq₂⟩ : ∃ q₁ : hexGraph.Walk v u, ∃ q₂ : hexGraph.Walk u w, p = q₁.append q₂ ∧ q₁.IsPath ∧ q₂.IsPath := by
      obtain ⟨q₁, q₂, hq₁⟩ := h_split
      have hq₁_path : q₁.IsPath := by
        simp_all +decide [ SimpleGraph.Walk.isPath_def ];
        exact hp.sublist ( by simp +decide [ SimpleGraph.Walk.support_append ] )
      have hq₂_path : q₂.IsPath := by
        grind +suggestions
      exact ⟨q₁, q₂, hq₁, hq₁_path, hq₂_path⟩;
    exact ⟨ ⟨ q₁, q₂ ⟩, ⟨ q₁, q₂ ⟩, hq₁, hq₂ ⟩;
  obtain ⟨z₁, hz₁⟩ : ∃ z₁, hexGraph.Adj u z₁ ∧ z₁ ∈ q₂.2.support ∧ z₁ ≠ u := by
    rcases q₂ with ⟨ q₁, q₂ ⟩ ; rcases q₂ with ( _ | ⟨ z₁, hz₁ ⟩ ) ; aesop;
    exact ⟨ _, z₁, by aesop ⟩;
  obtain ⟨z₂, hz₂⟩ : ∃ z₂, hexGraph.Adj z₂ u ∧ z₂ ∈ q₁.1.support ∧ z₂ ≠ u := by
    have := walk_has_pred q₁.1 u;
    obtain ⟨ z₂, hz₂₁, hz₂₂ ⟩ := this ( by aesop ) huv; use z₂; aesop;
  grind +suggestions

/-! ## TRUE vertex at strip boundary has FALSE neighbor at lower diagCoord -/

/-
If TRUE(x,y) with x+y = -T (T > 0) is an interior vertex of a
    self-avoiding path from paperStart to w (both with diagCoord 0),
    then the path contains a FALSE vertex with diagCoord -(T+1).

    Proof: TRUE(x,y) has 3 neighbors: FALSE(x,y) at diagCoord x+y = -T,
    FALSE(x-1,y) at diagCoord -(T+1), FALSE(x,y-1) at diagCoord -(T+1).
    By path_interior_two_distinct_neighbors, two distinct neighbors
    are in the path. Since only FALSE(x,y) has diagCoord -T,
    at least one neighbor has diagCoord -(T+1).
-/
lemma true_at_boundary_has_lower_false {T : ℕ}
    {w : HexVertex} (p : hexGraph.Walk paperStart w) (hp : p.IsPath)
    (hw : w.1 + w.2.1 = 0 ∧ w.2.2 = true ∧ w ≠ paperStart)
    (x y : ℤ) (hxy : x + y = -(T : ℤ))
    (ht : (x, y, true) ∈ p.support) (hT : 0 < T) :
    ∃ u ∈ p.support, u.1 + u.2.1 = -(T + 1 : ℤ) ∧ u.2.2 = false := by
  -- By path_interior_two_distinct_neighbors, there exist z₁, z₂ ∈ p.support, z₁ ≠ z₂, Adj (x,y,true) z₁, Adj z₂ (x,y,true).
  obtain ⟨z₁, z₂, hz₁, hz₂, h_distinct⟩ : ∃ z₁ z₂ : HexVertex, z₁ ≠ z₂ ∧ hexGraph.Adj (x, y, true) z₁ ∧ hexGraph.Adj z₂ (x, y, true) ∧ z₁ ∈ p.support ∧ z₂ ∈ p.support := by
    apply path_interior_two_distinct_neighbors p hp ht;
    · unfold paperStart; aesop;
    · grind;
  -- By adj_true_iff, z₁ and z₂ are either (x,y,false), (x-1,y,false), or (x,y-1,false).
  have hz_cases : (z₁ = (x, y, false) ∨ z₁ = (x - 1, y, false) ∨ z₁ = (x, y - 1, false)) ∧ (z₂ = (x, y, false) ∨ z₂ = (x - 1, y, false) ∨ z₂ = (x, y - 1, false)) := by
    exact ⟨ by simpa using adj_true_iff.mp hz₂, by simpa [ SimpleGraph.adj_comm ] using adj_true_iff.mp h_distinct.1.symm ⟩;
  grind

end