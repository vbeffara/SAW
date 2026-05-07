/-
# Walk Partition Infrastructure for Vertex Relation

Key helper lemmas for the walk partition into pairs and triplets
(Lemma 1 of Duminil-Copin & Smirnov 2012).
-/

import Mathlib
import RequestProject.SAWSubmult

noncomputable section

/-! ## DiagCoord adjacency bounds -/

/-
Adjacent vertices on the hex lattice have diagCoord (x+y) differing by at most 1.
-/
lemma diagCoord_adj_bound {v w : HexVertex} (h : hexGraph.Adj v w) :
    |w.1 + w.2.1 - (v.1 + v.2.1)| ≤ 1 := by
  cases h ; norm_num [ *, abs_le ];
  · omega;
  · exact abs_le.mpr ⟨ by omega, by omega ⟩

/-! ## Neighbor classification -/

/-
The neighbors of a FALSE vertex (x,y,false) are exactly
    (x,y,true), (x+1,y,true), (x,y+1,true).
-/
lemma false_vertex_adj (x y : ℤ) (w : HexVertex) :
    hexGraph.Adj (x, y, false) w ↔
    w = (x, y, true) ∨ w = (x + 1, y, true) ∨ w = (x, y + 1, true) := by
  rcases w with ⟨ x', y', b ⟩;
  cases b <;> simp +decide [ hexGraph ];
  grind

/-
The neighbors of a TRUE vertex (x,y,true) are exactly
    (x,y,false), (x-1,y,false), (x,y-1,false).
-/
lemma true_vertex_adj (x y : ℤ) (w : HexVertex) :
    hexGraph.Adj (x, y, true) w ↔
    w = (x, y, false) ∨ w = (x - 1, y, false) ∨ w = (x, y - 1, false) := by
  rcases w with ⟨ x', y', b' ⟩ ; unfold hexGraph; aesop;

/-
c_0 = 1.
-/
lemma saw_count_zero : saw_count 0 = 1 := by
  refine' Fintype.card_eq_one_iff.mpr _;
  use ⟨ hexOrigin, ⟨ SimpleGraph.Walk.nil, by simp +decide ⟩, by simp +decide ⟩;
  rintro ⟨ w, ⟨ p, hp ⟩, l ⟩;
  cases p <;> aesop

end