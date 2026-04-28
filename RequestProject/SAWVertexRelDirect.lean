/-
# Walk Extension for Vertex Relation

Helper lemma: a SAW can be extended by one step if the neighbor
is fresh and in the strip. This is the key construction for the
triplet part of the vertex relation.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk extension by one step -/

/-- Extend a path by appending one edge to a fresh vertex. -/
def extendPath {u v : HexVertex} (p : hexGraph.Path u v)
    (w : HexVertex) (hadj : hexGraph.Adj v w)
    (hw_fresh : w ∉ p.1.support) :
    hexGraph.Path u w :=
  ⟨p.1.append (.cons hadj .nil), by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
        SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
    exact List.nodup_append.mpr
      ⟨p.2.support_nodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
       by intro x hx; simp at *; rintro rfl; exact hw_fresh hx⟩⟩

/-- Length of extended path. -/
@[simp] lemma extendPath_length {u v : HexVertex} (p : hexGraph.Path u v)
    (w : HexVertex) (hadj : hexGraph.Adj v w) (hw_fresh : w ∉ p.1.support) :
    (extendPath p w hadj hw_fresh).1.length = p.1.length + 1 := by
  simp [extendPath, SimpleGraph.Walk.length_append]

/-- Support of extended path. -/
lemma extendPath_support {u v : HexVertex} (p : hexGraph.Path u v)
    (w : HexVertex) (hadj : hexGraph.Adj v w) (hw_fresh : w ∉ p.1.support) :
    (extendPath p w hadj hw_fresh).1.support = p.1.support ++ [w] := by
  simp [extendPath, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil]

/-- Extended SAW stays in strip if the new vertex is in the strip. -/
lemma extendPath_in_strip {u v : HexVertex} (p : hexGraph.Path u v)
    (w : HexVertex) (hadj : hexGraph.Adj v w) (hw_fresh : w ∉ p.1.support)
    {T L : ℕ}
    (h_strip : ∀ z ∈ p.1.support, PaperFinStrip T L z)
    (hw_strip : PaperFinStrip T L w) :
    ∀ z ∈ (extendPath p w hadj hw_fresh).1.support, PaperFinStrip T L z := by
  rw [extendPath_support]
  intro z hz
  simp [List.mem_append] at hz
  rcases hz with hz | rfl
  · exact h_strip z hz
  · exact hw_strip

end
