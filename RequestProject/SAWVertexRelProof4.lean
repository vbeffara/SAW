/-
# Vertex Relation Proof Infrastructure

Walk extension lemmas for the vertex relation proof.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk extension by one step -/

/-- Extend a path by one step, appending an edge at the end. -/
def extendPath {a v w : HexVertex}
    (p : hexGraph.Path a v) (h_adj : hexGraph.Adj v w) (h_notin : w ∉ p.1.support) :
    hexGraph.Path a w :=
  ⟨p.1.concat h_adj, p.2.concat h_notin h_adj⟩

/-
The extended path has length = original + 1.
-/
lemma extendPath_length {a v w : HexVertex}
    (p : hexGraph.Path a v) (h_adj : hexGraph.Adj v w) (h_notin : w ∉ p.1.support) :
    (extendPath p h_adj h_notin).1.length = p.1.length + 1 := by
  convert SimpleGraph.Walk.length_concat ( p := p.1 ) ( h := h_adj )

/-
The support of the extended path is the original support ++ [w].
-/
lemma extendPath_support {a v w : HexVertex}
    (p : hexGraph.Path a v) (h_adj : hexGraph.Adj v w) (h_notin : w ∉ p.1.support) :
    (extendPath p h_adj h_notin).1.support = p.1.support ++ [w] := by
  unfold extendPath; aesop;

/-- Extend a SAW by one step. -/
def extendSAW {v : HexVertex} {n : ℕ} (s : SAW paperStart n)
    (hv : s.w = v) (w : HexVertex) (h_adj : hexGraph.Adj v w)
    (h_notin : w ∉ s.p.1.support) :
    SAW paperStart (n + 1) where
  w := w
  p := extendPath s.p (hv ▸ h_adj) h_notin
  l := by rw [extendPath_length, s.l]

/-- The endpoint of extendSAW is w. -/
lemma extendSAW_endpoint {v : HexVertex} {n : ℕ} (s : SAW paperStart n)
    (hv : s.w = v) (w : HexVertex) (h_adj : hexGraph.Adj v w)
    (h_notin : w ∉ s.p.1.support) :
    (extendSAW s hv w h_adj h_notin).w = w := rfl

end