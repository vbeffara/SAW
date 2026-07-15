import RequestProject.SAWUmlaufEarSplit

/-!
# Chord-piece length infrastructure for the Umlaufsatz

This file proves the finite list-length fact needed by the exterior-path branch.
It is imported by `SAWUmlaufPolygon` and therefore belongs to the main proof
chain.
-/

open Real Complex
noncomputable section
namespace HexArea

/-
A chord piece with at least three vertices which omits a vertex of the
original cycle can occur only when the cycle has at least four vertices.  The
three-vertex premise is essential: without it, the left piece of a triangle cut
at `k = 1` is `[a,b]` and omits `c`.
-/
lemma chordPiece_omits_vertex_length_four
    (W : List ℂ) (k : ℕ) (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (P : List ℂ) (hP : P = chordLeft W k ∨ P = chordRight W k)
    (hP3 : 3 ≤ P.length) (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P) :
    4 ≤ W.length := by
  rcases hP with ( rfl | rfl ) <;> simp_all +arith +decide [ chordLeft, chordRight ];
  · rcases W with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | W ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
    · lia;
    · interval_cases k ; aesop;
  · rcases W with ( _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | W ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
    · interval_cases k ; contradiction;
    · interval_cases k <;> simp_all +decide

end HexArea