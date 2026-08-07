import Mathlib
import RequestProject.SAWUmlaufJordanInduction

/-!
# `SAWUmlaufTriangleExample` — a concrete instance of the planar Umlaufsatz

The planar Umlaufsatz `polygon_umlaufsatz_final`
(`RequestProject.SAWUmlaufJordanInduction`) carries three hypotheses
(`3 ≤ V.length`, `PolygonSimple V`, `polyNondeg (V ++ [V[0], V[1]])`).  This file
exhibits them for the concrete triangle `[0, 1, i]`, so that the theorem is
visibly **not vacuous**: its conclusion is here obtained as an unconditional
numerical identity.

NOT a dead branch, and not part of the proof: it is a sanity check on the
statement of the main theorem, imported by nothing.
-/

open Real Complex

noncomputable section

namespace UmlaufTriangleExample

/-- The triangle `0, 1, i`. -/
def T : List ℂ := [0, 1, Complex.I]

lemma T_length : T.length = 3 := rfl

/-- The three vertices of `T` are distinct. -/
lemma T_nodup : T.Nodup := by
  simp [T, List.nodup_cons, Complex.ext_iff]

/-- Any two closed edges of a triangle share an endpoint, so the
non-self-intersection clause of `PolygonSimple` holds vacuously. -/
lemma T_polygonSimple : PolygonSimple T := by
  refine ⟨T_nodup, ?_⟩
  intro e₁ he₁ e₂ he₂ h11 h12 h21 h22
  have hE : closedEdges T = [((0 : ℂ), (1 : ℂ)), ((1 : ℂ), Complex.I), (Complex.I, (0 : ℂ))] := by
    simp [closedEdges, T, List.rotate]
  rw [hE] at he₁ he₂
  fin_cases he₁ <;> fin_cases he₂ <;> simp_all

lemma T_polyNondeg :
    polyNondeg (T ++ [T[0]'(by simp [T_length]), T[1]'(by simp [T_length])]) := by
  show polyNondeg [(0 : ℂ), 1, Complex.I, 0, 1]
  refine ⟨?_, ?_, ?_, trivial⟩ <;>
    simp [HexArea.cross]

/-- **The planar Umlaufsatz, unconditionally, for the triangle `0, 1, i`.**  The
hypotheses of `polygon_umlaufsatz_final` are all satisfied here, so its
conclusion is a genuine, hypothesis-free identity. -/
theorem umlaufsatz_triangle :
    polyWind [(0 : ℂ), 1, Complex.I, 0, 1]
      = 2 * Real.pi * (if 0 < HexArea.shoelace2 [(0 : ℂ), 1, Complex.I] then 1 else -1) :=
  polygon_umlaufsatz_final T (by simp [T_length]) T_polygonSimple T_polyNondeg

end UmlaufTriangleExample

end
