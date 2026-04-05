/-
# Discrete Stokes Theorem Infrastructure for the Hexagonal Lattice

Infrastructure for proving B_paper ≤ 1 via the parafermionic observable.

## Reference

Section 3 of: Hugo Duminil-Copin and Stanislav Smirnov,
"The connective constant of the honeycomb lattice equals √(2+√2)",
Annals of Mathematics, 175(3), 1653--1665, 2012.
-/

import Mathlib
import RequestProject.SAWObservableProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Direction factors for hex edges -/

/-- Direction from FALSE(x,y) to TRUE(x,y) is (1, 0). -/
lemma hex_dir_false_true_same (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) =
    (1 : ℂ) := by
  unfold correctHexEmbed; simp [Complex.ext_iff]

/-- Direction from TRUE(x,y) to FALSE(x,y) is (-1, 0). -/
lemma hex_dir_true_false_same (x y : ℤ) :
    correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true) =
    (-1 : ℂ) := by
  unfold correctHexEmbed; simp [Complex.ext_iff]

/-! ## Interior cancellation -/

theorem interior_cancellation (u w : HexVertex) :
    (correctHexEmbed w - correctHexEmbed u) +
    (correctHexEmbed u - correctHexEmbed w) = 0 := by
  ring

/-! ## Hex neighbors -/

def falseNeighbors (x y : ℤ) : Fin 3 → HexVertex
  | 0 => (x, y, true)
  | 1 => (x + 1, y, true)
  | 2 => (x, y + 1, true)

def trueNeighbors (x y : ℤ) : Fin 3 → HexVertex
  | 0 => (x, y, false)
  | 1 => (x - 1, y, false)
  | 2 => (x, y - 1, false)

lemma false_adj (x y : ℤ) (i : Fin 3) :
    hexGraph.Adj (x, y, false) (falseNeighbors x y i) := by
  fin_cases i <;> simp [falseNeighbors, hexGraph]

lemma true_adj (x y : ℤ) (i : Fin 3) :
    hexGraph.Adj (x, y, true) (trueNeighbors x y i) := by
  fin_cases i <;> simp [trueNeighbors, hexGraph]

/-! ## Right boundary and starting direction factors -/

lemma right_boundary_dir (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) =
    (1 : ℂ) :=
  hex_dir_false_true_same x y

lemma starting_dir :
    correctHexEmbed (0, 0, false) - correctHexEmbed (0, 0, true) =
    (-1 : ℂ) :=
  hex_dir_true_false_same 0 0

/-- FALSE(0,0) is not in PaperInfStrip T for T ≥ 1. -/
lemma false_00_not_in_strip (T : ℕ) (hT : 1 ≤ T) :
    ¬ PaperInfStrip T (0, 0, false) := by
  unfold PaperInfStrip; simp

end
