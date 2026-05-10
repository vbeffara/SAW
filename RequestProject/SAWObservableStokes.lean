/-
# Parafermionic Observable — Edge Direction Infrastructure

Infrastructure for the vertex relation and discrete Stokes identity
(Lemma 2 of Duminil-Copin & Smirnov 2012).

## Main results

- `hexEdgeDirC`: direction vector of a hex edge as a complex number
- `hexEdgeDirC_F_T_same`: FALSE→TRUE direction is 1
- `hexEdgeDirC_T_F_same`: TRUE→FALSE direction is -1
- `hexEdgeDirC_sum_zero_false`: directions from FALSE vertex sum to 0
- `hexEdgeDirC_sum_zero_true`: directions from TRUE vertex sum to 0
- `hexEdgeDirC_start`: direction from paperStart to hexOrigin is -1
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-- Direction vector of a hex edge as a complex number.
    Returns the difference of embeddings: embed(w) - embed(v).
    Each hex edge has unit length, so |hexEdgeDirC v w| = 1
    for adjacent v, w. -/
def hexEdgeDirC (v w : HexVertex) : ℂ :=
  correctHexEmbed w - correctHexEmbed v

/-- FALSE(x,y) → TRUE(x,y) has direction 1 (angle 0). -/
lemma hexEdgeDirC_F_T_same (x y : ℤ) :
    hexEdgeDirC (x, y, false) (x, y, true) = 1 := by
  unfold hexEdgeDirC correctHexEmbed; simp only
  apply Complex.ext <;> simp

/-- TRUE(x,y) → FALSE(x,y) has direction -1 (angle π). -/
lemma hexEdgeDirC_T_F_same (x y : ℤ) :
    hexEdgeDirC (x, y, true) (x, y, false) = -1 := by
  unfold hexEdgeDirC correctHexEmbed; simp only
  apply Complex.ext <;> simp

/-- At each FALSE vertex, the three direction vectors sum to zero.
    This is a consequence of the 3-fold rotational symmetry. -/
lemma hexEdgeDirC_sum_zero_false (x y : ℤ) :
    hexEdgeDirC (x, y, false) (x, y, true) +
    hexEdgeDirC (x, y, false) (x + 1, y, true) +
    hexEdgeDirC (x, y, false) (x, y + 1, true) = 0 := by
  unfold hexEdgeDirC correctHexEmbed
  apply Complex.ext <;> simp <;> ring

/-- At each TRUE vertex, the three direction vectors sum to zero. -/
lemma hexEdgeDirC_sum_zero_true (x y : ℤ) :
    hexEdgeDirC (x, y, true) (x, y, false) +
    hexEdgeDirC (x, y, true) (x - 1, y, false) +
    hexEdgeDirC (x, y, true) (x, y - 1, false) = 0 := by
  unfold hexEdgeDirC correctHexEmbed
  apply Complex.ext <;> simp <;> ring

/-- Direction from paperStart to hexOrigin is -1 (leftward). -/
lemma hexEdgeDirC_start : hexEdgeDirC paperStart hexOrigin = -1 := by
  unfold hexEdgeDirC correctHexEmbed paperStart hexOrigin
  apply Complex.ext <;> simp

/-- Direction from hexOrigin to paperStart is 1 (rightward). -/
lemma hexEdgeDirC_start' : hexEdgeDirC hexOrigin paperStart = 1 := by
  unfold hexEdgeDirC correctHexEmbed paperStart hexOrigin
  apply Complex.ext <;> simp

/-- The direction vector is antisymmetric: dir(v,w) = -dir(w,v). -/
lemma hexEdgeDirC_antisymm (v w : HexVertex) :
    hexEdgeDirC v w = -hexEdgeDirC w v := by
  unfold hexEdgeDirC; ring

end
