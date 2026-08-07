/-
# The winding of a configuration, modulo `2π`

Combines the telescoping law `hexWalkWinding_angle_eq` with the normalisation
of `FreshTrail.winding` (measured from the initial mid-edge `a`, whose
direction is `+1`, i.e. angle `0`):

  `freshTrail_winding_angle`:
  `(γ.winding : ℝ/2πℤ) = arg (correctHexEmbed next - correctHexEmbed prev)`.

So the winding of a configuration is completely determined, *modulo* `2π`, by
its final mid-edge.  This is the algebraic half of the geometric input of the
boundary evaluation; the other half is a bound ruling out extra full turns,
which is where the self-avoidance and the simple connectivity of the strip
enter.
-/

import Mathlib
import RequestProject.SAWWindingTelescope
import RequestProject.SAWFreshTrailPath

open Real Complex ComplexConjugate Filter Topology

noncomputable section

lemma correctHexEmbed_hexOrigin : correctHexEmbed hexOrigin = 0 := by
  simp [correctHexEmbed, hexOrigin, Complex.ext_iff]

lemma correctHexEmbed_paperStart' : correctHexEmbed paperStart = 1 := by
  simp [correctHexEmbed, paperStart, Complex.ext_iff]

lemma hexOrigin_ne_paperStart_embed :
    correctHexEmbed hexOrigin ≠ correctHexEmbed paperStart := by
  rw [correctHexEmbed_hexOrigin, correctHexEmbed_paperStart']
  exact zero_ne_one

/-- The vertex list of a configuration, split off its head. -/
lemma freshTrail_fullSupport_cons {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) :
    γ.fullSupport = paperStart :: (γ.walk.support.tail ++ [next]) := by
  conv_lhs => rw [FreshTrail.fullSupport, γ.walk.support_eq_cons]
  rfl

/-- The vertex list of a configuration, with the outside endpoint of the
initial mid-edge prepended, is a chain of distinct embeddings. -/
lemma freshTrail_chain {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) :
    HexDistinctChain (hexOrigin :: γ.fullSupport) := by
  have hsnoc : HexDistinctChain γ.fullSupport := by
    refine HexDistinctChain.snoc γ.walk.support (by simp) next
      (hexDistinctChain_of_walk_support γ.walk) ?_
    rw [γ.walk.getLast_support]
    intro h
    exact hex_embed_sub_ne_zero' prev next γ.adj (by rw [h]; ring)
  rw [freshTrail_fullSupport_cons γ] at hsnoc ⊢
  exact ⟨hexOrigin_ne_paperStart_embed, hsnoc⟩

/-- The direction of the last edge of a configuration. -/
lemma freshTrail_lastDir {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) :
    hexLastDir hexOrigin γ.fullSupport
      = correctHexEmbed next - correctHexEmbed prev := by
  rw [FreshTrail.fullSupport, hexLastDir_snoc,
    List.getLast_cons (l := γ.walk.support) (by simp), γ.walk.getLast_support]

/-- **The winding of a configuration modulo `2π`.**  It equals the direction
angle of its final mid-edge, because the initial mid-edge `a` has direction
angle `0`. -/
theorem freshTrail_winding_angle {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) :
    ((γ.winding : Real.Angle))
      = (Complex.arg (correctHexEmbed next - correctHexEmbed prev) : Real.Angle) := by
  have hchain := freshTrail_chain γ
  have hlast := freshTrail_lastDir γ
  rw [FreshTrail.winding, freshTrail_fullSupport_cons γ] at *
  rw [hexWalkWinding_angle_eq hexOrigin paperStart _ hchain, hlast,
    correctHexEmbed_hexOrigin, correctHexEmbed_paperStart']
  simp

end
