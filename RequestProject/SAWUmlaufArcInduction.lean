import Mathlib
import RequestProject.SAWUmlaufArcBasics
import RequestProject.SAWUmlaufArcDetour

/-!
# Polygonal-arc non-separation: induction interface

This is the live planar-topology leaf used by the Umlaufsatz proof.  The list
induction is complete here and delegates its sole geometric step to
`SAWUmlaufArcDetour`, where the remaining local-detour theorem is retained as an
honest partial theorem.  This separation lets later rounds refine the detour
construction without disturbing the polygon/ear development.

The induction removes the first segment of a simple arc.  By
`PlaneArcSimple.tail`, the remaining chain is simple.  A path in its complement
can meet the removed segment only in a compact parameter set; each genuinely
new crossing is replaced by a small semicircular detour.  Portions overlapping
an adjacent collinear tail edge require no detour because they are already part
of the tail carrier.
-/

open Real Complex

noncomputable section

namespace HexArea

/-- The local extension step needed for induction on a simple polygonal arc.
If the tail carrier does not separate the plane, adjoining the first segment of
a simple arc still does not separate it.  This is the precise finite detour
lemma: its hypotheses retain the complete simplicity information of the longer
chain, not merely endpoint incidence. -/
lemma pathConnected_compl_cons_segment
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    (htail : IsPathConnected (chainCarrier (b :: L))ᶜ) :
    IsPathConnected (chainCarrier (a :: b :: L))ᶜ := by
  exact pathConnected_compl_cons_segment_of_detours a b L hsimple htail

/-- A simple finite polygonal arc does not separate the complex plane.

This is the exact topological theorem consumed by `SAWUmlaufArcEscape`.  The
proof skeleton is now an explicit list induction: the empty and singleton
chains have empty carrier, while the nontrivial step is isolated as
`pathConnected_compl_cons_segment`. -/
lemma simpleArc_complement_isPathConnected_inductive (L : List ℂ)
    (hsimple : PlaneArcSimple L) : IsPathConnected (chainCarrier L)ᶜ := by
  induction L with
  | nil =>
      simpa [chainCarrier] using (isPathConnected_univ : IsPathConnected (Set.univ : Set ℂ))
  | cons a L ih =>
      cases L with
      | nil =>
          simpa [chainCarrier] using (isPathConnected_univ : IsPathConnected (Set.univ : Set ℂ))
      | cons b L =>
          apply pathConnected_compl_cons_segment a b L hsimple
          exact ih hsimple.tail

end HexArea
