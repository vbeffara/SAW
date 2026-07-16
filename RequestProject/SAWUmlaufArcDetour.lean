import Mathlib
import RequestProject.SAWUmlaufArcBasics

/-!
# Local detours for simple polygonal arcs

This file records the geometric construction needed by the live polygonal
Umlaufsatz branch.  It is imported by `SAWUmlaufArcInduction`, which is imported
by `SAWUmlaufArcEscape`, and hence by `SAWUmlaufPolygon`; none of the declarations
below is a detached branch.

A subtlety exposed while formalizing the detour is that `PlaneArcSimple` only
controls nonincident edges.  It deliberately permits a collinear backtracking
pair such as `[0,2,1]`, whose adjacent segments overlap beyond their common
endpoint.  Therefore the tempting assertion that the first segment intersects
the tail carrier only at the attachment endpoint is false under
`PlaneArcSimple` alone.  We do not retain that false assertion as a theorem.
Instead `FirstEdgeAttachedOnly` names the stronger local condition, and the
clearance lemma below states exactly where it is needed.  The final detour
statement remains at the correct, more general `PlaneArcSimple` level: overlap
is harmless because adjoining a subsegment already in the tail changes no
complement, while the genuinely new portions are handled by local detours.

The construction is split into reusable layers rather than hidden in the final
arc non-separation theorem:

1. a compact tail has positive clearance from each compact portion of a new
   edge whose closure avoids the tail;
2. paths in the tail complement can be replaced by paths avoiding the new edge;
3. the replacement gives path connectedness after adjoining that edge.

The second item is the substantive planar detour argument.  It is retained as
an honest partial theorem so later rounds can refine the finite collection of
semicircular detours without changing the downstream Umlaufsatz interfaces.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- The first edge of an arc is attached to the tail carrier only at its terminal
endpoint.  This is stronger than `PlaneArcSimple`: adjacent collinear edges may
overlap under the latter predicate. -/
def FirstEdgeAttachedOnly (a b : ℂ) (L : List ℂ) : Prop :=
  segment ℝ a b ∩ chainCarrier (b :: L) ⊆ ({b} : Set ℂ)

/-- A compact subset of the first edge which avoids the attachment endpoint is
disjoint from the tail, under the precise attachment-only hypothesis.  This is
the set-theoretic input to the positive-distance construction. -/
lemma compact_firstSegment_disjoint_tail
    (a b : ℂ) (L : List ℂ) (C : Set ℂ)
    (hattach : FirstEdgeAttachedOnly a b L)
    (hCsub : C ⊆ segment ℝ a b) (hbC : b ∉ C) :
    Disjoint C (chainCarrier (b :: L)) := by
  rw [Set.disjoint_left]
  intro z hzC hzTail
  have hzb : z = b := by
    have : z ∈ ({b} : Set ℂ) := hattach ⟨hCsub hzC, hzTail⟩
    simpa using this
  exact hbC (hzb ▸ hzC)

/-
A closed compact portion of the first segment bounded away from the tail
has positive metric clearance from the tail carrier.  This is the compactness
layer of the local detour construction.
-/
lemma firstSegment_compact_clearance
    (a b : ℂ) (L : List ℂ)
    (C : Set ℂ) (hCcompact : IsCompact C)
    (hattach : FirstEdgeAttachedOnly a b L)
    (hCsub : C ⊆ segment ℝ a b) (hbC : b ∉ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ C,
      Metric.ball z ε ∩ chainCarrier (b :: L) = ∅ := by
  have := @Metric.exists_pos_forall_lt_edist;
  specialize this hCcompact ( isClosed_chainCarrier ( b :: L ) ) ( compact_firstSegment_disjoint_tail a b L C hattach hCsub hbC );
  obtain ⟨ ε, hε₁, hε₂ ⟩ := this; use ε; simp_all +decide [ Set.ext_iff, edist_dist ] ;
  exact fun z hz x hx₁ hx₂ => not_lt_of_ge ( le_of_lt ( hε₂ z hz x hx₂ ) ) ( by simpa [ dist_comm, nndist_comm ] using hx₁ )

/-- **Finite local-detour theorem.**  Any two points avoiding a simple arc's
whole carrier can be joined while avoiding the whole carrier, provided the tail
complement is path connected.  The intended proof starts with a path in the
tail complement, separates portions of `[a,b]` already contained in the tail,
uses compactness of the parameter interval to isolate finitely many crossings
of the remaining portions, and replaces those crossings inside clearance discs
by semicircular arcs. -/
lemma joinedIn_compl_cons_segment_of_tail
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    (htail : IsPathConnected (chainCarrier (b :: L))ᶜ)
    (x y : ℂ) (hx : x ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hy : y ∈ (chainCarrier (a :: b :: L))ᶜ) :
    JoinedIn (chainCarrier (a :: b :: L))ᶜ x y := by
  sorry

/-- Adjoining the first edge of a simple polygonal arc preserves path
connectedness of the complement.  This packages the local-detour theorem in the
exact form consumed by the list induction in `SAWUmlaufArcInduction`. -/
lemma pathConnected_compl_cons_segment_of_detours
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    (htail : IsPathConnected (chainCarrier (b :: L))ᶜ) :
    IsPathConnected (chainCarrier (a :: b :: L))ᶜ := by
  obtain ⟨R, _hRpos, hR⟩ :=
    HexArea.exists_norm_bound_segments (chainEdges (a :: b :: L))
  let x : ℂ := (R + 1 : ℝ)
  have hx : x ∈ (chainCarrier (a :: b :: L))ᶜ := by
    simpa [chainCarrier] using
      (HexArea.mem_compl_iUnion_segments_of_norm_gt
        (chainEdges (a :: b :: L)) R x hR (by
          change R < ‖((R + 1 : ℝ) : ℂ)‖
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
          linarith))
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact joinedIn_compl_cons_segment_of_tail a b L hsimple htail x y hx hy

end HexArea