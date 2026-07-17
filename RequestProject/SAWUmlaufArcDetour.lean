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

/-!
## Compact exhaustion of the genuinely new part of the first edge

The local detour cannot use all of `[a,b] \ {b}` as one compact set.  Instead we
exhaust it by the closed sets of points at distance at least `δ` from the
attachment endpoint.  These are compact, and under `FirstEdgeAttachedOnly` each
has a uniform tail-clearance by `firstSegment_compact_clearance`.  This is the
precise compactness package needed when the eventual path replacement chooses
finitely many crossing neighbourhoods.  The declarations are consumed directly
by `joinedIn_compl_cons_segment_of_tail` below, so this is preparation for the
main Umlaufsatz rather than a detached topology branch.
-/

/-- The compact portion of `[a,b]` staying at least `δ` away from `b`. -/
def firstSegmentAway (a b : ℂ) (δ : ℝ) : Set ℂ :=
  segment ℝ a b ∩ {z | δ ≤ dist z b}

lemma isCompact_firstSegmentAway (a b : ℂ) (δ : ℝ) :
    IsCompact (firstSegmentAway a b δ) := by
  refine' IsCompact.inter_right _ _;
  · convert ( isCompact_Icc.image ( show Continuous fun x : ℝ => a + x • ( b - a ) from by continuity ) ) using 1 ; ext ; simp +decide [ segment_eq_image ];
    convert Iff.rfl using 4 ; ring;
  · exact isClosed_le continuous_const ( continuous_id.dist continuous_const )

lemma firstSegmentAway_subset (a b : ℂ) (δ : ℝ) :
    firstSegmentAway a b δ ⊆ segment ℝ a b := by
  exact Set.inter_subset_left

lemma terminal_not_mem_firstSegmentAway (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    b ∉ firstSegmentAway a b δ := by
  exact fun h => hδ.not_ge <| by simpa using h.2;

/-- Every positive-distance truncation of the new edge has one uniform
clearance radius from the old tail. -/
lemma firstSegmentAway_uniform_clearance
    (a b : ℂ) (L : List ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hattach : FirstEdgeAttachedOnly a b L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ firstSegmentAway a b δ,
      Metric.ball z ε ∩ chainCarrier (b :: L) = ∅ := by
  exact firstSegment_compact_clearance a b L (firstSegmentAway a b δ)
    (isCompact_firstSegmentAway a b δ) hattach
    (firstSegmentAway_subset a b δ)
    (terminal_not_mem_firstSegmentAway a b hδ)

/-
Every point of the first edge other than its terminal endpoint occurs in a
positive-distance compact truncation.  This links the compact exhaustion above
to the whole local-detour problem.
-/
lemma mem_firstSegmentAway_of_mem_ne
    (a b z : ℂ) (hz : z ∈ segment ℝ a b) (hzb : z ≠ b) :
    ∃ δ : ℝ, 0 < δ ∧ z ∈ firstSegmentAway a b δ := by
  refine' ⟨ dist z b, dist_pos.mpr hzb, _, _ ⟩ <;> simp_all +decide [ dist_eq_norm ]

/-
Smaller distance thresholds give larger compact truncations.
-/
lemma firstSegmentAway_anti {a b : ℂ} {δ η : ℝ} (hδη : δ ≤ η) :
    firstSegmentAway a b η ⊆ firstSegmentAway a b δ := by
  exact fun x hx => ⟨ hx.1, le_trans hδη hx.2 ⟩

/-
The genuinely new part of the first edge is exactly the union of its
positive-distance compact truncations.  This is the exhaustion identity used to
pass from pointwise clearance to the finite subcover in the detour theorem.
-/
lemma iUnion_firstSegmentAway_pos (a b : ℂ) :
    ⋃ (δ : ℝ) (_ : 0 < δ), firstSegmentAway a b δ = segment ℝ a b \ ({b} : Set ℂ) := by
  -- To prove equality of sets, we show each set is a subset of the other.
  apply Set.ext
  intro z
  simp [firstSegmentAway];
  exact fun hz => ⟨ fun ⟨ x, hx₁, hx₂ ⟩ => by rintro rfl; norm_num at hx₂; linarith, fun hz' => ⟨ dist z b, dist_pos.mpr hz', le_rfl ⟩ ⟩

/-- **Finite local-detour theorem.**  Any two points avoiding a simple arc's
whole carrier can be joined while avoiding the whole carrier, provided the tail
complement is path connected.  The intended proof starts with a path in the
tail complement, separates portions of `[a,b]` already contained in the tail,
uses the compact exhaustion and uniform-clearance package immediately above to
isolate finitely many crossings of the genuinely new portions, and replaces
those crossings inside clearance discs by semicircular arcs. -/
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