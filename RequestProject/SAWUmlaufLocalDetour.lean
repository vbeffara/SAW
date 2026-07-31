import Mathlib
import RequestProject.SAWUmlaufArcBasics
import RequestProject.SAWUmlaufSemicircle

/-!
# Closed local detours for the Umlaufsatz

This file is part of the live finite-detour construction.  It is imported by
`SAWUmlaufDetourConstruction`, whose output is consumed by
`SAWUmlaufArcDetour → SAWUmlaufArcInduction → SAWUmlaufArcEscape →
SAWUmlaufPolygon` and hence by the main Umlaufsatz.

`SAWUmlaufSemicircle` proves the analytic facts about a translated semicircle.
Here they are converted into the two set-avoidance facts needed by the geometric
construction: avoiding a forbidden segment contained in the diameter line, and
avoiding the old tail when the detour lies in a clearance ball.  This is the
local replacement brick which the remaining finite crossing selection must
place between endpoint connectors; it is therefore linked future preparation,
not a dead branch.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- A nondegenerate simple arc has a nondegenerate first edge. -/
lemma PlaneArcSimple.head_ne_of_cons_cons {a b : ℂ} {L : List ℂ}
    (h : PlaneArcSimple (a :: b :: L)) : a ≠ b := by
  intro hab
  subst b
  simpa using h.1

/-- The segment from `a` to `b` lies in the affine line through `a` in
 direction `b-a`. -/
lemma segment_subset_diameterLine (a b : ℂ) :
    segment ℝ a b ⊆ {z : ℂ | ∃ s : ℝ, z = a + s • (b - a)} := by
  intro z hz
  rw [segment_eq_image] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  refine ⟨s, ?_⟩
  module

/-- Any path lying in a ball disjoint from a forbidden set avoids that set. -/
lemma path_avoids_of_mem_ball_of_ball_disjoint
    {p q c : ℂ} (δ : Path p q) {ε : ℝ} (F : Set ℂ)
    (hδ : ∀ t, δ t ∈ Metric.ball c ε)
    (hdisj : Metric.ball c ε ∩ F = ∅) :
    ∀ t, δ t ∉ F := by
  intro t ht
  have : δ t ∈ Metric.ball c ε ∩ F := ⟨hδ t, ht⟩
  rw [hdisj] at this
  exact this

/-- The straight path between two complex points.  This is used for the short
connectors from retained path values to translated semicircular detours. -/
def affinePath (p q : ℂ) : Path p q :=
  ⟨⟨fun t => (1 - (t : ℝ)) • p + (t : ℝ) • q, by continuity⟩, by simp, by simp⟩

@[simp] lemma affinePath_apply (p q : ℂ) (t : unitInterval) :
    affinePath p q t = (1 - (t : ℝ)) • p + (t : ℝ) • q := rfl

/-- The straight connector has image in its closed segment. -/
lemma affinePath_mem_segment (p q : ℂ) (t : unitInterval) :
    affinePath p q t ∈ segment ℝ p q := by
  rw [segment_eq_image]
  exact ⟨t, t.property, rfl⟩

/-- A straight connector whose entire segment lies in a clearance ball avoids
any set disjoint from that ball. -/
lemma affinePath_avoids_of_segment_subset_ball
    (p q c : ℂ) {ε : ℝ} (F : Set ℂ)
    (hseg : segment ℝ p q ⊆ Metric.ball c ε)
    (hclear : Metric.ball c ε ∩ F = ∅) :
    ∀ t, affinePath p q t ∉ F := by
  apply path_avoids_of_mem_ball_of_ball_disjoint (affinePath p q) F
  · exact fun t => hseg (affinePath_mem_segment p q t)
  · exact hclear

/-- In a normed plane, two points of the same open ball are joined by a
straight path staying in that ball. -/
lemma affinePath_mem_ball_of_endpoints
    (p q c : ℂ) {ε : ℝ} (hp : p ∈ Metric.ball c ε)
    (hq : q ∈ Metric.ball c ε) :
    ∀ t, affinePath p q t ∈ Metric.ball c ε := by
  intro t
  exact (convex_ball c ε).segment_subset hp hq (affinePath_mem_segment p q t)

/-- Consequently such a straight connector avoids every set from which the
ball has positive clearance. -/
lemma affinePath_avoids_of_endpoints_mem_ball
    (p q c : ℂ) {ε : ℝ} (F : Set ℂ)
    (hp : p ∈ Metric.ball c ε) (hq : q ∈ Metric.ball c ε)
    (hclear : Metric.ball c ε ∩ F = ∅) :
    ∀ t, affinePath p q t ∉ F := by
  exact path_avoids_of_mem_ball_of_ball_disjoint (affinePath p q) F
    (affinePath_mem_ball_of_endpoints p q c hp hq) hclear

/-- Concatenate two paths while preserving avoidance of a forbidden set. -/
lemma Path.trans_avoids {p q r : ℂ} (α : Path p q) (β : Path q r)
    (F : Set ℂ) (hα : ∀ t, α t ∉ F) (hβ : ∀ t, β t ∉ F) :
    ∀ t, α.trans β t ∉ F := by
  intro t ht
  rw [Path.trans_apply] at ht
  split at ht
  · exact hα _ ht
  · exact hβ _ ht

/-- Attach straight endpoint connectors to a local detour.  This is the
three-piece replacement shape used by each finite crossing block. -/
def connectedDetour {p q l r : ℂ} (δ : Path l r) : Path p q :=
  (affinePath p l).trans (δ.trans (affinePath r q))

/-- The connected detour avoids a set when its two connectors and middle path
do. -/
lemma connectedDetour_avoids {p q l r : ℂ} (δ : Path l r) (F : Set ℂ)
    (hleft : ∀ t, affinePath p l t ∉ F)
    (hmiddle : ∀ t, δ t ∉ F)
    (hright : ∀ t, affinePath r q t ∉ F) :
    ∀ t, connectedDetour (p := p) (q := q) δ t ∉ F := by
  apply Path.trans_avoids (affinePath p l) (δ.trans (affinePath r q)) F hleft
  exact Path.trans_avoids δ (affinePath r q) F hmiddle hright

/-- A translated semicircle avoids every forbidden set contained in its
original diameter line, including at both path endpoints. -/
lemma liftedSemicirclePath_avoids_of_subset_diameterLine
    (c u : ℂ) (S : Set ℂ) {r h : ℝ}
    (hr : 0 ≤ r) (hh : 0 < h) (hu : u ≠ 0)
    (hS : S ⊆ {z : ℂ | ∃ s : ℝ, z = c + s • u}) :
    ∀ t : unitInterval, liftedSemicirclePath c u r h t ∉ S := by
  intro t ht
  exact (liftedSemicirclePoint_not_mem_diameterLine c u hr hh hu
    t.property.1 t.property.2) (hS ht)

/-- Specialization of the preceding local fact to a nondegenerate closed line
segment. -/
lemma liftedSemicirclePath_avoids_segment
    (a b : ℂ) {r h : ℝ} (hr : 0 ≤ r) (hh : 0 < h) (hab : a ≠ b) :
    ∀ t : unitInterval,
      liftedSemicirclePath a (b - a) r h t ∉ segment ℝ a b := by
  exact liftedSemicirclePath_avoids_of_subset_diameterLine
    a (b - a) (segment ℝ a b) hr hh (sub_ne_zero.mpr hab.symm)
    (segment_subset_diameterLine a b)

/-- **Packaged local Umlaufsatz detour.**  A translated semicircle around the
new edge, chosen inside a clearance ball from the old tail, simultaneously
avoids the closed new segment and the entire old tail.  The remaining global
constructor only has to select finitely many such balls and attach endpoint
connectors. -/
lemma liftedSemicirclePath_avoids_segment_and_tail
    (a b : ℂ) (oldTail : Set ℂ) {r h ε : ℝ}
    (hr : 0 ≤ r) (hh : 0 < h) (hrhε : r + h < ε)
    (hab : a ≠ b)
    (hclear : Metric.ball a ε ∩ oldTail = ∅) :
    (∀ t : unitInterval,
      liftedSemicirclePath a (b - a) r h t ∉ segment ℝ a b) ∧
    (∀ t : unitInterval,
      liftedSemicirclePath a (b - a) r h t ∉ oldTail) := by
  have hu : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  obtain ⟨hball, _hline⟩ :=
    liftedSemicirclePath_local_detour a (b - a) hr hh hrhε hu
  exact ⟨liftedSemicirclePath_avoids_segment a b hr hh hab,
    path_avoids_of_mem_ball_of_ball_disjoint
      (liftedSemicirclePath a (b - a) r h) oldTail hball hclear⟩

/-- Every positive clearance radius admits positive translation and
semicircle radii whose sum remains strictly inside the clearance ball. -/
lemma exists_positive_detour_radii {ε : ℝ} (hε : 0 < ε) :
    ∃ r h : ℝ, 0 < r ∧ 0 < h ∧ r + h < ε := by
  refine ⟨ε / 4, ε / 4, by linarith, by linarith, by linarith⟩

/-- The actual local replacement obtained by attaching straight connectors to
a translated semicircle. -/
def connectedLiftedSemicircleDetour
    (p q c u : ℂ) (r h : ℝ) : Path p q :=
  connectedDetour (p := p) (q := q) (liftedSemicirclePath c u r h)

/-- A fully connected translated-semicircle replacement avoids the new edge and
old tail once the two short connector segments have the same avoidance
properties.  This theorem separates the remaining finite geometric selection
problem from all path concatenation bookkeeping. -/
lemma connectedLiftedSemicircleDetour_avoids
    (p q c u : ℂ) (newEdge oldTail : Set ℂ) {r h ε : ℝ}
    (hr : 0 ≤ r) (hh : 0 < h) (hrhε : r + h < ε) (hu : u ≠ 0)
    (hnew : newEdge ⊆ {z : ℂ | ∃ s : ℝ, z = c + s • u})
    (hclear : Metric.ball c ε ∩ oldTail = ∅)
    (hleftNew : ∀ t, affinePath p
      (c + ((r : ℂ) / ‖u‖) * u + ((h : ℂ) / ‖u‖) * Complex.I * u) t ∉ newEdge)
    (hrightNew : ∀ t, affinePath
      (c - ((r : ℂ) / ‖u‖) * u + ((h : ℂ) / ‖u‖) * Complex.I * u) q t ∉ newEdge)
    (hleftTail : ∀ t, affinePath p
      (c + ((r : ℂ) / ‖u‖) * u + ((h : ℂ) / ‖u‖) * Complex.I * u) t ∉ oldTail)
    (hrightTail : ∀ t, affinePath
      (c - ((r : ℂ) / ‖u‖) * u + ((h : ℂ) / ‖u‖) * Complex.I * u) q t ∉ oldTail) :
    (∀ t, connectedLiftedSemicircleDetour p q c u r h t ∉ newEdge) ∧
    (∀ t, connectedLiftedSemicircleDetour p q c u r h t ∉ oldTail) := by
  have hmiddleNew : ∀ t, liftedSemicirclePath c u r h t ∉ newEdge :=
    liftedSemicirclePath_avoids_of_subset_diameterLine c u newEdge hr hh hu hnew
  obtain ⟨hmiddleBall, _⟩ :=
    liftedSemicirclePath_local_detour c u hr hh hrhε hu
  have hmiddleTail : ∀ t, liftedSemicirclePath c u r h t ∉ oldTail :=
    path_avoids_of_mem_ball_of_ball_disjoint
      (liftedSemicirclePath c u r h) oldTail hmiddleBall hclear
  exact ⟨connectedDetour_avoids _ newEdge hleftNew hmiddleNew hrightNew,
    connectedDetour_avoids _ oldTail hleftTail hmiddleTail hrightTail⟩

end HexArea
