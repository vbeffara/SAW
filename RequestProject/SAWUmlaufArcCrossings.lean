import Mathlib
import RequestProject.SAWUmlaufArcBasics

/-!
# Compact crossing data for the polygonal-arc detour

This file is on the live Umlaufsatz proof path: it is imported by
`SAWUmlaufArcDetour`, whose finite crossing-replacement theorem feeds
`SAWUmlaufArcInduction → SAWUmlaufArcEscape → SAWUmlaufPolygon` and hence the
main Umlaufsatz.

The remaining local planar construction starts from a path in the complement
of the old tail and modifies it near the times at which it meets the newly
adjoined first segment.  The declarations below put that argument into its
natural compact form.  In particular, the path image and the crossing-time set
are compact, and the entire path has one positive metric clearance from the
closed old tail.  Thus the future local replacements may be selected by a
finite subcover while remaining uniformly disjoint from the tail.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- The image of a path, written as a set so it can be used in compactness and
separation arguments. -/
def pathCarrier {x y : ℂ} (γ : Path x y) : Set ℂ := Set.range γ

/-- The parameter times at which a path meets a set. -/
def pathHitTimes {x y : ℂ} (γ : Path x y) (S : Set ℂ) : Set unitInterval :=
  γ ⁻¹' S

lemma isCompact_pathCarrier {x y : ℂ} (γ : Path x y) :
    IsCompact (pathCarrier γ) := by
  exact isCompact_range γ.continuous

/-
A complex line segment is compact.  This local compatibility lemma avoids
reopening the interval parametrization at every crossing-set use.
-/
lemma isCompact_complex_segment (a b : ℂ) : IsCompact (segment ℝ a b) := by
  rw [ segment_eq_image ];
  exact CompactIccSpace.isCompact_Icc.image ( by continuity )

/-
The times at which a path crosses one fixed segment form a compact subset
of the compact parameter interval.
-/
lemma isCompact_pathHitTimes_segment {x y : ℂ} (γ : Path x y) (a b : ℂ) :
    IsCompact (pathHitTimes γ (segment ℝ a b)) := by
  convert ( isCompact_univ.inter_right _ ) using 1;
  any_goals exact { x : unitInterval | γ x ∈ segment ℝ a b };
  · grind +qlia;
  · exact isCompact_iff_compactSpace.mp CompactIccSpace.isCompact_Icc;
  · convert isClosed_complex_segment a b |> IsClosed.preimage γ.continuous using 1

/-
If a path lies in the complement of a set, its carrier is disjoint from
that set.
-/
lemma pathCarrier_disjoint_of_mapsTo_compl
    {x y : ℂ} (γ : Path x y) (S : Set ℂ)
    (hγ : ∀ t, γ t ∈ Sᶜ) : Disjoint (pathCarrier γ) S := by
  exact Set.disjoint_left.mpr fun x hx => by obtain ⟨ t, rfl ⟩ := hx; exact hγ t;

/-
**Uniform path-to-tail clearance.**  A path in the complement of a closed
polygonal tail stays a single positive distance from that tail.  This is the
metric input for all the small crossing detours: every replacement made inside
an `ε`-ball about the old path automatically avoids the tail.
-/
lemma path_uniform_clearance_from_tail
    {x y : ℂ} (γ : Path x y) (L : List ℂ)
    (hγ : ∀ t, γ t ∈ (chainCarrier L)ᶜ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t,
      Metric.ball (γ t) ε ∩ chainCarrier L = ∅ := by
  obtain ⟨ ε, hε ⟩ := Metric.exists_pos_forall_lt_edist
    (isCompact_pathCarrier γ) (isClosed_chainCarrier L)
    (pathCarrier_disjoint_of_mapsTo_compl γ (chainCarrier L) hγ);
  refine' ⟨ ε, mod_cast hε.1, fun t => Set.eq_empty_iff_forall_notMem.mpr _ ⟩ ; intro z hz ; contrapose! hε ; simp_all +decide [ edist_dist ];
  exact fun _ => ⟨ γ t, Set.mem_range_self _, z, hz.2, by simpa [ nndist_comm ] using hz.1.le ⟩

/-
The crossing points themselves form a compact subset of the new segment.
Together with `isCompact_pathHitTimes_segment`, this supports either a
parameter-space or image-space finite-subcover implementation of the eventual
semicircular replacement.
-/
lemma isCompact_pathCrossingPoints
    {x y : ℂ} (γ : Path x y) (a b : ℂ) :
    IsCompact (pathCarrier γ ∩ segment ℝ a b) := by
  convert (isCompact_pathCarrier γ).inter_right (isClosed_complex_segment a b) using 1

/-
**Finite crossing neighbourhoods.**  At any prescribed positive scale, a
finite set of crossing times supplies balls whose path-preimages cover every
crossing time.  Later detour work can refine this finite cover (for example by
Lebesgue-number subdivision) without again invoking compactness.
-/
lemma exists_finite_crossing_ball_cover
    {x y : ℂ} (γ : Path x y) (a b : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset unitInterval,
      pathHitTimes γ (segment ℝ a b) ⊆
        ⋃ t ∈ T, γ ⁻¹' Metric.ball (γ t) ε := by
  have h_compact : IsCompact (pathHitTimes γ (segment ℝ a b)) := by
    convert isCompact_pathHitTimes_segment γ a b;
  have h_finite_subcover : ∀ {S : Set unitInterval}, IsCompact S → ∀ ε > 0, ∃ T : Finset unitInterval, S ⊆ ⋃ t ∈ T, Metric.ball t ε := by
    intro S hS ε hε;
    have := hS.elim_nhds_subcover ( fun t => Metric.ball t ε ) fun t ht => Metric.ball_mem_nhds t hε; aesop;
  have h_uniform_cont : UniformContinuous (γ : unitInterval → ℂ) := by
    exact CompactSpace.uniformContinuous_of_continuous γ.continuous;
  rcases Metric.uniformContinuous_iff.mp h_uniform_cont ε hε with ⟨ δ, hδ, hδε ⟩;
  exact Exists.elim ( h_finite_subcover h_compact δ hδ ) fun T hT => ⟨ T, fun t ht => by rcases Set.mem_iUnion₂.mp ( hT ht ) with ⟨ u, hu, hu' ⟩ ; exact Set.mem_iUnion₂.mpr ⟨ u, hu, hδε hu' ⟩ ⟩

end HexArea