import Mathlib

/-!
# Unbounded exterior points for finite polygonal data

This file isolates the boundedness fact used by the exterior-path branch of the
planar Umlaufsatz.  A polygon has finitely many vertices, hence its convex hull
is bounded; consequently there are points outside that hull, arbitrarily far
from any prescribed centre.

This is not a dead branch: `RequestProject.SAWUmlaufPolygon` imports this file
and uses `exists_not_mem_convexHull_finset` when reducing the remaining
Jordan-connectivity statement `vertex_escape_joinedIn` to connectivity toward a
fixed exterior endpoint.
-/

open Real Complex

noncomputable section

namespace HexArea

/-
The convex hull of a finite set in a nontrivial real normed space does not
contain every point.
-/
lemma exists_not_mem_convexHull_finset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (s : Finset E) :
    ∃ q : E, q ∉ convexHull ℝ (s : Set E) := by
  -- By definition of convex hull, if the convex hull of s were equal to E, then E would be bounded.
  by_contra h_contra
  have h_bounded : Bornology.IsBounded (Set.univ : Set E) := by
    -- By definition of convex hull, if the convex hull of s were equal to E, then E would be bounded. This follows from the fact that a finite set in a normed space is bounded.
    have h_bounded : Bornology.IsBounded (convexHull ℝ (s : Set E)) := by
      exact ( isBounded_convexHull.mpr <| s.finite_toSet.isBounded );
    simpa [ show ( convexHull ℝ ( s : Set E ) ) = Set.univ from Set.eq_univ_of_forall fun x => by aesop ] using h_bounded;
  rcases h_bounded.exists_pos_norm_le with ⟨ M, hM_pos, hM ⟩;
  obtain ⟨ x, hx ⟩ := exists_ne ( 0 : E );
  -- Choose a scalar $t$ such that $t \|x\| > M$.
  obtain ⟨ t, ht ⟩ : ∃ t : ℝ, t > 0 ∧ t * ‖x‖ > M := by
    exact ⟨ ( M + 1 ) / ‖x‖, div_pos ( add_pos hM_pos zero_lt_one ) ( norm_pos_iff.mpr hx ), by rw [ div_mul_cancel₀ _ ( norm_ne_zero_iff.mpr hx ) ] ; linarith ⟩;
  exact not_le_of_gt ht.2 ( by simpa [ norm_smul, abs_of_pos ht.1 ] using hM ( t • x ) trivial )

/-
Exterior points can be chosen with arbitrarily large norm.  This is the
quantitative endpoint form needed when an avoiding path is routed through a
large circle surrounding all polygon edges.
-/
lemma exists_not_mem_convexHull_finset_norm_gt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (s : Finset E) (R : ℝ) :
    ∃ q : E, q ∉ convexHull ℝ (s : Set E) ∧ R < ‖q‖ := by
  -- The convex hull of the finite set is bounded.
  have h_bounded : Bornology.IsBounded (convexHull ℝ (s : Set E)) := by
    simp +zetaDelta at *;
    exact s.finite_toSet.isBounded;
  obtain ⟨ M, hM ⟩ := h_bounded.exists_pos_norm_le;
  obtain ⟨ q, hq ⟩ := exists_ne ( 0 : E );
  -- Choose $t$ such that $t \|q\| > \max(M, R)$.
  obtain ⟨ t, ht ⟩ : ∃ t : ℝ, t > 0 ∧ t * ‖q‖ > max M R := by
    exact ⟨ ( Max.max M R + 1 ) / ‖q‖, div_pos ( by linarith [ le_max_left M R, le_max_right M R ] ) ( norm_pos_iff.mpr hq ), by rw [ div_mul_cancel₀ _ ( norm_ne_zero_iff.mpr hq ) ] ; linarith ⟩;
  refine' ⟨ t • q, _, _ ⟩ <;> simp_all +decide [ norm_smul, abs_of_pos ];
  exact fun h => by have := hM.2 _ h; rw [ norm_smul, Real.norm_of_nonneg ht.1.le ] at this; linarith;

/-- List-specialized form used by polygon exteriors. -/
lemma exists_not_mem_convexHull_list
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [DecidableEq E] (L : List E) :
    ∃ q : E, q ∉ convexHull ℝ (L.toFinset : Set E) := by
  exact exists_not_mem_convexHull_finset L.toFinset

/-- Quantitative list-specialized exterior endpoint. -/
lemma exists_not_mem_convexHull_list_norm_gt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [DecidableEq E] (L : List E) (R : ℝ) :
    ∃ q : E, q ∉ convexHull ℝ (L.toFinset : Set E) ∧ R < ‖q‖ := by
  exact exists_not_mem_convexHull_finset_norm_gt L.toFinset R

/-
Every finite union of line segments is contained in a norm ball.  This is
used to choose the large-circle part of an exterior avoiding path in the
Umlaufsatz Jordan core.
-/
lemma exists_norm_bound_segments (S : List (ℂ × ℂ)) :
    ∃ R : ℝ, 0 < R ∧ ∀ s ∈ S, ∀ z ∈ segment ℝ s.1 s.2, ‖z‖ < R := by
  -- By the properties of the union of line segments, we can find such an R.
  have h_union : ∀ s : ℂ × ℂ, ∃ R > 0, ∀ z ∈ segment ℝ s.1 s.2, ‖z‖ < R := by
    intro s
    obtain ⟨R, hR⟩ : ∃ R > 0, ∀ z ∈ segment ℝ s.1 s.2, ‖z‖ ≤ R := by
      exact ⟨ ‖s.1‖ + ‖s.2‖ + 1, by positivity, fun z hz => by rcases hz with ⟨ a, b, ha, hb, hab, rfl ⟩ ; exact le_trans ( norm_add_le _ _ ) ( by rw [ norm_smul, norm_smul ] ; exact by rw [ Real.norm_of_nonneg ha, Real.norm_of_nonneg hb ] ; nlinarith [ norm_nonneg s.1, norm_nonneg s.2 ] ) ⟩;
    exact ⟨ R + 1, by linarith, fun z hz => by linarith [ hR.2 z hz ] ⟩;
  choose! R hR using h_union;
  exact ⟨ Max.max ( ∑ s ∈ S.toFinset, R s ) 1, by positivity, fun s hs z hz => lt_of_lt_of_le ( hR s |>.2 z hz ) ( le_max_of_le_left <| Finset.single_le_sum ( fun x _ => le_of_lt <| hR x |>.1 ) <| List.mem_toFinset.mpr hs ) ⟩

/-- A point beyond a strict norm bound cannot lie on any segment satisfying
that bound. -/
lemma not_mem_segment_of_norm_bound {s : ℂ × ℂ} {R : ℝ} {q : ℂ}
    (hseg : ∀ z ∈ segment ℝ s.1 s.2, ‖z‖ < R) (hq : R < ‖q‖) :
    q ∉ segment ℝ s.1 s.2 := by
  intro hmem
  exact (not_lt_of_ge hq.le) (hseg q hmem)

/-
A point beyond a common strict norm bound belongs to the complement of the
union of all segments in the finite family.
-/
lemma mem_compl_iUnion_segments_of_norm_gt (S : List (ℂ × ℂ)) (R : ℝ) (q : ℂ)
    (hS : ∀ s ∈ S, ∀ z ∈ segment ℝ s.1 s.2, ‖z‖ < R) (hq : R < ‖q‖) :
    q ∈ (⋃ s ∈ S, segment ℝ s.1 s.2)ᶜ := by
  simp +zetaDelta at *;
  exact fun a b hab hq' => not_lt_of_ge ( le_of_lt hq ) ( hS a b hab q hq' )

/-
A real line segment in `ℂ` is closed, via its compact
parametrization by the interval `[0,1]`.
-/
lemma isClosed_complex_segment (a b : ℂ) : IsClosed (segment ℝ a b) := by
  convert ( isCompact_Icc.image ( show Continuous fun x : ℝ => ( 1 - x ) • a + x • b from by fun_prop ) ) |> IsCompact.isClosed using 1;
  convert segment_eq_image ℝ a b

/-
The complement of a finite list-union of complex line segments is open.
This is the local-topology premise needed to turn connected components into
path components in the remaining Jordan step.
-/
lemma isOpen_compl_iUnion_segments (S : List (ℂ × ℂ)) :
    IsOpen ((⋃ s ∈ S, segment ℝ s.1 s.2)ᶜ) := by
  induction S <;> simp_all +decide [ not_or, not_and, IsClosed, Set.compl_def ];
  rename_i h₁ h₂ h₃;
  convert h₃.inter ( isOpen_compl_iff.mpr ( isClosed_complex_segment h₁.1 h₁.2 ) ) using 1 ; aesop

/-
The exterior of a positive-radius closed ball in the complex plane is
path connected.  This provides the large-circle routing region used after a
local polygon-boundary escape reaches beyond all forbidden segments.
-/
lemma isPathConnected_norm_gt (R : ℝ) (hR : 0 < R) :
    IsPathConnected {z : ℂ | R < ‖z‖} := by
  -- The set {z : ℂ | R < ‖z‖} is the complement of the closed ball of radius R centered at the origin.
  set D := Metric.closedBall (0 : ℂ) R with hD;
  -- The complement of a closed disk in the complex plane is path-connected.
  have h_compl_path_connected : IsPathConnected (Dᶜ) := by
    have h_compl : Dᶜ = Set.image (fun (p : ℝ × ℝ) => p.1 * Complex.exp (p.2 * Complex.I)) {p : ℝ × ℝ | p.1 > R} := by
      ext; simp [D];
      constructor;
      · intro hx;
        exact ⟨ ‖‹ℂ›‖, hx, Complex.arg ‹ℂ›, by simp +decide [ Complex.norm_mul_exp_arg_mul_I ] ⟩;
      · rintro ⟨ a, ha, b, rfl ⟩ ; simp +decide [ Complex.norm_exp, abs_of_pos ( lt_trans hR ha ) ] ; linarith
    rw [ h_compl ];
    apply_rules [ IsPathConnected.image, isConnected_iff_connectedSpace.mp ];
    · -- The set {p : ℝ × ℝ | p.1 > R} is convex, hence path-connected.
      have h_convex : Convex ℝ {p : ℝ × ℝ | p.1 > R} := by
        exact convex_iff_forall_pos.mpr fun x hx y hy a b ha hb hab => by norm_num at *; nlinarith;
      exact h_convex.isPathConnected ⟨ ⟨ R + 1, 0 ⟩, by norm_num ⟩;
    · fun_prop;
  convert h_compl_path_connected using 1 ; ext ; aesop

/-- Any two points beyond a positive norm radius can be joined while remaining
beyond that radius. -/
lemma joinedIn_norm_gt (R : ℝ) (hR : 0 < R) {p q : ℂ}
    (hp : R < ‖p‖) (hq : R < ‖q‖) :
    JoinedIn {z : ℂ | R < ‖z‖} p q := by
  exact (isPathConnected_norm_gt R hR).joinedIn p hp q hq

/-
Simultaneously choose an endpoint outside a finite convex hull and a circle
strictly surrounding every segment in a prescribed finite family.  This is the
precise elementary endpoint package consumed by the fixed-endpoint Jordan
routing step of the Umlaufsatz.
-/
lemma exists_exterior_point_beyond_segments (V : List ℂ) (S : List (ℂ × ℂ)) :
    ∃ (R : ℝ) (q : ℂ), 0 < R ∧
      q ∉ convexHull ℝ (V.toFinset : Set ℂ) ∧ R < ‖q‖ ∧
      ∀ s ∈ S, ∀ z ∈ segment ℝ s.1 s.2, ‖z‖ < R := by
  obtain ⟨ R, hR₁, hR₂ ⟩ := exists_norm_bound_segments S;
  obtain ⟨ q, hq₁, hq₂ ⟩ := exists_not_mem_convexHull_list_norm_gt V R;
  exact ⟨ R, q, hR₁, hq₁, hq₂, hR₂ ⟩

end HexArea