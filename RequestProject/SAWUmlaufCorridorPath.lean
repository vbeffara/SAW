import Mathlib
import RequestProject.SAWUmlaufEdgeCoords

/-!
# The detour corridor around the new edge is connected off the edge

This file is preparation for `SAWUmlaufCorridorSelect`, which closes the last
geometric residue of the Umlaufsatz finite-detour construction; it is therefore
on the live route to the main theorem and not a dead branch.

In the edge coordinates of `SAWUmlaufEdgeCoords` the corridor is the open
rectangle `-η < α < s₁`, `|β| < η`, while the new edge is the coordinate
segment `β = 0`, `0 ≤ α ≤ 1`.  Removing the edge from the rectangle leaves a
path-connected set: the rectangle overhangs the free endpoint `a` on the left
(`α < 0`), so the two half-corridors `β > 0` and `β < 0` are joined around `a`.

The connection is realized by an explicit three-leg polyline, so no abstract
connectivity theory is needed.  Every leg is a straight `affinePath`, and the
corridor is convex, hence each leg stays inside it.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- Any pointwise property shared by two paths is shared by their
concatenation. -/
lemma Path.trans_forall {p q r : ℂ} (α : Path p q) (β : Path q r) (P : ℂ → Prop)
    (hα : ∀ t, P (α t)) (hβ : ∀ t, P (β t)) : ∀ t, P ((α.trans β) t) := by
  intro t
  rw [Path.trans_apply]
  split_ifs with h
  · exact hα _
  · exact hβ _

/-- Straight connectors stay in the (convex) corridor. -/
lemma affinePath_mem_corridorSet (a u : ℂ) (s₁ η : ℝ) (p q : ℂ)
    (hp : p ∈ corridorSet a u s₁ η) (hq : q ∈ corridorSet a u s₁ η) :
    ∀ t, affinePath p q t ∈ corridorSet a u s₁ η := fun t =>
  (convex_corridorSet a u s₁ η).segment_subset hp hq (affinePath_mem_segment p q t)

/-- A connector between two points strictly above the edge line avoids the
edge. -/
lemma affinePath_avoid_segment_of_edgeNormal_pos (a u p q : ℂ) (hu : u ≠ 0)
    (hp : 0 < edgeNormal a u p) (hq : 0 < edgeNormal a u q) :
    ∀ t, affinePath p q t ∉ segment ℝ a (a + u) := by
  intro t ht
  rw [mem_segment_iff_edgeCoords a u _ hu] at ht
  rw [edgeNormal_affinePath] at ht
  have h0 : (0 : ℝ) ≤ 1 - (t : ℝ) := by linarith [t.prop.2]
  have h1 : (0 : ℝ) ≤ (t : ℝ) := t.prop.1
  have := real_convex_lt_comb (r := 1 - (t : ℝ)) (s := (t : ℝ)) h0 h1 (by ring) hp hq
  linarith [ht.1]

/-- A connector between two points strictly below the edge line avoids the
edge. -/
lemma affinePath_avoid_segment_of_edgeNormal_neg (a u p q : ℂ) (hu : u ≠ 0)
    (hp : edgeNormal a u p < 0) (hq : edgeNormal a u q < 0) :
    ∀ t, affinePath p q t ∉ segment ℝ a (a + u) := by
  intro t ht
  rw [mem_segment_iff_edgeCoords a u _ hu] at ht
  rw [edgeNormal_affinePath] at ht
  have h0 : (0 : ℝ) ≤ 1 - (t : ℝ) := by linarith [t.prop.2]
  have h1 : (0 : ℝ) ≤ (t : ℝ) := t.prop.1
  have := real_convex_comb_lt (r := 1 - (t : ℝ)) (s := (t : ℝ)) h0 h1 (by ring) hp hq
  linarith [ht.1]

/-- A connector beyond the free endpoint `a` avoids the edge. -/
lemma affinePath_avoid_segment_of_edgeParam_neg (a u p q : ℂ) (hu : u ≠ 0)
    (hp : edgeParam a u p < 0) (hq : edgeParam a u q < 0) :
    ∀ t, affinePath p q t ∉ segment ℝ a (a + u) := by
  intro t ht
  rw [mem_segment_iff_edgeCoords a u _ hu] at ht
  rw [edgeParam_affinePath] at ht
  have h0 : (0 : ℝ) ≤ 1 - (t : ℝ) := by linarith [t.prop.2]
  have h1 : (0 : ℝ) ≤ (t : ℝ) := t.prop.1
  have := real_convex_comb_lt (r := 1 - (t : ℝ)) (s := (t : ℝ)) h0 h1 (by ring) hp hq
  linarith [ht.2.1]

/-- A connector beyond the far endpoint `a + u` avoids the edge. -/
lemma affinePath_avoid_segment_of_edgeParam_gt_one (a u p q : ℂ) (hu : u ≠ 0)
    (hp : 1 < edgeParam a u p) (hq : 1 < edgeParam a u q) :
    ∀ t, affinePath p q t ∉ segment ℝ a (a + u) := by
  intro t ht
  rw [mem_segment_iff_edgeCoords a u _ hu] at ht
  rw [edgeParam_affinePath] at ht
  have h0 : (0 : ℝ) ≤ 1 - (t : ℝ) := by linarith [t.prop.2]
  have h1 : (0 : ℝ) ≤ (t : ℝ) := t.prop.1
  have := real_convex_lt_comb (r := 1 - (t : ℝ)) (s := (t : ℝ)) h0 h1 (by ring) hp hq
  linarith [ht.2.2]

/-- The base point of the corridor, sitting beyond the free endpoint `a`. -/
def corridorBase (a u : ℂ) (η : ℝ) : ℂ := edgePt a u (-η / 2) 0

lemma edgeParam_corridorBase (a u : ℂ) (hu : u ≠ 0) (η : ℝ) :
    edgeParam a u (corridorBase a u η) = -η / 2 := by
  simp [corridorBase, edgeParam_edgePt a u hu]

lemma edgeNormal_corridorBase (a u : ℂ) (hu : u ≠ 0) (η : ℝ) :
    edgeNormal a u (corridorBase a u η) = 0 := by
  simp [corridorBase, edgeNormal_edgePt a u hu]

lemma corridorBase_mem (a u : ℂ) (hu : u ≠ 0) {s₁ η : ℝ} (hη : 0 < η)
    (hs₁ : 0 < s₁) : corridorBase a u η ∈ corridorSet a u s₁ η := by
  refine ⟨?_, ?_, ?_⟩
  · rw [edgeParam_corridorBase a u hu]; linarith
  · rw [edgeParam_corridorBase a u hu]; linarith
  · rw [edgeNormal_corridorBase a u hu]; simpa using hη

/-- **Connectivity core.**  Every point of the corridor off the new edge is
joined to the corridor base by a polyline staying in the corridor and off the
edge. -/
lemma exists_path_to_corridorBase (a u : ℂ) (hu : u ≠ 0) (s₁ η : ℝ)
    (hη : 0 < η) (hs₁ : 0 < s₁) (p : ℂ)
    (hp : p ∈ corridorSet a u s₁ η) (hpseg : p ∉ segment ℝ a (a + u)) :
    ∃ δ : Path p (corridorBase a u η),
      (∀ t, δ t ∈ corridorSet a u s₁ η) ∧
        (∀ t, δ t ∉ segment ℝ a (a + u)) := by
  set α := edgeParam a u p with hα
  set β := edgeNormal a u p with hβ
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hpmem : p ∈ corridorSet a u s₁ η := ⟨hp1, hp2, hp3⟩
  -- the two auxiliary corner points, on whichever side is used
  have hbase : corridorBase a u η ∈ corridorSet a u s₁ η :=
    corridorBase_mem a u hu hη hs₁
  have hbaseParam : edgeParam a u (corridorBase a u η) = -η / 2 :=
    edgeParam_corridorBase a u hu η
  have hbaseNormal : edgeNormal a u (corridorBase a u η) = 0 :=
    edgeNormal_corridorBase a u hu η
  -- Build the generic "go up (or down), go left, come back to the axis" route.
  have route : ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (∀ t, affinePath p (edgePt a u α (σ * (η / 2))) t ∉ segment ℝ a (a + u)) →
      ∃ δ : Path p (corridorBase a u η),
        (∀ t, δ t ∈ corridorSet a u s₁ η) ∧
          (∀ t, δ t ∉ segment ℝ a (a + u)) := by
    intro σ hσ hleg1
    set m₁ := edgePt a u α (σ * (η / 2)) with hm₁
    set m₂ := edgePt a u (-η / 2) (σ * (η / 2)) with hm₂
    have hm₁param : edgeParam a u m₁ = α := by simp [hm₁, edgeParam_edgePt a u hu]
    have hm₁normal : edgeNormal a u m₁ = σ * (η / 2) := by
      simp [hm₁, edgeNormal_edgePt a u hu]
    have hm₂param : edgeParam a u m₂ = -η / 2 := by simp [hm₂, edgeParam_edgePt a u hu]
    have hm₂normal : edgeNormal a u m₂ = σ * (η / 2) := by
      simp [hm₂, edgeNormal_edgePt a u hu]
    have habs : |σ * (η / 2)| < η := by
      have hs : |σ| = 1 := by rcases hσ with h | h <;> simp [h]
      rw [abs_mul, hs, one_mul, abs_of_pos (by linarith : (0:ℝ) < η / 2)]
      linarith
    have hm₁mem : m₁ ∈ corridorSet a u s₁ η := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hm₁param]; exact hp1
      · rw [hm₁param]; exact hp2
      · rw [hm₁normal]; exact habs
    have hm₂mem : m₂ ∈ corridorSet a u s₁ η := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hm₂param]; linarith
      · rw [hm₂param]; linarith
      · rw [hm₂normal]; exact habs
    refine ⟨(affinePath p m₁).trans ((affinePath m₁ m₂).trans
      (affinePath m₂ (corridorBase a u η))), ?_, ?_⟩
    · refine Path.trans_forall _ _ (fun z => z ∈ corridorSet a u s₁ η)
        (affinePath_mem_corridorSet a u s₁ η p m₁ hpmem hm₁mem) ?_
      exact Path.trans_forall _ _ (fun z => z ∈ corridorSet a u s₁ η)
        (affinePath_mem_corridorSet a u s₁ η m₁ m₂ hm₁mem hm₂mem)
        (affinePath_mem_corridorSet a u s₁ η m₂ _ hm₂mem hbase)
    · refine Path.trans_forall _ _ (fun z => z ∉ segment ℝ a (a + u)) hleg1 ?_
      refine Path.trans_forall _ _ (fun z => z ∉ segment ℝ a (a + u)) ?_ ?_
      · -- horizontal leg at constant nonzero normal coordinate
        rcases hσ with h | h
        · refine affinePath_avoid_segment_of_edgeNormal_pos a u m₁ m₂ hu ?_ ?_ <;>
            simp [hm₁normal, hm₂normal, h] <;> linarith
        · refine affinePath_avoid_segment_of_edgeNormal_neg a u m₁ m₂ hu ?_ ?_ <;>
            simp [hm₁normal, hm₂normal, h] <;> linarith
      · refine affinePath_avoid_segment_of_edgeParam_neg a u m₂ _ hu ?_ ?_
        · rw [hm₂param]; linarith
        · rw [hbaseParam]; linarith
  rcases lt_trichotomy β 0 with hneg | hzero | hpos
  · -- below the edge line: go down
    refine route (-1) (Or.inr rfl) ?_
    refine affinePath_avoid_segment_of_edgeNormal_neg a u p _ hu (by rw [← hβ]; exact hneg) ?_
    rw [edgeNormal_edgePt a u hu]; linarith
  · -- on the edge line: `p` is off the edge, so it is beyond one endpoint
    have hoff : α < 0 ∨ 1 < α := by
      by_contra hcon
      push_neg at hcon
      exact hpseg ((mem_segment_iff_edgeCoords a u p hu).mpr
        ⟨hzero, hcon.1, hcon.2⟩)
    rcases hoff with hlt | hgt
    · refine ⟨affinePath p (corridorBase a u η), ?_, ?_⟩
      · exact affinePath_mem_corridorSet a u s₁ η p _ hpmem hbase
      · refine affinePath_avoid_segment_of_edgeParam_neg a u p _ hu hlt ?_
        rw [hbaseParam]; linarith
    · refine route 1 (Or.inl rfl) ?_
      refine affinePath_avoid_segment_of_edgeParam_gt_one a u p _ hu hgt ?_
      rw [edgeParam_edgePt a u hu]; exact hgt
  · -- above the edge line: go up
    refine route 1 (Or.inl rfl) ?_
    refine affinePath_avoid_segment_of_edgeNormal_pos a u p _ hu (by rw [← hβ]; exact hpos) ?_
    rw [edgeNormal_edgePt a u hu]; linarith

/-- **The corridor minus the new edge is path connected.**  Two corridor points
off the new edge are joined by a path that stays in the corridor and misses the
edge. -/
lemma exists_corridorPath (a u : ℂ) (hu : u ≠ 0) (s₁ η : ℝ)
    (hη : 0 < η) (hs₁ : 0 < s₁) (p q : ℂ)
    (hp : p ∈ corridorSet a u s₁ η) (hpseg : p ∉ segment ℝ a (a + u))
    (hq : q ∈ corridorSet a u s₁ η) (hqseg : q ∉ segment ℝ a (a + u)) :
    ∃ δ : Path p q,
      (∀ t, δ t ∈ corridorSet a u s₁ η) ∧
        (∀ t, δ t ∉ segment ℝ a (a + u)) := by
  obtain ⟨δ₁, hδ₁C, hδ₁S⟩ := exists_path_to_corridorBase a u hu s₁ η hη hs₁ p hp hpseg
  obtain ⟨δ₂, hδ₂C, hδ₂S⟩ := exists_path_to_corridorBase a u hu s₁ η hη hs₁ q hq hqseg
  refine ⟨δ₁.trans δ₂.symm, ?_, ?_⟩
  · exact Path.trans_forall _ _ (fun z => z ∈ corridorSet a u s₁ η) hδ₁C
      (fun t => hδ₂C _)
  · exact Path.trans_forall _ _ (fun z => z ∉ segment ℝ a (a + u)) hδ₁S
      (fun t => hδ₂S _)

/-! ### The two half corridors

The two open half corridors are convex, hence path connected, and each is
disjoint from the whole carrier line of the edge (not just from the edge).
This is the *local two-sidedness* of a segment in the plane.

These declarations are **preparation, not a dead branch**: the residual
Umlaufsatz gaps recorded in `PROOF_STATUS.md`
(`vertex_escape_joinedIn_arbitrarily_far_one_diag`, `clipped_ear_escape_walk`)
need a polygon Jordan statement, whose standard proof starts exactly here — a
small neighbourhood of a point in the relative interior of one edge meets the
polygon in a diameter and splits into two path-connected halves.  Recording the
bricks here keeps them on the live corridor file rather than in a detached
file. -/

/-- The open half corridor strictly above the edge line. -/
def corridorUpper (a u : ℂ) (s₁ η : ℝ) : Set ℂ :=
  {z | z ∈ corridorSet a u s₁ η ∧ 0 < edgeNormal a u z}

/-- The open half corridor strictly below the edge line. -/
def corridorLower (a u : ℂ) (s₁ η : ℝ) : Set ℂ :=
  {z | z ∈ corridorSet a u s₁ η ∧ edgeNormal a u z < 0}

lemma convex_corridorUpper (a u : ℂ) (s₁ η : ℝ) :
    Convex ℝ (corridorUpper a u s₁ η) := by
  intro p hp q hq r s hr hs hrs
  refine ⟨(convex_corridorSet a u s₁ η) hp.1 hq.1 hr hs hrs, ?_⟩
  rw [edgeNormal_smul_add a u p q r s hrs]
  exact real_convex_lt_comb hr hs hrs hp.2 hq.2

lemma convex_corridorLower (a u : ℂ) (s₁ η : ℝ) :
    Convex ℝ (corridorLower a u s₁ η) := by
  intro p hp q hq r s hr hs hrs
  refine ⟨(convex_corridorSet a u s₁ η) hp.1 hq.1 hr hs hrs, ?_⟩
  rw [edgeNormal_smul_add a u p q r s hrs]
  exact real_convex_comb_lt hr hs hrs hp.2 hq.2

/-- Straight connectors inside the upper half corridor stay there and miss the
edge. -/
lemma exists_path_in_corridorUpper (a u : ℂ) (hu : u ≠ 0) (s₁ η : ℝ) (p q : ℂ)
    (hp : p ∈ corridorUpper a u s₁ η) (hq : q ∈ corridorUpper a u s₁ η) :
    ∃ δ : Path p q,
      (∀ t, δ t ∈ corridorUpper a u s₁ η) ∧
        (∀ t, δ t ∉ segment ℝ a (a + u)) := by
  refine ⟨affinePath p q, fun t =>
    (convex_corridorUpper a u s₁ η).segment_subset hp hq
      (affinePath_mem_segment p q t), ?_⟩
  exact affinePath_avoid_segment_of_edgeNormal_pos a u p q hu hp.2 hq.2

/-- Straight connectors inside the lower half corridor stay there and miss the
edge. -/
lemma exists_path_in_corridorLower (a u : ℂ) (hu : u ≠ 0) (s₁ η : ℝ) (p q : ℂ)
    (hp : p ∈ corridorLower a u s₁ η) (hq : q ∈ corridorLower a u s₁ η) :
    ∃ δ : Path p q,
      (∀ t, δ t ∈ corridorLower a u s₁ η) ∧
        (∀ t, δ t ∉ segment ℝ a (a + u)) := by
  refine ⟨affinePath p q, fun t =>
    (convex_corridorLower a u s₁ η).segment_subset hp hq
      (affinePath_mem_segment p q t), ?_⟩
  exact affinePath_avoid_segment_of_edgeNormal_neg a u p q hu hp.2 hq.2

/-- Every corridor point off the edge line lies in one of the two half
corridors; the remaining corridor points off the *edge* lie beyond one of its
two endpoints. -/
lemma corridorSet_trichotomy (a u : ℂ) (hu : u ≠ 0) (s₁ η : ℝ) (z : ℂ)
    (hz : z ∈ corridorSet a u s₁ η) (hzseg : z ∉ segment ℝ a (a + u)) :
    z ∈ corridorUpper a u s₁ η ∨ z ∈ corridorLower a u s₁ η ∨
      (edgeNormal a u z = 0 ∧ (edgeParam a u z < 0 ∨ 1 < edgeParam a u z)) := by
  rcases lt_trichotomy (edgeNormal a u z) 0 with h | h | h
  · exact Or.inr (Or.inl ⟨hz, h⟩)
  · refine Or.inr (Or.inr ⟨h, ?_⟩)
    by_contra hcon
    push_neg at hcon
    exact hzseg ((mem_segment_iff_edgeCoords a u z hu).mpr ⟨h, hcon.1, hcon.2⟩)
  · exact Or.inl ⟨hz, h⟩

end HexArea
