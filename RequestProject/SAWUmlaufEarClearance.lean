/-
# Ear clearance without cyclic non-degeneracy

`RequestProject.SAWUmlaufTriangleClosed` proves the *ear clearance* property —
no interior point of a cyclic edge lies strictly inside an empty ear triangle —
for a simple polygon that is **cyclically non-degenerate** (`polyCycNondeg L`).
The non-degeneracy is used there only at the three ear corners `a`, `b`, `c`, and
only to rule out that an edge of `L` incident to `a` (or to `c`) runs *along* an
ear side.

The chord pieces produced by a diagonal cut of a simple polygon are simple, but
they need **not** be cyclically non-degenerate: the two seam corners at the cut
endpoints may be flat (this is the content of
`RequestProject.SAWUmlaufFlatClipCounterexample`).  This file therefore reproves
the clearance property assuming only

* `PolygonSimple L`, `4 ≤ L.length`, and
* non-degeneracy of the **ear tip corner alone**, `hD : cross (b-a) (c-b) ≠ 0`
  (which is available in the application: the ear tip of a chord piece is an
  interior corner of the original polygon).

The two flat-corner subcases of `ear_exit_on_base` are replaced by the sharper
combinatorial input `simple_edge_openSegment_not_mem`
(`RequestProject.SAWUmlaufCycleAdjacent`): in a simple polygon with at least four
vertices, an interior point of an edge lies on no other edge — adjacent edges
included.

## Contents

* `ear_exit_on_base_tip` — every exit of an edge from the ear triangle lies on
  the base `[c, a]`.
* `ear_edge_interior_not_strict_tip` — no interior point of a cyclic edge lies
  strictly inside the ear triangle.
* `ear_strict_interior_off_closedEdges` — a point strictly inside an empty ear
  triangle lies on **no** closed edge of the polygon at all.

## Downstream use (NOT a dead branch)

`ear_strict_interior_off_closedEdges` is exactly the hypothesis needed to apply
the winding-number dichotomy and the edge-crossing jump at a point of the ear
interior, in `RequestProject.SAWUmlaufJordanCore`.
-/

import Mathlib
import RequestProject.SAWUmlaufCycleAdjacent

open Real Complex

noncomputable section

set_option maxHeartbeats 1000000

/-- **Every exit of an edge from the ear triangle lies on the base `[c, a]`** —
version assuming only non-degeneracy of the ear *tip* corner (compare
`ear_exit_on_base`, which assumes `polyCycNondeg L`).  The two subcases in which
an incident edge could run along an ear side are excluded by
`simple_edge_openSegment_not_mem` instead of by non-flatness of the corner. -/
lemma ear_exit_on_base_tip (L : List ℂ) (h4 : 4 ≤ L.length) (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (p q : ℂ) (hpq : (p, q) ∈ closedEdges L) (hbp : b ≠ p) (hbq : b ≠ q)
    (v : ℂ) (hv : v ∈ openSegment ℝ p q)
    (y : ℂ) (hy : y = p ∨ y = q) (hyout : ¬ HexArea.inTriangleClosed a b c y)
    (z : ℂ) (hzy : z ∈ segment ℝ v y) (hzc : HexArea.inTriangleClosed a b c z)
    (hzero : HexArea.cross (b - a) (z - a) * HexArea.cross (b - a) (c - b) = 0 ∨
             HexArea.cross (c - b) (z - b) * HexArea.cross (b - a) (c - b) = 0 ∨
             HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) = 0) :
    z ∈ segment ℝ c a := by
  have hNodup : L.Nodup := hsimple.1
  have hab : (a, b) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L ρ, hrot]; simp [closedEdges]
  have hbc : (b, c) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L ρ, hrot]; simp [closedEdges]
  have hpqne : p ≠ q := closedEdges_ne L hNodup (by omega) p q hpq
  have hpa : p ≠ a := by
    rintro rfl
    exact hbq (closedEdges_succ_unique L hNodup p q b hpq hab).symm
  have hqc : q ≠ c := by
    rintro rfl
    exact hbp (closedEdges_pred_unique L hNodup q p b hpq hbc).symm
  have hvseg : v ∈ segment ℝ p q := openSegment_subset_segment ℝ p q hv
  have hyseg : y ∈ segment ℝ p q := by
    rcases hy with rfl | rfl
    · exact left_mem_segment ℝ y q
    · exact right_mem_segment ℝ p y
  have hzpq : z ∈ segment ℝ p q := (convex_segment p q).segment_subset hvseg hyseg hzy
  rcases hzero with h1 | h2 | h3
  · -- `z` would lie on the ear side `[a, b]`
    exfalso
    have hf1 : HexArea.cross (b - a) (z - a) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hD
    have hzab : z ∈ segment ℝ a b := HexArea.mem_side_ab_of_closed a b c z hD hzc hf1
    by_cases hqa : q = a
    · -- the edge is `(p, a)`, sharing the vertex `a` with the ear side `(a, b)`
      have hya : y = p := by
        rcases hy with h | h
        · exact h
        · exact absurd (by rw [h, hqa]; exact HexArea.inTriangleClosed_vertex_a a b c) hyout
      have hzq : z ≠ q := by
        intro h
        refine HexArea.not_mem_segment_of_openSegment p q v hpqne hv ?_
        rw [← h, ← hya]; exact hzy
      -- `p` is off the ear side `[a, b]`, so `z ≠ p`
      obtain ⟨p'', hp''⟩ := exists_closedEdges_pred L p (mem_of_fst_mem_closedEdges L p q hpq)
      have hp''a : p'' ≠ a := by
        intro h
        exact hbp (closedEdges_succ_unique L hNodup a p b (h ▸ hp'') hab).symm
      have hp''b : p'' ≠ b := by
        intro h
        exact closedEdges_no_three_cycle L hNodup h4 b p q (h ▸ hp'') hpq
          (by rw [hqa]; exact hab)
      have hpoff : p ∉ segment ℝ a b :=
        vertex_off_edge_via_pred L hsimple a b p p'' hab hp'' hp''a hp''b hpa (Ne.symm hbp)
      have hzp : z ≠ p := by intro h; exact hpoff (h ▸ hzab)
      have hzopen : z ∈ openSegment ℝ p q := by
        rw [← insert_endpoints_openSegment] at hzpq
        simp only [Set.mem_insert_iff] at hzpq
        rcases hzpq with h | h | h
        · exact absurd h hzp
        · exact absurd h hzq
        · exact h
      exact simple_edge_openSegment_not_mem L h4 hsimple p q a b hpq hab
        (fun h => hpa h.1) z hzopen hzab
    · have hdisj := hsimple.2 (a, b) hab (p, q) hpq (by simpa using (Ne.symm hpa))
        (by simpa using (Ne.symm hqa)) (by simpa using hbp) (by simpa using hbq)
      exact Set.disjoint_left.mp hdisj hzab hzpq
  · -- `z` would lie on the ear side `[b, c]`
    exfalso
    have hf2 : HexArea.cross (c - b) (z - b) = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hD
    have hzbc : z ∈ segment ℝ b c := HexArea.mem_side_bc_of_closed a b c z hD hzc hf2
    by_cases hpc : p = c
    · -- the edge is `(c, q)`, sharing the vertex `c` with the ear side `(b, c)`
      have hyq : y = q := by
        rcases hy with h | h
        · exact absurd (by rw [h, hpc]; exact HexArea.inTriangleClosed_vertex_c a b c) hyout
        · exact h
      have hzp : z ≠ p := by
        intro h
        refine HexArea.not_mem_segment_of_openSegment q p v (Ne.symm hpqne) ?_ ?_
        · rw [openSegment_symm]; exact hv
        · rw [← h, ← hyq]; exact hzy
      obtain ⟨q', hq'⟩ := exists_closedEdges_succ L q (mem_of_snd_mem_closedEdges L p q hpq)
      have hq'c : q' ≠ c := by
        intro h
        exact hbq (closedEdges_pred_unique L hNodup c q b (h ▸ hq') hbc).symm
      have hq'b : q' ≠ b := by
        intro h
        exact closedEdges_no_three_cycle L hNodup h4 q b c (h ▸ hq') hbc
          (by rw [← hpc]; exact hpq)
      have hqoff : q ∉ segment ℝ b c :=
        vertex_off_edge_via_succ L hsimple b c q q' hbc hq' (Ne.symm hbq) hqc hq'b hq'c
      have hzq : z ≠ q := by intro h; exact hqoff (h ▸ hzbc)
      have hzopen : z ∈ openSegment ℝ p q := by
        rw [← insert_endpoints_openSegment] at hzpq
        simp only [Set.mem_insert_iff] at hzpq
        rcases hzpq with h | h | h
        · exact absurd h hzp
        · exact absurd h hzq
        · exact h
      exact simple_edge_openSegment_not_mem L h4 hsimple p q b c hpq hbc
        (fun h => hbp h.1.symm) z hzopen hzbc
    · have hdisj := hsimple.2 (b, c) hbc (p, q) hpq (by simpa using hbp) (by simpa using hbq)
        (by simpa using (Ne.symm hpc)) (by simpa using (Ne.symm hqc))
      exact Set.disjoint_left.mp hdisj hzbc hzpq
  · -- `z` lies on the base `[c, a]`
    have hf3 : HexArea.cross (a - c) (z - c) = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h hD
    exact HexArea.mem_side_ca_of_closed a b c z hD hzc hf3

/-- **No interior point of a cyclic edge lies strictly inside the ear triangle** —
version assuming only non-degeneracy of the ear tip corner (compare
`ear_edge_interior_not_strict`). -/
lemma ear_edge_interior_not_strict_tip (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (p q : ℂ) (hpq : (p, q) ∈ closedEdges L) (hbp : b ≠ p) (hbq : b ≠ q)
    (v : ℂ) (hv : v ∈ openSegment ℝ p q) :
    ¬ HexArea.inTriangleStrict a b c v := by
  intro hstrict
  have hvT : HexArea.inTriangleClosed a b c v := HexArea.inTriangleClosed_of_strict a b c v hstrict
  have hg3v : 0 < HexArea.cross (a - c) (v - c) * HexArea.cross (b - a) (c - b) :=
    HexArea.scaled_pos_of_strict a b c v hstrict
  have hza : HexArea.cross (a - c) (a - c) = 0 := by simp [HexArea.cross]; ring
  have hzc : HexArea.cross (a - c) (c - c) = 0 := by simp [HexArea.cross]
  have key : ∀ w : ℂ, (w = p ∨ w = q) →
      ∃ z ∈ segment ℝ v w, HexArea.cross (a - c) (z - c) = 0 ∧ z ≠ v := by
    intro w hw
    have hwL : w ∈ L := by
      rcases hw with h | h
      · rw [h]; exact (mem_of_mem_closedEdges L p q hpq).1
      · rw [h]; exact (mem_of_mem_closedEdges L p q hpq).2
    have hwmem : w = a ∨ w = b ∨ w = c ∨ w ∈ rest := by
      rw [← List.mem_rotate (n := ρ), hrot] at hwL
      simpa using hwL
    rcases hwmem with hwa | hwb | hwc | hwrest
    · refine ⟨w, right_mem_segment ℝ v w, by rw [hwa]; exact hza, ?_⟩
      intro h
      rw [← h, hwa, hza, zero_mul] at hg3v
      exact lt_irrefl 0 hg3v
    · exfalso
      rcases hw with h | h
      · exact hbp (by rw [← hwb]; exact h)
      · exact hbq (by rw [← hwb]; exact h)
    · refine ⟨w, right_mem_segment ℝ v w, by rw [hwc]; exact hzc, ?_⟩
      intro h
      rw [← h, hwc, hzc, zero_mul] at hg3v
      exact lt_irrefl 0 hg3v
    · have hwout : ¬ HexArea.inTriangleClosed a b c w :=
        ear_rest_not_closed L h4 hsimple ρ a b c rest hrot hD hempty hdiag w hwrest
      obtain ⟨z, hzseg, hzcl, hzero⟩ := HexArea.exit_point a b c v w hvT hwout
      have hzbase : z ∈ segment ℝ c a :=
        ear_exit_on_base_tip L h4 hsimple ρ a b c rest hrot hD p q hpq hbp hbq v hv w hw
          hwout z hzseg hzcl hzero
      have hz3 : HexArea.cross (a - c) (z - c) = 0 := by
        rw [segment_symm] at hzbase
        exact (HexArea.inTriangleClosed_of_mem_ac a b c z hzbase).2
      refine ⟨z, hzseg, hz3, ?_⟩
      intro h
      rw [← h, hz3, zero_mul] at hg3v
      exact lt_irrefl 0 hg3v
  obtain ⟨z₁, hz1seg, hz13, hz1ne⟩ := key p (Or.inl rfl)
  obtain ⟨z₂, hz2seg, hz23, hz2ne⟩ := key q (Or.inr rfl)
  obtain ⟨α, β, hα, hβ, hsum, hveq⟩ :=
    mem_segment_of_between p q v z₁ z₂ hv hz1seg hz2seg hz1ne hz2ne
  have hveq' : v = (1 - β) • z₁ + β • z₂ := by
    rw [← hveq, show α = 1 - β by linarith]
  have hzero : HexArea.cross (a - c) (v - c) = 0 := by
    rw [hveq', HexArea.cross_affine, hz13, hz23]
    ring
  rw [hzero, zero_mul] at hg3v
  exact lt_irrefl 0 hg3v

/-- **A point strictly inside an empty ear triangle lies on no closed edge.**
Combines `ear_edge_interior_not_strict_tip` (for the edges not incident to the
ear tip `b`) with the two ear sides (where strict interiority already excludes
the point, since it is off the two side lines) and the fact that a strict
interior point is not a vertex. -/
lemma ear_strict_interior_off_closedEdges (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (x : ℂ) (hin : HexArea.inTriangleStrict a b c x)
    (p q : ℂ) (hpq : (p, q) ∈ closedEdges L) :
    x ∉ segment ℝ p q := by
  have hNodup : L.Nodup := hsimple.1
  have hab : (a, b) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L ρ, hrot]; simp [closedEdges]
  have hbc : (b, c) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L ρ, hrot]; simp [closedEdges]
  -- a strict interior point is not a vertex
  have hxL : x ∉ L := by
    intro hxl
    rw [← List.mem_rotate (n := ρ), hrot] at hxl
    simp only [List.mem_cons] at hxl
    rcases hxl with h | h | h | h
    · exact HexArea.inTriangleStrict_ne_a a b c x hin h
    · exact HexArea.inTriangleStrict_ne_b a b c x hin h
    · exact HexArea.inTriangleStrict_ne_c a b c x hin h
    · exact hempty x h hin
  have hxp : x ≠ p := fun h => hxL (h ▸ (mem_of_mem_closedEdges L p q hpq).1)
  have hxq : x ≠ q := fun h => hxL (h ▸ (mem_of_mem_closedEdges L p q hpq).2)
  intro hx
  have hxopen : x ∈ openSegment ℝ p q := by
    rw [← insert_endpoints_openSegment] at hx
    simp only [Set.mem_insert_iff] at hx
    rcases hx with h | h | h
    · exact absurd h hxp
    · exact absurd h hxq
    · exact h
  by_cases hbp : b = p
  · -- the edge is the ear side `(b, c)`
    subst hbp
    have hqc : q = c := closedEdges_succ_unique L hNodup b q c hpq hbc
    subst hqc
    have h0 : HexArea.cross (q - b) (x - b) = 0 :=
      HexArea.cross_combo_segment b q x hx
    rcases hin with ⟨_, h2, _⟩ | ⟨_, h2, _⟩ <;> rw [h0] at h2 <;> exact lt_irrefl 0 h2
  by_cases hbq : b = q
  · -- the edge is the ear side `(a, b)`
    subst hbq
    have hpa : p = a := closedEdges_pred_unique L hNodup b p a hpq hab
    subst hpa
    have h0 : HexArea.cross (b - p) (x - p) = 0 :=
      HexArea.cross_combo_segment p b x hx
    rcases hin with ⟨h1, _, _⟩ | ⟨h1, _, _⟩ <;> rw [h0] at h1 <;> exact lt_irrefl 0 h1
  · exact ear_edge_interior_not_strict_tip L h4 hsimple ρ a b c rest hrot hD hempty hdiag
      p q hpq hbp hbq x hxopen hin
