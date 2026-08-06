/-
# Adjacent edges of a simple polygon meet only at their shared vertex

This file supplies the elementary *cyclic combinatorics* of the closed edge list
`closedEdges L = L.zip (L.rotate 1)` of a `Nodup` vertex cycle, and the resulting
geometric separation statement

* `simple_edge_openSegment_not_mem` — in a simple polygon with at least four
  vertices, an **interior point of one edge lies on no other edge**, *including*
  the two adjacent ones.

For non-adjacent edges this is exactly the `PolygonSimple` disjointness clause.
For the two edges adjacent to `(p, q)` the clause does not apply (they share a
vertex), and the statement is a genuine consequence of simplicity *plus* the
`Nodup` cyclic structure: an overlap of two adjacent edges would place a third
vertex in the relative interior of an edge, and the edge incident to *that*
vertex on the far side is then non-incident to `(p, q)`, contradicting
disjointness — unless the cycle closes up after two or three vertices, which is
excluded by `4 ≤ L.length`.

## Contents

* `mem_closedEdges_getElem`, `closedEdges_index`, `closedEdges_succ_getElem` —
  the index description of the closed edge list.
* `closedEdges_no_two_cycle`, `closedEdges_no_three_cycle` — a `Nodup` cycle of
  length `≥ 4` has no sub-cycle of length `2` or `3`.
* `exists_closedEdges_succ`, `exists_closedEdges_pred` — every vertex has a
  cyclic successor and predecessor.
* `vertex_off_edge_via_succ`, `vertex_off_edge_via_pred` — a vertex whose
  successor (resp. predecessor) edge is non-incident to `(P, Q)` is off `[P,Q]`.
* `openSegment_overlap_ray` — the ray form of an overlap of two segments sharing
  the endpoint `p`.
* `simple_edge_openSegment_not_mem` — the main statement above.

## Downstream use (NOT a dead branch)

Consumed by `RequestProject.SAWUmlaufJordanCore`: the winding-number jump
`ptWind_jump_edge` across an edge of a polygon requires the chosen interior point
of the edge to be off *all other* edges of the cycle, which is precisely
`simple_edge_openSegment_not_mem`.  That jump is the local input of the
Jordan-separation keystone of the Umlaufsatz.
-/

import Mathlib
import RequestProject.SAWUmlaufTriangleClosed

open Real Complex

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. Index description of the closed edge list -/

/-- The `i`-th closed edge of a vertex cycle. -/
lemma mem_closedEdges_getElem (V : List ℂ) (i : ℕ) (hi : i < V.length) :
    (V[i], V[(i + 1) % V.length]'(Nat.mod_lt _ (by omega))) ∈ closedEdges V := by
  rw [closedEdges, List.mem_iff_getElem]
  refine ⟨i, by simpa using hi, ?_⟩
  rw [List.getElem_zip]
  simp [List.getElem_rotate]

/-- Every closed edge is the `i`-th one for some index `i`. -/
lemma closedEdges_index (V : List ℂ) (x y : ℂ) (h : (x, y) ∈ closedEdges V) :
    ∃ i, ∃ hi : i < V.length,
      V[i] = x ∧ y = V[(i + 1) % V.length]'(Nat.mod_lt _ (by omega)) := by
  rw [closedEdges, List.mem_iff_getElem] at h
  obtain ⟨i, hi, he⟩ := h
  simp only [List.length_zip, List.length_rotate, min_self] at hi
  rw [List.getElem_zip] at he
  refine ⟨i, hi, congrArg Prod.fst he, ?_⟩
  have h2 := congrArg Prod.snd he
  simp only at h2
  rw [← h2, List.getElem_rotate]

/-- In a `Nodup` cycle the successor of the `i`-th vertex is the `(i+1)`-st. -/
lemma closedEdges_succ_getElem (V : List ℂ) (hnd : V.Nodup) (i : ℕ) (hi : i < V.length) (y : ℂ)
    (h : (V[i], y) ∈ closedEdges V) :
    y = V[(i + 1) % V.length]'(Nat.mod_lt _ (by omega)) :=
  closedEdges_succ_unique V hnd _ y _ h (mem_closedEdges_getElem V i hi)

/-- Every vertex of a cycle has a cyclic successor. -/
lemma exists_closedEdges_succ (V : List ℂ) (x : ℂ) (hx : x ∈ V) :
    ∃ y, (x, y) ∈ closedEdges V := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  exact ⟨_, mem_closedEdges_getElem V i hi⟩

/-- Every vertex of a cycle has a cyclic predecessor. -/
lemma exists_closedEdges_pred (V : List ℂ) (x : ℂ) (hx : x ∈ V) :
    ∃ y, (y, x) ∈ closedEdges V := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hlen : 0 < V.length := by omega
  set j := (i + V.length - 1) % V.length with hj
  have hjlt : j < V.length := Nat.mod_lt _ hlen
  have hkey : (j + 1) % V.length = i := by
    have h1 : (i + V.length - 1 + 1) % V.length = i % V.length := by
      have : i + V.length - 1 + 1 = i + V.length := by omega
      rw [this, Nat.add_mod_right]
    rw [hj, Nat.mod_add_mod, h1, Nat.mod_eq_of_lt hi]
  have := mem_closedEdges_getElem V j hjlt
  simp only [hkey] at this
  exact ⟨V[j], this⟩

/-- A vertex of `L` occurring in an edge is a member of `L`. -/
lemma mem_of_fst_mem_closedEdges (V : List ℂ) (x y : ℂ) (h : (x, y) ∈ closedEdges V) : x ∈ V := by
  obtain ⟨i, hi, hx, _⟩ := closedEdges_index V x y h
  exact hx ▸ List.getElem_mem hi

/-- The second vertex of an edge is a member of `L`. -/
lemma mem_of_snd_mem_closedEdges (V : List ℂ) (x y : ℂ) (h : (x, y) ∈ closedEdges V) : y ∈ V := by
  obtain ⟨i, hi, _, hy⟩ := closedEdges_index V x y h
  exact hy ▸ List.getElem_mem _

/-! ## 2. No short sub-cycles -/

/-- A `Nodup` cycle of length `≥ 3` has no `2`-cycle. -/
lemma closedEdges_no_two_cycle (V : List ℂ) (hnd : V.Nodup) (h3 : 3 ≤ V.length) (p q : ℂ)
    (h1 : (p, q) ∈ closedEdges V) (h2 : (q, p) ∈ closedEdges V) : False := by
  obtain ⟨i, hi, hp, hq⟩ := closedEdges_index V p q h1
  subst hp
  rw [hq] at h2
  have h3' := closedEdges_succ_getElem V hnd _ (Nat.mod_lt _ (by omega)) _ h2
  have hidx : i = ((i + 1) % V.length + 1) % V.length :=
    (List.Nodup.getElem_inj_iff hnd (i := i) (j := ((i + 1) % V.length + 1) % V.length)
      (hi := hi) (hj := Nat.mod_lt _ (by omega))).mp h3'
  have he : ((i + 1) % V.length + 1) % V.length = (i + 2) % V.length := by
    rw [Nat.mod_add_mod]
  rw [he] at hidx
  have hmod : (i + 2) % V.length = i % V.length := by
    rw [← hidx, Nat.mod_eq_of_lt hi]
  have hdvd : V.length ∣ 2 := by
    have hmodeq : i + 2 ≡ i [MOD V.length] := hmod
    have h := (Nat.modEq_iff_dvd' (by omega)).mp hmodeq.symm
    simpa using h
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- A `Nodup` cycle of length `≥ 4` has no `3`-cycle. -/
lemma closedEdges_no_three_cycle (V : List ℂ) (hnd : V.Nodup) (h4 : 4 ≤ V.length) (p q s : ℂ)
    (h1 : (p, q) ∈ closedEdges V) (h2 : (q, s) ∈ closedEdges V) (h3 : (s, p) ∈ closedEdges V) :
    False := by
  obtain ⟨i, hi, hp, hq⟩ := closedEdges_index V p q h1
  subst hp
  rw [hq] at h2
  have hs := closedEdges_succ_getElem V hnd _ (Nat.mod_lt _ (by omega)) _ h2
  rw [hs] at h3
  have hp3 := closedEdges_succ_getElem V hnd _ (Nat.mod_lt _ (by omega)) _ h3
  have hidx : i = ((((i + 1) % V.length + 1) % V.length) + 1) % V.length :=
    (List.Nodup.getElem_inj_iff hnd (i := i)
      (j := ((((i + 1) % V.length + 1) % V.length) + 1) % V.length)
      (hi := hi) (hj := Nat.mod_lt _ (by omega))).mp hp3
  have he : ((((i + 1) % V.length + 1) % V.length) + 1) % V.length = (i + 3) % V.length := by
    rw [Nat.mod_add_mod, show (i + 1) % V.length + 1 + 1 = (i + 1) % V.length + 2 from by omega,
      Nat.mod_add_mod]

  rw [he] at hidx
  have hmod : (i + 3) % V.length = i % V.length := by
    rw [← hidx, Nat.mod_eq_of_lt hi]
  have hdvd : V.length ∣ 3 := by
    have hmodeq : i + 3 ≡ i [MOD V.length] := hmod
    have h := (Nat.modEq_iff_dvd' (by omega)).mp hmodeq.symm
    simpa using h
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-! ## 3. A vertex is off every edge non-incident to one of its own edges -/

/-- If the successor edge `(x, x')` of the vertex `x` shares no endpoint with the
edge `(P, Q)`, then `x` is off the segment `[P, Q]`. -/
lemma vertex_off_edge_via_succ (L : List ℂ) (hsimple : PolygonSimple L) (P Q x x' : ℂ)
    (hPQ : (P, Q) ∈ closedEdges L) (hxx' : (x, x') ∈ closedEdges L)
    (h1 : x ≠ P) (h2 : x ≠ Q) (h3 : x' ≠ P) (h4 : x' ≠ Q) :
    x ∉ segment ℝ P Q := by
  intro hx
  have hdisj := hsimple.2 (x, x') hxx' (P, Q) hPQ h1 h2 h3 h4
  exact Set.disjoint_left.mp hdisj (left_mem_segment ℝ x x') hx

/-- If the predecessor edge `(x'', x)` of the vertex `x` shares no endpoint with
the edge `(P, Q)`, then `x` is off the segment `[P, Q]`. -/
lemma vertex_off_edge_via_pred (L : List ℂ) (hsimple : PolygonSimple L) (P Q x x'' : ℂ)
    (hPQ : (P, Q) ∈ closedEdges L) (hxx : (x'', x) ∈ closedEdges L)
    (h1 : x'' ≠ P) (h2 : x'' ≠ Q) (h3 : x ≠ P) (h4 : x ≠ Q) :
    x ∉ segment ℝ P Q := by
  intro hx
  have hdisj := hsimple.2 (x'', x) hxx (P, Q) hPQ h1 h2 h3 h4
  exact Set.disjoint_left.mp hdisj (right_mem_segment ℝ x'' x) hx

/-! ## 4. Overlap of two segments sharing an endpoint -/

/-- If the segment `[w, p]` contains an interior point of `[p, q]`, then `w` lies
on the ray from `p` through `q`: either `w ∈ [p, q]` or `q ∈ [p, w]`. -/
lemma openSegment_overlap_ray (p q w m : ℂ) (hpq : p ≠ q) (hm : m ∈ openSegment ℝ p q)
    (hmem : m ∈ segment ℝ w p) :
    w ∈ segment ℝ p q ∨ q ∈ segment ℝ p w := by
  obtain ⟨t1, t2, ht1, ht2, htsum, hmv⟩ := hm
  obtain ⟨u1, u2, hu1, hu2, husum, hmw⟩ := hmem
  have hts : (t1 : ℂ) + (t2 : ℂ) = 1 := by exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) htsum
  have hus : (u1 : ℂ) + (u2 : ℂ) = 1 := by exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) husum
  have e1 : m - p = (t2 : ℂ) * (q - p) := by
    rw [← hmv]; simp only [Complex.real_smul]; linear_combination p * hts
  have e2 : m - p = (u1 : ℂ) * (w - p) := by
    rw [← hmw]; simp only [Complex.real_smul]; linear_combination p * hus
  have hqp : (q : ℂ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have hkey : (u1 : ℂ) * (w - p) = (t2 : ℂ) * (q - p) := by rw [← e2, e1]
  have hu1pos : 0 < u1 := by
    rcases hu1.lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : (t2 : ℂ) * (q - p) = 0 := by rw [← hkey, ← h]; simp
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd (by exact_mod_cast h' : t2 = 0) (by linarith)
      · exact hqp h'
  have hu1C : (u1 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu1pos
  set lam : ℝ := t2 / u1 with hlamdef
  have hlampos : 0 < lam := div_pos ht2 hu1pos
  have hlamC : ((lam : ℝ) : ℂ) = (t2 : ℂ) / (u1 : ℂ) := by rw [hlamdef]; push_cast; ring
  have hw : w = p + ((lam : ℝ) : ℂ) * (q - p) := by
    rw [hlamC]
    field_simp
    linear_combination hkey
  by_cases hle : lam ≤ 1
  · left
    refine ⟨1 - lam, lam, by linarith, hlampos.le, by ring, ?_⟩
    simp only [Complex.real_smul]
    rw [hw]; push_cast; ring
  · right
    push_neg at hle
    have hlne : ((lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hlampos
    refine ⟨1 - 1 / lam, 1 / lam, by rw [sub_nonneg, div_le_one hlampos]; linarith,
      by positivity, by ring, ?_⟩
    have hq : q = p + ((1 / lam : ℝ) : ℂ) * (w - p) := by
      have h1 : ((1 / lam : ℝ) : ℂ) = 1 / ((lam : ℝ) : ℂ) := by push_cast; ring
      rw [h1, hw]; field_simp; ring
    simp only [Complex.real_smul]
    rw [hq]; push_cast; field_simp; ring

/-! ## 5. Main statement -/

/-- **An interior point of an edge of a simple polygon lies on no other edge.**
`L` is a simple polygon with at least four vertices, `(p, q)` and `(r, s)` are
distinct closed edges, and `m` is an interior point of `[p, q]`; then `m` is off
`[r, s]`.  The non-adjacent case is the `PolygonSimple` disjointness clause; the
two adjacent cases use the cyclic structure (no `2`- or `3`-cycles). -/
lemma simple_edge_openSegment_not_mem (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L) (p q r s : ℂ)
    (h1 : (p, q) ∈ closedEdges L) (h2 : (r, s) ∈ closedEdges L)
    (hne : ¬ (p = r ∧ q = s)) (m : ℂ) (hm : m ∈ openSegment ℝ p q) :
    m ∉ segment ℝ r s := by
  have hnd : L.Nodup := hsimple.1
  have hpq : p ≠ q := closedEdges_ne L hnd (by omega) p q h1
  have hrs : r ≠ s := closedEdges_ne L hnd (by omega) r s h2
  -- the four incidence cases
  by_cases hpr : p = r
  · exfalso; exact hne ⟨hpr, closedEdges_succ_unique L hnd p q s h1 (hpr ▸ h2)⟩
  by_cases hqs : q = s
  · exfalso; exact hne ⟨closedEdges_pred_unique L hnd q p r h1 (hqs ▸ h2), hqs⟩
  by_cases hps : p = s
  · -- predecessor case: the other edge is `(r, p)`
    subst hps
    intro hmem
    obtain hw | hw := openSegment_overlap_ray p q r m hpq hm hmem
    · -- `r` lies on the edge `[p, q]`
      have hrp : r ≠ p := closedEdges_ne L hnd (by omega) r p h2
      have hrq : r ≠ q := by
        intro h; subst h
        exact closedEdges_no_two_cycle L hnd (by omega) p r h1 h2
      obtain ⟨r'', hr''⟩ := exists_closedEdges_pred L r (mem_of_fst_mem_closedEdges L r p h2)
      have hr''p : r'' ≠ p := by
        intro h; subst h
        exact hrq (closedEdges_succ_unique L hnd r'' q r h1 hr'').symm
      have hr''q : r'' ≠ q := by
        intro h; subst h
        exact closedEdges_no_three_cycle L hnd h4 p r'' r h1 hr'' h2
      exact vertex_off_edge_via_pred L hsimple p q r r'' h1 hr'' hr''p hr''q hrp hrq hw
    · -- `q` lies on the edge `[r, p]`
      have hqr : q ≠ r := by
        intro h; subst h
        exact closedEdges_no_two_cycle L hnd (by omega) p q h1 h2
      obtain ⟨q', hq'⟩ := exists_closedEdges_succ L q (mem_of_snd_mem_closedEdges L p q h1)
      have hq'r : q' ≠ r := by
        intro h; subst h
        exact closedEdges_no_three_cycle L hnd h4 p q q' h1 hq' h2
      have hq'p : q' ≠ p := by
        intro h; subst h
        exact hqr (closedEdges_pred_unique L hnd q' q r hq' h2)
      have hmemrp : q ∈ segment ℝ r p := by
        rw [segment_symm]; exact hw
      exact vertex_off_edge_via_succ L hsimple r p q q' h2 hq' hqr hpq.symm hq'r hq'p hmemrp
  by_cases hqr : q = r
  · -- successor case: the other edge is `(q, s)`
    subst hqr
    intro hmem
    have hmqp : m ∈ openSegment ℝ q p := by rw [openSegment_symm]; exact hm
    have hmemsq : m ∈ segment ℝ s q := by rw [segment_symm]; exact hmem
    obtain hw | hw := openSegment_overlap_ray q p s m (Ne.symm hpq) hmqp hmemsq
    · -- `s` lies on the edge `[q, p]`, i.e. on `[p, q]`
      have hsq : s ≠ q := (closedEdges_ne L hnd (by omega) q s h2).symm
      have hsp : s ≠ p := by
        intro h; subst h
        exact closedEdges_no_two_cycle L hnd (by omega) s q h1 h2
      obtain ⟨s', hs'⟩ := exists_closedEdges_succ L s (mem_of_snd_mem_closedEdges L q s h2)
      have hs'p : s' ≠ p := by
        intro h; subst h
        exact closedEdges_no_three_cycle L hnd h4 s' q s h1 h2 hs'
      have hs'q : s' ≠ q := by
        intro h; subst h
        exact hsp (closedEdges_pred_unique L hnd s' s p hs' h1)
      have hmempq : s ∈ segment ℝ p q := by rw [segment_symm]; exact hw
      exact vertex_off_edge_via_succ L hsimple p q s s' h1 hs' hsp hsq hs'p hs'q hmempq
    · -- `p` lies on the edge `[q, s]`
      have hpq' : p ≠ q := hpq
      have hps' : p ≠ s := by
        intro h; subst h
        exact closedEdges_no_two_cycle L hnd (by omega) p q h1 h2
      obtain ⟨p'', hp''⟩ := exists_closedEdges_pred L p (mem_of_fst_mem_closedEdges L p q h1)
      have hp''q : p'' ≠ q := by
        intro h; subst h
        exact hps' (closedEdges_succ_unique L hnd p'' p s hp'' h2)
      have hp''s : p'' ≠ s := by
        intro h; subst h
        exact closedEdges_no_three_cycle L hnd h4 p'' p q hp'' h1 h2
      exact vertex_off_edge_via_pred L hsimple q s p p'' h2 hp'' hp''q hp''s hpq' hps' hw
  · -- non-adjacent: the simplicity clause applies
    intro hmem
    have hdisj := hsimple.2 (p, q) h1 (r, s) h2 hpr hps hqr hqs
    exact Set.disjoint_left.mp hdisj (openSegment_subset_segment ℝ p q hm) hmem
