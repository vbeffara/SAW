import Mathlib
import RequestProject.SAWUmlaufEarConvex
import RequestProject.SAWUmlaufPolyChord
import RequestProject.SAWUmlaufFlatRemoval

/-!
# `SAWUmlaufTriangleClosed` — the closed corner triangle, and the clearance of an ear

The Meisters development needs, at two places, the classical fact that the
triangle of an *empty ear* of a simple polygon is **clear**: no edge of the
polygon (other than the two ear sides) meets it, except possibly at the two base
vertices `a`, `c` themselves.

This file provides the convex-geometry toolkit for that:

* `HexArea.inTriangleClosed` — the closed triangle, in the orientation-free
  *scaled* form (each edge cross product multiplied by the triangle
  orientation), so that no case distinction on the orientation is ever needed;
* `HexArea.inTriangleClosed_of_strict`, `HexArea.inTriangleClosed_of_mem_ac` —
  the strict interior and the base side are contained in it;
* `HexArea.mem_side_ab_of_closed`, `..._bc_...`, `..._ca_...` — a point of the
  closed triangle at which one of the three edge cross products vanishes lies on
  the corresponding closed side (barycentric reconstruction);
* `HexArea.exit_point` — the *first exit*: on a segment from a point of the
  closed triangle to a point outside it there is a point of the closed triangle
  at which one of the three cross products vanishes, i.e. a point of the
  boundary.  Proved by the intermediate value theorem applied to the minimum of
  the three (affine, hence continuous) scaled cross products.

On top of it the file proves the clearance property itself, `sorry`-free:

* `ear_rest_not_closed` — no vertex of the tail lies in the *closed* ear
  triangle;
* `ear_exit_on_base` — every boundary point at which an edge leaves the triangle
  lies on the base `[c, a]` (the two ear sides are edges of the polygon, so
  simplicity and `polyCycNondeg` exclude them);
* `ear_edge_interior_not_strict` — no interior point of an edge lies in the
  strict interior of the triangle (two base exits force the base coordinate,
  which is affine along the edge, to vanish at the point);
* `ear_base_collinear_case`, `ear_edge_interior_not_base` — no interior point of
  an edge lies on the base either: either a short step reaches the strict
  interior, or the whole edge is collinear with the base and then `a` or `c`
  would lie in the interior of that edge.

The two conclusions are consumed by `flatSeam_avoids_ear`
(`RequestProject.SAWUmlaufFlatSeamLift`).
-/

open Real Complex

noncomputable section

namespace HexArea

/-- Along a segment the cross product is an affine function of the parameter. -/
lemma cross_affine (u w x y : ℂ) (t : ℝ) :
    cross u (((1 - t) • x + t • y) - w) = (1 - t) * cross u (x - w) + t * cross u (y - w) := by
  simp [cross, Complex.real_smul, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im]
  ring

/-- **The closed triangle `a, b, c`, in orientation-free scaled form.**  Each of
the three edge cross products is multiplied by the triangle orientation
`cross (b-a) (c-b)`, so the predicate is insensitive to the orientation of the
triple (and is empty when the triple is degenerate). -/
def inTriangleClosed (a b c x : ℂ) : Prop :=
  0 ≤ cross (b - a) (x - a) * cross (b - a) (c - b) ∧
  0 ≤ cross (c - b) (x - b) * cross (b - a) (c - b) ∧
  0 ≤ cross (a - c) (x - c) * cross (b - a) (c - b)

/-- The strict interior is contained in the closed triangle. -/
lemma inTriangleClosed_of_strict (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    inTriangleClosed a b c x := by
  have hsum := cross_bary_sum a b c x
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hD : 0 < cross (b - a) (c - b) := by linarith
    exact ⟨by positivity, by positivity, by positivity⟩
  · have hD : cross (b - a) (c - b) < 0 := by linarith
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- The base side `[a, c]` is contained in the closed triangle, and the third
cross product vanishes there. -/
lemma inTriangleClosed_of_mem_ac (a b c x : ℂ) (h : x ∈ segment ℝ a c) :
    inTriangleClosed a b c x ∧ cross (a - c) (x - c) = 0 := by
  obtain ⟨α, γ, hα, hγ, hsum, hx⟩ := h
  have hx' : x = (α : ℂ) * a + (γ : ℂ) * c := by
    rw [← hx]; simp [Complex.real_smul]
  have hα' : (α : ℝ) = 1 - γ := by linarith
  have e1 : cross (b - a) (x - a) = γ * cross (b - a) (c - b) := by
    rw [hx', hα']; simp [cross, Complex.mul_re, Complex.mul_im]; ring
  have e3 : cross (a - c) (x - c) = 0 := by
    rw [hx', hα']; simp [cross, Complex.mul_re, Complex.mul_im]; ring
  have e2 : cross (c - b) (x - b) = α * cross (b - a) (c - b) := by
    rw [hx', hα']; simp [cross, Complex.mul_re, Complex.mul_im]; ring
  refine ⟨⟨?_, ?_, ?_⟩, e3⟩
  · rw [e1]; nlinarith [sq_nonneg (cross (b - a) (c - b))]
  · rw [e2]; nlinarith [sq_nonneg (cross (b - a) (c - b))]
  · rw [e3]; simp

/-- A point of the closed triangle whose `c`-weight vanishes lies on the side
`[a, b]`.  Barycentric reconstruction (`cross_bary_recon`). -/
lemma mem_side_ab_of_closed (a b c x : ℂ) (hD : cross (b - a) (c - b) ≠ 0)
    (h : inTriangleClosed a b c x) (h1 : cross (b - a) (x - a) = 0) :
    x ∈ segment ℝ a b := by
  obtain ⟨-, h2, h3⟩ := h
  set D := cross (b - a) (c - b) with hDdef
  have hsum := cross_bary_sum a b c x
  rw [h1] at hsum
  have hrecon := cross_bary_recon a b c x
  rw [h1] at hrecon
  have hDC : (D : ℂ) ≠ 0 := by simpa using hD
  refine ⟨cross (c - b) (x - b) / D, cross (a - c) (x - c) / D, ?_, ?_, ?_, ?_⟩
  · rw [div_eq_mul_inv]
    rcases lt_or_gt_of_ne hD with h | h
    · have hinv : (D : ℝ)⁻¹ < 0 := inv_neg''.mpr h
      nlinarith
    · have hinv : (0 : ℝ) < (D : ℝ)⁻¹ := by positivity
      nlinarith
  · rw [div_eq_mul_inv]
    rcases lt_or_gt_of_ne hD with h | h
    · have hinv : (D : ℝ)⁻¹ < 0 := inv_neg''.mpr h
      nlinarith
    · have hinv : (0 : ℝ) < (D : ℝ)⁻¹ := by positivity
      nlinarith
  · field_simp
    linarith [hsum]
  · have hrec : (D : ℂ) • x
        = (cross (c - b) (x - b) : ℝ) • a + (cross (a - c) (x - c) : ℝ) • b := by
      simpa using hrecon
    simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_div] at hrec ⊢
    field_simp
    linear_combination -hrec

/-- The closed triangle predicate is invariant under cyclic rotation of the
vertex triple. -/
lemma inTriangleClosed_cyc (a b c x : ℂ) :
    inTriangleClosed a b c x ↔ inTriangleClosed b c a x := by
  have hD : cross (c - b) (a - c) = cross (b - a) (c - b) := by
    simp [cross]; ring
  unfold inTriangleClosed
  rw [hD]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h3, h1⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h3, h1, h2⟩

/-- A point of the closed triangle whose `a`-weight vanishes lies on `[b, c]`. -/
lemma mem_side_bc_of_closed (a b c x : ℂ) (hD : cross (b - a) (c - b) ≠ 0)
    (h : inTriangleClosed a b c x) (h2 : cross (c - b) (x - b) = 0) :
    x ∈ segment ℝ b c := by
  have hD' : cross (c - b) (a - c) ≠ 0 := by
    rw [show cross (c - b) (a - c) = cross (b - a) (c - b) by simp [cross]; ring]; exact hD
  exact mem_side_ab_of_closed b c a x hD' ((inTriangleClosed_cyc a b c x).mp h) h2

/-- A point of the closed triangle whose `b`-weight vanishes lies on `[c, a]`. -/
lemma mem_side_ca_of_closed (a b c x : ℂ) (hD : cross (b - a) (c - b) ≠ 0)
    (h : inTriangleClosed a b c x) (h3 : cross (a - c) (x - c) = 0) :
    x ∈ segment ℝ c a := by
  have hD' : cross (a - c) (b - a) ≠ 0 := by
    rw [show cross (a - c) (b - a) = cross (b - a) (c - b) by simp [cross]; ring]; exact hD
  refine mem_side_ab_of_closed c a b x hD' ?_ h3
  exact (inTriangleClosed_cyc b c a x).mp ((inTriangleClosed_cyc a b c x).mp h)

/-- **First exit from the closed triangle.**  On the segment from a point `x` of
the closed triangle to a point `y` outside it there is a point `z` of the closed
triangle at which one of the three edge cross products vanishes — i.e. a point of
the boundary, lying (by the three side lemmas above) on one of the three closed
sides.

The proof is the intermediate value theorem applied to the minimum of the three
scaled cross products, which is continuous (each is affine in the parameter by
`cross_affine`), nonnegative at `x` and negative at `y`. -/
lemma exit_point (a b c x y : ℂ) (hx : inTriangleClosed a b c x)
    (hy : ¬ inTriangleClosed a b c y) :
    ∃ z ∈ segment ℝ x y, inTriangleClosed a b c z ∧
      (cross (b - a) (z - a) * cross (b - a) (c - b) = 0 ∨
       cross (c - b) (z - b) * cross (b - a) (c - b) = 0 ∨
       cross (a - c) (z - c) * cross (b - a) (c - b) = 0) := by
  set D := cross (b - a) (c - b) with hD
  set f : ℝ → ℝ := fun t =>
    min (min (cross (b - a) (((1 - t) • x + t • y) - a) * D)
             (cross (c - b) (((1 - t) • x + t • y) - b) * D))
        (cross (a - c) (((1 - t) • x + t • y) - c) * D) with hf
  have hcont : Continuous f := by
    rw [hf]
    refine Continuous.min (Continuous.min ?_ ?_) ?_ <;>
      · simp only [cross_affine]
        fun_prop
  have hf0 : 0 ≤ f 0 := by
    rw [hf]
    simp only [cross_affine]
    obtain ⟨h1, h2, h3⟩ := hx
    simp only [sub_zero, one_mul, zero_mul, add_zero, le_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simpa using by linarith
  have hf1 : f 1 < 0 := by
    rw [hf]
    simp only [cross_affine]
    simp only [sub_self, zero_mul, one_mul, zero_add, min_lt_iff]
    rcases not_and_or.mp hy with h | h
    · left; left; simpa using lt_of_not_ge h
    · rcases not_and_or.mp h with h | h
      · left; right; simpa using lt_of_not_ge h
      · right; simpa using lt_of_not_ge h
  obtain ⟨t, ht, hteq⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, f t = 0 := by
    have hIVT := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn
    exact hIVT ⟨le_of_lt hf1, hf0⟩
  set z : ℂ := (1 - t) • x + t • y with hz
  have hmin : min (min (cross (b - a) (z - a) * D) (cross (c - b) (z - b) * D))
      (cross (a - c) (z - c) * D) = 0 := hteq
  refine ⟨z, ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, rfl⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← hmin]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  · rw [← hmin]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  · rw [← hmin]; exact min_le_right _ _
  · rcases min_cases (min (cross (b - a) (z - a) * D) (cross (c - b) (z - b) * D))
      (cross (a - c) (z - c) * D) with ⟨he, -⟩ | ⟨he, -⟩
    · rw [he] at hmin
      rcases min_cases (cross (b - a) (z - a) * D) (cross (c - b) (z - b) * D) with
        ⟨he2, -⟩ | ⟨he2, -⟩
      · exact Or.inl (by rw [← he2]; exact hmin)
      · exact Or.inr (Or.inl (by rw [← he2]; exact hmin))
    · exact Or.inr (Or.inr (by rw [← he]; exact hmin))


/-- A point of the closed triangle at which all three scaled cross products are
*strictly* positive lies in the strict interior. -/
lemma inTriangleStrict_of_closed_pos (a b c x : ℂ)
    (h1 : 0 < cross (b - a) (x - a) * cross (b - a) (c - b))
    (h2 : 0 < cross (c - b) (x - b) * cross (b - a) (c - b))
    (h3 : 0 < cross (a - c) (x - c) * cross (b - a) (c - b)) :
    inTriangleStrict a b c x := by
  rcases lt_trichotomy (cross (b - a) (c - b)) 0 with hD | hD | hD
  · exact Or.inr ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rw [hD] at h1; simp at h1
  · exact Or.inl ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- Two segments emanating from the same point `a` and sharing a second point are
collinear. -/
lemma cross_eq_zero_of_shared_ray (a b p z : ℂ) (hz1 : z ∈ segment ℝ a b)
    (hz2 : z ∈ segment ℝ a p) (hza : z ≠ a) :
    cross (b - a) (p - a) = 0 := by
  obtain ⟨α1, β1, hα1, hβ1, hsum1, h1⟩ := hz1
  obtain ⟨α2, β2, hα2, hβ2, hsum2, h2⟩ := hz2
  have e1 : z - a = (β1 : ℂ) * (b - a) := by
    rw [← h1]; simp [Complex.real_smul]
    have hc : (α1 : ℂ) = 1 - β1 := by
      have h : α1 = 1 - β1 := by linarith
      rw [h]; push_cast; ring
    rw [hc]; ring
  have e2 : z - a = (β2 : ℂ) * (p - a) := by
    rw [← h2]; simp [Complex.real_smul]
    have hc : (α2 : ℂ) = 1 - β2 := by
      have h : α2 = 1 - β2 := by linarith
      rw [h]; push_cast; ring
    rw [hc]; ring
  have hβ1' : β1 ≠ 0 := by
    intro h; rw [h] at e1; simp at e1; exact hza (by linear_combination e1)
  have hβ2' : β2 ≠ 0 := by
    intro h; rw [h] at e2; simp at e2; exact hza (by linear_combination e2)
  have hβ1C : (β1 : ℂ) ≠ 0 := by simpa using hβ1'
  have hβ2C : (β2 : ℂ) ≠ 0 := by simpa using hβ2'
  have hb : b - a = (β1 : ℂ)⁻¹ * (z - a) := by
    rw [e1, ← mul_assoc, inv_mul_cancel₀ hβ1C, one_mul]
  have hp : p - a = (β2 : ℂ)⁻¹ * (z - a) := by
    rw [e2, ← mul_assoc, inv_mul_cancel₀ hβ2C, one_mul]
  rw [hb, hp]
  simp [cross, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im]
  ring

/-- An endpoint of a segment does not lie on the segment joining an interior
point to the other endpoint. -/
lemma not_mem_segment_of_openSegment (p q v : ℂ) (hpq : p ≠ q)
    (hv : v ∈ openSegment ℝ p q) : q ∉ segment ℝ v p := by
  obtain ⟨s1, s2, hs1, hs2, hsum, hv'⟩ := hv
  rintro ⟨α, β, hα, hβ, hsum2, hq⟩
  have hv'' : v = (s1 : ℂ) * p + (s2 : ℂ) * q := by
    rw [← hv']; simp [Complex.real_smul]
  have hq' : q = (α : ℂ) * v + (β : ℂ) * p := by
    rw [← hq]; simp [Complex.real_smul]
  rw [hv''] at hq'
  have key : ((1 - α * s2 : ℝ) : ℂ) * (q - p) = 0 := by
    have hab : (β : ℂ) = 1 - α := by
      have h : β = 1 - α := by linarith
      rw [h]; push_cast; ring
    have hs : (s1 : ℂ) = 1 - s2 := by
      have h : s1 = 1 - s2 := by linarith
      rw [h]; push_cast; ring
    rw [hab, hs] at hq'
    push_cast
    linear_combination hq'
  have hqp : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have hz : ((1 - α * s2 : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · exact absurd h hqp
  have hreal : (1 : ℝ) - α * s2 = 0 := by exact_mod_cast hz
  nlinarith

end HexArea

/-! ## Cyclic successors and predecessors are unique -/

/-- In a `Nodup` cycle each vertex has a unique cyclic successor. -/
lemma closedEdges_succ_unique (V : List ℂ) (hnd : V.Nodup) (x y z : ℂ)
    (h1 : (x, y) ∈ closedEdges V) (h2 : (x, z) ∈ closedEdges V) : y = z := by
  simp only [closedEdges, List.mem_iff_getElem] at h1 h2
  obtain ⟨i, hi, hie⟩ := h1
  obtain ⟨j, hj, hje⟩ := h2
  rw [List.length_zip, List.length_rotate, min_self] at hi hj
  rw [List.getElem_zip] at hie hje
  have hxi : V[i] = x := congrArg Prod.fst hie
  have hxj : V[j] = x := congrArg Prod.fst hje
  have hij : i = j :=
    (List.Nodup.getElem_inj_iff hnd (i := i) (j := j) (hi := hi) (hj := hj)).mp (by rw [hxi, hxj])
  subst hij
  have h : (x, y) = (x, z) := by rw [← hie, ← hje]
  exact congrArg Prod.snd h

/-- In a `Nodup` cycle each vertex has a unique cyclic predecessor. -/
lemma closedEdges_pred_unique (V : List ℂ) (hnd : V.Nodup) (x y z : ℂ)
    (h1 : (y, x) ∈ closedEdges V) (h2 : (z, x) ∈ closedEdges V) : y = z := by
  simp only [closedEdges, List.mem_iff_getElem] at h1 h2
  obtain ⟨i, hi, hie⟩ := h1
  obtain ⟨j, hj, hje⟩ := h2
  rw [List.length_zip, List.length_rotate, min_self] at hi hj
  rw [List.getElem_zip] at hie hje
  have hxi : (V.rotate 1)[i]'(by simpa using hi) = x := congrArg Prod.snd hie
  have hxj : (V.rotate 1)[j]'(by simpa using hj) = x := congrArg Prod.snd hje
  have hndr : (V.rotate 1).Nodup := List.nodup_rotate.mpr hnd
  have hij : i = j :=
    (List.Nodup.getElem_inj_iff hndr (i := i) (j := j) (hi := by simpa using hi)
      (hj := by simpa using hj)).mp (by rw [hxi, hxj])
  subst hij
  have h : (y, x) = (z, x) := by rw [← hie, ← hje]
  exact congrArg Prod.fst h

/-! ## The vertices of an empty ear's tail are outside the closed triangle -/

/-- **No vertex of the tail lies in the CLOSED ear triangle.**  For an empty ear
`a, b, c` of a simple polygon `L` with at least four vertices, a vertex of the
tail lies neither in the strict interior (`hempty`), nor on the base `[a, c]`
(`hdiag`), nor on the two ear sides `[a, b]`, `[b, c]` — the latter are edges of
`L`, so `simple_vertex_not_on_far_edge` applies. -/
lemma ear_rest_not_closed (L : List ℂ) (h4 : 4 ≤ L.length) (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (x : ℂ) (hx : x ∈ rest) : ¬ HexArea.inTriangleClosed a b c x := by
  have hnd : (a :: b :: c :: rest).Nodup := hrot ▸ (List.nodup_rotate.mpr hsimple.1)
  have hxL : x ∈ L := by
    rw [← List.mem_rotate (n := ρ), hrot]; simp [hx]
  have hxa : x ≠ a := by intro h; simp at hnd; rw [h] at hx; tauto
  have hxb : x ≠ b := by intro h; simp at hnd; rw [h] at hx; tauto
  have hxc : x ≠ c := by intro h; simp at hnd; rw [h] at hx; tauto
  have hab : (a, b) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L ρ, hrot]; simp [closedEdges]
  have hbc : (b, c) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L ρ, hrot]; simp [closedEdges]
  rintro ⟨h1, h2, h3⟩
  rcases eq_or_lt_of_le h1 with he1 | hlt1
  · have hf1 : HexArea.cross (b - a) (x - a) = 0 := by
      rcases mul_eq_zero.mp he1.symm with h | h
      · exact h
      · exact absurd h hD
    exact simple_vertex_not_on_far_edge L h4 hsimple x hxL (a, b) hab hxa hxb
      (HexArea.mem_side_ab_of_closed a b c x hD ⟨h1, h2, h3⟩ hf1)
  rcases eq_or_lt_of_le h2 with he2 | hlt2
  · have hf2 : HexArea.cross (c - b) (x - b) = 0 := by
      rcases mul_eq_zero.mp he2.symm with h | h
      · exact h
      · exact absurd h hD
    exact simple_vertex_not_on_far_edge L h4 hsimple x hxL (b, c) hbc hxb hxc
      (HexArea.mem_side_bc_of_closed a b c x hD ⟨h1, h2, h3⟩ hf2)
  rcases eq_or_lt_of_le h3 with he3 | hlt3
  · have hf3 : HexArea.cross (a - c) (x - c) = 0 := by
      rcases mul_eq_zero.mp he3.symm with h | h
      · exact h
      · exact absurd h hD
    have hmem := HexArea.mem_side_ca_of_closed a b c x hD ⟨h1, h2, h3⟩ hf3
    rw [segment_symm] at hmem
    exact hdiag x hx hmem
  exact hempty x hx (HexArea.inTriangleStrict_of_closed_pos a b c x hlt1 hlt2 hlt3)


/-- In a `Nodup` cycle with at least two vertices, the two endpoints of a cyclic
edge are distinct. -/
lemma closedEdges_ne (V : List ℂ) (hnd : V.Nodup) (h2 : 2 ≤ V.length) (x y : ℂ)
    (h : (x, y) ∈ closedEdges V) : x ≠ y := by
  simp only [closedEdges, List.mem_iff_getElem] at h
  obtain ⟨i, hi, hie⟩ := h
  rw [List.length_zip, List.length_rotate, min_self] at hi
  rw [List.getElem_zip] at hie
  have hx : V[i] = x := congrArg Prod.fst hie
  have hy : (V.rotate 1)[i]'(by simpa using hi) = y := congrArg Prod.snd hie
  rw [List.getElem_rotate] at hy
  intro hxy
  have hlt : (i + 1) % V.length < V.length := Nat.mod_lt _ (by omega)
  have heq : i = (i + 1) % V.length := by
    refine (List.Nodup.getElem_inj_iff hnd (i := i) (j := (i + 1) % V.length)
      (hi := hi) (hj := hlt)).mp ?_
    rw [hx, hxy, ← hy]
  rcases Nat.lt_or_ge (i + 1) V.length with hlt2 | hge
  · rw [Nat.mod_eq_of_lt hlt2] at heq; omega
  · have he : i + 1 = V.length := by omega
    rw [he, Nat.mod_self] at heq
    omega

namespace HexArea

/-- The vertex `a` lies in the closed triangle. -/
lemma inTriangleClosed_vertex_a (a b c : ℂ) : inTriangleClosed a b c a := by
  have e1 : cross (b - a) (a - a) = 0 := by simp [cross]
  have e3 : cross (a - c) (a - c) = 0 := by simp [cross]; ring
  have e2 : cross (c - b) (a - b) = cross (b - a) (c - b) := by simp [cross]; ring
  refine ⟨by rw [e1]; simp, ?_, by rw [e3]; simp⟩
  rw [e2]; nlinarith [sq_nonneg (cross (b - a) (c - b))]

/-- The vertex `c` lies in the closed triangle. -/
lemma inTriangleClosed_vertex_c (a b c : ℂ) : inTriangleClosed a b c c := by
  have e2 : cross (c - b) (c - b) = 0 := by simp [cross]; ring
  have e3 : cross (a - c) (c - c) = 0 := by simp [cross]
  have e1 : cross (b - a) (c - a) = cross (b - a) (c - b) := by simp [cross]; ring
  refine ⟨?_, by rw [e2]; simp, by rw [e3]; simp⟩
  rw [e1]; nlinarith [sq_nonneg (cross (b - a) (c - b))]

end HexArea

/-- **Every exit of an edge from the ear triangle lies on the base `[c, a]`.**

This is the heart of the ear-clearance property.  Let `a, b, c` be an ear of the
simple, cyclically non-degenerate polygon `L`, let `(p, q)` be a cyclic edge with
`b ∉ {p, q}` and let `v` be an interior point of that edge.  If `y ∈ {p, q}` lies
outside the closed triangle and `z` — on the segment from `v` to `y` — is a point
of the closed triangle at which one of the three edge cross products vanishes
(i.e. a boundary point, as produced by `HexArea.exit_point`), then `z` lies on the
base side `[c, a]`.

Indeed `z` cannot lie on the ear side `[a, b]`: the edges `(a, b)` and `(p, q)`
of `L` are then disjoint by simplicity unless they share the endpoint `a` — which
forces `q = a` (an ordered cyclic edge cannot start at `a`, else it would end at
`b`), and then `z ≠ a` and the two segments from `a` are collinear, making the
corner of `L` at `a` degenerate, contrary to `polyCycNondeg L`.  Symmetrically for
the ear side `[b, c]` with the corner at `c`. -/
lemma ear_exit_on_base (L : List ℂ) (h4 : 4 ≤ L.length) (hsimple : PolygonSimple L)
    (hndL : polyCycNondeg L)
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
  have hlen : (a :: b :: c :: rest).length = L.length := by rw [← hrot]; simp
  have hrest : rest ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  obtain ⟨q₀, tl0, hrest0⟩ : ∃ q₀ tl0, rest = q₀ :: tl0 := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons q₀ tl0 => exact ⟨q₀, tl0, rfl⟩
  obtain ⟨mid, p₀, hrest1⟩ : ∃ mid p₀, rest = mid ++ [p₀] := by
    rcases List.eq_nil_or_concat rest with h | ⟨mid, p₀, hh⟩
    · exact absurd h hrest
    · exact ⟨mid, p₀, by simpa using hh⟩
  have hab : (a, b) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L ρ, hrot]; simp [closedEdges]
  have hbc : (b, c) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L ρ, hrot]; simp [closedEdges]
  have hcq0 : (c, q₀) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L ρ, hrot, hrest0]; simp [closedEdges]
  have hrot2 : L.rotate (ρ + (mid.length + 3)) = p₀ :: a :: b :: c :: mid := by
    rw [← List.rotate_rotate, hrot, hrest1, List.rotate_eq_drop_append_take (by simp)]
    simp
  have hp0a : (p₀, a) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L (ρ + (mid.length + 3)), hrot2]; simp [closedEdges]
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
    · have hya : y = p := by
        rcases hy with h | h
        · exact h
        · exact absurd (by rw [h, hqa]; exact HexArea.inTriangleClosed_vertex_a a b c) hyout
      have hza : z ≠ a := by
        intro h
        refine HexArea.not_mem_segment_of_openSegment p q v hpqne hv ?_
        rw [hqa, ← h, ← hya]; exact hzy
      have hzap : z ∈ segment ℝ a p := by
        have hv' : v ∈ segment ℝ a p := by rw [← hqa, segment_symm]; exact hvseg
        exact (convex_segment a p).segment_subset hv' (right_mem_segment ℝ a p) (hya ▸ hzy)
      have hcol := HexArea.cross_eq_zero_of_shared_ray a b p z hzab hzap hza
      have hp0 : p = p₀ := closedEdges_pred_unique L hNodup a p p₀ (hqa ▸ hpq) hp0a
      have hcorner : HexArea.cross (a - p₀) (b - a) ≠ 0 :=
        polyCycNondeg_rotate_head L p₀ a b (c :: mid) (ρ + (mid.length + 3)) (by omega) hndL hrot2
      apply hcorner
      rw [← hp0]
      have hid : HexArea.cross (a - p) (b - a) = HexArea.cross (b - a) (p - a) := by
        simp [HexArea.cross]; ring
      rw [hid]; exact hcol
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
    · have hyq : y = q := by
        rcases hy with h | h
        · exact absurd (by rw [h, hpc]; exact HexArea.inTriangleClosed_vertex_c a b c) hyout
        · exact h
      have hzcne : z ≠ c := by
        intro h
        refine HexArea.not_mem_segment_of_openSegment q p v (Ne.symm hpqne) ?_ ?_
        · rw [openSegment_symm]; exact hv
        · rw [hpc, ← h, ← hyq]; exact hzy
      have hzcq : z ∈ segment ℝ c q := by
        have hv' : v ∈ segment ℝ c q := by rw [← hpc]; exact hvseg
        exact (convex_segment c q).segment_subset hv' (right_mem_segment ℝ c q) (hyq ▸ hzy)
      have hzcb : z ∈ segment ℝ c b := by rw [segment_symm]; exact hzbc
      have hcol := HexArea.cross_eq_zero_of_shared_ray c b q z hzcb hzcq hzcne
      have hq0 : q = q₀ := closedEdges_succ_unique L hNodup c q q₀ (hpc ▸ hpq) hcq0
      have hrot3 : L.rotate (ρ + 1) = b :: c :: q₀ :: (tl0 ++ [a]) := by
        rw [← List.rotate_rotate, hrot, hrest0, HexArea.rotate_one_cons]
        simp
      have hcorner : HexArea.cross (c - b) (q₀ - c) ≠ 0 :=
        polyCycNondeg_rotate_head L b c q₀ (tl0 ++ [a]) (ρ + 1) (by omega) hndL hrot3
      apply hcorner
      rw [← hq0]
      have hid : HexArea.cross (c - b) (q - c) = - HexArea.cross (b - c) (q - c) := by
        simp [HexArea.cross]; ring
      rw [hid, hcol]; simp
    · have hdisj := hsimple.2 (b, c) hbc (p, q) hpq (by simpa using hbp) (by simpa using hbq)
        (by simpa using (Ne.symm hpc)) (by simpa using (Ne.symm hqc))
      exact Set.disjoint_left.mp hdisj hzbc hzpq
  · -- `z` lies on the base `[c, a]`
    have hf3 : HexArea.cross (a - c) (z - c) = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h hD
    exact HexArea.mem_side_ca_of_closed a b c z hD hzc hf3

/-! ## Auxiliary segment lemmas -/

/-- Both endpoints of a cyclic edge are vertices. -/
lemma mem_of_mem_closedEdges (V : List ℂ) (x y : ℂ) (h : (x, y) ∈ closedEdges V) :
    x ∈ V ∧ y ∈ V := by
  simp only [closedEdges, List.mem_iff_getElem] at h
  obtain ⟨i, hi, hie⟩ := h
  rw [List.length_zip, List.length_rotate, min_self] at hi
  rw [List.getElem_zip] at hie
  have hx : V[i] = x := congrArg Prod.fst hie
  have hy : (V.rotate 1)[i]'(by simpa using hi) = y := congrArg Prod.snd hie
  refine ⟨hx ▸ List.getElem_mem hi, ?_⟩
  rw [← hy]
  exact List.mem_rotate.mp (List.getElem_mem (by simpa using hi))

namespace HexArea

/-- The scaled base coordinate is strictly positive in the strict interior. -/
lemma scaled_pos_of_strict (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    0 < cross (a - c) (x - c) * cross (b - a) (c - b) := by
  have hsum := cross_bary_sum a b c x
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hD : 0 < cross (b - a) (c - b) := by linarith
    positivity
  · have hD : cross (b - a) (c - b) < 0 := by linarith
    nlinarith

end HexArea

/-- Explicit convex combination: a point with affine parameter `u` between the
parameters `A < u < B` of two points of a line lies on the segment joining
them. -/
lemma mem_segment_of_param_between (p q v z₁ z₂ : ℂ) (A B u : ℝ)
    (hA : A < u) (hB : u < B)
    (hz1 : z₁ = ((1 - A : ℝ) : ℂ) * p + (A : ℂ) * q)
    (hz2 : z₂ = ((1 - B : ℝ) : ℂ) * p + (B : ℂ) * q)
    (hv : v = ((1 - u : ℝ) : ℂ) * p + (u : ℂ) * q) : v ∈ segment ℝ z₁ z₂ := by
  have hBA : 0 < B - A := by linarith
  set μ : ℝ := (u - A) / (B - A) with hμ
  have hμ0 : 0 ≤ μ := div_nonneg (by linarith) (le_of_lt hBA)
  have hμ1 : μ ≤ 1 := by rw [hμ, div_le_one hBA]; linarith
  refine ⟨1 - μ, μ, by linarith, hμ0, by ring, ?_⟩
  simp only [Complex.real_smul]
  rw [hz1, hz2, hv]
  have hkey : (1 - μ) * A + μ * B = u := by
    rw [hμ]; field_simp; ring
  have hkeyC : ((1 - μ : ℝ) : ℂ) * (A : ℂ) + ((μ : ℝ) : ℂ) * (B : ℂ) = (u : ℂ) := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hkey
  push_cast at hkeyC ⊢
  linear_combination (q - p) * hkeyC

/-- If `v` is interior to `[p, q]` and `z₁ ≠ v`, `z₂ ≠ v` lie on `[v, p]`,
`[v, q]` respectively, then `v` lies between `z₁` and `z₂`. -/
lemma mem_segment_of_between (p q v z₁ z₂ : ℂ) (hv : v ∈ openSegment ℝ p q)
    (h1 : z₁ ∈ segment ℝ v p) (h2 : z₂ ∈ segment ℝ v q) (hz1 : z₁ ≠ v) (hz2 : z₂ ≠ v) :
    v ∈ segment ℝ z₁ z₂ := by
  obtain ⟨u1, u, hu1, hu, husum, hvdef⟩ := hv
  obtain ⟨α1, s1, hα1, hs1, hsum1, hz1def⟩ := h1
  obtain ⟨α2, s2, hα2, hs2, hsum2, hz2def⟩ := h2
  have hvC : v = ((1 - u : ℝ) : ℂ) * p + (u : ℂ) * q := by
    rw [← hvdef]
    simp only [Complex.real_smul]
    push_cast
    have h : (u1 : ℂ) = 1 - u := by
      have hh : u1 = 1 - u := by linarith
      rw [hh]; push_cast; ring
    rw [h]
  have hs1pos : 0 < s1 := by
    rcases eq_or_lt_of_le hs1 with h | h
    · exfalso; apply hz1
      rw [← hz1def, ← h]
      simp only [Complex.real_smul]
      have hh : (α1 : ℂ) = 1 := by
        have h1 : α1 = 1 := by linarith
        rw [h1]; norm_num
      rw [hh]; push_cast; ring
    · exact h
  have hs2pos : 0 < s2 := by
    rcases eq_or_lt_of_le hs2 with h | h
    · exfalso; apply hz2
      rw [← hz2def, ← h]
      simp only [Complex.real_smul]
      have hh : (α2 : ℂ) = 1 := by
        have h1 : α2 = 1 := by linarith
        rw [h1]; norm_num
      rw [hh]; push_cast; ring
    · exact h
  have hu1' : u < 1 := by linarith
  refine mem_segment_of_param_between p q v z₁ z₂ (α1 * u) (s2 + α2 * u) u ?_ ?_ ?_ ?_ hvC
  · nlinarith
  · nlinarith
  · rw [← hz1def, hvC]
    simp only [Complex.real_smul]
    have hα : (α1 : ℂ) = 1 - s1 := by
      have h : α1 = 1 - s1 := by linarith
      rw [h]; push_cast; ring
    push_cast
    rw [hα]
    ring
  · rw [← hz2def, hvC]
    simp only [Complex.real_smul]
    have hα : (α2 : ℂ) = 1 - s2 := by
      have h : α2 = 1 - s2 := by linarith
      rw [h]; push_cast; ring
    push_cast
    rw [hα]
    ring

/-! ## Clearance of an empty ear -/

/-- **No interior point of an edge lies in the strict interior of the ear
triangle (PROVED).**

Let `L` be a simple, cyclically non-degenerate polygon with at least four
vertices carrying the empty ear `a, b, c` (`hempty`, `hdiag`), and let `(p, q)`
be a cyclic edge of `L` with `b ∉ {p, q}`.  Then no interior point `v` of that
edge lies strictly inside the triangle `a, b, c`.

Proof.  Towards each endpoint `w ∈ {p, q}` there is a point `z_w ≠ v` of the
segment `[v, w]` on the base line of the triangle: if `w` is outside the closed
triangle (which is the case for every vertex of the tail, by
`ear_rest_not_closed`) then `HexArea.exit_point` produces a boundary point, which
lies on the base by `ear_exit_on_base`; and if `w` is inside the closed triangle
then `w ∈ {a, c}`, which lies on the base line itself.  As `v` lies between
`z_p` and `z_q` (`mem_segment_of_between`) and the base coordinate is affine
(`HexArea.cross_affine`), the base coordinate of `v` vanishes — contradicting
strict interiority. -/
lemma ear_edge_interior_not_strict (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L) (hndL : polyCycNondeg L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (p q : ℂ) (hpq : (p, q) ∈ closedEdges L) (hbp : b ≠ p) (hbq : b ≠ q)
    (v : ℂ) (hv : v ∈ openSegment ℝ p q) :
    ¬ HexArea.inTriangleStrict a b c v := by
  intro hstrict
  have hD : HexArea.cross (b - a) (c - b) ≠ 0 :=
    polyCycNondeg_rotate_head L a b c rest ρ (by omega) hndL hrot
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
        ear_exit_on_base L h4 hsimple hndL ρ a b c rest hrot hD p q hpq hbp hbq v hv w hw
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

/-! ## The base case of the clearance property -/

namespace HexArea

/-- In the relative interior of the base the two other scaled cross products are
strictly positive. -/
lemma scaled_pos_of_mem_openSegment_ac (a b c x : ℂ) (hD : cross (b - a) (c - b) ≠ 0)
    (h : x ∈ openSegment ℝ a c) :
    0 < cross (b - a) (x - a) * cross (b - a) (c - b) ∧
    0 < cross (c - b) (x - b) * cross (b - a) (c - b) ∧
    cross (a - c) (x - c) = 0 := by
  obtain ⟨α, γ, hα, hγ, hsum, hx⟩ := h
  have hx' : x = (α : ℂ) * a + (γ : ℂ) * c := by
    rw [← hx]; simp [Complex.real_smul]
  have hα' : (α : ℝ) = 1 - γ := by linarith
  have e1 : cross (b - a) (x - a) = γ * cross (b - a) (c - b) := by
    rw [hx', hα']; simp [cross, Complex.mul_re, Complex.mul_im]; ring
  have e3 : cross (a - c) (x - c) = 0 := by
    rw [hx', hα']; simp [cross, Complex.mul_re, Complex.mul_im]; ring
  have e2 : cross (c - b) (x - b) = α * cross (b - a) (c - b) := by
    rw [hx', hα']; simp [cross, Complex.mul_re, Complex.mul_im]; ring
  refine ⟨?_, ?_, e3⟩
  · rw [e1]; have := mul_self_pos.mpr hD; nlinarith
  · rw [e2]; have := mul_self_pos.mpr hD; nlinarith

end HexArea

/-- Moving from an interior point of a segment towards one of its endpoints stays
in the open segment. -/
lemma openSegment_perturb (p q v w : ℂ) (hv : v ∈ openSegment ℝ p q) (hw : w = p ∨ w = q)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : (1 - t) • v + t • w ∈ openSegment ℝ p q := by
  obtain ⟨u1, u, hu1, hu, husum, hvdef⟩ := hv
  rcases hw with rfl | rfl
  · refine ⟨(1 - t) * u1 + t, (1 - t) * u, by nlinarith, by nlinarith, by nlinarith, ?_⟩
    rw [← hvdef]
    simp only [Complex.real_smul]
    push_cast
    ring
  · refine ⟨(1 - t) * u1, (1 - t) * u + t, by nlinarith, by nlinarith, by nlinarith, ?_⟩
    rw [← hvdef]
    simp only [Complex.real_smul]
    push_cast
    ring

/-- A small step keeps an affine expression with positive value at `0` positive. -/
lemma exists_pos_combo (A B : ℝ) (hA : 0 < A) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1/2 ∧ 0 < (1 - t) * A + t * B := by
  have habs : (0:ℝ) ≤ |B| := abs_nonneg B
  have hden : 0 < 2 * (A + |B|) := by linarith
  refine ⟨min (1/2) (A / (2 * (A + |B|))), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  set t := min (1/2) (A / (2 * (A + |B|))) with ht
  have ht2 : t ≤ 1/2 := min_le_left _ _
  have ht3 : t ≤ A / (2 * (A + |B|)) := min_le_right _ _
  have hB : -|B| ≤ B := neg_abs_le B
  have h3 : 0 < t := lt_min (by norm_num) (by positivity)
  have h1 : t * |B| ≤ (A / (2 * (A + |B|))) * |B| := mul_le_mul_of_nonneg_right ht3 habs
  have h2 : (A / (2 * (A + |B|))) * |B| < A / 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  nlinarith

/-- The same for two affine expressions simultaneously. -/
lemma exists_pos_combo2 (A1 B1 A2 B2 : ℝ) (h1 : 0 < A1) (h2 : 0 < A2) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 0 < (1 - t) * A1 + t * B1 ∧ 0 < (1 - t) * A2 + t * B2 := by
  obtain ⟨t1, ht1, ht1', hS1⟩ := exists_pos_combo A1 B1 h1
  obtain ⟨t2, ht2, ht2', hS2⟩ := exists_pos_combo A2 B2 h2
  refine ⟨min t1 t2, lt_min ht1 ht2, by
    have := min_le_left t1 t2; linarith, ?_, ?_⟩
  · set t := min t1 t2 with ht
    have hle : t ≤ t1 := min_le_left _ _
    have hpos : 0 < t := lt_min ht1 ht2
    have key : t1 * ((1 - t) * A1 + t * B1) = (t1 - t) * A1 + t * ((1 - t1) * A1 + t1 * B1) := by
      ring
    nlinarith
  · set t := min t1 t2 with ht
    have hle : t ≤ t2 := min_le_right _ _
    have hpos : 0 < t := lt_min ht1 ht2
    have key : t2 * ((1 - t) * A2 + t * B2) = (t2 - t) * A2 + t * ((1 - t2) * A2 + t2 * B2) := by
      ring
    nlinarith

/-- **Perturbation into the strict interior.**  If `v` is on the base line of the
triangle with the two other scaled coordinates positive, and `w` is a point with
positive scaled base coordinate, then a short step from `v` towards `w` reaches
the strict interior. -/
lemma exists_strict_on_edge (a b c v w : ℂ)
    (hg1 : 0 < HexArea.cross (b - a) (v - a) * HexArea.cross (b - a) (c - b))
    (hg2 : 0 < HexArea.cross (c - b) (v - b) * HexArea.cross (b - a) (c - b))
    (hg3v : HexArea.cross (a - c) (v - c) = 0)
    (hg3w : 0 < HexArea.cross (a - c) (w - c) * HexArea.cross (b - a) (c - b)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ HexArea.inTriangleStrict a b c ((1 - t) • v + t • w) := by
  obtain ⟨t, ht0, ht1, hp1, hp2⟩ := exists_pos_combo2
    (HexArea.cross (b - a) (v - a) * HexArea.cross (b - a) (c - b))
    (HexArea.cross (b - a) (w - a) * HexArea.cross (b - a) (c - b))
    (HexArea.cross (c - b) (v - b) * HexArea.cross (b - a) (c - b))
    (HexArea.cross (c - b) (w - b) * HexArea.cross (b - a) (c - b)) hg1 hg2
  refine ⟨t, ht0, ht1, ?_⟩
  apply HexArea.inTriangleStrict_of_closed_pos
  · rw [HexArea.cross_affine]; nlinarith
  · rw [HexArea.cross_affine]; nlinarith
  · rw [HexArea.cross_affine, hg3v]; nlinarith

/-- Explicit convex combination along a line: a point whose line parameter lies
between those of `p` and `q` lies on the segment `[p, q]`. -/
lemma mem_segment_of_line_param (c d p q z : ℂ) (tp tq s : ℝ)
    (hp : p = c + (tp : ℂ) * d) (hq : q = c + (tq : ℂ) * d) (hz : z = c + (s : ℂ) * d)
    (hlt : tp < tq) (h1 : tp ≤ s) (h2 : s ≤ tq) : z ∈ segment ℝ p q := by
  have hden : 0 < tq - tp := by linarith
  set lam : ℝ := (s - tp) / (tq - tp) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (by linarith) (le_of_lt hden)
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hden]; linarith
  refine ⟨1 - lam, lam, by linarith, hlam0, by ring, ?_⟩
  have hkey : (1 - lam) * tp + lam * tq = s := by
    rw [hlam]; field_simp; ring
  have hkeyC : ((1 - lam : ℝ) : ℂ) * (tp : ℂ) + ((lam : ℝ) : ℂ) * (tq : ℂ) = (s : ℂ) := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hkey
  simp only [Complex.real_smul]
  rw [hp, hq, hz]
  push_cast at hkeyC ⊢
  linear_combination d * hkeyC

/-- **The collinear case of the base clearance (PROVED).**

Setting of `ear_edge_interior_not_base`, in the case where the cyclic edge
`(p, q)` lies entirely on the base *line* of the ear (both endpoints have
vanishing base coordinate), while an interior point `v` of the edge lies on the
base *segment* `[a, c]`.  This is impossible.

Proof.  Write every point `x` of the base line as `c + t (a - c)` (possible by
`exists_real_of_cross_zero`; `a ≠ c` because `L` is `Nodup`).  The parameters
satisfy `t_v ∈ [0, 1]` (as `v ∈ [a, c]`) and `t_v = (1 - u) t_p + u t_q` with
`u ∈ (0, 1)` (as `v` is interior to `[p, q]`), while `t_p, t_q ∉ (0, 1)`: a vertex
of the tail is outside the closed triangle, hence off `[c, a]`
(`ear_rest_not_closed`), and the only remaining possibilities are `p = c`
(`t_p = 0`) and `q = a` (`t_q = 1`).  Hence `0` or `1` lies between `t_p` and
`t_q`, i.e. `c` or `a` lies on the edge `(p, q)` without being an endpoint of it,
contradicting `simple_vertex_not_on_far_edge`; and `p = c` together with `q = a`
is impossible because the cyclic successor of `c` is the head of `rest`. -/
lemma ear_base_collinear_case (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (p q : ℂ) (hpq : (p, q) ∈ closedEdges L) (hbp : b ≠ p) (hbq : b ≠ q)
    (hp3 : HexArea.cross (a - c) (p - c) = 0) (hq3 : HexArea.cross (a - c) (q - c) = 0)
    (v : ℂ) (hv : v ∈ openSegment ℝ p q) (hvac : v ∈ segment ℝ a c) : False := by
  have hNodup : L.Nodup := hsimple.1
  have hrotNodup : (a :: b :: c :: rest).Nodup := hrot ▸ (List.nodup_rotate.mpr hNodup)
  have hac : a ≠ c := by simp at hrotNodup; tauto
  have hanr : a ∉ rest := by simp at hrotNodup; tauto
  have hd : a - c ≠ 0 := sub_ne_zero.mpr hac
  obtain ⟨tp, htp⟩ := exists_real_of_cross_zero (a - c) (p - c) hd hp3
  obtain ⟨tq, htq⟩ := exists_real_of_cross_zero (a - c) (q - c) hd hq3
  have hpC : p = c + (tp : ℂ) * (a - c) := by linear_combination htp
  have hqC : q = c + (tq : ℂ) * (a - c) := by linear_combination htq
  obtain ⟨α, γ, hα, hγ, hsum, hvdef⟩ := hvac
  have hvC : v = c + (α : ℂ) * (a - c) := by
    rw [← hvdef]
    simp only [Complex.real_smul]
    have h : (γ : ℂ) = 1 - α := by
      have h' : γ = 1 - α := by linarith
      rw [h']; push_cast; ring
    rw [h]; ring
  obtain ⟨u1, u, hu1, hu, husum, hvu⟩ := id hv
  have hu1' : u1 = 1 - u := by linarith
  have hvu2 : v = c + (((1 - u) * tp + u * tq : ℝ) : ℂ) * (a - c) := by
    rw [← hvu, hu1', hpC, hqC]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hαeq : α = (1 - u) * tp + u * tq := by
    have h : ((α : ℝ) : ℂ) * (a - c) = (((1 - u) * tp + u * tq : ℝ) : ℂ) * (a - c) := by
      have h2 := hvC.symm.trans hvu2
      linear_combination h2
    exact_mod_cast mul_right_cancel₀ hd h
  have hα1 : α ≤ 1 := by linarith
  have hpL : p ∈ L := (mem_of_mem_closedEdges L p q hpq).1
  have hqL : q ∈ L := (mem_of_mem_closedEdges L p q hpq).2
  have haL : a ∈ L := by rw [← List.mem_rotate (n := ρ), hrot]; simp
  have hcL : c ∈ L := by rw [← List.mem_rotate (n := ρ), hrot]; simp
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
  have hp_cases : p = c ∨ p ∈ rest := by
    have hmem : p = a ∨ p = b ∨ p = c ∨ p ∈ rest := by
      rw [← List.mem_rotate (n := ρ), hrot] at hpL; simpa using hpL
    rcases hmem with h | h | h | h
    · exact absurd h hpa
    · exact absurd h.symm hbp
    · exact Or.inl h
    · exact Or.inr h
  have hq_cases : q = a ∨ q ∈ rest := by
    have hmem : q = a ∨ q = b ∨ q = c ∨ q ∈ rest := by
      rw [← List.mem_rotate (n := ρ), hrot] at hqL; simpa using hqL
    rcases hmem with h | h | h | h
    · exact Or.inl h
    · exact absurd h.symm hbq
    · exact absurd h hqc
    · exact Or.inr h
  have hrange : ∀ (x : ℂ) (t : ℝ), (x - c = (t : ℂ) * (a - c)) → x ∈ rest → t ≤ 0 ∨ 1 ≤ t := by
    intro x t hx hxr
    by_contra hcon
    push_neg at hcon
    have hxseg : x ∈ segment ℝ c a :=
      mem_segment_of_param c a t (le_of_lt hcon.1) (le_of_lt hcon.2) x hx
    exact ear_rest_not_closed L h4 hsimple ρ a b c rest hrot hD hempty hdiag x hxr
      ((HexArea.inTriangleClosed_of_mem_ac a b c x (by rwa [segment_symm] at hxseg)).1)
  have htp_range : tp ≤ 0 ∨ 1 ≤ tp := by
    rcases hp_cases with hpc | hpr
    · left
      have h0 : (tp : ℂ) * (a - c) = 0 := by rw [← htp, hpc]; ring
      rcases mul_eq_zero.mp h0 with h | h
      · have : tp = 0 := by exact_mod_cast h
        linarith
      · exact absurd h hd
    · exact hrange p tp htp hpr
  have htq_range : tq ≤ 0 ∨ 1 ≤ tq := by
    rcases hq_cases with hqa | hqr
    · right
      have h0 : ((tq : ℂ) - 1) * (a - c) = 0 := by rw [hqa] at htq; linear_combination -htq
      rcases mul_eq_zero.mp h0 with h | h
      · have : tq = 1 := by
          have hh : (tq : ℂ) = 1 := by linear_combination h
          exact_mod_cast hh
        linarith
      · exact absurd h hd
    · exact hrange q tq htq hqr
  rcases lt_trichotomy tp tq with hlt | heq | hgt
  · have hαlt1 : tp < α := by rw [hαeq]; nlinarith
    have hαlt2 : α < tq := by rw [hαeq]; nlinarith
    have htp0 : tp ≤ 0 := by
      rcases htp_range with h | h
      · exact h
      · linarith
    have htq1 : 1 ≤ tq := by
      rcases htq_range with h | h
      · linarith
      · exact h
    rcases lt_or_eq_of_le htp0 with htpneg | htpzero
    · have hcp : c ≠ p := by
        intro h
        have h0 : (tp : ℂ) * (a - c) = 0 := by rw [← htp, ← h]; ring
        rcases mul_eq_zero.mp h0 with hh | hh
        · have : tp = 0 := by exact_mod_cast hh
          linarith
        · exact absurd hh hd
      have hcseg : c ∈ segment ℝ p q :=
        mem_segment_of_line_param c (a - c) p q c tp tq 0 hpC hqC (by push_cast; ring) hlt
          (le_of_lt htpneg) (by linarith)
      exact simple_vertex_not_on_far_edge L h4 hsimple c hcL (p, q) hpq
        (by simpa using hcp) (by simpa using (Ne.symm hqc)) hcseg
    · have hpc : p = c := by rw [hpC, htpzero]; push_cast; ring
      rcases lt_or_eq_of_le htq1 with htqgt | htqone
      · have hqa' : q ≠ a := by
          intro h
          have h0 : ((tq : ℂ) - 1) * (a - c) = 0 := by rw [h] at hqC; linear_combination -hqC
          rcases mul_eq_zero.mp h0 with hh | hh
          · have : tq = 1 := by
              have hh2 : (tq : ℂ) = 1 := by linear_combination hh
              exact_mod_cast hh2
            linarith
          · exact absurd hh hd
        have haseg : a ∈ segment ℝ p q :=
          mem_segment_of_line_param c (a - c) p q a tp tq 1 hpC hqC (by push_cast; ring) hlt
            (by linarith) (le_of_lt htqgt)
        exact simple_vertex_not_on_far_edge L h4 hsimple a haL (p, q) hpq
          (by simpa using (Ne.symm hpa)) (by simpa using (Ne.symm hqa')) haseg
      · have hqa : q = a := by rw [hqC, ← htqone]; push_cast; ring
        rw [hpc, hqa] at hpq
        obtain ⟨q₀, tl0, hrest0⟩ : ∃ q₀ tl0, rest = q₀ :: tl0 := by
          cases hrr : rest with
          | nil =>
              exfalso
              have hlen : (a :: b :: c :: rest).length = L.length := by rw [← hrot]; simp
              rw [hrr] at hlen; simp at hlen; omega
          | cons q₀ tl0 => exact ⟨q₀, tl0, rfl⟩
        have hcq0 : (c, q₀) ∈ closedEdges L := by
          rw [← mem_closedEdges_rotate L ρ, hrot, hrest0]; simp [closedEdges]
        have heq0 : a = q₀ := closedEdges_succ_unique L hNodup c a q₀ hpq hcq0
        exact hanr (by rw [heq0, hrest0]; simp)
  · exact hpqne (by rw [hpC, hqC, heq])
  · have hαlt1 : tq < α := by rw [hαeq]; nlinarith
    have hαlt2 : α < tp := by rw [hαeq]; nlinarith
    have htq0 : tq ≤ 0 := by
      rcases htq_range with h | h
      · exact h
      · linarith
    have hqcne : tq < 0 := by
      rcases lt_or_eq_of_le htq0 with h | h
      · exact h
      · exfalso
        apply hqc
        rw [hqC, h]; push_cast; ring
    have hcq : c ≠ q := Ne.symm hqc
    have hcp : c ≠ p := by
      intro h
      have h0 : (tp : ℂ) * (a - c) = 0 := by rw [← htp, ← h]; ring
      rcases mul_eq_zero.mp h0 with hh | hh
      · have : tp = 0 := by exact_mod_cast hh
        linarith
      · exact absurd hh hd
    have hcseg : c ∈ segment ℝ q p :=
      mem_segment_of_line_param c (a - c) q p c tq tp 0 hqC hpC (by push_cast; ring) hgt
        (le_of_lt hqcne) (by linarith)
    rw [segment_symm] at hcseg
    exact simple_vertex_not_on_far_edge L h4 hsimple c hcL (p, q) hpq
      (by simpa using hcp) (by simpa using hcq) hcseg

/-- **No interior point of an edge lies on the base of the ear triangle.**

Same setting as `ear_edge_interior_not_strict`: an interior point `v` of a cyclic
edge `(p, q)` with `b ∉ {p, q}` does not lie on the closed base `[a, c]` of the
ear.

Proof.  `v` is distinct from `a` and from `c` (a vertex cannot lie in the interior
of a non-incident edge, and `a`, `c` can only occur as *endpoints* of the edge),
so `v` lies in the relative interior of the base, where the two other scaled
coordinates are strictly positive.  The base coordinate is affine along the edge
and vanishes at `v`; so either it vanishes at both endpoints — the collinear case
`ear_base_collinear_case` — or it is strictly positive at one endpoint, in which
case a short step from `v` towards that endpoint reaches the strict interior of
the triangle while staying inside the edge, contradicting
`ear_edge_interior_not_strict`. -/
lemma ear_edge_interior_not_base (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L) (hndL : polyCycNondeg L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (p q : ℂ) (hpq : (p, q) ∈ closedEdges L) (hbp : b ≠ p) (hbq : b ≠ q)
    (v : ℂ) (hv : v ∈ openSegment ℝ p q) :
    v ∉ segment ℝ a c := by
  intro hvac
  have hNodup : L.Nodup := hsimple.1
  have hD : HexArea.cross (b - a) (c - b) ≠ 0 :=
    polyCycNondeg_rotate_head L a b c rest ρ (by omega) hndL hrot
  have hpqne : p ≠ q := closedEdges_ne L hNodup (by omega) p q hpq
  have hab : (a, b) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L ρ, hrot]; simp [closedEdges]
  have hbc : (b, c) ∈ closedEdges L := by
    rw [← mem_closedEdges_rotate L ρ, hrot]; simp [closedEdges]
  have haL : a ∈ L := by rw [← List.mem_rotate (n := ρ), hrot]; simp
  have hcL : c ∈ L := by rw [← List.mem_rotate (n := ρ), hrot]; simp
  have hpa : p ≠ a := by
    rintro rfl
    exact hbq (closedEdges_succ_unique L hNodup p q b hpq hab).symm
  have hqc : q ≠ c := by
    rintro rfl
    exact hbp (closedEdges_pred_unique L hNodup q p b hpq hbc).symm
  have hva : v ≠ a := by
    intro h
    by_cases hqa : q = a
    · rw [h, ← hqa] at hv
      exact hpqne (right_mem_openSegment_iff.mp hv)
    · exact simple_vertex_not_on_far_edge L h4 hsimple a haL (p, q) hpq
        (by simpa using (Ne.symm hpa)) (by simpa using (Ne.symm hqa))
        (h ▸ openSegment_subset_segment ℝ p q hv)
  have hvc : v ≠ c := by
    intro h
    by_cases hpc : p = c
    · rw [h, ← hpc] at hv
      exact hpqne (left_mem_openSegment_iff.mp hv)
    · exact simple_vertex_not_on_far_edge L h4 hsimple c hcL (p, q) hpq
        (by simpa using (Ne.symm hpc)) (by simpa using (Ne.symm hqc))
        (h ▸ openSegment_subset_segment ℝ p q hv)
  have hvopen : v ∈ openSegment ℝ a c :=
    mem_openSegment_of_ne_left_right (Ne.symm hva) (Ne.symm hvc) hvac
  obtain ⟨hg1, hg2, hf3v⟩ := HexArea.scaled_pos_of_mem_openSegment_ac a b c v hD hvopen
  obtain ⟨u1, u, hu1, hu, husum, hvdef⟩ := id hv
  have hvC : v = (1 - u) • p + u • q := by
    rw [← hvdef, show u1 = 1 - u by linarith]
  have haffine :
      (1 - u) * HexArea.cross (a - c) (p - c) + u * HexArea.cross (a - c) (q - c) = 0 := by
    rw [← HexArea.cross_affine, ← hvC]; exact hf3v
  by_cases hboth : HexArea.cross (a - c) (p - c) = 0 ∧ HexArea.cross (a - c) (q - c) = 0
  · exact absurd (ear_base_collinear_case L h4 hsimple ρ a b c rest hrot hD hempty hdiag
      p q hpq hbp hbq hboth.1 hboth.2 v hv hvac) not_false
  · obtain ⟨w, hw, hgw⟩ : ∃ w : ℂ, (w = p ∨ w = q) ∧
        0 < HexArea.cross (a - c) (w - c) * HexArea.cross (b - a) (c - b) := by
      by_cases h1 : 0 < HexArea.cross (a - c) (p - c) * HexArea.cross (b - a) (c - b)
      · exact ⟨p, Or.inl rfl, h1⟩
      by_cases h2 : 0 < HexArea.cross (a - c) (q - c) * HexArea.cross (b - a) (c - b)
      · exact ⟨q, Or.inr rfl, h2⟩
      exfalso
      push_neg at h1 h2
      apply hboth
      have hu0 : 0 < 1 - u := by linarith
      have hkey : (1 - u) * (HexArea.cross (a - c) (p - c) * HexArea.cross (b - a) (c - b))
          + u * (HexArea.cross (a - c) (q - c) * HexArea.cross (b - a) (c - b)) = 0 := by
        linear_combination HexArea.cross (b - a) (c - b) * haffine
      have e1 : HexArea.cross (a - c) (p - c) * HexArea.cross (b - a) (c - b) = 0 := by
        nlinarith
      have e2 : HexArea.cross (a - c) (q - c) * HexArea.cross (b - a) (c - b) = 0 := by
        nlinarith
      constructor
      · rcases mul_eq_zero.mp e1 with h | h
        · exact h
        · exact absurd h hD
      · rcases mul_eq_zero.mp e2 with h | h
        · exact h
        · exact absurd h hD
    obtain ⟨t, ht0, ht1, hstrict⟩ := exists_strict_on_edge a b c v w hg1 hg2 hf3v hgw
    exact ear_edge_interior_not_strict L h4 hsimple hndL ρ a b c rest hrot hempty hdiag
      p q hpq hbp hbq ((1 - t) • v + t • w)
      (openSegment_perturb p q v w hv hw t (le_of_lt ht0) ht1) hstrict

end
