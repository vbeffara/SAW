/-
# The dart counterexample: "disjoint from non-incident edges" does NOT make a chord
  an *interior* diagonal

This file is a **soundness audit** of the chord-splitting branch of the polygon
Umlaufsatz (`RequestProject.SAWUmlaufPolygon`).

Several lemmas of that branch describe the cut `W[0]–W[k]` of a simple polygon
`W` only through the *disjointness* hypothesis

```
hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
          Disjoint (segment ℝ u v) (segment ℝ e.1 e.2)
```

(the conclusion shape of `interior_chord_is_diagonal`).  That hypothesis is
**not** enough to know that the chord runs through the *inside* of the polygon:
the *exterior* chord of a dart (a non-convex quadrilateral) satisfies it
vacuously, because in a quadrilateral every edge is incident to one of the two
chord endpoints.

Concretely, take the dart

```
  q = -2        x = -i        p = 2        r = -4i
  dartW = [q, x, p, r]
```

whose vertex `x` is reflex, and cut it along `k = 2`, i.e. along `u = q`,
`v = p`.  Then `chordRight dartW 2 = [p, r, q] =: dartP` is a triangle and the
*other* vertex `x` of `dartW` lies **strictly inside** it.  All the hypotheses of
the chord lemmas hold, but their conclusions ("a vertex of the other piece is
not inside an ear triangle of `P`", "the winding of `P` around such a vertex is
`0`", "such a vertex can escape to infinity avoiding the edges") all fail.

The three `..._general_false` theorems below are formal disproofs of exactly the
hypothesis shapes used in `SAWUmlaufPolygon`.  They are the justification for the
extra *interior-chord* hypotheses (extremality of `u` together with `v` inside
the corner triangle at `u`) that the chord branch must carry; those hypotheses
are exactly what is available at the sole call site (Meisters' interior branch,
`meisters_reduction_interior2`), where `u = b` is the extreme corner apex and
`v = w` lies strictly inside the corner triangle `a, b, c`.

This file is imported by `RequestProject.SAWFinal`.
-/
import Mathlib
import RequestProject.SAWUmlaufPolygon

open Real Complex

namespace DartCE

/-- The dart quadrilateral `q = -2`, `x = -i`, `p = 2`, `r = -4i`.
The vertex `x = -i` is the reflex tip. -/
def dartW : List ℂ := [-2, -Complex.I, 2, -4 * Complex.I]

/-- The right chord piece of the cut `dartW[0]–dartW[2]`: the triangle `p, r, q`. -/
def dartP : List ℂ := [2, -4 * Complex.I, -2]

lemma dartP_eq : dartP = HexArea.chordRight dartW 2 := by
  simp [dartP, dartW, HexArea.chordRight]

/-- The two non-adjacent edges `[q, x]` and `[p, r]` of the dart are disjoint:
the first lies in `{re ≤ 0}` and the second in `{re ≥ 0}`, and they meet the
line `re = 0` in the two distinct points `-i` and `-4i`. -/
lemma dart_seg_disjoint₁ :
    Disjoint (segment ℝ (-2 : ℂ) (-Complex.I)) (segment ℝ (2 : ℂ) (-4 * Complex.I)) := by
  have h : 0 < HexArea.cross (-4 * Complex.I - 2) (-2 - 2) * HexArea.cross (-4 * Complex.I - 2) (-Complex.I - 2) := by
    simp [HexArea.cross]
    norm_num
  exact (HexArea.segment_disjoint_of_strictSameSide (2 : ℂ) (-4 * Complex.I) (-2) (-Complex.I) h).symm

/-- The two non-adjacent edges `[x, p]` and `[r, q]` of the dart are disjoint. -/
lemma dart_seg_disjoint₂ :
    Disjoint (segment ℝ (-Complex.I) (2 : ℂ)) (segment ℝ (-4 * Complex.I) (-2 : ℂ)) := by
  rw [Set.disjoint_left]
  rintro z ⟨t1, t2, ht1, ht2, hsum, hz⟩ ⟨s1, s2, hs1, hs2, hssum, hw⟩
  rw [← hw] at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp at hre him
  nlinarith [hre, him, ht1, ht2, hs1, hs2, hsum, hssum]

/-- The dart is a simple polygon. -/
lemma dartW_simple : PolygonSimple dartW := by
  constructor
  · simp [dartW, Complex.ext_iff]
    norm_num
  · intro e1 h1 e2 h2 a b c d
    simp [closedEdges, dartW] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      try simp_all
    all_goals rw [show (-(4 * Complex.I) : ℂ) = -4 * Complex.I by ring]
    · exact dart_seg_disjoint₁
    · exact dart_seg_disjoint₂
    · exact dart_seg_disjoint₁.symm
    · exact dart_seg_disjoint₂.symm

/-- The dart has no flat corner. -/
lemma dartW_nondeg : polyCycNondeg dartW := by
  simp [polyCycNondeg, polyNondeg, dartW, HexArea.cross]
  norm_num

/-- The triangle piece is a simple polygon (all edge pairs share an endpoint). -/
lemma dartP_simple : PolygonSimple dartP := by
  constructor
  · simp [dartP, Complex.ext_iff]
    norm_num
  · intro e1 h1 e2 h2 a b c d
    simp [closedEdges, dartP] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

/-- The reflex tip `x = -i` lies strictly inside the triangle `p, r, q`. -/
lemma dart_tip_inside : HexArea.inTriangleStrict 2 (-4 * Complex.I) (-2) (-Complex.I) := by
  simp [HexArea.inTriangleStrict, HexArea.cross]

/-- Every edge of the dart is incident to one of the two chord endpoints
`u = -2`, `v = 2`, so the diagonal-disjointness hypothesis holds vacuously. -/
lemma dart_hdiag : ∀ e ∈ closedEdges dartW, (-2 : ℂ) ≠ e.1 → (-2 : ℂ) ≠ e.2 →
    (2 : ℂ) ≠ e.1 → (2 : ℂ) ≠ e.2 →
    Disjoint (segment ℝ (-2 : ℂ) 2) (segment ℝ e.1 e.2) := by
  intro e he hne1 hne2 h2e1 h2e2
  simp [closedEdges, dartW] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

/-- The orientation-matching hypothesis for the degenerate clip of the triangle
piece: both sides are false, since `shoelace2 [2, -4i, -2] = -16 < 0` and
`shoelace2 [2, -2] = 0`. -/
lemma dart_horient :
    ((0 : ℝ) < HexArea.shoelace2 [2, -4 * Complex.I, -2]
      ↔ (0 : ℝ) < HexArea.shoelace2 ([(2 : ℂ), -2])) := by
  simp [HexArea.shoelace2, HexArea.shoelaceOpen, HexArea.cross]; norm_num

lemma dart_x_mem : (-Complex.I) ∈ dartW := by
  simp [dartW]

lemma dart_x_not_mem_P : (-Complex.I) ∉ dartP := by
  simp only [dartP, List.mem_cons, List.not_mem_nil, or_false]
  push_neg
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;>
    simpa [Complex.ext_iff] using congrArg Complex.im h

/-- The tip is not on the dart edge `[p, r]`. -/
lemma dart_tip_not_mem_seg₁ : (-Complex.I) ∉ segment ℝ (2 : ℂ) (-4 * Complex.I) := by
  rintro ⟨t1, t2, ht1, ht2, hsum, hz⟩
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp at hre him
  nlinarith [hre, him, ht1, ht2, hsum]

/-- The tip is not on the dart edge `[r, q]`. -/
lemma dart_tip_not_mem_seg₂ : (-Complex.I) ∉ segment ℝ (-4 * Complex.I) (-2 : ℂ) := by
  rintro ⟨t1, t2, ht1, ht2, hsum, hz⟩
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp at hre him
  nlinarith [hre, him, ht1, ht2, hsum]

/-- The tip is not on the chord `[q, p]`. -/
lemma dart_tip_not_mem_chord : (-Complex.I) ∉ segment ℝ (-2 : ℂ) (2 : ℂ) := by
  rintro ⟨t1, t2, ht1, ht2, hsum, hz⟩
  have him := congrArg Complex.im hz
  simp at him

/-! ## The corrected hypothesis excludes the counterexample -/

/-- **The fix works.**  The dart's exterior chord `q–p` is *not* an
`InteriorChord` of the dart: the far endpoint `p = 2` does not lie strictly
inside the corner triangle `(r, q, x)` at the rooted endpoint `q = -2`.  So the
strengthened chord branch of `RequestProject.SAWUmlaufPolygon` genuinely excludes
this configuration. -/
theorem dart_chord_not_interiorChord : ¬ InteriorChord dartW (-2) 2 := by
  rintro ⟨pu, nu, hhead, hlast, hnu, hext, hcone⟩
  have hpu : pu = -4 * Complex.I := by
    have : dartW.getLast? = some (-4 * Complex.I) := by simp [dartW]
    rw [this] at hlast
    exact (Option.some.injEq _ _ ▸ hlast).symm
  have hnu' : nu = -Complex.I := by
    have : dartW[1]? = some (-Complex.I) := by simp [dartW]
    rw [this] at hnu
    exact (Option.some.injEq _ _ ▸ hnu).symm
  rw [hpu, hnu'] at hcone
  simp [HexArea.inTriangleStrict, HexArea.cross] at hcone
  norm_num at hcone

/-! ## The three disproofs -/

/-- **Disproof 1 (`chord_ear_empty_other` shape).**  With only the disjointness
hypothesis on the cut, a vertex of the other chord piece CAN lie strictly inside
an ear triangle of the piece `P`. -/
theorem chord_ear_empty_other_general_false :
    ¬ (∀ (W : List ℂ), PolygonSimple W → polyCycNondeg W → ∀ (k : ℕ),
        1 ≤ k → k + 1 ≤ W.length →
        ∀ (u v : ℂ), W[0]? = some u → W[k]? = some v →
        (∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
            Disjoint (segment ℝ u v) (segment ℝ e.1 e.2)) →
        ∀ (P : List ℂ), PolygonSimple P →
        (P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k) →
        ∀ (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ), P.rotate s = a' :: b' :: c' :: tlP →
        (∀ y ∈ tlP, ¬ HexArea.inTriangleStrict a' b' c' y) →
        ((0 : ℝ) < HexArea.shoelace2 [a', b', c']
          ↔ (0 : ℝ) < HexArea.shoelace2 (a' :: c' :: tlP)) →
        ∀ (x : ℂ), x ∈ W → x ∉ P → ¬ HexArea.inTriangleStrict a' b' c' x) := by
  intro h
  refine h dartW dartW_simple dartW_nondeg 2 (by norm_num) (by simp [dartW])
    (-2) 2 (by simp [dartW]) (by simp [dartW]) dart_hdiag dartP dartP_simple
    (Or.inr dartP_eq) 2 (-4 * Complex.I) (-2) 0 [] (by simp [dartP])
    (by simp) dart_horient (-Complex.I) dart_x_mem dart_x_not_mem_P dart_tip_inside

/-- **Disproof 2 (`chord_ear_other_ptWind_zero` shape).**  With only the
disjointness hypothesis on the cut, the winding number of the piece `P` around a
vertex of the other piece need NOT be `0`. -/
theorem chord_ear_other_ptWind_zero_general_false :
    ¬ (∀ (W : List ℂ), PolygonSimple W → polyCycNondeg W → ∀ (k : ℕ),
        1 ≤ k → k + 1 ≤ W.length →
        ∀ (u v : ℂ), W[0]? = some u → W[k]? = some v →
        (∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
            Disjoint (segment ℝ u v) (segment ℝ e.1 e.2)) →
        ∀ (P : List ℂ), PolygonSimple P →
        (P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k) →
        ∀ (x : ℂ), x ∈ W → x ∉ P → HexArea.ptWind x P = 0) := by
  intro h
  have hzero : HexArea.ptWind (-Complex.I) dartP = 0 :=
    h dartW dartW_simple dartW_nondeg 2 (by norm_num) (by simp [dartW])
      (-2) 2 (by simp [dartW]) (by simp [dartW]) dart_hdiag dartP dartP_simple
      (Or.inr dartP_eq) (-Complex.I) dart_x_mem dart_x_not_mem_P
  exact HexArea.ptWind_triangle_ne_zero 2 (-4 * Complex.I) (-2) (-Complex.I)
    dart_tip_inside (by simpa [dartP] using hzero)

/-- The escape-walk conclusion is impossible for the dart tip: an edge-avoiding
polyline out of the convex hull would force `ptWind x dartP = 0`. -/
lemma dart_no_escape_walk :
    ¬ ∃ zs : List ℂ,
      List.IsChain (fun a b =>
          (∀ e ∈ closedEdges dartW, e.1 ≠ (-Complex.I) → e.2 ≠ (-Complex.I) →
              Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) ∧
          (∀ s ∈ [((-2 : ℂ), (2 : ℂ))], Disjoint (segment ℝ a b) (segment ℝ s.1 s.2)))
        ((-Complex.I) :: zs) ∧
      (zs.getLastD (-Complex.I)) ∉ convexHull ℝ (dartW.toFinset : Set ℂ) := by
  rintro ⟨zs, hchain, hlast⟩
  -- The three cycle edges of the triangle piece are two `dartW`-edges avoiding the
  -- tip together with the chord, so the walk avoids all of them.
  have hcyc : HexArea.cycleEdges dartP
      = [((2 : ℂ), -4 * Complex.I), ((-4 * Complex.I : ℂ), (-2 : ℂ)), ((-2 : ℂ), (2 : ℂ))] := by
    simp [HexArea.cycleEdges, dartP]
  have hchain' : List.IsChain (fun a b => ∀ e ∈ HexArea.cycleEdges dartP,
      Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) ((-Complex.I) :: zs) := by
    refine hchain.imp ?_
    intro a b hab e he
    rw [hcyc] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact hab.1 _ (by simp [closedEdges, dartW]) (by simp [Complex.ext_iff])
        (by simp [Complex.ext_iff])
    · exact hab.1 _ (by simp [closedEdges, dartW]) (by simp [Complex.ext_iff])
        (by simp [Complex.ext_iff])
    · exact hab.2 _ (by simp)
  have hsub : ∀ y ∈ dartP, y ∈ dartW := by
    intro y hy
    simp only [dartP, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> simp [dartW]
  have hzero := HexArea.ptWind_zero_of_walk_to_not_hull dartP (-Complex.I) zs hchain'
    (HexArea.not_mem_convexHull_sub dartP dartW hsub _ hlast)
  exact HexArea.ptWind_triangle_ne_zero 2 (-4 * Complex.I) (-2) (-Complex.I)
    dart_tip_inside (by simpa [dartP] using hzero)

/-- **Disproof 3 (`vertex_escape_walk_core` shape).**  With only the
disjointness hypothesis on the diagonals, a boundary vertex need NOT be able to
escape past the convex hull along an edge-avoiding polyline. -/
theorem vertex_escape_walk_core_general_false :
    ¬ (∀ (W : List ℂ), PolygonSimple W →
        ∀ (x : ℂ), x ∈ W → ∀ (diags : List (ℂ × ℂ)),
        (∀ s ∈ diags, s.1 ≠ x ∧ s.2 ≠ x) →
        diags.length ≤ 1 →
        (∀ s ∈ diags, x ∉ segment ℝ s.1 s.2) →
        (x ∈ ((⋃ s ∈ ((closedEdges W).filter
            (fun e => decide (e.1 ≠ x) && decide (e.2 ≠ x)) ++ diags),
            segment ℝ s.1 s.2)ᶜ)) →
        (∀ s ∈ diags, ∀ e ∈ closedEdges W,
            s.1 ≠ e.1 → s.1 ≠ e.2 → s.2 ≠ e.1 → s.2 ≠ e.2 →
            Disjoint (segment ℝ s.1 s.2) (segment ℝ e.1 e.2)) →
        ∃ zs : List ℂ,
          List.IsChain (fun a b =>
              (∀ e ∈ closedEdges W, e.1 ≠ x → e.2 ≠ x →
                  Disjoint (segment ℝ a b) (segment ℝ e.1 e.2)) ∧
              (∀ s ∈ diags, Disjoint (segment ℝ a b) (segment ℝ s.1 s.2))) (x :: zs) ∧
          (zs.getLastD x) ∉ convexHull ℝ (W.toFinset : Set ℂ)) := by
  intro h
  apply dart_no_escape_walk
  refine h dartW dartW_simple (-Complex.I) dart_x_mem [((-2 : ℂ), (2 : ℂ))] ?_ (by simp) ?_ ?_ ?_
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    constructor <;> intro hcon <;> simpa [Complex.ext_iff] using congrArg Complex.im hcon
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact dart_tip_not_mem_chord
  · -- the tip lies on none of the two non-incident dart edges nor on the chord
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro s hs
    simp [closedEdges, dartW, Complex.ext_iff] at hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using dart_tip_not_mem_seg₁
    · simpa using dart_tip_not_mem_seg₂
    · simpa using dart_tip_not_mem_chord
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact dart_hdiag

end DartCE
