import Mathlib
import RequestProject.SAWUmlaufCornerEscape
import RequestProject.SAWUmlaufConeStrict
import RequestProject.SAWUmlaufPolyChord

/-!
# The chord pieces seen from the extreme cut endpoint

This file connects the elementary escape theorem
`HexArea.ptWind_zero_of_extreme_corner` (in `RequestProject.SAWUmlaufCornerEscape`)
with the chord-splitting branch of the Umlaufsatz.

Setting: `W` is a simple closed polygon, rooted so that `u = W[0]`, and the cut
chord is `u–v` with `v = W[k]`.  The predicate `InteriorChord W u v` records the
diagonal-validity data available at the sole call site (Meisters' interior
branch): `u` is the *lex-minimal* — hence strictly extreme — vertex of `W`, so
there is a direction `d` with `0 < cdot d (y - u)` for every other vertex `y`,
and the far endpoint `v` lies strictly inside the corner triangle
`(pu, u, nu)` spanned by `u` and its two cyclic neighbours.

The main result `chordPiece_other_neighbour_ptWind_zero` produces the *witness*
required by `chord_ear_other_ptWind_zero_of_witness`: the cyclic neighbour of
`u` belonging to the **other** chord piece has winding number `0` around the
piece `P`.  The proof is the corner escape: that neighbour is seen from `u` in a
direction outside the cone spanned by the two edges of `P` at `u`, and `u` is
strictly extreme, so a straight ray escapes without meeting `P`.

This removes the polygon-Jordan detour (escape walks around the whole polygon)
from the "outside ⟹ winding `0`" half of the chord branch.

Imported by `RequestProject.SAWUmlaufPolyEscape`, hence on the live route to the
main theorem.
-/

open Real Complex

noncomputable section

set_option maxHeartbeats 1000000

/-- **Interior chord at a rooted endpoint** (the diagonal-validity data).  The
chord `u–v` of the cyclically-rooted polygon `W` (`u = W[0]`) *enters the
polygon* at `u`:

* `u` is strictly extreme: some direction `d` has `0 < cdot d (y - u)` for every
  other vertex `y` of `W` (at the call site `u` is the lex-minimal vertex);
* no triangle spanned by vertices of `W` contains `u` strictly (kept because it
  is what the dart counterexample refutes, and it is free at the call site);
* the far endpoint `v` lies strictly inside the corner *cone* `(pu, u, nu)`
  spanned by `u` and its two cyclic neighbours (`HexArea.inConeStrict`).  This is
  the exact relaxation of the earlier clause `inTriangleStrict pu u nu v`: every
  consumer of `InteriorChord` only ever uses the cone, and the blocked-base
  branch of the Meisters recursion (`RequestProject.SAWUmlaufBaseBlocked`) needs
  a chord whose far endpoint sits on the *base* of the corner triangle, which is
  in the cone but not in the triangle's interior.

**Why this is needed (soundness).**  Edge-disjointness alone is NOT enough.  For
a dart (non-convex quadrilateral) every edge is incident to one of the two chord
endpoints, so the disjointness hypothesis holds vacuously for the *exterior*
chord, and the reflex vertex of the dart then lies strictly inside the triangle
cut off by that chord; see `RequestProject.SAWUmlaufDartCounterexample`. -/
def InteriorChord (W : List ℂ) (u v : ℂ) : Prop :=
  ∃ pu nu : ℂ, W.head? = some u ∧ W.getLast? = some pu ∧ W[1]? = some nu ∧
    (∀ y ∈ W, ∀ z ∈ W, ∀ t ∈ W, ¬ HexArea.inTriangleStrict y z t u) ∧
    (∃ d : ℂ, ∀ y ∈ W, y ≠ u → 0 < HexArea.cdot d (y - u)) ∧
    HexArea.inConeStrict pu u nu v

namespace HexArea

/-- The cyclic edge list used by the winding machinery agrees with `closedEdges`.
-/
lemma cycleEdges_eq_closedEdges (V : List ℂ) : cycleEdges V = closedEdges V := by
  rcases V with _ | ⟨a, L⟩
  · rfl
  · apply List.ext_getElem
    · simp [cycleEdges, closedEdges]
    · intro i h1 h2
      have hlen : i < (a :: L).length := by simpa [closedEdges] using h2
      simp only [cycleEdges, closedEdges, List.getElem_zip, List.getElem_drop, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [List.getElem_append, dif_pos hlen]
      · rw [List.getElem_append, List.getElem_rotate]
        by_cases h : 1 + i < (a :: L).length
        · rw [dif_pos h]
          have hmod : (i + 1) % (a :: L).length = i + 1 := Nat.mod_eq_of_lt (by omega)
          simp only [hmod]
          congr 1
          omega
        · rw [dif_neg h]
          have hi1 : i + 1 = (a :: L).length := by omega
          have hmod : (i + 1) % (a :: L).length = 0 := by rw [hi1]; simp
          simp only [hmod]
          simp

/-- **The cycle edges incident to the head of a `Nodup` polygon.**  In a closed
polygon with distinct vertices, the only cycle edges touching the first vertex
`u` are `(u, n₁)` (with `n₁` the second vertex) and `(n₂, u)` (with `n₂` the last
vertex). -/
lemma cycleEdges_at_head (P : List ℂ) (hnd : P.Nodup) (u n₁ n₂ : ℂ)
    (hu : P.head? = some u) (hn1 : P[1]? = some n₁) (hn2 : P.getLast? = some n₂)
    (h2 : 2 ≤ P.length)
    (e : ℂ × ℂ) (he : e ∈ cycleEdges P) :
    (e.1 ≠ u ∧ e.2 ≠ u) ∨ e = (u, n₁) ∨ e = (n₂, u) := by
  classical
  have hu0 : P[0]'(by omega) = u := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hu
    exact (Option.some.injEq _ _ ▸ hu)
  have hu1 : P[1]'(by omega) = n₁ := by
    rw [List.getElem?_eq_getElem (by omega)] at hn1
    exact (Option.some.injEq _ _ ▸ hn1)
  have hu2 : P[P.length - 1]'(by omega) = n₂ := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hn2
    exact (Option.some.injEq _ _ ▸ hn2)
  obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp he
  have hilen : i < P.length := by
    simp [cycleEdges, List.length_zip] at hi
    omega
  have hlenQ : i + 1 < (P ++ P.take 1).length := by simp; omega
  have hfst : (cycleEdges P)[i]'hi
      = ((P ++ P.take 1)[i]'(by simp; omega), (P ++ P.take 1)[i+1]'hlenQ) := by
    simp [cycleEdges, List.getElem_zip]
  have hQ1 : (P ++ P.take 1)[i]'(by simp; omega) = P[i]'hilen := by
    rw [List.getElem_append]; simp [hilen]
  have hQ2 : (P ++ P.take 1)[i+1]'hlenQ
      = if h : i + 1 < P.length then P[i+1]'h else P[0]'(by omega) := by
    by_cases h : i + 1 < P.length
    · rw [dif_pos h, List.getElem_append, dif_pos h]
    · rw [dif_neg h, List.getElem_append, dif_neg h]
      have hii : i + 1 - P.length = 0 := by omega
      simp [hii]
  rw [hfst, hQ1, hQ2] at hei
  by_cases hlast : i + 1 < P.length
  · rw [dif_pos hlast] at hei
    by_cases h1 : P[i]'hilen = u
    · have hi0 : i = 0 := (List.Nodup.getElem_inj_iff hnd).mp (by rw [h1, hu0])
      subst hi0
      right; left
      rw [← hei]; simp [hu0, hu1]
    · by_cases h2' : P[i+1]'hlast = u
      · exfalso
        have := (List.Nodup.getElem_inj_iff hnd (i := i+1) (j := 0)).mp (by rw [h2', hu0])
        omega
      · left; rw [← hei]; exact ⟨h1, h2'⟩
  · rw [dif_neg hlast] at hei
    have hi1 : i = P.length - 1 := by omega
    subst hi1
    right; right
    rw [← hei]
    simp [hu0, hu2]

/-- **Corner escape at the head vertex.**  Packaging of
`ptWind_zero_of_extreme_corner` for a polygon presented with the extreme vertex
`u` first: the hypothesis on the cycle edges at `u` is discharged by
`cycleEdges_at_head` together with convexity of the corner cone. -/
lemma ptWind_zero_of_corner_head (P : List ℂ) (hnd : P.Nodup) (h2 : 2 ≤ P.length)
    (u n₁ n₂ x₀ d : ℂ)
    (hu : P.head? = some u) (hn1 : P[1]? = some n₁) (hn2 : P.getLast? = some n₂)
    (hpos : ∀ y ∈ P, y ≠ u → 0 < cdot d (y - u))
    (hx₀ : x₀ ≠ u) (hcone : x₀ ∉ cornerCone u n₁ n₂)
    (hsegu : ∀ e ∈ cycleEdges P, ∀ w ∈ segment ℝ u x₀,
        w ∈ segment ℝ e.1 e.2 → w = u) :
    ptWind x₀ P = 0 := by
  have hn1P : n₁ ∈ P := by
    rw [List.getElem?_eq_getElem (by omega)] at hn1
    have : P[1]'(by omega) = n₁ := (Option.some.injEq _ _ ▸ hn1)
    exact this ▸ List.getElem_mem _
  have hn2P : n₂ ∈ P := List.mem_of_mem_getLast? hn2
  have hu0 : P[0]'(by omega) = u := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hu
    exact (Option.some.injEq _ _ ▸ hu)
  have hn1u : n₁ ≠ u := by
    rw [List.getElem?_eq_getElem (by omega)] at hn1
    have h1 : P[1]'(by omega) = n₁ := (Option.some.injEq _ _ ▸ hn1)
    intro hcontra
    have : (1 : ℕ) = 0 := (List.Nodup.getElem_inj_iff hnd).mp (by rw [h1, hu0, hcontra])
    omega
  have hn2u : n₂ ≠ u := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hn2
    have h1 : P[P.length - 1]'(by omega) = n₂ := (Option.some.injEq _ _ ▸ hn2)
    intro hcontra
    have : P.length - 1 = 0 := (List.Nodup.getElem_inj_iff hnd).mp (by rw [h1, hu0, hcontra])
    omega
  refine ptWind_zero_of_extreme_corner P u n₁ n₂ x₀ d hx₀ hn1P hn2P hn1u hn2u hpos ?_ hcone hsegu
  intro e he
  rcases cycleEdges_at_head P hnd u n₁ n₂ hu hn1 hn2 h2 e he with h | h | h
  · exact Or.inl h
  · refine Or.inr ?_
    rw [h]
    exact segment_subset_cornerCone u n₁ n₂ u n₁ (mem_cornerCone_self u n₁ n₂)
      (mem_cornerCone_left u n₁ n₂)
  · refine Or.inr ?_
    rw [h]
    exact segment_subset_cornerCone u n₁ n₂ n₂ u (mem_cornerCone_right u n₁ n₂)
      (mem_cornerCone_self u n₁ n₂)

end HexArea

/-- An interior chord is a genuine diagonal: its far endpoint is neither of the
two cyclic neighbours of the root, so the cut index satisfies `2 ≤ k` and
`k + 2 ≤ W.length`.  (If `k = 1` or `k + 1 = W.length` then `v` would be a
vertex of the corner triangle, contradicting `inTriangleStrict`.) -/
lemma InteriorChord.index_bounds (W : List ℂ) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length) (u v : ℂ)
    (hv : W[k]? = some v) (hint : InteriorChord W u v) :
    2 ≤ k ∧ k + 2 ≤ W.length := by
  obtain ⟨pu, nu, hhead, hlast, hnu, hext, hdir, hin⟩ := hint
  have hvk : W[k]'(by omega) = v := by
    rw [List.getElem?_eq_getElem (by omega)] at hv
    exact (Option.some.injEq _ _ ▸ hv)
  have hnuk : W[1]'(by omega) = nu := by
    rw [List.getElem?_eq_getElem (by omega)] at hnu
    exact (Option.some.injEq _ _ ▸ hnu)
  have hpuk : W[W.length - 1]'(by omega) = pu := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    exact (Option.some.injEq _ _ ▸ hlast)
  constructor
  · rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · exfalso
        have : v = nu := by rw [← hvk, ← hnuk]
        exact (HexArea.inConeStrict_ne_right pu u nu v hin) this
    · exact h
  · by_contra hcon
    have : v = pu := by
      rw [← hvk, ← hpuk]
      exact getElem_congr rfl (by omega) (by omega)
    exact (HexArea.inConeStrict_ne_left pu u nu v hin) this


/-! ### Elementary bricks -/

/-- Two segments issuing from a common apex in linearly independent directions
meet only at the apex. -/
lemma segment_meet_apex (u a b : ℂ) (h : HexArea.cross (a - u) (b - u) ≠ 0)
    (w : ℂ) (hwa : w ∈ segment ℝ u a) (hwb : w ∈ segment ℝ u b) : w = u := by
  obtain ⟨s1, s2, hs1, hs2, hs, hw1⟩ := hwa
  obtain ⟨t1, t2, ht1, ht2, ht, hw2⟩ := hwb
  have h1 : w - u = s2 • (a - u) := by
    rw [← hw1]
    have hc : (s1 : ℂ) + s2 = 1 := by exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hs
    push_cast [Complex.real_smul]
    linear_combination (norm := ring) u * hc
  have h2 : w - u = t2 • (b - u) := by
    rw [← hw2]
    have hc : (t1 : ℂ) + t2 = 1 := by exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) ht
    push_cast [Complex.real_smul]
    linear_combination (norm := ring) u * hc
  have heq : s2 • (a - u) = t2 • (b - u) := by rw [← h1, h2]
  have hs2z : s2 = 0 := by
    by_contra hne
    apply h
    have hcr := congrArg (fun z => HexArea.cross z (b - u)) heq
    simp [HexArea.cross, Complex.real_smul] at hcr
    have hkey : s2 * HexArea.cross (a - u) (b - u) = 0 := by
      simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]
      linear_combination hcr
    rcases mul_eq_zero.mp hkey with h' | h'
    · exact absurd h' hne
    · exact h'
  rw [hs2z] at h1
  simp at h1
  exact sub_eq_zero.mp h1

/-- The three corner directions at the rooted endpoint of an interior chord are
pairwise independent. -/
lemma corner_cross_ne (p u n v : ℂ) (h : HexArea.inTriangleStrict p u n v) :
    HexArea.cross (p - u) (n - u) ≠ 0 ∧ HexArea.cross (p - u) (v - u) ≠ 0 ∧
      HexArea.cross (n - u) (v - u) ≠ 0 := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hv⟩ := HexArea.inTriangleStrict_convexCombo p u n v h
  have hpn : HexArea.cross (p - u) (n - u) ≠ 0 := by
    have hnd := HexArea.inTriangleStrict_nondeg p u n v h
    simpa [HexArea.cross, Complex.ext_iff] using
      fun hc => hnd (by simp [HexArea.cross] at hc ⊢; linarith)
  have hvu : v - u = α • (p - u) + γ • (n - u) := by
    rw [hv]
    have hb : β = 1 - α - γ := by linarith
    rw [hb]
    push_cast [Complex.real_smul]
    ring
  refine ⟨hpn, ?_, ?_⟩
  · have hc : HexArea.cross (p - u) (v - u) = γ * HexArea.cross (p - u) (n - u) := by
      rw [hvu]; simp [HexArea.cross, Complex.real_smul]; ring
    rw [hc]
    exact mul_ne_zero (ne_of_gt hγ) hpn
  · have hc : HexArea.cross (n - u) (v - u) = -(α * HexArea.cross (p - u) (n - u)) := by
      rw [hvu]; simp [HexArea.cross, Complex.real_smul]; ring
    rw [hc]
    simpa using mul_ne_zero (ne_of_gt hα) hpn

/-- `cross` is antisymmetric, so independence is symmetric in the two vectors. -/
lemma cross_ne_swap (a b : ℂ) (h : HexArea.cross a b ≠ 0) : HexArea.cross b a ≠ 0 := by
  intro hc; apply h; simp [HexArea.cross] at hc ⊢; linarith

/-- Consecutive vertices (cyclically) form a closed edge. -/
lemma mem_closedEdges_pair (W : List ℂ) (i j : ℕ) (hi : i < W.length) (hj : j < W.length)
    (hij : j = (i + 1) % W.length) (a b : ℂ) (ha : W[i]'hi = a) (hb : W[j]'hj = b) :
    (a, b) ∈ closedEdges W := by
  subst ha; subst hb; subst hij
  rw [List.mem_iff_getElem]
  refine ⟨i, by simp [closedEdges]; omega, ?_⟩
  simp only [closedEdges, List.getElem_zip, List.getElem_rotate]

/-- A vertex at an index `≥ m` of a `Nodup` list is not among its first `m`. -/
lemma not_mem_take_of_getElem (W : List ℂ) (hnd : W.Nodup) (i m : ℕ) (hi : i < W.length)
    (him : m ≤ i) : W[i]'hi ∉ W.take m := by
  intro hmem
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hmem
  rw [List.length_take] at hj
  rw [List.getElem_take] at hje
  have : j = i := (List.Nodup.getElem_inj_iff hnd).mp hje
  omega

/-- A vertex at an index strictly between `1` and `k` of a `Nodup` list is not a
vertex of the right chord piece. -/
lemma not_mem_drop_append_take (W : List ℂ) (hnd : W.Nodup) (i k : ℕ) (hi : i < W.length)
    (h1 : 1 ≤ i) (h2 : i < k) : W[i]'hi ∉ W.drop k ++ W.take 1 := by
  intro hmem
  rcases List.mem_append.mp hmem with h | h
  · obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp h
    rw [List.length_drop] at hj
    rw [List.getElem_drop] at hje
    have : k + j = i := (List.Nodup.getElem_inj_iff hnd).mp hje
    omega
  · obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp h
    rw [List.length_take] at hj
    rw [List.getElem_take] at hje
    have : j = i := (List.Nodup.getElem_inj_iff hnd).mp hje
    omega

/-- **Combinatorial edge structure of a chord piece.**  Every closed cycle edge
`e` of a chord piece `P = chordLeft W k` / `chordRight W k` has both endpoints in
`P`, and is *either* an honest closed edge of `W` *or* the cut diagonal (its
segment equals `segment ℝ u v`).  This is the purely combinatorial content behind
the corner escape of `chordPiece_other_neighbour_ptWind_zero` below: to control
the cycle edges of a piece it suffices to control `W`'s edges together with the
single diagonal `u–v`.  It is also consumed by the escape-walk branch in
`RequestProject.SAWUmlaufPolyEscape`. -/
lemma chordPiece_cycleEdge_or_diag (W : List ℂ) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (P : List ℂ) (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (e : ℂ × ℂ) (he : e ∈ HexArea.cycleEdges P) :
    (e.1 ∈ P ∧ e.2 ∈ P) ∧
      (e ∈ closedEdges W ∨ segment ℝ e.1 e.2 = segment ℝ u v) := by
  cases' hP with hP_left hP_right;
  · simp_all +decide [ HexArea.cycleEdges, List.zip ];
    obtain ⟨ i, hi, rfl ⟩ := List.mem_iff_get.mp he; simp_all +decide [ HexArea.chordLeft ] ;
    by_cases hi : ( i : ℕ ) < k <;> simp_all +decide [ List.getElem_append, List.getElem?_take ];
    · split_ifs <;> simp_all +decide [ List.mem_iff_getElem ];
      · refine' ⟨ ⟨ ⟨ i, by linarith, rfl ⟩, ⟨ i + 1, by linarith, rfl ⟩ ⟩, Or.inl ⟨ i, _, _ ⟩ ⟩ <;> norm_num [ closedEdges ];
        linarith;
        have hlt : (i : ℕ) + 1 < W.length := by omega
        rw [List.getElem_rotate]
        simp [Nat.mod_eq_of_lt hlt]
      · grind;
    · split_ifs <;> simp_all +decide [ List.getElem?_eq_none ];
      · cases hi.eq_or_lt <;> first | linarith | simp_all +decide [ List.getElem?_eq_none ] ;
        refine' ⟨ ⟨ _, _ ⟩, Or.inr _ ⟩;
        · rw [ List.mem_iff_get ];
          use ⟨ i, by
            simp +arith +decide [ List.length_take, hk ] ⟩
          generalize_proofs at *;
          grind;
        · rw [ List.mem_iff_getElem ] ; aesop;
        · rw [ segment_symm ];
          grind;
      · grind +suggestions;
  · unfold HexArea.cycleEdges at he; simp_all +decide [ List.mem_iff_get ] ;
    obtain ⟨ n, rfl ⟩ := he;
    by_cases hn : n.val < (HexArea.chordRight W k).length - 1;
    · refine' ⟨ ⟨ _, _ ⟩, Or.inl _ ⟩;
      · grind;
      · use ⟨ n + 1, by
          exact Nat.lt_pred_iff.mp hn ⟩
        generalize_proofs at *;
        grind;
      · use ⟨ n + k, by
          unfold HexArea.chordRight at hn; simp_all +decide [ List.length_append, List.length_take ] ;
          unfold closedEdges; simp +arith +decide [ List.length_zip ] ; omega; ⟩
        generalize_proofs at *;
        unfold closedEdges; simp +decide [ *, List.getElem_append ] ;
        unfold HexArea.chordRight; simp +decide [ *, List.getElem?_eq_getElem ] ;
        have hW0 : 0 < W.length := by omega
        have hlenR : (HexArea.chordRight W k).length = W.length - k + 1 := by
          simp [HexArea.chordRight]; omega
        have hn' : (n : ℕ) < W.length - k := by omega
        rw [dif_pos (by omega), dif_pos (by omega)]
        constructor
        · rw [List.getElem_append, dif_pos (by simpa using hn')]
          simp [List.getElem_drop, Nat.add_comm]
        · rw [List.getElem_rotate]
          by_cases hcase : (n : ℕ) + 1 < W.length - k
          · rw [List.getElem_append, dif_pos (by simpa using hcase)]
            have hmod : ((n : ℕ) + k + 1) % W.length = (n : ℕ) + k + 1 :=
              Nat.mod_eq_of_lt (by omega)
            simp only [hmod, List.getElem_drop]
            congr 1
            omega
          · have hEq : (n : ℕ) + 1 = W.length - k := by omega
            rw [List.getElem_append, dif_neg (by simp; omega)]
            have hmod : ((n : ℕ) + k + 1) % W.length = 0 := by
              have h1 : (n : ℕ) + k + 1 = W.length := by omega
              simp [h1]
            simp only [hmod, hEq]
            simp
    · have h_last : n.val = (HexArea.chordRight W k).length - 1 := by
        grind +qlia;
      rcases k with ( _ | k ) <;> simp_all +decide [ HexArea.chordRight ];
      rcases W with ( _ | ⟨ x, _ | ⟨ y, W ⟩ ⟩ ) <;> simp_all +decide [ List.getElem_append ];
      refine' ⟨ ⟨ ⟨ W.length + 1 - k, _ ⟩, _ ⟩, ⟨ ⟨ 0, _ ⟩, _ ⟩ ⟩ <;> simp_all +decide [ Nat.sub_sub ]

/-- Dropping the head does not change the last element of a nonempty tail. -/
lemma getLast?_cons_ne (a : ℂ) (L : List ℂ) (h : L ≠ []) : (a :: L).getLast? = L.getLast? := by
  cases L with
  | nil => simp at h
  | cons b M => simp [List.getLast?_cons_cons]

/-- **The cyclic neighbour of `u` in the other chord piece.**  For the left piece
`P = chordLeft W k = W.take (k+1)` the other piece contributes the cyclic
predecessor `W.getLast` of `u`; for the right piece
`P = chordRight W k = W.drop k ++ W.take 1` it contributes the cyclic successor
`W[1]`.  In both cases that vertex is a vertex of `W` outside `P`, and the
polygon `P` does not wind around it.

This is the witness consumed by `chord_ear_other_ptWind_zero_of_witness`, and it
is produced *without* any Jordan-curve input: `u` is strictly extreme, the two
cycle edges of `P` at `u` span a convex cone, the neighbour lies outside that
cone (because `v` is strictly inside the corner triangle), and the segment from
`u` to the neighbour is an edge of `W`, so it meets `P` only at `u`.  Hence
`HexArea.ptWind_zero_of_extreme_corner` applies. -/
lemma chordPiece_other_neighbour_ptWind_zero
    (W : List ℂ) (hsimple : PolygonSimple W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hint : InteriorChord W u v)
    (P : List ℂ) (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k) :
    ∃ y0 : ℂ, y0 ∈ W ∧ y0 ∉ P ∧ HexArea.ptWind y0 P = 0 := by
  classical
  obtain ⟨pu, nu, hhead, hlast, hnu, hext, hdir, hin⟩ := hint
  obtain ⟨d, hd⟩ := hdir
  obtain ⟨hk2, hkn⟩ := InteriorChord.index_bounds W k hk1 hk u v hv
    ⟨pu, nu, hhead, hlast, hnu, hext, ⟨d, hd⟩, hin⟩
  have hWnd : W.Nodup := hsimple.1
  have hu0 : W[0]'(by omega) = u := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
    exact (Option.some.injEq _ _ ▸ hhead)
  have hnu0 : W[1]'(by omega) = nu := by
    rw [List.getElem?_eq_getElem (by omega)] at hnu
    exact (Option.some.injEq _ _ ▸ hnu)
  have hpu0 : W[W.length - 1]'(by omega) = pu := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    exact (Option.some.injEq _ _ ▸ hlast)
  have hvk : W[k]'(by omega) = v := by
    rw [List.getElem?_eq_getElem (by omega)] at hv
    exact (Option.some.injEq _ _ ▸ hv)
  obtain ⟨hcpn, hcpv, hcnv⟩ := HexArea.cone_cross_ne pu u nu v hin
  rcases hP with hPl | hPr
  · -- **Left piece**: the other piece contributes the cyclic predecessor `pu` of `u`.
    subst hPl
    set P := HexArea.chordLeft W k with hPdef
    have hpuP : pu ∉ P := by
      rw [hPdef, HexArea.chordLeft]
      exact hpu0 ▸ not_mem_take_of_getElem W hWnd (W.length - 1) (k + 1) (by omega) (by omega)
    refine ⟨pu, hpu0 ▸ List.getElem_mem _, hpuP, ?_⟩
    have hPnd : P.Nodup := HexArea.chordLeft_nodup W k hWnd
    have hPlen : P.length = k + 1 := HexArea.chordLeft_length W k hk
    have hPhead : P.head? = some u := by
      rw [hPdef, HexArea.chordLeft_head]; exact hhead
    have hP1 : P[1]? = some nu := by
      rw [hPdef, HexArea.chordLeft, List.getElem?_take_of_lt (by omega)]
      exact hnu
    have hPlast : P.getLast? = some v := by
      rw [hPdef, HexArea.chordLeft_getLast W k (by omega)]; exact hv
    have hpuU : pu ≠ u := by
      rw [← hpu0, ← hu0]
      intro hcon
      have : W.length - 1 = 0 := (List.Nodup.getElem_inj_iff hWnd).mp hcon
      omega
    refine HexArea.ptWind_zero_of_corner_head P hPnd (by omega) u nu v pu d hPhead hP1 hPlast
      ?_ hpuU ?_ ?_
    · intro y hy hyu
      exact hd y (HexArea.mem_of_mem_chordLeft W k hy) hyu
    · exact HexArea.not_mem_cornerCone_of_inConeStrict pu u nu v hin
    · intro e he w hw hwe
      rcases HexArea.cycleEdges_at_head P hPnd u nu v hPhead hP1 hPlast (by omega) e he with
        hboth | hcase | hcase
      · obtain ⟨⟨he1P, he2P⟩, hclass⟩ :=
          chordPiece_cycleEdge_or_diag W k hk1 hk u v hu hv P (Or.inl rfl) e he
        rcases hclass with heW | hseg
        · exfalso
          have hpuE : (pu, u) ∈ closedEdges W := by
            refine mem_closedEdges_pair W (W.length - 1) 0 (by omega) (by omega) ?_ pu u hpu0 hu0
            have h : W.length - 1 + 1 = W.length := by omega
            rw [h, Nat.mod_self]
          have h1 : e.1 ≠ pu := fun hc => hpuP (hc ▸ he1P)
          have h2 : e.2 ≠ pu := fun hc => hpuP (hc ▸ he2P)
          have hdisj := hsimple.2 e heW (pu, u) hpuE h1 hboth.1 h2 hboth.2
          rw [Set.disjoint_left] at hdisj
          exact hdisj hwe (by rw [segment_symm] at hw; exact hw)
        · rw [hseg] at hwe
          exact segment_meet_apex u pu v hcpv w hw hwe
      · rw [hcase] at hwe
        exact segment_meet_apex u pu nu hcpn w hw hwe
      · rw [hcase] at hwe
        simp only at hwe
        rw [segment_symm] at hwe
        exact segment_meet_apex u pu v hcpv w hw hwe
  · -- **Right piece**: the other piece contributes the cyclic successor `nu` of `u`.
    subst hPr
    set R := HexArea.chordRight W k with hRdef
    set Q := u :: W.drop k with hQdef
    have hQrot : R.rotate (W.length - k) = Q := by
      have h1 : W.take 1 = [u] := by
        rcases W with _ | ⟨a, L⟩
        · simp at hu
        · simp at hu ⊢; exact hu
      have hdroplen : (W.drop k).length = W.length - k := by simp
      rw [hRdef, HexArea.chordRight, List.rotate_eq_drop_append_take (by simp)]
      rw [← hdroplen, List.drop_left, List.take_left, h1]
      rfl
    have hnuR : nu ∉ R := by
      rw [hRdef, HexArea.chordRight]
      exact hnu0 ▸ not_mem_drop_append_take W hWnd 1 k (by omega) le_rfl (by omega)
    refine ⟨nu, hnu0 ▸ List.getElem_mem _, hnuR, ?_⟩
    have hRnd : R.Nodup := HexArea.chordRight_nodup W k hk1 (by omega) hWnd
    have hQnd : Q.Nodup := by rw [← hQrot]; exact List.nodup_rotate.mpr hRnd
    have hrot : HexArea.ptWind nu Q = HexArea.ptWind nu R := by
      rw [← hQrot, HexArea.ptWind_rotate]
    rw [← hrot]
    have hQlen : 2 ≤ Q.length := by rw [hQdef]; simp; omega
    have hQhead : Q.head? = some u := rfl
    have hQ1 : Q[1]? = some v := by
      rw [hQdef]
      simp only [List.getElem?_cons_succ, List.getElem?_drop]
      simpa using hv
    have hQlast : Q.getLast? = some pu := by
      rw [hQdef, getLast?_cons_ne _ _ (by simp; omega), List.getLast?_eq_getElem?]
      simp only [List.getElem?_drop, List.length_drop]
      have h : k + (W.length - k - 1) = W.length - 1 := by omega
      rw [h, List.getElem?_eq_getElem (by omega), hpu0]
    have hnuU : nu ≠ u := by
      rw [← hnu0, ← hu0]
      intro hcon
      have : (1:ℕ) = 0 := (List.Nodup.getElem_inj_iff hWnd).mp hcon
      omega
    refine HexArea.ptWind_zero_of_corner_head Q hQnd hQlen u v pu nu d hQhead hQ1 hQlast
      ?_ hnuU ?_ ?_
    · intro y hy hyu
      refine hd y ?_ hyu
      rw [hQdef] at hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hu0 ▸ List.getElem_mem _
      · exact List.mem_of_mem_drop hy'
    · exact HexArea.not_mem_cornerCone_of_inConeStrict' pu u nu v hin
    · intro e he w hw hwe
      have heR : e ∈ HexArea.cycleEdges R := by
        rw [HexArea.cycleEdges_eq_closedEdges] at he ⊢
        rw [← hQrot] at he
        exact (mem_closedEdges_rotate R (W.length - k) e).mp he
      rcases HexArea.cycleEdges_at_head Q hQnd u v pu hQhead hQ1 hQlast hQlen e he with
        hboth | hcase | hcase
      · obtain ⟨⟨he1P, he2P⟩, hclass⟩ :=
          chordPiece_cycleEdge_or_diag W k hk1 hk u v hu hv R (Or.inr rfl) e heR
        rcases hclass with heW | hseg
        · exfalso
          have hnuE : (u, nu) ∈ closedEdges W := by
            refine mem_closedEdges_pair W 0 1 (by omega) (by omega) ?_ u nu hu0 hnu0
            rw [Nat.mod_eq_of_lt (by omega)]
          have h1 : e.1 ≠ nu := fun hc => hnuR (hc ▸ he1P)
          have h2 : e.2 ≠ nu := fun hc => hnuR (hc ▸ he2P)
          have hdisj := hsimple.2 e heW (u, nu) hnuE hboth.1 h1 hboth.2 h2
          rw [Set.disjoint_left] at hdisj
          exact hdisj hwe hw
        · rw [hseg] at hwe
          exact segment_meet_apex u nu v hcnv w hw hwe
      · rw [hcase] at hwe
        exact segment_meet_apex u nu v hcnv w hw hwe
      · rw [hcase] at hwe
        simp only at hwe
        rw [segment_symm] at hwe
        exact segment_meet_apex u nu pu (cross_ne_swap _ _ hcpn) w hw hwe

end
