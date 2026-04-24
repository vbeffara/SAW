/-
# Hammersley-Welsh Bridge Decomposition helpers

Helper lemmas for the bridge decomposition counting inequality.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWHWCore

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk max diagCoord -/

/-- Maximum diagCoord achieved in a walk, using foldl max. -/
def maxDiagInWalk' {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map diagCoordZ).foldl max (diagCoordZ v)

/-
Every vertex in the walk has diagCoord ≤ maxDiagInWalk'.
-/
lemma maxDiagInWalk'_ge {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    diagCoordZ u ≤ maxDiagInWalk' p := by
  have h_foldl : ∀ {l : List ℤ}, u ∈ p.support → diagCoordZ u ∈ l → diagCoordZ u ≤ List.foldl max (diagCoordZ v) l := by
    intros l hu hl; induction' l using List.reverseRecOn with l ih <;> aesop;
  exact h_foldl hu ( List.mem_map.mpr ⟨ u, hu, rfl ⟩ )

/-
The maxDiag is achieved by some vertex.
-/
lemma maxDiagInWalk'_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, diagCoordZ u = maxDiagInWalk' p := by
  unfold maxDiagInWalk';
  induction' p using SimpleGraph.Walk.recOn with p ih;
  · aesop;
  · simp +zetaDelta at *;
    rename_i h₁ h₂ h₃;
    by_cases h : List.foldl max ( diagCoordZ ih ) ( List.map diagCoordZ h₂.support ) = diagCoordZ ih;
    · exact Or.inl h.symm;
    · have h_max : ∀ {l : List ℤ}, l ≠ [] → ∃ x ∈ l, x = List.foldl max (List.head! l) l := by
        intros l hl_nonempty; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ] ;
        cases l <;> simp_all +decide [ List.foldl ];
        grind;
      specialize @h_max ( List.map diagCoordZ h₂.support |> List.cons ( diagCoordZ ih ) ) ; simp_all +decide

/-- Start diagCoord ≤ max. -/
lemma maxDiagInWalk'_ge_start {v w : HexVertex} (p : hexGraph.Walk v w) :
    diagCoordZ v ≤ maxDiagInWalk' p :=
  maxDiagInWalk'_ge p v p.start_mem_support

/-
Width (max - min) ≤ length for any walk.
-/
lemma walk_width_le_length' {v w : HexVertex} (p : hexGraph.Walk v w) :
    (maxDiagInWalk' p - walkMinDiagCoord p).toNat ≤ p.length := by
  -- Let $u$ be a vertex in $p$ such that $diagCoordZ u = maxDiagInWalk' p$.
  obtain ⟨u, hu⟩ : ∃ u ∈ p.support, diagCoordZ u = maxDiagInWalk' p := by
    exact?;
  obtain ⟨q₁, q₂, hq⟩ : ∃ q₁ : hexGraph.Walk v u, ∃ q₂ : hexGraph.Walk u w, p = q₁.append q₂ := by
    exact ⟨ p.takeUntil u hu.1, p.dropUntil u hu.1, by aesop ⟩;
  -- Let $v$ be a vertex in $p$ such that $diagCoordZ v = walkMinDiagCoord p$.
  obtain ⟨v, hv⟩ : ∃ v ∈ p.support, diagCoordZ v = walkMinDiagCoord p := by
    apply walkMinDiagCoord_achieved;
  by_cases hvu : v ∈ q₁.support;
  · have h_subwalk : ∃ q : hexGraph.Walk v u, q.length ≤ p.length ∧ diagCoordZ u - diagCoordZ v ≤ q.length := by
      use q₁.dropUntil v hvu;
      have h_subwalk : diagCoordZ u - diagCoordZ v ≤ (q₁.dropUntil v hvu).length := by
        have := walk_diagCoordZ_bound ( q₁.dropUntil v hvu ) u ?_ <;> aesop;
      simp_all +decide [ SimpleGraph.Walk.length_append ];
      exact le_add_right ( by exact? );
    grind;
  · obtain ⟨q₃, q₄, hq'⟩ : ∃ q₃ : hexGraph.Walk u v, ∃ q₄ : hexGraph.Walk v w, q₂ = q₃.append q₄ := by
      exact ⟨ q₂.takeUntil v ( by aesop ), q₂.dropUntil v ( by aesop ), by aesop ⟩;
    have := walk_diagCoordZ_bound q₃ v; simp_all +decide ;
    linarith

/-! ## Product expansion identity -/

/-- ∏(1 + f(i)) = ∑_{S⊆range} ∏_{i∈S} f(i) -/
lemma prod_one_add_eq (N : ℕ) (f : ℕ → ℝ) :
    ∏ T ∈ Finset.range N, (1 + f T) =
    ∑ S ∈ (Finset.range N).powerset, ∏ T ∈ S, f T :=
  Finset.prod_one_add (s := Finset.range N) (f := f)

end