/-
# Half-plane Walk Decomposition Helpers

Key helper lemmas for the Hammersley-Welsh bridge decomposition.
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## diagCoord and walk properties -/

/-- The diagonal coordinate of a hex vertex. -/
def diagCoordHW (v : HexVertex) : ℤ := v.1 + v.2.1

@[simp] lemma diagCoordHW_paperStart : diagCoordHW paperStart = 0 := by
  simp [diagCoordHW, paperStart]

/-- The minimum diagCoord over a nonempty list of integers. -/
def listMin : List ℤ → ℤ
  | [] => 0
  | [a] => a
  | a :: b :: l => min a (listMin (b :: l))

/-- The minimum diagCoord value in a walk's support. -/
def walk_min_dc {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map diagCoordHW).foldl min (diagCoordHW v)

/-
Every vertex in the support has diagCoord ≥ walk_min_dc.
-/
lemma walk_min_dc_le {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    walk_min_dc p ≤ diagCoordHW u := by
  have h_foldl_min : ∀ {l : List ℤ} {x : ℤ}, x ∈ l → List.foldl min (diagCoordHW v) l ≤ x := by
    intros l x hx; induction' l using List.reverseRecOn with l IH <;> aesop;
  exact h_foldl_min <| List.mem_map.mpr ⟨ u, hu, rfl ⟩

/-
walk_min_dc is achieved by some vertex.
-/
lemma walk_min_dc_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, diagCoordHW u = walk_min_dc p := by
  simp_all +decide [ walk_min_dc ];
  have h_min : ∀ {l : List ℤ}, l ≠ [] → ∃ x ∈ l, x = List.foldl min (List.head! l) l := by
    intros l hl_nonempty; induction' l using List.reverseRecOn with l ih; aesop;
    cases l <;> simp_all +decide [ List.foldl_append ];
    grind;
  specialize @h_min ( List.map diagCoordHW p.support ) ; simp_all +decide [ List.map ];
  cases p <;> aesop

/-- The width of a walk from paperStart: |min diagCoord|. -/
def walk_width {w : HexVertex} (p : hexGraph.Walk paperStart w) : ℕ :=
  (-(walk_min_dc p)).toNat

/-
Walk width is bounded by walk length (each step changes diagCoord by ≤ 1).
-/
lemma walk_width_le_length {w : HexVertex} (p : hexGraph.Walk paperStart w) :
    walk_width p ≤ p.length := by
  rw [ walk_width ];
  rw [ Int.toNat_le ];
  -- Apply the lemma that states the minimum of the diagonal coordinates of the walk is greater than or equal to the negative of the length of the walk.
  apply le_of_not_gt; intro h_contra;
  -- By definition of `walk_min_dc`, there exists a vertex `u` in the support of `p` such that `diagCoordHW u = walk_min_dc p`.
  obtain ⟨u, hu⟩ : ∃ u ∈ p.support, diagCoordHW u = walk_min_dc p := by
    exact?;
  have := hexGraph_walk_sum_bound_neg ( p.takeUntil u hu.1 ) ; simp_all +decide [ diagCoordHW ] ;
  unfold diagCoordHW at hu; norm_num [ paperStart ] at *; linarith [ show ( p.takeUntil u hu.1 |> SimpleGraph.Walk.length ) ≤ p.length from by exact? ] ;

/-- The suffix of a walk after a vertex at minimum diagCoord
    has all vertices with diagCoord ≥ that of the splitting vertex. -/
lemma suffix_dc_bound {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support)
    (hu_min : ∀ z ∈ p.support, diagCoordHW u ≤ diagCoordHW z) :
    ∀ z ∈ (p.dropUntil u hu).support, diagCoordHW u ≤ diagCoordHW z := by
  intro z hz
  exact hu_min z (p.support_dropUntil_subset hu hz)

end