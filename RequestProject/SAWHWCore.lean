/-
# Core lemmas for the Hammersley-Welsh bridge decomposition
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## DiagCoord basics -/

/-- Diagonal coordinate of a HexVertex. -/
def diagCoordZ (v : HexVertex) : ℤ := v.1 + v.2.1

@[simp] lemma diagCoordZ_paperStart : diagCoordZ paperStart = 0 := by
  simp [diagCoordZ, paperStart]

/-- Each hex edge changes diagCoord by at most 1 in absolute value. -/
lemma diagCoordZ_adj_bound {v w : HexVertex} (h : hexGraph.Adj v w) :
    diagCoordZ w - diagCoordZ v ≤ 1 ∧ -(1 : ℤ) ≤ diagCoordZ w - diagCoordZ v := by
  unfold diagCoordZ hexGraph at *
  rcases h with ⟨_, _, h3 | h3 | h3⟩ | ⟨_, _, h3 | h3 | h3⟩ <;>
    simp_all <;> omega

/-
In a walk, all diagCoords are within walk length of the start.
-/
lemma walk_diagCoordZ_bound {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    diagCoordZ u - diagCoordZ v ≤ p.length ∧
    -(p.length : ℤ) ≤ diagCoordZ u - diagCoordZ v := by
  induction' p with v w p ih generalizing u ; simp_all +decide [ SimpleGraph.Walk.support ];
  cases hu;
  · grind;
  · rename_i h₁ h₂ h₃;
    have := diagCoordZ_adj_bound ‹_›;
    constructor <;> norm_num <;> linarith [ h₂ u h₃ ]

/-! ## Walk minimum diagCoord -/

/-- The minimum diagCoord achieved in a walk. -/
def walkMinDiagCoord {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  p.support.foldl (fun m u => min m (diagCoordZ u)) (diagCoordZ v)

/-
The minimum is ≤ every vertex's diagCoord.
-/
lemma walkMinDiagCoord_le {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    walkMinDiagCoord p ≤ diagCoordZ u := by
  have h_min_le : ∀ {l : List HexVertex}, u ∈ l → List.foldl (fun m u => min m (diagCoordZ u)) (diagCoordZ v) l ≤ diagCoordZ u := by
    intros l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
  exact h_min_le hu

/-- The minimum is ≤ the start's diagCoord. -/
lemma walkMinDiagCoord_le_start {v w : HexVertex} (p : hexGraph.Walk v w) :
    walkMinDiagCoord p ≤ diagCoordZ v :=
  walkMinDiagCoord_le p v p.start_mem_support

/-
The minimum is achieved by some vertex in the support.
-/
lemma walkMinDiagCoord_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, diagCoordZ u = walkMinDiagCoord p := by
  induction' p with v w p ih;
  · exact ⟨ v, by simp +decide [ walkMinDiagCoord ] ⟩;
  · unfold walkMinDiagCoord; simp +decide [ SimpleGraph.Walk.support_cons ] ;
    have h_min : ∀ {l : List HexVertex}, l ≠ [] → ∃ u ∈ l, List.foldl (fun m u => min m (diagCoordZ u)) (diagCoordZ w) l = diagCoordZ u ∨ List.foldl (fun m u => min m (diagCoordZ u)) (diagCoordZ w) l = diagCoordZ w := by
      intros l hl_nonempty; induction' l using List.reverseRecOn with l ih;
      · contradiction;
      · grind +splitImp;
    specialize @h_min ( ‹hexGraph.Walk p ih›.support ) ; aesop

/-! ## Bridge width and length -/

/-
A PaperBridge of width T has walk length ≥ T.
    The bridge goes from diagCoord 0 to diagCoord -T, and each step
    changes diagCoord by at most 1.
-/
lemma hw_bridge_length_ge (T : ℕ) (b : PaperBridge T) :
    T ≤ b.walk.1.length := by
  apply paper_bridge_length_ge

/-! ## Walk splitting at a vertex -/

/-
A walk can be split at any vertex in its support. The total length
    equals the sum of the two halves.
-/
lemma walk_split_at_vertex {v w u : HexVertex} (p : hexGraph.Walk v w)
    (hu : u ∈ p.support) :
    (p.takeUntil u hu).length + (p.dropUntil u hu).length = p.length := by
  convert congr_arg SimpleGraph.Walk.length ( SimpleGraph.Walk.take_spec p hu ) using 1;
  rw [ SimpleGraph.Walk.length_append ]

/-
If a vertex has min diagCoord in a half of a split walk,
    it also has min diagCoord in that half.
-/
lemma dropUntil_min_diagCoord {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support)
    (hmin : ∀ z ∈ p.support, diagCoordZ u ≤ diagCoordZ z) :
    ∀ z ∈ (p.dropUntil u hu).support, diagCoordZ u ≤ diagCoordZ z := by
  intro z hz;
  apply hmin;
  -- Since $z$ is in the support of $p.dropUntil u hu$, it must be in the support of $p$.
  have h_support_subset : (p.dropUntil u hu).support ⊆ p.support := by
    exact?;
  exact h_support_subset hz

/-! ## Bridge weight bounds -/

/-
For 0 < x ≤ 1 and walk length n ≥ sum of bridge lengths + gaps,
    x^n ≤ product of x^{bridge_lengths}.
-/
lemma pow_le_prod_pow {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    {n : ℕ} {lengths : List ℕ} (hsum : lengths.sum ≤ n) :
    x ^ n ≤ (lengths.map (x ^ ·)).prod := by
  have h_prod_exp : (List.map (fun x_1 => x ^ x_1) lengths).prod = x ^ lengths.sum := by
    induction lengths <;> simp_all +decide [ pow_add ];
    exact Or.inl <| ‹ ( _ : List ℕ ).sum ≤ n → _› <| by linarith;
  exact h_prod_exp.symm ▸ pow_le_pow_of_le_one hx.le hx1 hsum

end