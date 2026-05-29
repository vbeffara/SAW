/-
# Bridge count any ≤ bridge count + shifted bridge count

Proof that bridge_count_any T k ≤ bridge_count T k + bridge_count T (k-1).
-/

import Mathlib
import RequestProject.SAWHWStepHelpers
import RequestProject.SAWHWConvBound

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 8000000

/-- Count of bridges with TRUE endpoint at dc=-T. -/
def bridge_count_true (T k : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun s : SAW paperStart k =>
    s.w.1 + s.w.2.1 = -(T : ℤ) ∧ s.w.2.2 = true ∧
    ∀ v ∈ s.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0))

lemma bridge_count_any_eq_sum (T k : ℕ) :
    bridge_count_any T k = bridge_count T k + bridge_count_true T k := by
  simp [bridge_count_any, bridge_count, bridge_count_true];
  rw [ ← Finset.card_union_of_disjoint ];
  · congr with s ; by_cases h : s.w.2.2 = false <;> aesop;
  · exact Finset.disjoint_filter.mpr ( by aesop )

lemma true_bridge_penultimate_false (T k : ℕ) (hk : 0 < k)
    (s : SAW paperStart k)
    (hdc : s.w.1 + s.w.2.1 = -(T : ℤ))
    (htrue : s.w.2.2 = true)
    (hstrip : ∀ v ∈ s.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) :
    (s.p.1.getVert (k - 1)).2.2 = false ∧
    (s.p.1.getVert (k - 1)).1 + (s.p.1.getVert (k - 1)).2.1 = -(T : ℤ) ∧
    s.p.1.getVert (k - 1) = (s.w.1, s.w.2.1, false) := by
  have h_walk_length : (SimpleGraph.Walk.getVert (s.p.1) k) = s.w := by
    grind +suggestions;
  have h_last_vertex : hexGraph.Adj (SimpleGraph.Walk.getVert (s.p.1) (k - 1)) (SimpleGraph.Walk.getVert (s.p.1) k) := by
    convert s.p.1.adj_getVert_succ _ using 1;
    · rw [ Nat.sub_add_cancel hk ];
    · rw [ s.l ] ; omega;
  unfold hexGraph at h_last_vertex; simp_all +decide ;
  grind +suggestions

/-! ## Truncation function -/

def truncateTrueBridge (T : ℕ) (k : ℕ)
    (s : SAW paperStart (k + 1))
    (hdc : s.w.1 + s.w.2.1 = -(T : ℤ))
    (htrue : s.w.2.2 = true)
    (hstrip : ∀ v ∈ s.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) :
    SAW paperStart k :=
  ⟨s.p.1.getVert k,
   ⟨s.p.1.take k, walk_take_isPath s.p.1 s.p.2 k⟩,
   by simp [SimpleGraph.Walk.take_length, s.l]⟩

lemma truncateTrueBridge_is_bridge (T : ℕ) (k : ℕ)
    (s : SAW paperStart (k + 1))
    (hdc : s.w.1 + s.w.2.1 = -(T : ℤ))
    (htrue : s.w.2.2 = true)
    (hstrip : ∀ v ∈ s.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) :
    let t := truncateTrueBridge T k s hdc htrue hstrip
    t.w.1 + t.w.2.1 = -(T : ℤ) ∧
    t.w.2.2 = false ∧
    ∀ v ∈ t.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0 := by
  obtain ⟨h_false, h_dc, h_true⟩ := true_bridge_penultimate_false T (k + 1) (Nat.succ_pos k) s hdc htrue hstrip;
  unfold truncateTrueBridge;
  refine' ⟨ h_dc, h_false, fun v hv => hstrip v _ ⟩;
  have h_support_take : ∀ {u v : HexVertex} {p : hexGraph.Walk u v} {k : ℕ}, (p.take k).support ⊆ p.support := by
    intros u v p k; induction' p with u v p ih generalizing k <;> simp +decide [ *, SimpleGraph.Walk.take ] ;
    cases k <;> simp +decide [ *, SimpleGraph.Walk.take ];
  exact h_support_take hv

/-
A walk of length 1 has support [start, end].
-/
lemma walk_length_one_support {u v : HexVertex} (p : hexGraph.Walk u v)
    (hp : p.length = 1) :
    p.support = [u, v] := by
  rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> aesop

/-
The truncation is injective.
-/
lemma truncateTrueBridge_injective (T : ℕ) (k : ℕ)
    (s₁ s₂ : SAW paperStart (k + 1))
    (h₁dc : s₁.w.1 + s₁.w.2.1 = -(T : ℤ)) (h₂dc : s₂.w.1 + s₂.w.2.1 = -(T : ℤ))
    (h₁t : s₁.w.2.2 = true) (h₂t : s₂.w.2.2 = true)
    (h₁s : ∀ v ∈ s₁.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
    (h₂s : ∀ v ∈ s₂.p.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
    (h_eq : truncateTrueBridge T k s₁ h₁dc h₁t h₁s =
            truncateTrueBridge T k s₂ h₂dc h₂t h₂s) :
    s₁ = s₂ := by
  apply suffix_fiber_injective (k + 1) k s₁ s₂;
  · linarith [ s₁.l ];
  · linarith [ s₂.l ];
  · convert congr_arg ( fun s : SAW paperStart k => s.p.1.support ) h_eq using 1;
  · rw [ walk_length_one_support, walk_length_one_support ];
    · have := true_bridge_penultimate_false T ( k + 1 ) ( Nat.succ_pos _ ) s₁ h₁dc h₁t h₁s; have := true_bridge_penultimate_false T ( k + 1 ) ( Nat.succ_pos _ ) s₂ h₂dc h₂t h₂s; simp_all +decide [ truncateTrueBridge ] ;
      grind;
    · simp +decide [ SimpleGraph.Walk.drop_length, s₂.l ];
    · simp +decide [ SimpleGraph.Walk.drop_length, s₁.l ]

lemma bridge_count_true_zero (T : ℕ) (hT : 1 ≤ T) : bridge_count_true T 0 = 0 := by
  convert Finset.card_eq_zero.mpr ?_;
  ext ⟨ w, p, hl ⟩ ; simp +decide [ SAW ] ;
  rcases p with ⟨ _ | ⟨ a, p ⟩, hp ⟩ <;> simp_all +decide [ SimpleGraph.Walk.length ];
  exact fun h => absurd h ( by norm_num [ paperStart ] ; linarith )

lemma bridge_count_true_succ_le (T : ℕ) (k : ℕ) (hT : 1 ≤ T) :
    bridge_count_true T (k + 1) ≤ bridge_count T k := by
  unfold bridge_count_true bridge_count;
  apply Finset.card_le_card_of_injOn;
  case f => exact fun s => ⟨ s.p.1.getVert k, ⟨ s.p.1.take k, walk_take_isPath s.p.1 s.p.2 k ⟩, by simp +decide [ SimpleGraph.Walk.take_length, s.l ] ⟩;
  · intro s hs; simp_all +decide [ Set.MapsTo ] ;
    convert truncateTrueBridge_is_bridge T k s hs.1 hs.2.1 _;
    all_goals norm_num [ truncateTrueBridge ];
    congr! 3;
    exact hs.2.2;
  · intro s hs t ht h_eq;
    apply truncateTrueBridge_injective T k s t (by
    grind) (by
    grind) (by
    grind +splitImp) (by
    grind) (by
    grind +ring) (by
    grind) h_eq

lemma bridge_count_true_le_shifted (T k : ℕ) (hT : 1 ≤ T) :
    bridge_count_true T k ≤ bridge_count T (k - 1) := by
  rcases k with _ | k
  · simp [bridge_count_true_zero T hT]
  · simp; exact bridge_count_true_succ_le T k hT

theorem bridge_count_any_le_shifted' (T k : ℕ) (hT : 1 ≤ T) :
    bridge_count_any T k ≤ bridge_count T k + bridge_count T (k - 1) := by
  calc bridge_count_any T k = bridge_count T k + bridge_count_true T k :=
        bridge_count_any_eq_sum T k
    _ ≤ bridge_count T k + bridge_count T (k - 1) :=
        Nat.add_le_add_left (bridge_count_true_le_shifted T k hT) _

end