/-
# Walk Splitting at Minimum DiagCoord

For the Hammersley-Welsh bridge decomposition, we split each SAW at its
first vertex of minimal diagCoord (= x + y). This gives two half-plane walks.

## Key results

- `walk_min_diagCoord_exists`: every non-empty walk achieves its minimum diagCoord
- `saw_split_at_minDiag`: split an n-step SAW at the first vertex of minimum diagCoord
- `saw_half_maxDiag_bound`: the maximum diagCoord in each half is bounded

## Reference

Section 3 of Duminil-Copin & Smirnov (2012).
-/

import Mathlib
import RequestProject.SAWWalkPartition

noncomputable section

/-- The diagonal coordinate of a hex vertex. -/
abbrev diagCoord (v : HexVertex) : ℤ := v.1 + v.2.1

/-- The minimum diagCoord over the support of a walk. -/
def walk_min_diagCoord {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map diagCoord).foldl min (diagCoord v)

/-
The minimum diagCoord is at most the start's diagCoord.
-/
lemma walk_min_diagCoord_le_start {v w : HexVertex} (p : hexGraph.Walk v w) :
    walk_min_diagCoord p ≤ diagCoord v := by
  unfold walk_min_diagCoord;
  induction p.support using List.reverseRecOn <;> aesop

/-
Every vertex in the support has diagCoord ≥ walk_min_diagCoord.
-/
lemma walk_min_diagCoord_bound {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    walk_min_diagCoord p ≤ diagCoord u := by
  -- Apply the property of the minimum function repeatedly to show that the minimum of a list is less than or equal to any element in the list.
  have h_foldl_min_le : ∀ (l : List ℤ) (x : ℤ), x ∈ l → List.foldl min (diagCoord v) l ≤ x := by
    intros l x hx; induction' l using List.reverseRecOn with l IH <;> aesop;
  exact h_foldl_min_le _ _ ( List.mem_map.mpr ⟨ u, hu, rfl ⟩ )

/-
The minimum diagCoord is achieved by some vertex in the support.
-/
lemma walk_min_diagCoord_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, diagCoord u = walk_min_diagCoord p := by
  -- The list of diagonal coordinates in the support is non-empty since it includes the starting vertex.
  have h_nonempty : (p.support.map diagCoord).length > 0 := by
    cases p <;> aesop;
  have h_min_achieved : ∀ {l : List ℤ}, l.length > 0 → ∃ u ∈ l, u = List.foldl min (l.head!) l := by
    intros l hl_nonempty
    induction' l using List.reverseRecOn with l ih;
    · contradiction;
    · cases l <;> simp_all +decide [ List.foldl_append ];
      grind;
  convert h_min_achieved h_nonempty using 1;
  simp +decide [ walk_min_diagCoord ];
  cases p <;> aesop

/-
The number of distinct SAWs from hexOrigin of length 1 is 3.
-/
lemma saw_count_one : saw_count 1 = 3 := by
  convert Fintype.card_eq_nat_card;
  convert Nat.card_congr ?_;
  rotate_left;
  exact { w : HexVertex // hexGraph.Adj hexOrigin w };
  · refine' Equiv.ofBijective _ ⟨ _, _ ⟩;
    refine' fun w => ⟨ w.val, ⟨ SimpleGraph.Walk.cons w.prop SimpleGraph.Walk.nil, by
      simp +decide [ SimpleGraph.Walk.isPath_def ];
      exact fun h => by have := w.2; simp_all +decide [ hexGraph ] ; ⟩, by
      rfl ⟩
    all_goals generalize_proofs at *;
    · intro w₁ w₂ h; aesop;
    · rintro ⟨ w, p, l ⟩;
      rcases p with ⟨ _ | ⟨ _, _ ⟩, _ ⟩ ; aesop;
      cases ‹SimpleGraph.Walk _ _ _› <;> aesop;
  · rw [ show { w : HexVertex // hexGraph.Adj hexOrigin w } = { w : HexVertex | hexGraph.Adj hexOrigin w } by rfl, show { w : HexVertex | hexGraph.Adj hexOrigin w } = { ( 0, 0, true ), ( 1, 0, true ), ( 0, 1, true ) } from ?_ ];
    · simp +decide [ Set.toFinset_card ];
    · ext w; simp [hexOrigin, hexGraph];
      grind

/-
The number of distinct SAWs from hexOrigin of length 2 is 6.
-/
lemma saw_count_two : saw_count 2 = 6 := by
  have h_saw_count_2 : saw_count 2 = 6 := by
    have h_saw_count_2 : saw_count 2 = Fintype.card (SAW hexOrigin 2) := by
      rfl
    convert Fintype.card_eq.mpr _;
    rotate_left;
    exact { p : HexVertex × HexVertex // hexGraph.Adj hexOrigin p.1 ∧ hexGraph.Adj p.1 p.2 ∧ hexOrigin ≠ p.2 };
    exact Fintype.ofFinset ( Finset.filter ( fun p : HexVertex × HexVertex => hexGraph.Adj hexOrigin p.1 ∧ hexGraph.Adj p.1 p.2 ∧ hexOrigin ≠ p.2 ) ( Finset.product ( Finset.image ( fun x : ℤ × ℤ => ( x.1, x.2, true ) ) ( Finset.Icc ( -1 ) 1 ×ˢ Finset.Icc ( -1 ) 1 ) ) ( Finset.image ( fun x : ℤ × ℤ => ( x.1, x.2, false ) ) ( Finset.Icc ( -1 ) 1 ×ˢ Finset.Icc ( -1 ) 1 ) ) ) ) ( by
      intro p; constructor <;> intro hp <;> simp_all +decide [ hexGraph ] ;
      · exact ⟨ hp.2.1, hp.2.2.1, hp.2.2.2 ⟩;
      · rcases hp with ⟨ hp₁, hp₂, hp₃ ⟩ ; rcases p with ⟨ ⟨ a, b, c ⟩, ⟨ d, e, f ⟩ ⟩ ; simp_all +decide [ hexOrigin ] ;
        omega );
    · refine' ⟨ _ ⟩;
      refine' Equiv.ofBijective ( fun s => ⟨ ( s.p.1.getVert 1, s.p.1.getVert 2 ), _, _, _ ⟩ ) ⟨ _, _ ⟩;
      all_goals norm_num [ Function.Injective, Function.Surjective ];
      · rcases s with ⟨ p, hp ⟩;
        rcases hp with ⟨ _ | ⟨ a, _ | ⟨ b, _ | hp ⟩ ⟩ ⟩ <;> aesop;
      · rcases s with ⟨ ⟨ p, hp ⟩, l ⟩;
        rcases l with ⟨ _ | ⟨ a, _ | ⟨ b, _ | l ⟩ ⟩ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
        · contradiction;
        · cases ‹_›;
      · rcases s with ⟨ _ | ⟨ a, _ | ⟨ b, _ | s ⟩ ⟩, _ | ⟨ c, _ | ⟨ d, _ | t ⟩ ⟩, _ | ⟨ e, _ | ⟨ f, _ | u ⟩ ⟩ ⟩ <;> simp +decide [ HexVertex ] at *;
        · aesop;
        · exact ne_of_apply_ne Prod.fst ( by simp +decide [ hexOrigin ] );
        · exact ne_of_apply_ne Prod.fst ( by simp +decide [ hexOrigin ] );
      · rintro ⟨ w₁, p₁, hp₁ ⟩ ⟨ w₂, p₂, hp₂ ⟩ h₁ h₂;
        rcases p₁ with ⟨ _ | ⟨ a, _ | ⟨ b, _ | p₁ ⟩ ⟩ ⟩ <;> rcases p₂ with ⟨ _ | ⟨ c, _ | ⟨ d, _ | p₂ ⟩ ⟩ ⟩ <;> norm_num at *;
        all_goals norm_num [ SimpleGraph.Walk.length ] at *;
        · aesop;
        · lia;
        · linarith;
        · grind;
      · intro a b;
        constructor <;> intro a_1 a_2 <;> constructor <;> intro h₁ h₂ h₃;
        · cases h₁ ; cases h₂ ; aesop;
          · tauto;
          · cases ‹_› ; contradiction;
        · refine' ⟨ ⟨ ( a_1, a_2, true ), ⟨ SimpleGraph.Walk.cons h₁ ( SimpleGraph.Walk.cons h₂ SimpleGraph.Walk.nil ), _ ⟩, _ ⟩, _, _ ⟩ <;> simp +decide [ SimpleGraph.Walk.getVert ];
          exact ⟨ by rintro ⟨ ⟩ ; contradiction, h₃ ⟩;
        · refine' ⟨ ⟨ ( a_1, a_2, false ), ⟨ SimpleGraph.Walk.cons h₁ ( SimpleGraph.Walk.cons h₂ SimpleGraph.Walk.nil ), _ ⟩, _ ⟩, _, _ ⟩ <;> simp +decide [ SimpleGraph.Walk.getVert ];
          exact ⟨ by rintro ⟨ ⟩, h₃ ⟩;
        · cases h₂ ; aesop;
          tauto;
    · all_goals generalize_proofs at *;
      rw [ Fintype.card_of_subtype ];
      rotate_left;
      exact Finset.filter ( fun p => hexGraph.Adj hexOrigin p.1 ∧ hexGraph.Adj p.1 p.2 ∧ hexOrigin ≠ p.2 ) ( Finset.product ( Finset.image ( fun x : ℤ × ℤ => ( x.1, x.2, true ) ) ( Finset.Icc ( -1 ) 1 ×ˢ Finset.Icc ( -1 ) 1 ) ) ( Finset.image ( fun x : ℤ × ℤ => ( x.1, x.2, false ) ) ( Finset.Icc ( -1 ) 1 ×ˢ Finset.Icc ( -1 ) 1 ) ) );
      · assumption;
      · simp +decide [ hexGraph ];
  exact h_saw_count_2

end