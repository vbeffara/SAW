/-
# Winding Relations for the Pair Involution

Proves the winding reversal property for hexagonal lattice trail walks
and provides the algebraic framework for pair cancellation.

## Main results

* `hex_turn_value` — all turns in hex trails are ±π/3
* `arg_inv_of_ne_pi` — arg(z⁻¹) = -arg(z) for arg(z) = ±π/3
* `hexWalkWinding_reverse_walk` — winding of reversed trail = -original
-/

import Mathlib
import RequestProject.SAWPairInvolution

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## All hex lattice trail turns are ±π/3 -/

/-- The turn angle at any vertex of a hex lattice trail is ±π/3. -/
lemma hex_turn_value (v₀ v₁ v₂ : HexVertex)
    (h₁ : hexGraph.Adj v₀ v₁) (h₂ : hexGraph.Adj v₁ v₂)
    (h_ne : s(v₀, v₁) ≠ s(v₁, v₂)) :
    Complex.arg ((correctHexEmbed v₂ - correctHexEmbed v₁) /
                 (correctHexEmbed v₁ - correctHexEmbed v₀)) = Real.pi / 3 ∨
    Complex.arg ((correctHexEmbed v₂ - correctHexEmbed v₁) /
                 (correctHexEmbed v₁ - correctHexEmbed v₀)) = -(Real.pi / 3) := by
  rcases v₀ with ⟨ x₀, y₀ ⟩ ; rcases v₁ with ⟨ x₁, y₁ ⟩ ; rcases v₂ with ⟨ x₂, y₂ ⟩ ; simp_all +decide [ hexGraph ] ;
  rcases y₀ with ⟨ y₀, b₀ ⟩ ; rcases y₁ with ⟨ y₁, b₁ ⟩ ; rcases y₂ with ⟨ y₂, b₂ ⟩ ; simp_all +decide [ correctHexEmbed ] ;
  cases b₀ <;> cases b₁ <;> cases b₂ <;> simp_all +decide [ Complex.arg ];
  · rcases h₁ with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num at *;
    · rcases h₂ with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num at *;
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inr ( by rw [ mul_one_div, ← Real.sin_pi_div_three, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] );
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inl ( by rw [ show Real.sqrt 3 * ( 1 / 2 ) = Real.sin ( Real.pi / 3 ) by rw [ Real.sin_pi_div_three ] ; ring, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] );
    · rcases h₂ with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num at *;
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inl ( by rw [ show Real.sqrt 3 * ( 1 / 2 ) = Real.sin ( Real.pi / 3 ) by rw [ Real.sin_pi_div_three ] ; ring, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] );
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inr ( by rw [ mul_one_div, ← Real.sin_pi_div_three, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] );
    · rcases h₂ with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num at *;
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inr ( by rw [ mul_one_div, ← Real.sin_pi_div_three, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] );
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inl ( by rw [ show Real.sqrt 3 * ( 1 / 2 ) = Real.sin ( Real.pi / 3 ) by rw [ Real.sin_pi_div_three ] ; ring, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] );
  · rcases h₁ with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num at *;
    · rcases h₂ with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num at *;
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inr ( by rw [ mul_one_div, ← Real.sin_pi_div_three, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] );
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inl ( by rw [ show Real.sqrt 3 * ( 1 / 2 ) = Real.sin ( Real.pi / 3 ) by rw [ Real.sin_pi_div_three ] ; ring, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] );
    · rcases h₂ with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num at *;
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inl ( by rw [ show Real.sqrt 3 * ( 1 / 2 ) = Real.sin ( Real.pi / 3 ) by rw [ Real.sin_pi_div_three ] ; ring, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] );
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inr ( by rw [ mul_one_div, ← Real.sin_pi_div_three, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] );
    · rcases h₂ with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num at *;
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inr ( by rw [ mul_one_div, ← Real.sin_pi_div_three, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] );
      · norm_num [ Complex.normSq, Complex.norm_def, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] at *;
        exact Or.inl ( by rw [ show Real.sqrt 3 * ( 1 / 2 ) = Real.sin ( Real.pi / 3 ) by rw [ Real.sin_pi_div_three ] ; ring, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ] )

/-- For turns of ±π/3, Complex.arg satisfies the negation property. -/
lemma arg_inv_of_ne_pi (z : ℂ) (hz : z ≠ 0)
    (h : Complex.arg z = Real.pi / 3 ∨ Complex.arg z = -(Real.pi / 3)) :
    Complex.arg z⁻¹ = -Complex.arg z := by
  convert Complex.arg_inv_coe_angle z using 1;
  cases h <;> simp +decide [ *, Complex.arg_inv ] at *;
  · split_ifs <;> norm_num [ Complex.ext_iff ] at * ; linarith [ Real.pi_pos ];
    exact fun h => absurd h ( by linarith [ Real.pi_pos ] );
  · grind +splitImp

/-! ## Helpers for winding reversal -/

/-
The direction difference between adjacent hex vertices is nonzero.
-/
lemma hex_embed_sub_ne_zero' (a b : HexVertex) (h : hexGraph.Adj a b) :
    correctHexEmbed b - correctHexEmbed a ≠ 0 := by
  rcases a with ⟨ a₁, a₂ ⟩ ; rcases b with ⟨ b₁, b₂ ⟩ ; simp_all +decide [ sub_eq_zero ];
  cases a₂ ; cases b₂ ; simp +decide [ HexVertex ] at h ⊢;
  cases ‹Bool› <;> cases ‹Bool› <;> simp_all +decide [ hexGraph ];
  · unfold correctHexEmbed; simp +decide [ Complex.ext_iff ] ;
    grind;
  · unfold correctHexEmbed;
    grind

/-
The reversed turn angle is the negative.
-/
lemma hex_turn_neg' (v₀ v₁ v₂ : HexVertex)
    (h₁ : hexGraph.Adj v₀ v₁) (h₂ : hexGraph.Adj v₁ v₂)
    (h_ne : s(v₀, v₁) ≠ s(v₁, v₂)) :
    Complex.arg ((correctHexEmbed v₀ - correctHexEmbed v₁) /
                 (correctHexEmbed v₁ - correctHexEmbed v₂)) =
    -Complex.arg ((correctHexEmbed v₂ - correctHexEmbed v₁) /
                  (correctHexEmbed v₁ - correctHexEmbed v₀)) := by
  rw [ ← arg_inv_of_ne_pi ];
  · grind +qlia;
  · exact div_ne_zero ( sub_ne_zero_of_ne <| by intro h; have := hex_embed_sub_ne_zero' v₁ v₂ h₂; aesop ) ( sub_ne_zero_of_ne <| by intro h; have := hex_embed_sub_ne_zero' v₀ v₁ h₁; aesop );
  · exact hex_turn_value v₀ v₁ v₂ h₁ h₂ h_ne

/-- Trail condition on lists. -/
def HexTrailList : List HexVertex → Prop
  | [] | [_] | [_, _] => True
  | v₀ :: v₁ :: v₂ :: rest =>
    hexGraph.Adj v₀ v₁ ∧ hexGraph.Adj v₁ v₂ ∧
    s(v₀, v₁) ≠ s(v₁, v₂) ∧ HexTrailList (v₁ :: v₂ :: rest)

/-
Walk support satisfies HexTrailList.
-/
lemma walk_support_is_hex_trail_list' {u w : HexVertex}
    (walk : hexGraph.Walk u w) (h_trail : walk.IsTrail) :
    HexTrailList walk.support := by
  induction' walk with u v w huv hw ih;
  · trivial;
  · cases' ih with x hx;
    · trivial;
    · cases' ‹SimpleGraph.Walk hexGraph _ _› with x hx;
      · exact ⟨ hw, by assumption, by aesop ⟩;
      · constructor;
        · assumption;
        · simp_all +decide [ SimpleGraph.Walk.isTrail_def ]

/-
hexWalkWinding of a reversed HexTrailList is the negation.
-/
theorem hexWalkWinding_reverse_list' (L : List HexVertex) (h : HexTrailList L)
    (hlen : 3 ≤ L.length) :
    hexWalkWinding L.reverse = -hexWalkWinding L := by
  induction' L with a L ih <;> simp_all +decide [ List.length ];
  rcases L with ( _ | ⟨ b, _ | ⟨ c, L ⟩ ⟩ ) <;> simp_all +decide [ List.length ];
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h;
  by_cases hL : L = [] <;> simp_all +decide [ hexWalkWinding ];
  · convert hex_turn_neg' a b c h₁ h₂ _ using 1;
    aesop;
  · rw [ hexWalkWinding_extend ];
    rw [ ih ( List.length_pos_iff.mpr hL ) ];
    rw [ ← hex_turn_neg' a b c h₁ h₂ ( by aesop ) ]

/-! ## Winding reversal for hex trail walks -/

/-- hexWalkWinding of a reversed hex walk support = -original, for trails. -/
lemma hexWalkWinding_reverse_walk {u w : HexVertex}
    (walk : hexGraph.Walk u w) (h_trail : walk.IsTrail)
    (h_len : 2 ≤ walk.length) :
    hexWalkWinding walk.reverse.support = -hexWalkWinding walk.support := by
  rw [SimpleGraph.Walk.support_reverse]
  apply hexWalkWinding_reverse_list'
  · exact walk_support_is_hex_trail_list' walk h_trail
  · have : walk.support.length = walk.length + 1 := SimpleGraph.Walk.length_support walk
    omega

end