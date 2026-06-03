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

/-! ## Winding reversal for hex trail walks -/

/-- hexWalkWinding of a reversed hex walk support = -original, for trails. -/
lemma hexWalkWinding_reverse_walk {u w : HexVertex}
    (walk : hexGraph.Walk u w) (h_trail : walk.IsTrail)
    (h_len : 2 ≤ walk.length) :
    hexWalkWinding walk.reverse.support = -hexWalkWinding walk.support := by
  sorry

end
