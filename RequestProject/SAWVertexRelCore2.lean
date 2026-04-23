/-
# Vertex relation winding computations

Computes the hexTurn values needed for the vertex relation
(Lemma 1 of Duminil-Copin & Smirnov 2012).
-/

import Mathlib
import RequestProject.SAWObservableProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## HexTurn computations at FALSE vertices -/

lemma hexTurn_false_w1_w1 (x y : ℤ) :
    hexTurn (x, y, true) (x, y, false) (x, y, true) = -3 := by
  simp [hexTurn, hexEdgeDir, hexGraph]

lemma hexTurn_false_w1_w2 (x y : ℤ) :
    hexTurn (x, y, true) (x, y, false) (x + 1, y, true) = -1 := by
  simp [hexTurn, hexEdgeDir, hexGraph]

lemma hexTurn_false_w1_w3 (x y : ℤ) :
    hexTurn (x, y, true) (x, y, false) (x, y + 1, true) = 1 := by
  simp [hexTurn, hexEdgeDir, hexGraph]

lemma hexTurn_false_w2_w1 (x y : ℤ) :
    hexTurn (x + 1, y, true) (x, y, false) (x, y, true) = 1 := by
  simp [hexTurn, hexEdgeDir, hexGraph]

lemma hexTurn_false_w2_w2 (x y : ℤ) :
    hexTurn (x + 1, y, true) (x, y, false) (x + 1, y, true) = -3 := by
  simp [hexTurn, hexEdgeDir, hexGraph]

lemma hexTurn_false_w2_w3 (x y : ℤ) :
    hexTurn (x + 1, y, true) (x, y, false) (x, y + 1, true) = -1 := by
  simp [hexTurn, hexEdgeDir, hexGraph]

lemma hexTurn_false_w3_w1 (x y : ℤ) :
    hexTurn (x, y + 1, true) (x, y, false) (x, y, true) = -1 := by
  simp [hexTurn, hexEdgeDir, hexGraph]

lemma hexTurn_false_w3_w2 (x y : ℤ) :
    hexTurn (x, y + 1, true) (x, y, false) (x + 1, y, true) = 1 := by
  simp [hexTurn, hexEdgeDir, hexGraph]

lemma hexTurn_false_w3_w3 (x y : ℤ) :
    hexTurn (x, y + 1, true) (x, y, false) (x, y + 1, true) = -3 := by
  simp [hexTurn, hexEdgeDir, hexGraph]

/-! ## HexTurn computations at TRUE vertices -/

lemma hexTurn_true_w1_w1 (x y : ℤ) :
    hexTurn (x, y, false) (x, y, true) (x, y, false) = -3 := by
  unfold hexTurn; simp +decide ;
  unfold hexEdgeDir;
  unfold hexGraph; simp +decide ;

lemma hexTurn_true_w1_w2 (x y : ℤ) :
    hexTurn (x, y, false) (x, y, true) (x - 1, y, false) = -1 := by
  unfold hexTurn hexEdgeDir; simp +decide ;
  split_ifs <;> simp_all +decide [ hexGraph ]

lemma hexTurn_true_w1_w3 (x y : ℤ) :
    hexTurn (x, y, false) (x, y, true) (x, y - 1, false) = 1 := by
  unfold hexTurn; simp +decide ;
  unfold hexEdgeDir; simp +decide [ hexGraph ] ;

lemma hexTurn_true_w2_w1 (x y : ℤ) :
    hexTurn (x - 1, y, false) (x, y, true) (x, y, false) = 1 := by
  unfold hexTurn hexEdgeDir;
  simp +decide [ hexGraph ];
  split_ifs <;> norm_num ; omega

lemma hexTurn_true_w2_w2 (x y : ℤ) :
    hexTurn (x - 1, y, false) (x, y, true) (x - 1, y, false) = -3 := by
  unfold hexTurn hexEdgeDir;
  simp +decide [ hexGraph ];
  split_ifs <;> norm_num;
  linarith

lemma hexTurn_true_w2_w3 (x y : ℤ) :
    hexTurn (x - 1, y, false) (x, y, true) (x, y - 1, false) = -1 := by
  unfold hexTurn hexEdgeDir;
  unfold hexGraph; simp +decide [ SimpleGraph.adj_comm ] ;
  split_ifs <;> norm_num ; omega

lemma hexTurn_true_w3_w1 (x y : ℤ) :
    hexTurn (x, y - 1, false) (x, y, true) (x, y, false) = -1 := by
  unfold hexTurn hexEdgeDir;
  simp +decide [ hexGraph ];
  split_ifs <;> norm_num;
  linarith

lemma hexTurn_true_w3_w2 (x y : ℤ) :
    hexTurn (x, y - 1, false) (x, y, true) (x - 1, y, false) = 1 := by
  unfold hexTurn hexEdgeDir;
  simp +decide [ hexGraph ];
  split_ifs <;> norm_num ; omega

lemma hexTurn_true_w3_w3 (x y : ℤ) :
    hexTurn (x, y - 1, false) (x, y, true) (x, y - 1, false) = -3 := by
  unfold hexTurn hexEdgeDir;
  simp +decide [ hexGraph ];
  split_ifs <;> norm_num ; omega

/-! ## Triplet cancellation connecting hexTurn to algebraic identity

The triplet contribution at a FALSE vertex v, for a walk γ of length n
entering from w₁, with walkWindingInt = W, is:

  (w₁-v)·exp(-iσ·(W-3)·π/3)·xc^{n+1}     -- v-side, exit reversal at v
  + (w₂-v)·exp(-iσ·(W-4)·π/3)·xc^{n+2}   -- w₂-side, extension to w₂, exit reversal at w₂
  + (w₃-v)·exp(-iσ·(W-2)·π/3)·xc^{n+2}   -- w₃-side, extension to w₃, exit reversal at w₃

= exp(-iσ·(W-3)·π/3)·xc^{n+1} · [1 + xc·j·conj(λ) + xc·conj(j)·λ]

= 0 by triplet_cancellation.

The winding differences are:
  v-side (reversal): hexTurn(w₁,v,w₁) = -3
  w₂ extension: hexTurn(w₁,v,w₂) + hexTurn(v,w₂,v) = -1 + (-3) = -4
  w₃ extension: hexTurn(w₁,v,w₃) + hexTurn(v,w₃,v) = +1 + (-3) = -2

Relative to the v-side (winding W-3):
  w₂ extension phase shift: -4-(-3) = -1, so factor = exp(iσπ/3) = conj(λ)
  w₃ extension phase shift: -2-(-3) = +1, so factor = exp(-iσπ/3) = λ

Direction factors: (w₁-v)=1, (w₂-v)=j, (w₃-v)=conj(j)
xc factor: extensions have one more edge, contributing factor xc

Result: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0  ✓ (triplet_cancellation)
-/

/-
The relative phase shift for the w₂ extension:
    exp(iσ·π/3) = conj(λ).
-/
lemma exit_phase_w2 :
    Complex.exp (Complex.I * ↑sigma * (↑(1 : ℤ) * ↑Real.pi / 3)) = conj lam := by
  unfold sigma lam; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring;
  norm_num

/-
The relative phase shift for the w₃ extension:
    exp(-iσ·π/3) = λ.
-/
lemma exit_phase_w3 :
    Complex.exp (Complex.I * ↑sigma * (↑(-1 : ℤ) * ↑Real.pi / 3)) = lam := by
  unfold sigma lam; ring;
  push_cast; ring;

end