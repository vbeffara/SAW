/-
# General Winding Relations for Triplet Extensions

Proves the winding relation for triplet extensions at any vertex
index j ∈ Fin 3, generalizing triplet_winding_ext1/ext2.
-/

import Mathlib
import RequestProject.SAWCancellationIdentity

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 3200000

/-! ## Turning angle at a hex vertex -/

/-
For (k, l) = fin3_other j, the ratio -midEdgeDir v k / midEdgeDir v j = -j.
-/
lemma neg_midEdgeDir_ratio_k (v : HexVertex) (ji : Fin 3) :
    -midEdgeDir v (fin3_other ji).1 / midEdgeDir v ji = -j := by
  fin_cases ji <;> simp +decide [ *, neg_div ];
  · rw [ div_eq_iff ] <;> norm_num [ midEdgeDir_zero_ne_zero, j_ne_zero, conj_j_ne_zero, midEdgeDir_j_relation ];
    exact midEdgeDir_j_relation v |>.1;
  · unfold fin3_other;
    simp +decide [ midEdgeDir_j_relation, div_eq_iff, midEdgeDir_zero_ne_zero ];
    rw [ div_eq_iff ] <;> ring!;
    · rw [ show j ^ 2 = conj j from j_sq_eq_conj' ] ; ring!;
    · exact mul_ne_zero j_ne_zero ( midEdgeDir_zero_ne_zero v );
  · unfold fin3_other;
    rw [ div_eq_iff ] <;> simp +decide [ midEdgeDir_j_relation ];
    · rw [ ← mul_assoc, mul_comm j, mul_assoc ];
      rw [ ← mul_assoc, show ( starRingEnd ℂ j ) * j = 1 by
                          unfold j; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring; norm_num; ] ; ring;
    · exact ⟨ j_ne_zero, midEdgeDir_zero_ne_zero v ⟩

/-
For (k, l) = fin3_other j, -midEdgeDir v l / midEdgeDir v j = -conj(j).
-/
lemma neg_midEdgeDir_ratio_l (v : HexVertex) (ji : Fin 3) :
    -midEdgeDir v (fin3_other ji).2 / midEdgeDir v ji = -conj j := by
  fin_cases ji <;> simp +decide [ *, Fin.forall_fin_one ];
  · rw [ div_eq_iff ] <;> norm_num [ midEdgeDir_zero_ne_zero, j_sq_eq_conj' ];
    exact midEdgeDir_j_relation v |>.2;
  · unfold fin3_other; simp +decide [ *, midEdgeDir_j_relation ] ;
    rw [ div_eq_iff ] <;> ring <;> norm_num [ j_cube_eq_one', j_ne_zero, conj_j_ne_zero ];
    · rw [ mul_assoc, show ( starRingEnd ℂ ) j * j = 1 by
                        unfold j; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring_nf ; norm_num;, mul_one ];
    · exact midEdgeDir_zero_ne_zero v;
  · unfold fin3_other;
    rw [ div_eq_iff ] <;> norm_num [ midEdgeDir_zero_ne_zero, j_ne_zero, conj_j_ne_zero, midEdgeDir_j_relation ];
    unfold j; norm_num [ Complex.ext_iff ] ; ring;
    norm_num [ Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring ; norm_num;
    constructor <;> ring

/-- The turning angle for the first extension is -π/3. -/
lemma turning_angle_k (v : HexVertex) (ji : Fin 3) :
    Complex.arg (-midEdgeDir v (fin3_other ji).1 / midEdgeDir v ji) = -Real.pi / 3 := by
  rw [neg_midEdgeDir_ratio_k]; exact arg_neg_j

/-- The turning angle for the second extension is +π/3. -/
lemma turning_angle_l (v : HexVertex) (ji : Fin 3) :
    Complex.arg (-midEdgeDir v (fin3_other ji).2 / midEdgeDir v ji) = Real.pi / 3 := by
  rw [neg_midEdgeDir_ratio_l]; exact arg_neg_conj_j

/-! ## hexWalkWinding append decomposition -/

/-
For a walk support L ++ [nⱼ], appending [v, nₖ] gives:
    winding(L ++ [nⱼ, v, nₖ]) = winding(L ++ [nⱼ, v]) + arg((nₖ-v)/(v-nⱼ))
-/
lemma hexWalkWinding_extend (L : List HexVertex) (nⱼ v nₖ : HexVertex) :
    hexWalkWinding (L ++ [nⱼ, v, nₖ]) =
    hexWalkWinding (L ++ [nⱼ, v]) +
    Complex.arg ((correctHexEmbed nₖ - correctHexEmbed v) /
                 (correctHexEmbed v - correctHexEmbed nⱼ)) := by
  induction' L with x L ih;
  · exact add_comm _ _;
  · rcases L with ( _ | ⟨ y, _ | ⟨ z, L ⟩ ⟩ ) <;> simp_all +decide [ hexWalkWinding ];
    · grind;
    · ring

/-! ## General winding relation for triplet extension -/

/-- The full support of the extension. -/
lemma tripletExtendStrip_fullSupport' {T L : ℕ} (v : HexVertex) (ji k : Fin 3)
    (γ : StripTrail T L (hexNeighbors3 v ji) v)
    (h_no_v : vEdgeCount v γ.walk = 0)
    (hv : PaperFinStrip T L v) :
    (tripletExtendStrip v ji k γ h_no_v hv).fullSupport =
    γ.walk.support ++ [v, hexNeighbors3 v k] := by
  simp [tripletExtendStrip, StripTrail.fullSupport, SimpleGraph.Walk.support_append]

/-
General winding relation for the k-extension (winding decreases by π/3).
-/
theorem triplet_winding_general_k {T L : ℕ} (v : HexVertex) (ji : Fin 3)
    (γ : StripTrail T L (hexNeighbors3 v ji) v)
    (h_no_v : vEdgeCount v γ.walk = 0)
    (hv : PaperFinStrip T L v) :
    (tripletExtendStrip v ji (fin3_other ji).1 γ h_no_v hv).winding =
    γ.winding - Real.pi / 3 := by
  unfold StripTrail.winding;
  have h_support : γ.walk.support = γ.walk.support.dropLast ++ [hexNeighbors3 v ji] := by
    rw [ List.dropLast_append_getLast? ];
    have h_support : ∀ {u v : HexVertex} {w : hexGraph.Walk u v}, v ∈ w.support.getLast? := by
      intros u v w
      induction' w with u v w ih;
      · simp +decide [ SimpleGraph.Walk.support ];
      · grind +locals;
    exact h_support;
  have h_winding : hexWalkWinding (γ.walk.support.dropLast ++ [hexNeighbors3 v ji, v, hexNeighbors3 v (fin3_other ji).1]) = hexWalkWinding (γ.walk.support.dropLast ++ [hexNeighbors3 v ji, v]) + Complex.arg ((correctHexEmbed (hexNeighbors3 v (fin3_other ji).1) - correctHexEmbed v) / (correctHexEmbed v - correctHexEmbed (hexNeighbors3 v ji))) := by
    rw [ hexWalkWinding_extend ];
  convert h_winding using 1;
  · rw [ tripletExtendStrip_fullSupport' ];
    grind;
  · rw [ show γ.fullSupport = γ.walk.support ++ [ v ] from rfl, h_support ];
    rw [ show ( correctHexEmbed ( hexNeighbors3 v ( fin3_other ji ).1 ) - correctHexEmbed v ) / ( correctHexEmbed v - correctHexEmbed ( hexNeighbors3 v ji ) ) = -midEdgeDir v ( fin3_other ji ).1 / midEdgeDir v ji from ?_ ];
    · rw [ turning_angle_k ] ; norm_num [ List.dropLast ] ; ring;
    · unfold midEdgeDir;
      rw [ ← neg_div_neg_eq ] ; ring

/-- General winding relation for the l-extension (winding increases by π/3). -/
theorem triplet_winding_general_l {T L : ℕ} (v : HexVertex) (ji : Fin 3)
    (γ : StripTrail T L (hexNeighbors3 v ji) v)
    (h_no_v : vEdgeCount v γ.walk = 0)
    (hv : PaperFinStrip T L v) :
    (tripletExtendStrip v ji (fin3_other ji).2 γ h_no_v hv).winding =
    γ.winding + Real.pi / 3 := by
  unfold StripTrail.winding
  have h_support : γ.walk.support = γ.walk.support.dropLast ++ [hexNeighbors3 v ji] := by
    rw [List.dropLast_append_getLast?]
    have h_support : ∀ {u v : HexVertex} {w : hexGraph.Walk u v}, v ∈ w.support.getLast? := by
      intros u v w
      induction' w with u v w ih
      · simp +decide [SimpleGraph.Walk.support]
      · grind +locals
    exact h_support
  have h_winding : hexWalkWinding (γ.walk.support.dropLast ++ [hexNeighbors3 v ji, v, hexNeighbors3 v (fin3_other ji).2]) = hexWalkWinding (γ.walk.support.dropLast ++ [hexNeighbors3 v ji, v]) + Complex.arg ((correctHexEmbed (hexNeighbors3 v (fin3_other ji).2) - correctHexEmbed v) / (correctHexEmbed v - correctHexEmbed (hexNeighbors3 v ji))) := by
    rw [hexWalkWinding_extend]
  convert h_winding using 1
  · rw [tripletExtendStrip_fullSupport']; grind
  · rw [show γ.fullSupport = γ.walk.support ++ [v] from rfl, h_support]
    rw [show (correctHexEmbed (hexNeighbors3 v (fin3_other ji).2) - correctHexEmbed v) / (correctHexEmbed v - correctHexEmbed (hexNeighbors3 v ji)) = -midEdgeDir v (fin3_other ji).2 / midEdgeDir v ji from ?_]
    · rw [turning_angle_l]
      congr 1
      simp [List.dropLast_append_of_ne_nil]
    · unfold midEdgeDir; rw [← neg_div_neg_eq]; ring

/-! ## Triplet cancellation for StripTrail

Using the winding and length relations, the triplet contribution at
vertex v vanishes for any root walk. -/

/-
Each complete triplet of strip trails contributes zero to the vertex sum.
-/
theorem stripTrail_triplet_cancel {T L : ℕ} (v : HexVertex) (ji : Fin 3)
    (γ : StripTrail T L (hexNeighbors3 v ji) v)
    (h_no_v : vEdgeCount v γ.walk = 0)
    (hv : PaperFinStrip T L v) :
    midEdgeDir v (fin3_other ji).1 * (tripletExtendStrip v ji (fin3_other ji).1 γ h_no_v hv).weight +
    midEdgeDir v ji * γ.weight +
    midEdgeDir v (fin3_other ji).2 * (tripletExtendStrip v ji (fin3_other ji).2 γ h_no_v hv).weight = 0 := by
  convert strip_triplet_zero v ji γ.winding γ.len using 1;
  unfold StripTrail.weight stripTrailContrib; simp +decide [ triplet_winding_general_k, triplet_winding_general_l, tripletExtendStrip_len ] ; ring;

end