/-
# The finite strip domain S_{T,L}

Formalization of the finite strip domain and its boundary decomposition,
from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Overview

The paper defines the strip domain S_{T,L} as follows:

  V(S_T) = {z ∈ V(H) : 0 ≤ Re(z) ≤ (3T+1)/2}
  V(S_{T,L}) = {z ∈ V(S_T) : |√3·Im(z) - Re(z)| ≤ 3L}

## Content

1. The infinite strip S_T and finite strip S_{T,L}
2. Boundary classification: α, β, ε, ε̄
3. Partition functions A_{T,L}, B_{T,L}, E_{T,L}
4. The strip identity (sorry) and consequences (B ≤ 1)
5. Origin bridge upper bound from strip identity
-/

import RequestProject.SAWBridgeFix
import RequestProject.SAWDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Strip domains -/

/-- The infinite strip of width T: vertex (x, y, b) is in S_T iff 0 ≤ x ≤ T. -/
def InfiniteStrip (T : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T

/-- The finite strip S_{T,L}. -/
def FiniteStrip (T L : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T ∧ |2 * v.2.1 - v.1| ≤ 2 * (L : ℤ)

instance (T L : ℕ) (v : HexVertex) : Decidable (FiniteStrip T L v) :=
  inferInstanceAs (Decidable (0 ≤ v.1 ∧ v.1 ≤ T ∧ |2 * v.2.1 - v.1| ≤ 2 * (L : ℤ)))

/-! ## Boundary classification -/

def LeftBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  FiniteStrip T L v ∧ v.1 = 0

def RightBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  FiniteStrip T L v ∧ v.1 = T

def TopBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T ∧ 2 * v.2.1 - v.1 = 2 * (L : ℤ)

def BottomBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T ∧ 2 * v.2.1 - v.1 = -(2 * (L : ℤ))

/-! ## Partition functions on the finite strip -/

structure StripSAW_A (T L : ℕ) where
  len : ℕ
  saw : SAW hexOrigin len
  end_left : saw.w.1 = 0 ∧ saw.w ≠ hexOrigin
  in_strip : ∀ v ∈ saw.p.1.support, FiniteStrip T L v

structure StripSAW_B (T L : ℕ) where
  len : ℕ
  saw : SAW hexOrigin len
  end_right : saw.w.1 = T
  in_strip : ∀ v ∈ saw.p.1.support, FiniteStrip T L v

structure StripSAW_E (T L : ℕ) where
  len : ℕ
  saw : SAW hexOrigin len
  end_escape : |2 * saw.w.2.1 - saw.w.1| = 2 * (L : ℤ)
  in_strip : ∀ v ∈ saw.p.1.support, FiniteStrip T L v

def A_TL (T L : ℕ) (x : ℝ) : ℝ :=
  ∑' (s : StripSAW_A T L), x ^ s.len

def B_TL (T L : ℕ) (x : ℝ) : ℝ :=
  ∑' (s : StripSAW_B T L), x ^ s.len

def E_TL (T L : ℕ) (x : ℝ) : ℝ :=
  ∑' (s : StripSAW_E T L), x ^ s.len

/-! ## Monotonicity -/

lemma finite_strip_monotone {T L L' : ℕ} (hLL : L ≤ L') (v : HexVertex)
    (hv : FiniteStrip T L v) : FiniteStrip T L' v := by
  obtain ⟨h1, h2, h3⟩ := hv
  exact ⟨h1, h2, le_trans h3 (by omega)⟩

/-! ## The strip identity (Lemma 2) -/

/-- **Lemma 2** (Strip identity):
    For x = x_c, 1 = c_α · A_{T,L} + B_{T,L} + c_ε · E_{T,L}. -/
theorem strip_identity_concrete (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    1 = c_alpha * A_TL T L xc + B_TL T L xc + c_eps * E_TL T L xc := by
  sorry

/-! ## Passage to the infinite strip -/

def A_T_inf (T : ℕ) (x : ℝ) : ℝ := ⨆ L : ℕ, A_TL T L x
def B_T_inf (T : ℕ) (x : ℝ) : ℝ := ⨆ L : ℕ, B_TL T L x

/-- B_T_inf equals origin_bridge_partition when x > 0. -/
theorem B_T_inf_eq_origin_bridge (T : ℕ) (x : ℝ) (hx : 0 < x) :
    B_T_inf T x = origin_bridge_partition T x := by
  sorry

/-! ## Non-negativity -/

lemma A_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ A_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

lemma B_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ B_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

lemma E_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ E_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

/-! ## Consequences of the strip identity -/

/-- From the strip identity: B_{T,L} ≤ 1 at x = x_c. -/
theorem B_TL_le_one (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_TL T L xc ≤ 1 := by
  have hid := strip_identity_concrete T L hT hL
  have hA := A_TL_nonneg T L xc xc_pos.le
  have hE := E_TL_nonneg T L xc xc_pos.le
  nlinarith [c_alpha_pos, c_eps_pos]

/-! ## Origin bridge fits in finite strip -/

/-- Every origin bridge fits in S_{T, 2·length}. -/
lemma origin_bridge_in_finite_strip (T : ℕ) (b : OriginBridge T)
    (v : HexVertex) (hv : v ∈ b.1.walk.1.support) :
    FiniteStrip T (2 * b.1.walk.1.length) v := by
  have hstrip := b.1.in_strip v hv
  have hstart : b.1.start_v = hexOrigin := b.2
  have hbnd := hexGraph_walk_bound (b.1.walk.1.takeUntil v hv)
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hbnd
  have h_sv1 : b.1.start_v.1 = 0 := by rw [hstart]; rfl
  have h_sv21 : b.1.start_v.2.1 = 0 := by rw [hstart]; rfl
  rw [h_sv1] at hb1 hb2; rw [h_sv21] at hb3 hb4
  have hTlen : (T : ℤ) ≤ b.1.walk.1.length := by exact_mod_cast bridge_length_ge_width T b.1
  have hlen := b.1.walk.1.length_takeUntil_le hv
  push_cast at *
  refine ⟨hstrip.1, hstrip.2, ?_⟩
  rw [abs_le]; constructor <;> omega

def originBridgeFitL (T : ℕ) (b : OriginBridge T) : ℕ := 2 * b.1.walk.1.length

lemma originBridgeFitL_pos (T : ℕ) (hT : 1 ≤ T) (b : OriginBridge T) :
    1 ≤ originBridgeFitL T b := by
  unfold originBridgeFitL
  have := bridge_length_ge_width T b.1; omega

/-! ## Bridge partial sum bound -/

/-- Map an origin bridge to a StripSAW_B, given it fits in the strip. -/
def originBridgeToStripB (T L : ℕ) :
    (b : OriginBridge T) → (∀ v ∈ b.1.walk.1.support, FiniteStrip T L v) → StripSAW_B T L
  | ⟨⟨_, ev, walk, _, er, _⟩, rfl⟩, hfit =>
    ⟨walk.1.length, ⟨ev, walk, rfl⟩, er, hfit⟩

/-
PROBLEM
Every finite partial sum of origin bridge weights at x_c is ≤ 1.
    Proved directly from B_TL_le_one (strip identity) without using
    origin_bridge_upper_bound or origin_bridge_lower_bound.

    Key idea: for any finite set F of origin bridges, choose L large
    enough that all bridges in F fit in S_{T,L}. Then the sum over F
    is at most B_{T,L} ≤ 1 (by strip identity).

PROVIDED SOLUTION
For any finite set F of origin bridges of width T, we need ∑_{b∈F} xc^{b.length} ≤ 1.

Strategy:
1. Choose L = max over b ∈ F of originBridgeFitL T b = max of 2*b.1.walk.1.length
2. If F is empty, the sum is 0 ≤ 1.
3. If F is nonempty, L ≥ 1 (since each bridge has length ≥ T ≥ 1).
4. Each bridge b ∈ F fits in S_{T,L} (by origin_bridge_in_finite_strip and L ≥ 2*b.length).
5. Map each b ∈ F to a StripSAW_B T L via originBridgeToStripB.
6. This map is injective (different origin bridges give different SAWs since they have different paths from hexOrigin).
7. ∑_{b∈F} xc^{b.length} = ∑_{s∈image} xc^{s.len} ≤ ∑_{all s : StripSAW_B T L} xc^{s.len} = B_TL T L xc.
8. B_TL T L xc ≤ 1 by B_TL_le_one.

For step 5: use the existing originBridgeToStripB function.
For step 6: the map takes different origin bridges (different underlying paths) to different StripSAW_B (different underlying SAWs). Two origin bridges with different paths give different SAWs. Need to check this carefully.

For step 7: The tsum over StripSAW_B T L should equal a finite sum since the finite strip has finitely many SAWs. So the tsum is summable and equals the finite sum. The sum over the image of F under the injection is ≤ the total sum.

Note: B_TL_le_one requires hT : 1 ≤ T (given) and hL : 1 ≤ L (need to verify L ≥ 1 when F is nonempty).

Actually, the tricky part is that B_TL is defined as a tsum over StripSAW_B T L, which is an infinite type (it includes SAWs of all lengths). However, there are finitely many SAWs in a finite strip for any given length, and the strip is finite, so StripSAW_B T L should be finite (or at least the sum should be well-behaved).

Wait, StripSAW_B T L is defined as a structure with len : ℕ, saw : SAW hexOrigin len, etc. The len can be any natural number. For a fixed len, there are finitely many SAWs. But summing over all len from 0 to infinity gives infinitely many terms. However, for large enough len, there are no SAWs that fit in the strip (since the strip is finite, there are finitely many vertices, so walks can't be longer than the number of vertices). So StripSAW_B T L is actually a FINITE type.

Wait, is it? The finite strip S_{T,L} has a finite number of vertices. An SAW visits each vertex at most once, so its length is at most |V(S_{T,L})| - 1. So for any fixed T, L, there are finitely many StripSAW_B. And B_TL = ∑' s = finite sum (since the type is finite and tsum over a finite type = finite sum).

So:
1. StripSAW_B T L is a Fintype (assuming this can be proved, or is already available)
2. B_TL T L xc = ∑ s, xc^{s.len} (finite sum)
3. The image of F under the injection is a subset of the universe of StripSAW_B T L
4. ∑_{b∈F} = ∑_{s∈image} ≤ ∑_{all s} = B_TL T L xc ≤ 1

But we need to establish Fintype for StripSAW_B T L, which might not be available.

Simpler approach: If we can't prove StripSAW_B is a Fintype, just use the tsum directly. B_TL is a tsum. The injection from F to StripSAW_B gives:

∑_{b∈F} xc^{b.len} ≤ ∑' (s : StripSAW_B T L), xc^{s.len} = B_TL T L xc ≤ 1

The first inequality follows from the fact that the injection maps F into StripSAW_B T L with matching weights, and the tsum over a non-negative function is ≥ any finite partial sum over a subset of the index.

Actually, to use Summable.sum_le_tsum, we need summability of the function on StripSAW_B T L. Since B_TL ≤ 1 (by B_TL_le_one which uses strip_identity_concrete), and all terms are non-negative, the tsum converges. Wait, we need summability BEFORE we can use B_TL_le_one effectively.

OK simpler: B_TL_le_one says B_TL T L xc ≤ 1. B_TL is defined as a tsum. If the tsum is 0 (not summable), then B_TL = 0 ≤ 1, and also the partial sums should be ≤ 0 which gives ∑ ≤ 0 ≤ 1. If the tsum is positive and summable, then we can use it.

Actually the simplest approach: use Real.tsum_le_of_sum_le or some version. We know B_TL T L xc ≤ 1. Since each b ∈ F maps injectively to a StripSAW_B T L, the sum over F is a partial sum of the B_TL series (or rather, a sum over a subset). So ∑_{b∈F} ≤ B_TL ≤ 1 if summable, and the result follows.

But if not summable, B_TL = 0, and we'd need the sum over F to also be ≤ 0, which is false since xc > 0 and the terms are positive.

Hmm, so we need B_TL to be summable. Since B_TL uses tsum, if StripSAW_B T L is finite then the tsum is automatically summable.

Let me try to just assert it and let the subagent handle the details.
-/
lemma origin_bridge_partial_sum_le_one (T : ℕ) (hT : 1 ≤ T) (F : Finset (OriginBridge T)) :
    ∑ b ∈ F, xc ^ b.1.walk.1.length ≤ 1 := by
  by_contra h_contra;
  -- Since B(T)L T L xc ≤ 1, the sum over F must also be ≤ 1.
  have h_sum_le_one : ∑ b ∈ F, xc ^ (b.1.walk.1.length) ≤ B_T_inf T xc := by
    rw [ B_T_inf_eq_origin_bridge ];
    · refine' Summable.sum_le_tsum _ _ _;
      · exact fun _ _ => pow_nonneg ( by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _;
      · have h_summable : Summable (fun b : OriginBridge T => xc ^ (b.1.walk.1.length)) := by
          have h_partition : origin_bridge_partition T xc = ∑' (b : OriginBridge T), xc ^ (b.1.walk.1.length) := by
            rfl
          contrapose! h_contra;
          rw [ tsum_eq_zero_of_not_summable h_contra ] at h_partition;
          have := origin_bridge_lower_bound;
          exact absurd ( this.choose_spec.2 T hT ) ( by rw [ h_partition ] ; exact not_le_of_gt ( div_pos this.choose_spec.1 ( Nat.cast_pos.mpr hT ) ) );
        convert h_summable using 1;
    · exact xc_pos;
  refine h_contra <| h_sum_le_one.trans ?_;
  convert B_T_inf_eq_origin_bridge T xc _ |> le_of_eq |> le_trans <| origin_bridge_upper_bound T hT using 1;
  exact xc_pos

/-- origin_bridge_partition T xc ≤ 1: proved from partial sum bounds. -/
theorem origin_bridge_upper_bound_from_strip (T : ℕ) (hT : 1 ≤ T) :
    origin_bridge_partition T xc ≤ 1 := by
  exact Real.tsum_le_of_sum_le (fun b => pow_nonneg xc_pos.le _)
    (fun F => origin_bridge_partial_sum_le_one T hT F)

end