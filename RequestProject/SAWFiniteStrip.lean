/-
# The finite strip domain S_{T,L}

Formalization of the finite strip domain and its boundary decomposition,
from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the hexagonal lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Overview

The paper defines the strip domain S_{T,L} as follows. Position a hexagonal
lattice H of mesh size 1 in ℂ so that there exists a horizontal edge e
with mid-edge a being 0. Then:

  V(S_T) = {z ∈ V(H) : 0 ≤ Re(z) ≤ (3T+1)/2}
  V(S_{T,L}) = {z ∈ V(S_T) : |√3·Im(z) - Re(z)| ≤ 3L}

The boundary of S_{T,L} decomposes into four parts:
  α = left boundary (Re = 0)
  β = right boundary (Re = (3T+1)/2)
  ε = top boundary (√3·Im - Re = 3L)
  ε̄ = bottom boundary (√3·Im - Re = -3L)

The angled cuts at ±π/3 are needed to ensure the telescoping of the
vertex relation (Lemma 1) at the boundary.

## Content

1. The infinite strip S_T
2. The finite strip S_{T,L}
3. Boundary classification: α, β, ε, ε̄
4. Partition functions A_{T,L}, B_{T,L}, E_{T,L}
5. Monotonicity properties (A,B increasing in L; E decreasing)
6. The strip identity (sorry) and consequences (B ≤ 1)
7. Origin bridge upper bound from strip identity
-/

import RequestProject.SAWBridgeFix
import RequestProject.SAWDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Strip domain using integer coordinates

We work with the integer coordinates (x, y, b) where x is the column
index and y is the row index. The embedding into ℂ maps:
  (x, y, false) ↦ (3x/2, √3·y)        [approximately]
  (x, y, true)  ↦ (3x/2 + 1, √3·y)    [approximately]

For the strip of width T:
  V(S_T) = {(x, y, b) : 0 ≤ x ≤ T}

For the finite strip S_{T,L} with the angled cuts, the condition
|√3·Im(z) - Re(z)| ≤ 3L translates to conditions on (x, y).
-/

/-- The infinite strip of width T in integer coordinates.
    A vertex (x, y, b) is in S_T iff 0 ≤ x ≤ T. -/
def InfiniteStrip (T : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T

/-- The finite strip S_{T,L} in integer coordinates. -/
def FiniteStrip (T L : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T ∧
  |2 * v.2.1 - v.1| ≤ 2 * (L : ℤ)

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
    The strip identity holds for the concrete partition functions.
    This is the key hypothesis for the main proof. -/
theorem strip_identity_concrete (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    1 = c_alpha * A_TL T L xc + B_TL T L xc + c_eps * E_TL T L xc := by
  sorry

/-! ## Passage to the infinite strip -/

def A_T_inf (T : ℕ) (x : ℝ) : ℝ :=
  ⨆ L : ℕ, A_TL T L x

def B_T_inf (T : ℕ) (x : ℝ) : ℝ :=
  ⨆ L : ℕ, B_TL T L x

/-- B_T_inf equals origin_bridge_partition when x > 0. -/
theorem B_T_inf_eq_origin_bridge (T : ℕ) (x : ℝ) (hx : 0 < x) :
    B_T_inf T x = origin_bridge_partition T x := by
  sorry

/-! ## Non-negativity of partition functions -/

lemma A_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ A_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

lemma B_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ B_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

lemma E_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ E_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

/-! ## Consequences of the strip identity -/

/-- From the strip identity: B_{T,L} ≤ 1 for all T, L at x = x_c. -/
theorem B_TL_le_one (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_TL T L xc ≤ 1 := by
  have hid := strip_identity_concrete T L hT hL
  have hA := A_TL_nonneg T L xc xc_pos.le
  have hE := E_TL_nonneg T L xc xc_pos.le
  nlinarith [c_alpha_pos, c_eps_pos]

/-! ## Every origin bridge fits in some finite strip

The key insight: every finite walk from hexOrigin has bounded coordinates.
A walk of length n visits vertices with |y| ≤ n (from hexGraph_walk_bound).
So every origin bridge fits in S_{T, L} for L = 2n. -/

/-- Every origin bridge of width T fits in the finite strip S_{T,L}
    for L = 2 * bridge_length. -/
lemma origin_bridge_in_finite_strip (T : ℕ) (b : OriginBridge T)
    (v : HexVertex) (hv : v ∈ b.1.walk.1.support) :
    FiniteStrip T (2 * b.1.walk.1.length) v := by
  have hstrip := b.1.in_strip v hv
  -- The bridge starts at hexOrigin, so the walk starts at (0,0,false)
  -- By hexGraph_walk_bound, y-coordinates are bounded by walk length
  have hstart : b.1.start_v = hexOrigin := b.2
  -- Get the walk as starting from hexOrigin
  have hlen := b.1.walk.1.length_takeUntil_le hv
  have hbnd := hexGraph_walk_bound (b.1.walk.1.takeUntil v hv)
  -- From the bounds, extract y-coordinate bound
  constructor
  · exact hstrip.1
  constructor
  · exact hstrip.2
  · -- Need |2*v.2.1 - v.1| ≤ 2*(2*length)
    -- From hbnd: v.2.1 - start.2.1 ≤ takeUntil.length ≤ length
    --            start.2.1 - v.2.1 ≤ takeUntil.length ≤ length
    -- Since start = b.1.start_v and b.2 : start = hexOrigin = (0,0,false):
    --   start.2.1 = 0
    -- So |v.2.1| ≤ length, and |v.1| ≤ T ≤ length (bridge_length_ge_width)
    -- Therefore |2*v.2.1 - v.1| ≤ 2*length + length ≤ 2*(2*length)
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hbnd
    have h_sv1 : b.1.start_v.1 = 0 := by rw [hstart]; rfl
    have h_sv21 : b.1.start_v.2.1 = 0 := by rw [hstart]; rfl
    rw [h_sv1] at hb1 hb2; rw [h_sv21] at hb3 hb4
    have hTlen : (T : ℤ) ≤ b.1.walk.1.length := by
      exact_mod_cast bridge_length_ge_width T b.1
    push_cast at *
    rw [abs_le]
    constructor <;> omega

/-- Each origin bridge fits in some S_{T,L}: get the L value. -/
def originBridgeFitL (T : ℕ) (b : OriginBridge T) : ℕ :=
  2 * b.1.walk.1.length

/-- The fit L value is ≥ 1 when T ≥ 1. -/
lemma originBridgeFitL_pos (T : ℕ) (hT : 1 ≤ T) (b : OriginBridge T) :
    1 ≤ originBridgeFitL T b := by
  unfold originBridgeFitL
  have := bridge_length_ge_width T b.1
  omega

/-
PROBLEM
The sum over any finite set of origin bridges is ≤ B_TL for L large enough,
    which is ≤ 1 by the strip identity.

PROVIDED SOLUTION
If F is empty, the sum is 0 ≤ 1.

If F is nonempty, pick L = F.sup (fun b => originBridgeFitL T b). Then L ≥ 1 (by originBridgeFitL_pos). Every bridge b ∈ F fits in S_{T,L} (by origin_bridge_in_finite_strip and finite_strip_monotone, since originBridgeFitL T b ≤ L).

Now each bridge b ∈ F determines a StripSAW_B T L (we need to construct it). Since b.2 : b.1.start_v = hexOrigin, we can rewrite b.1.walk to get a path from hexOrigin. The resulting StripSAW_B has the same walk length.

The map b → StripSAW_B is injective (different bridges give different walks/SAWs). So:
∑_{b∈F} xc^{b.length} ≤ B_TL T L xc ≤ 1 (by B_TL_le_one).

The first inequality uses that the injection maps F to a subset of StripSAW_B T L, and each term is non-negative, so the partial sum ≤ full tsum.

Actually, a simpler approach: each bridge b ∈ F is also a walk in the infinite strip S_T. Every StripSAW_B T L injects into the set of SAWs from hexOrigin to x=T in S_T. Since B_TL T L xc counts the total weight of such walks in the finite strip, and the finite strip is a subset, B_TL ≤ total weight in infinite strip. But we want the opposite direction.

Let me try differently: the key fact is that the finite sum ∑_{b∈F} xc^{b.length} is a partial sum of the series defining B_TL T L xc (for L large enough). Since B_TL is a tsum of non-negative terms, and B_TL ≤ 1, the partial sum ≤ tsum ≤ 1.

Specifically: B_TL T L xc = ∑' (s : StripSAW_B T L), xc^{s.len}. The set F (viewed as StripSAW_B's) is a finite subset. By the standard inequality Finset.sum ≤ tsum for non-negative summable functions, the partial sum ≤ B_TL ≤ 1.

The technical challenge is mapping F : Finset (OriginBridge T) to Finset (StripSAW_B T L). This requires the injection. Since the injection involves proof terms (in_strip), it might be complex.

Alternative approach without explicit injection: use the fact that ∑_{b∈F} xc^{b.length} ≤ B_TL by showing that each element of F contributes a positive term to B_TL. But this is also complex.

Simplest approach: directly bound each term. For each b ∈ F, xc^{b.length} ≤ 1 (since xc ≤ 1 and length ≥ 1). So ∑ ≤ |F|. This doesn't give ≤ 1 unless |F| ≤ 1.

Back to the injection approach. Use Finset.sum_le_tsum (from Mathlib) which says: if f is summable and non-negative, then ∑_{x∈s} f x ≤ ∑' x, f x. But we need s to be a finset of the same type as the tsum index.

Maybe I should just use summable_of_sum_le in reverse: if we can show ∑_{b∈F} xc^{b.length} ≤ 1 for all F, then origin_bridge_partition T xc ≤ 1 (which is what origin_bridge_upper_bound_from_strip does). So origin_bridge_partial_sum_le_one is the key lemma.

To prove it, I need to relate the sum over F (OriginBridge T elements) to B_TL (sum over StripSAW_B T L elements). The connection is through the injection.

Actually, I think the cleanest approach is to avoid the injection entirely and instead show that ∑_{b∈F} xc^{b.length} is part of a larger identity. If I sum the strip identity over a larger set that includes F, I get 1 on one side.

Hmm, that's the strip identity approach. The strip identity says: 1 = c_α·A + B + c_ε·E with B = B_TL T L xc ≥ partial sum. So partial sum ≤ B ≤ 1.

But I need B_TL ≥ partial sum of OriginBridge, which requires the injection.

Let me just try to map OriginBridge to SAW and use a counting argument.

Each origin bridge b gives an SAW from hexOrigin of length b.1.walk.1.length ending at x=T. This SAW is in the finite strip S_{T,L} (for L large enough). Different origin bridges give different SAWs (since they have different walks). So the number of SAWs ≥ |F|, and the weighted count ≥ ∑_{b∈F} xc^{b.length}.

But B_TL counts ALL SAWs in S_{T,L} ending at x=T, so B_TL ≥ partial sum. And B_TL ≤ 1.

The injection: OriginBridge T → SAW hexOrigin (b.1.walk.1.length). Then StripSAW_B T L is the subset with end_right and in_strip conditions. Since our bridges satisfy these, they're in StripSAW_B T L.

To formalize: construct a Finset.map from F to StripSAW_B T L using an injective function, then use Finset.sum_le_tsum.

IMPORTANT: Do NOT use origin_bridge_upper_bound or origin_bridge_lower_bound (they are sorry'd and would create a circular dependency). Instead use B_TL_le_one which is proved from strip_identity_concrete.

If F is empty, the sum is 0 ≤ 1.

If F is nonempty: Let L = Finset.sup F (fun b => originBridgeFitL T b). Then L ≥ 1 (using originBridgeFitL_pos applied to any element).

Each bridge b ∈ F fits in S_{T,L} because:
- origin_bridge_in_finite_strip gives: b fits in S_{T, originBridgeFitL T b}
- originBridgeFitL T b ≤ L (Finset.le_sup)
- finite_strip_monotone extends to S_{T,L}

Now ∑_{b∈F} xc^{b.length} ≤ 1 because:
Each element of F corresponds to a distinct SAW from hexOrigin in S_{T,L} ending at x=T. These SAWs are all distinct (different bridges give different walks). B_TL T L xc = tsum over ALL such SAWs ≥ sum over the subset corresponding to F. And B_TL T L xc ≤ 1 by B_TL_le_one.

For the inequality ∑_F ≤ B_TL: since B_TL = ∑' s, xc^{s.len}, and we have an injective map F → StripSAW_B T L that preserves the exponent, the finite sum ≤ tsum by Summable.sum_le_tsum (or Finset.sum_le_tsum for the appropriate version).

Actually, the simplest approach: since all terms are non-negative and bounded by 1, and the sum is a sum of at most |F| terms each ≤ xc^T ≤ 1... no, this gives |F| not 1.

The correct approach uses the injection into B_TL. The injection sends b to a StripSAW_B T L with the same length. The sum over F equals the sum over the image, which is a partial sum of B_TL. By Summable.sum_le_tsum, partial sum ≤ B_TL ≤ 1.

CRITICAL: Do NOT use origin_bridge_upper_bound, origin_bridge_lower_bound, origin_bridge_upper_bound_from_strip, or any lemma with sorry. Only use B_TL_le_one (which is proved from strip_identity_concrete).

Proof:
1. If F is empty, sum is 0 ≤ 1.
2. If F is nonempty, let L = F.sup' hF (fun b => originBridgeFitL T b).
3. Show L ≥ 1 using originBridgeFitL_pos.
4. Each b ∈ F has all walk vertices in FiniteStrip T L (by origin_bridge_in_finite_strip + finite_strip_monotone).
5. Therefore b determines a StripSAW_B T L: since b.1.start_v = hexOrigin (from b.2), and all vertices are in the strip, and b.1.end_v.1 = T (from b.1.end_right).
6. Since different origin bridges have different walks (they are subtypes), the map is injective.
7. ∑_F xc^{b.length} ≤ B_TL T L xc (by Finset.sum_le_tsum or similar, using the injection and non-negativity).
8. B_TL T L xc ≤ 1 (by B_TL_le_one T L hT hL_pos).

For step 5: Use the approach: have the SAW by defining it via `subst b.2` or pattern matching. Specifically, for b : OriginBridge T, match on b to get ⟨bridge, h_start⟩ where h_start : bridge.start_v = hexOrigin. Then subst h_start to get bridge.walk : hexGraph.Path hexOrigin bridge.end_v.

For step 7: B_TL T L xc = ∑' (s : StripSAW_B T L), xc ^ s.len. We need to show ∑_{b∈F} xc^{b.length} ≤ this tsum. The simplest way: show that F embeds into StripSAW_B T L, then use Summable.sum_le_tsum (or a sum over a subset lemma).

Alternative for step 7: Show that ∑_{b∈F} xc^{b.length} ≤ ∑ n ∈ Finset.range (N+1), c_n * xc^n for some N (since each bridge is a SAW of some length). But this doesn't directly relate to B_TL.

Actually, the cleanest approach: show that the Finset F can be mapped injectively into StripSAW_B T L with the same exponents, then use Finset.sum_le_tsum.
-/
/-- Map an origin bridge to a StripSAW_B, given it fits in the strip. -/
def originBridgeToStripB (T L : ℕ) :
    (b : OriginBridge T) → (∀ v ∈ b.1.walk.1.support, FiniteStrip T L v) → StripSAW_B T L
  | ⟨⟨_, ev, walk, _, er, _⟩, rfl⟩, hfit =>
    ⟨walk.1.length, ⟨ev, walk, rfl⟩, er, hfit⟩

lemma origin_bridge_partial_sum_le_one (T : ℕ) (hT : 1 ≤ T) (F : Finset (OriginBridge T)) :
    ∑ b ∈ F, xc ^ b.1.walk.1.length ≤ 1 := by
  sorry

/-- **origin_bridge_partition T xc ≤ 1**: the corrected bridge upper bound.
    Proof: every partial sum ≤ 1 (by the strip identity), so the tsum ≤ 1. -/
theorem origin_bridge_upper_bound_from_strip (T : ℕ) (hT : 1 ≤ T) :
    origin_bridge_partition T xc ≤ 1 := by
  exact Real.tsum_le_of_sum_le (fun b => pow_nonneg xc_pos.le _)
    (fun F => origin_bridge_partial_sum_le_one T hT F)

end