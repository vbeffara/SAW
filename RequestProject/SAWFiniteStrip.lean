/-
# The finite strip domain S_{T,L}

Formalization of the finite strip domain and its boundary decomposition,
from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

1. The infinite strip S_T and finite strip S_{T,L}
2. Boundary classification: α, β, ε, ε̄
3. Partition functions A_{T,L}, B_{T,L}, E_{T,L}
4. The strip identity (sorry) and consequences (B ≤ 1)
5. B_TL summability (finite strip → finitely many walks)
6. Origin bridge upper bound from strip identity
-/

import Mathlib
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

/-! ## B_TL summability -/

/-
PROBLEM
The set of vertices in the finite strip is finite.

PROVIDED SOLUTION
FiniteStrip T L v means: 0 ≤ v.1 ≤ T (so v.1 ∈ Finset.Icc 0 T) and |2*v.2.1 - v.1| ≤ 2L (so v.2.1 is bounded: (v.1 - 2L)/2 ≤ v.2.1 ≤ (v.1 + 2L)/2, hence v.2.1 ∈ some bounded interval). Also v.2.2 ∈ {true, false}. So the set is a subset of a finite product of bounded integer intervals × Bool, hence finite. Use Set.Finite.subset with a product of finite sets.
-/
lemma finite_strip_finite (T L : ℕ) :
    Set.Finite {v : HexVertex | FiniteStrip T L v} := by
  -- The set of vertices in the finite strip is a subset of a finite product of bounded integer intervals × Bool, hence finite.
  have h_finite : ∀ v : HexVertex, FiniteStrip T L v → v.1 ≤ T ∧ v.1 ≥ 0 ∧ v.2.1 ≤ L + T ∧ v.2.1 ≥ -L := by
    grind +locals
  generalize_proofs at *; (
  -- The set of vertices in the finite strip is a subset of a finite product of bounded integer intervals × Bool, hence finite. Use Set.Finite.subset with a product of finite sets.
  have h_finite_subset : {v : HexVertex | FiniteStrip T L v} ⊆ Set.image (fun (p : ℤ × ℤ × Bool) => (p.1, p.2.1, p.2.2)) (Set.Icc 0 (T : ℤ) ×ˢ Set.Icc (-L : ℤ) (L + T) ×ˢ Set.univ) := by
    exact fun v hv => ⟨ ( v.1, v.2.1, v.2.2 ), ⟨ ⟨ h_finite v hv |>.2.1, h_finite v hv |>.1 ⟩, ⟨ h_finite v hv |>.2.2.2, h_finite v hv |>.2.2.1 ⟩, by simp +decide ⟩, rfl ⟩ ;
  generalize_proofs at *; (
  exact Set.Finite.subset ( Set.Finite.image _ <| Set.Finite.prod ( Set.finite_Icc _ _ ) <| Set.Finite.prod ( Set.finite_Icc _ _ ) <| Set.toFinite _ ) h_finite_subset))

/-
PROBLEM
A SAW in the finite strip has bounded length (at most the number of strip vertices).

PROVIDED SOLUTION
The SAW has s.len + 1 distinct vertices in its support (since paths are injective). All support vertices are in the strip (by s.in_strip). The support vertices form an injective map into the finite strip vertex set. So s.len + 1 ≤ card of the strip vertex set, hence s.len ≤ card. Use s.saw.p.2.support_nodup for distinctness, s.saw.l for length = s.len, and construct an injection from the support list (as a finset via List.toFinset) into finite_strip_finite.toFinset.
-/
lemma strip_saw_length_bound (T L : ℕ) (s : StripSAW_B T L) :
    s.len ≤ (finite_strip_finite T L).toFinset.card := by
  have h_distinct_vertices : (s.saw.p.1.support.toFinset).card ≤ (finite_strip_finite T L).toFinset.card := by
    exact Finset.card_le_card fun x hx => by have := s.in_strip x ( by aesop ) ; aesop;
  have h_support_length : (s.saw.p.1.support.toFinset).card = s.saw.p.1.length + 1 := by
    rw [ List.toFinset_card_of_nodup ] <;> aesop;
  linarith [ s.saw.l ]

/-
PROBLEM
B_TL is summable for 0 ≤ x ≤ 1: there are finitely many SAWs in a finite strip
    (bounded walk length due to finite vertex set).

PROVIDED SOLUTION
By strip_saw_length_bound, every s : StripSAW_B T L has s.len ≤ N where N = (finite_strip_finite T L).toFinset.card. So StripSAW_B T L is finite: for each n ≤ N, the set {s : StripSAW_B T L | s.len = n} embeds into SAW hexOrigin n (which is a Fintype via instFintypeSAW). There are finitely many possible n values (0 to N) and each gives finitely many s. So StripSAW_B T L is finite. Use Finite.summable or show Finite (StripSAW_B T L) and apply tsum_coe_ne_top_iff_summable or similar. Alternatively, since the type is finite, any function on it is summable.
-/
lemma B_TL_summable (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Summable (fun s : StripSAW_B T L => x ^ s.len) := by
  have h_finite : Finite (StripSAW_B T L) := by
    -- By definition of `StripSAW_B`, the set of SAWs in a finite strip is finite.
    have h_finite_strip : Set.Finite {v : HexVertex | FiniteStrip T L v} := by
      exact finite_strip_finite T L;
    have h_finite_saws : Finite {s : Σ n : ℕ, SAW hexOrigin n | ∀ v ∈ s.2.p.1.support, FiniteStrip T L v ∧ s.2.w.1 = T} := by
      have h_finite_saws : ∃ N : ℕ, ∀ s : Σ n : ℕ, SAW hexOrigin n, (∀ v ∈ s.2.p.1.support, FiniteStrip T L v ∧ s.2.w.1 = T) → s.1 ≤ N := by
        use h_finite_strip.toFinset.card;
        intro s hs
        have h_support : s.2.p.1.support.toFinset ⊆ h_finite_strip.toFinset := by
          intro v hv; specialize hs v; aesop;
        have := Finset.card_mono h_support; simp_all +decide [ SimpleGraph.Walk.length ] ;
        have h_support_card : (s.snd.p.1.support.toFinset).card = s.snd.p.1.length + 1 := by
          rw [ List.toFinset_card_of_nodup ] <;> aesop;
        linarith [ s.2.l ];
      cases' h_finite_saws with N hN
      have h_finite_saws : Finite {s : Σ n : ℕ, SAW hexOrigin n | ∀ v ∈ s.2.p.1.support, FiniteStrip T L v ∧ s.2.w.1 = T ∧ s.1 ≤ N} := by
        have h_finite_saws : {s : Σ n : ℕ, SAW hexOrigin n | ∀ v ∈ s.2.p.1.support, FiniteStrip T L v ∧ s.2.w.1 = T ∧ s.1 ≤ N} ⊆ Set.image (fun s : Σ n : Fin (N + 1), {s : SAW hexOrigin n | ∀ v ∈ s.p.1.support, FiniteStrip T L v ∧ s.w.1 = T} => ⟨s.1.val, s.2.val⟩) Set.univ := by
          intro s hs; use ⟨ ⟨ s.1, by linarith [ hs, hN s fun v hv => ⟨ hs v hv |>.1, hs v hv |>.2.1 ⟩ ] ⟩, ⟨ s.2, fun v hv => ⟨ hs v hv |>.1, hs v hv |>.2.1 ⟩ ⟩ ⟩ ; aesop;
        generalize_proofs at *; (
        exact Set.Finite.to_subtype <| Set.Finite.subset ( Set.Finite.image _ <| Set.toFinite _ ) h_finite_saws)
      generalize_proofs at *; (
      exact Set.Finite.to_subtype <| Set.Finite.subset ( Set.finite_coe_iff.mp h_finite_saws ) fun s hs => fun v hv => ⟨ hs v hv |>.1, hs v hv |>.2, hN s hs ⟩ ;);
    have h_finite_saws : Finite {s : Σ n : ℕ, SAW hexOrigin n | ∀ v ∈ s.2.p.1.support, FiniteStrip T L v ∧ s.2.w.1 = T ∧ s.2.w.1 = T} := by
      grind;
    convert h_finite_saws.of_injective _ _;
    exact fun s => ⟨ ⟨ s.len, s.saw ⟩, fun v hv => ⟨ s.in_strip v hv, s.end_right, s.end_right ⟩ ⟩;
    intro s t h; cases s; cases t; aesop;
  haveI := Fintype.ofFinite ( StripSAW_B T L ) ; exact ⟨ _, hasSum_fintype _ ⟩ ;

/-! ## Passage to the infinite strip -/

def A_T_inf (T : ℕ) (x : ℝ) : ℝ := ⨆ L : ℕ, A_TL T L x
def B_T_inf (T : ℕ) (x : ℝ) : ℝ := ⨆ L : ℕ, B_TL T L x

/-- B_T_inf equals origin_bridge_partition when x > 0. -/
theorem B_T_inf_eq_origin_bridge (T : ℕ) (x : ℝ) (hx : 0 < x) :
    B_T_inf T x = origin_bridge_partition T x := by
  sorry

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
The origin-bridge-to-strip map preserves the weight (walk length).

PROVIDED SOLUTION
Unfold originBridgeToStripB using the match definition. The result follows by the definition of the map which preserves the walk length. Need to carefully destructure the OriginBridge subtype and Bridge structure.
-/
lemma originBridgeToStripB_len (T L : ℕ) (b : OriginBridge T)
    (hfit : ∀ v ∈ b.1.walk.1.support, FiniteStrip T L v) :
    (originBridgeToStripB T L b hfit).len = b.1.walk.1.length := by
  unfold originBridgeToStripB; aesop;

/-
PROBLEM
The originBridgeToStripB map is injective: two distinct origin bridges
    map to distinct StripSAW_B elements.

PROVIDED SOLUTION
Unfold originBridgeToStripB. The StripSAW_B equality gives equal len fields and equal SAW fields. The SAW determines the Bridge (same endpoint, same walk), and the OriginBridge subtype property is proof-irrelevant. Use cases/match on b₁ and b₂ to destructure them as ⟨⟨_, _, walk₁, _, _, _⟩, rfl⟩, then extract the equalities.
-/
lemma originBridgeToStripB_injective (T L : ℕ)
    {b₁ b₂ : OriginBridge T}
    (hfit₁ : ∀ v ∈ b₁.1.walk.1.support, FiniteStrip T L v)
    (hfit₂ : ∀ v ∈ b₂.1.walk.1.support, FiniteStrip T L v)
    (h : originBridgeToStripB T L b₁ hfit₁ = originBridgeToStripB T L b₂ hfit₂) :
    b₁ = b₂ := by
  unfold originBridgeToStripB at h;
  grind

/-- xc < 1: since xc = 1/√(2+√2) and √(2+√2) > 1. -/
private lemma xc_lt_one' : xc < 1 := by
  unfold xc; rw [div_lt_one (Real.sqrt_pos.mpr (by positivity))]
  exact Real.lt_sqrt_of_sq_lt (by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)])

/-
PROBLEM
Every finite partial sum of origin bridge weights at x_c is ≤ 1.
    Proved from B_TL_le_one via the strip identity.

    Key idea: for any finite set F of origin bridges, choose L large enough
    that all bridges in F fit in S_{T,L}. Map them injectively to StripSAW_B,
    and bound the partial sum by B_{T,L} ≤ 1.

PROVIDED SOLUTION
Choose L = F.sup (originBridgeFitL T). Case F empty: sum = 0 ≤ 1. Case F nonempty: L ≥ 1 by originBridgeFitL_pos. Each b ∈ F fits in S_{T,L}. Define f : F → StripSAW_B T L by f(b) = originBridgeToStripB T L b (hfit b). f is injective by originBridgeToStripB_injective. By originBridgeToStripB_len, xc^{b.length} = xc^{(f b).len}. So ∑_{b ∈ F} xc^{b.length} = ∑_{b ∈ F} xc^{(f b).len}. Since f is injective, this equals ∑_{s ∈ F.image f} xc^{s.len} (reindexing). This ≤ ∑' s : StripSAW_B T L, xc^{s.len} by Finset.sum_le_tsum (using B_TL_summable). And this = B_TL T L xc ≤ 1 by B_TL_le_one.
-/
lemma origin_bridge_partial_sum_le_one (T : ℕ) (hT : 1 ≤ T) (F : Finset (OriginBridge T)) :
    ∑ b ∈ F, xc ^ b.1.walk.1.length ≤ 1 := by
  by_contra h_contra;
  -- Choose L such that all bridges in F fit in S_{T,L}.
  obtain ⟨L, hL⟩ : ∃ L : ℕ, 1 ≤ L ∧ ∀ b ∈ F, ∀ v ∈ b.1.walk.1.support, FiniteStrip T L v := by
    -- Choose L such that all bridges in F fit in S_{T,L} by taking L to be the maximum of the originBridgeFitL values of the bridges in F.
    obtain ⟨L, hL⟩ : ∃ L : ℕ, ∀ b ∈ F, originBridgeFitL T b ≤ L := by
      exact ⟨ Finset.sup F ( fun b => originBridgeFitL T b ), fun b hb => Finset.le_sup ( f := fun b => originBridgeFitL T b ) hb ⟩;
    refine' ⟨ L + 1, Nat.succ_pos _, fun b hb v hv => _ ⟩;
    -- Since $v$ is in the support of $b$, we have $FiniteStrip T (originBridgeFitL T b) v$ by definition of $originBridgeFitL$.
    have h_finite_strip : FiniteStrip T (originBridgeFitL T b) v := by
      exact originBridgeFitL_pos T hT b |> fun h => origin_bridge_in_finite_strip T b v hv;
    exact finite_strip_monotone ( by linarith [ hL b hb ] ) v h_finite_strip;
  -- By definition of $B_{T,L}$, we have $\sum_{b \in F} xc^{b.length} \leq B_{T,L}$.
  have h_sum_le_BT_L : ∑ b ∈ F, xc ^ b.1.walk.1.length ≤ B_TL T L xc := by
    -- Since F is a finite set of origin bridges, each bridge in F can be mapped to a StripSAW_B T L.
    have h_map : ∃ f : F → StripSAW_B T L, Function.Injective f ∧ ∀ b : F, xc ^ b.val.1.walk.1.length = xc ^ (f b).len := by
      use fun b => originBridgeToStripB T L b.val (hL.2 b.val b.property);
      exact ⟨ fun a b h => by have := originBridgeToStripB_injective T L ( hL.2 a a.2 ) ( hL.2 b b.2 ) h; aesop, fun b => by rw [ originBridgeToStripB_len ] ⟩;
    obtain ⟨ f, hf_inj, hf_eq ⟩ := h_map;
    -- Since $f$ is injective, the image of $F$ under $f$ is a finite subset of $StripSAW_B T L$.
    have h_image_finite : Set.Finite (Set.range f) := by
      exact Set.toFinite _;
    have h_sum_le_BT_L : ∑ b ∈ F, xc ^ b.1.walk.1.length = ∑ s ∈ h_image_finite.toFinset, xc ^ s.len := by
      refine' Finset.sum_bij ( fun b hb => f ⟨ b, hb ⟩ ) _ _ _ _ <;> simp_all +decide [ Function.Injective.eq_iff hf_inj ];
    rw [h_sum_le_BT_L];
    refine' Summable.sum_le_tsum _ _ _;
    · exact fun _ _ => pow_nonneg ( by unfold xc; positivity ) _;
    · convert B_TL_summable T L xc ( show 0 ≤ xc by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) ( show xc ≤ 1 by exact div_le_one_of_le₀ ( Real.le_sqrt_of_sq_le ( by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ) ) ( Real.sqrt_nonneg _ ) ) using 1;
  exact h_contra <| h_sum_le_BT_L.trans <| B_TL_le_one T L hT hL.1

/-- origin_bridge_partition T xc ≤ 1: proved from partial sum bounds.
    This supersedes the sorry'd `origin_bridge_upper_bound` in SAWBridgeFix. -/
theorem origin_bridge_upper_bound_from_strip (T : ℕ) (hT : 1 ≤ T) :
    origin_bridge_partition T xc ≤ 1 := by
  exact Real.tsum_le_of_sum_le (fun b => pow_nonneg xc_pos.le _)
    (fun F => origin_bridge_partial_sum_le_one T hT F)

end