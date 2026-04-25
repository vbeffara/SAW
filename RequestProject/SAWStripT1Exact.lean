/-
# Exact partition functions for the width-1 strip

In PaperInfStrip 1, the graph is a doubly-infinite path:
  ... TRUE(-1,1) - FALSE(-1,0) - TRUE(0,0) - FALSE(0,-1) - TRUE(1,-1) - ...

Every PaperBridge 1 is either a "right walk" (going toward positive x)
or a "left walk" (going toward negative x), of odd length 2m+1.

This gives:
  paper_bridge_partition 1 xc = 2·xc/(1-xc²)
-/

import Mathlib
import RequestProject.SAWStripT1Walks

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Path graph structure of width-1 strip

The width-1 strip has the structure of a doubly-infinite path graph.
Each vertex has exactly 2 neighbors in the strip. -/

/-- In the width-1 strip, each vertex has exactly 2 strip-neighbors:
    no third distinct neighbor exists. -/
lemma strip1_at_most_2_neighbors (v : HexVertex) (hv : PaperInfStrip 1 v) :
    ∀ w₁ w₂ w₃ : HexVertex,
      hexGraph.Adj v w₁ → PaperInfStrip 1 w₁ →
      hexGraph.Adj v w₂ → PaperInfStrip 1 w₂ →
      hexGraph.Adj v w₃ → PaperInfStrip 1 w₃ →
      w₁ = w₂ ∨ w₁ = w₃ ∨ w₂ = w₃ := by
  rcases v with ⟨ x, y, b ⟩;
  cases b <;> simp_all +decide [ hexGraph ];
  · unfold PaperInfStrip at *; norm_num at *; omega;
  · unfold PaperInfStrip at *;
    grind

/-! ## SAW uniqueness on path graphs

On the width-1 strip (a path graph), there is at most one SAW
from paperStart to any given endpoint. -/

/-- On the width-1 strip, a PaperBridge 1 is uniquely determined
    by its endpoint. -/
lemma paper_bridge_1_unique_by_endpoint (b₁ b₂ : PaperBridge 1)
    (h : b₁.end_v = b₂.end_v) : b₁ = b₂ := by
  sorry

/-! ## Vertex coordinates on the strip

In the width-1 strip, vertices are linearly ordered by a single coordinate.
Define the "position" of a vertex on the strip path. -/

/-- The position of a strip vertex: TRUE(k,-k) has position 2k,
    FALSE(k,-k-1) has position 2k+1. -/
def strip1_pos (v : HexVertex) : ℤ :=
  if v.2.2 then 2 * v.1 else 2 * v.1 + 1

/-
Adjacent strip-1 vertices have positions differing by exactly 1.
-/
lemma strip1_adj_pos_diff {v w : HexVertex}
    (hv : PaperInfStrip 1 v) (hw : PaperInfStrip 1 w)
    (hadj : hexGraph.Adj v w) :
    strip1_pos w - strip1_pos v = 1 ∨ strip1_pos w - strip1_pos v = -1 := by
  cases hadj;
  · unfold strip1_pos;
    grind;
  · unfold strip1_pos;
    grind

/-
On a path in the strip, consecutive position differences have
    constant sign: all +1 or all -1. This is because at each interior
    vertex, one of the two neighbors is already visited (since the
    graph has degree 2), so the walk is forced to continue in the
    same direction.
-/
lemma strip1_path_constant_sign {v w : HexVertex}
    (p : hexGraph.Walk v w) (hp : p.IsPath)
    (hstrip : ∀ u ∈ p.support, PaperInfStrip 1 u)
    (hlen : 2 ≤ p.length) :
    (∀ i, i + 1 < p.length →
      strip1_pos (p.getVert (i+2)) - strip1_pos (p.getVert (i+1)) =
      strip1_pos (p.getVert (i+1)) - strip1_pos (p.getVert i)) := by
  intro i hi
  have h_diff : strip1_pos (p.getVert (i + 2)) - strip1_pos (p.getVert (i + 1)) ∈ ({1, -1} : Set ℤ) ∧ strip1_pos (p.getVert (i + 1)) - strip1_pos (p.getVert i) ∈ ({1, -1} : Set ℤ) := by
    have h_diff : ∀ i : ℕ, i + 1 < p.length → hexGraph.Adj (p.getVert i) (p.getVert (i + 1)) := by
      grind +suggestions;
    apply And.intro;
    · apply strip1_adj_pos_diff;
      · apply hstrip;
        exact?;
      · apply hstrip;
        exact?;
      · exact?;
    · apply strip1_adj_pos_diff (hstrip (p.getVert i) (by
      exact?)) (hstrip (p.getVert (i + 1)) (by
      exact?)) (h_diff i hi);
  by_contra h_contra;
  have h_eq : strip1_pos (p.getVert (i + 2)) = strip1_pos (p.getVert i) := by
    grind;
  have h_eq : p.getVert (i + 2) = p.getVert i := by
    unfold strip1_pos at h_eq; simp_all +decide [ sub_eq_iff_eq_add ] ;
    split_ifs at h_eq <;> simp_all +decide [ Prod.ext_iff ];
    · have := hstrip ( p.getVert ( i + 2 ) |>.1 ) ( p.getVert ( i + 2 ) |>.2.1 ) ; have := hstrip ( p.getVert i |>.1 ) ( p.getVert i |>.2.1 ) ; simp_all +decide [ PaperInfStrip ] ;
      grind +suggestions;
    · omega;
    · omega;
    · have := hstrip ( p.getVert ( i + 2 ) |> Prod.fst ) ( p.getVert ( i + 2 ) |> Prod.snd |> Prod.fst ) ; have := hstrip ( p.getVert i |> Prod.fst ) ( p.getVert i |> Prod.snd |> Prod.fst ) ; simp_all +decide [ PaperInfStrip ] ;
      grind +suggestions;
  have := hp.getVert_injOn; simp_all +decide [ Set.InjOn ] ;
  exact absurd ( @this ( i + 2 ) ( by linarith ) i ( by linarith ) h_eq ) ( by linarith )

/-
The position changes monotonically along a SAW in the width-1 strip.
    That is, the positions are either strictly increasing or strictly decreasing.
-/
lemma strip1_saw_monotone {v w : HexVertex}
    (p : hexGraph.Walk v w) (hp : p.IsPath)
    (hstrip : ∀ u ∈ p.support, PaperInfStrip 1 u) :
    (∀ i j, i < j → j ≤ p.length →
      strip1_pos (p.getVert i) < strip1_pos (p.getVert j)) ∨
    (∀ i j, i < j → j ≤ p.length →
      strip1_pos (p.getVert j) < strip1_pos (p.getVert i)) := by
  by_cases hlen : p.length ≤ 1;
  · rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> simp_all +decide;
    · bv_omega;
    · rcases hstrip with ⟨ h₁, h₂ ⟩;
      cases strip1_adj_pos_diff h₁ h₂ ‹_› <;> simp_all +decide [ strip1_pos ];
      · exact Or.inl fun i j hij hj => by interval_cases j <;> interval_cases i ; simp +decide at * ; linarith;
      · exact Or.inr fun i j hij hj => by interval_cases j <;> interval_cases i ; simp +decide at * ; linarith;
  · -- By strip1_path_constant_sign, all consecutive position differences are equal. Let d = strip1_pos(p.getVert 1) - strip1_pos(p.getVert 0).
    obtain ⟨d, hd⟩ : ∃ d : ℤ, ∀ i < p.length, strip1_pos (p.getVert (i + 1)) - strip1_pos (p.getVert i) = d := by
      have h_monotone : ∀ i < p.length - 1, strip1_pos (p.getVert (i + 2)) - strip1_pos (p.getVert (i + 1)) = strip1_pos (p.getVert (i + 1)) - strip1_pos (p.getVert i) := by
        exact fun i hi => strip1_path_constant_sign p hp hstrip ( by linarith ) i ( by omega );
      use strip1_pos (p.getVert 1) - strip1_pos (p.getVert 0);
      intro i hi; induction' i with i ih <;> norm_num at *;
      rw [ h_monotone i ( Nat.lt_pred_iff.mpr hi ), ih ( Nat.lt_of_succ_lt hi ) ];
    -- By strip1_adj_pos_diff, d = 1 or d = -1.
    have hd_cases : d = 1 ∨ d = -1 := by
      have := hd 0 (by linarith)
      have := strip1_adj_pos_diff (hstrip (p.getVert 0) (by
      exact?)) (hstrip (p.getVert 1) (by
      cases p <;> aesop)) (by
      rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> aesop)
      aesop;
    -- By induction on $j - i$, we can show that the position difference is $d * (j - i)$.
    have h_ind : ∀ i j : ℕ, i ≤ j → j ≤ p.length → strip1_pos (p.getVert j) - strip1_pos (p.getVert i) = d * (j - i) := by
      intro i j hij hj; induction hij <;> norm_num at *;
      grind;
    cases hd_cases <;> [ left; right ] <;> intros i j hij hj <;> nlinarith [ h_ind i j hij.le hj ]

/-- paperStart has position 0. -/
@[simp] lemma strip1_pos_paperStart : strip1_pos paperStart = 0 := by
  simp [strip1_pos, paperStart]

/-- FALSE vertex with x+y=-1 has odd position. -/
lemma strip1_pos_false {k : ℤ} :
    strip1_pos (k, -k-1, false) = 2*k + 1 := by
  simp [strip1_pos]

/-
Position determines the vertex on the strip.
-/
lemma strip1_pos_injective (v w : HexVertex)
    (hv : PaperInfStrip 1 v) (hw : PaperInfStrip 1 w)
    (h : strip1_pos v = strip1_pos w) : v = w := by
  unfold strip1_pos at h;
  unfold PaperInfStrip at hv hw;
  grind

/-! ## Endpoint characterization -/

/-- A PaperBridge 1 going "right" (position increases) ends at
    FALSE(m, -m-1) with position 2m+1 for some m ≥ 0. -/
lemma paper_bridge_1_right_endpoint (b : PaperBridge 1)
    (h : strip1_pos b.end_v > 0) :
    ∃ m : ℕ, b.end_v = (↑m, -(↑m : ℤ)-1, false) ∧
      b.walk.1.length = 2*m + 1 := by
  sorry

/-- A PaperBridge 1 going "left" (position decreases) ends at
    FALSE(-m-1, m) with position -(2m+1) for some m ≥ 0. -/
lemma paper_bridge_1_left_endpoint (b : PaperBridge 1)
    (h : strip1_pos b.end_v < 0) :
    ∃ m : ℕ, b.end_v = (-(↑m : ℤ)-1, ↑m, false) ∧
      b.walk.1.length = 2*m + 1 := by
  sorry

/-! ## Bridge construction -/

/-
Explicit construction of a right bridge of length 2m+1.
    Uses induction: extend the previous bridge by 2 steps.
-/
lemma exists_right_bridge (m : ℕ) :
    ∃ b : PaperBridge 1, b.end_v = (↑m, -(↑m : ℤ)-1, false) ∧
      b.walk.1.length = 2*m + 1 := by
  induction' m with m ih;
  · use rightBridge0;
    aesop;
  · obtain ⟨b, hb⟩ := ih;
    refine' ⟨ ⟨ _, _, _, _ ⟩, _, _ ⟩;
    exact ( m + 1, - ( m + 1 ) - 1, false );
    refine' ⟨ _, _ ⟩;
    refine' b.walk.1.append ( SimpleGraph.Walk.cons _ ( SimpleGraph.Walk.cons _ SimpleGraph.Walk.nil ) );
    rotate_left;
    exact ( m + 1, - ( m + 1 ), true );
    all_goals norm_num [ hexGraph ];
    all_goals norm_num [ SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons, hb ];
    · rw [ List.nodup_append ];
      have h_support : ∀ a ∈ (b.walk.1.support), strip1_pos a ≤ 2 * m + 1 := by
        have h_support : ∀ i ≤ b.walk.1.length, strip1_pos (b.walk.1.getVert i) ≤ 2 * m + 1 := by
          have h_support : ∀ i ≤ b.walk.1.length, strip1_pos (b.walk.1.getVert i) ≤ strip1_pos (b.walk.1.getVert b.walk.1.length) := by
            have := strip1_saw_monotone b.walk.1 b.walk.2 ( fun u hu => b.in_strip u hu );
            cases this <;> simp_all +decide [ strip1_pos ];
            · grind;
            · rename_i h; specialize h 0 ( 2 * m + 1 ) ; simp_all +decide ;
              have := b.end_right; simp_all +decide [ paperStart ] ;
              grind +suggestions;
          grind +suggestions;
        intro a ha;
        rw [ SimpleGraph.Walk.mem_support_iff_exists_getVert ] at ha;
        grind;
      simp_all +decide [ strip1_pos ];
      grind;
    · intro a a_1; constructor <;> intro h <;> rcases h with ( h | h | h ) <;> simp_all +decide [ PaperInfStrip ] ;
      · have := b.in_strip ( a, a_1, false ) h; aesop;
      · constructor <;> linarith;
      · have := b.in_strip ( a, a_1, true ) h; aesop;
      · grind;
    · ring;
    · ring

/-
Explicit construction of a left bridge of length 2m+1.
-/
lemma exists_left_bridge (m : ℕ) :
    ∃ b : PaperBridge 1, b.end_v = (-(↑m : ℤ)-1, ↑m, false) ∧
      b.walk.1.length = 2*m + 1 := by
  by_contra h_contra;
  convert exists_right_bridge m using 1;
  constructor <;> intro h <;> cases' h with b hb;
  refine' h_contra ⟨ _, _, _ ⟩;
  -- Define the new bridge by reflecting the original bridge over the line y = -x.
  use (b.end_v.2.1, b.end_v.1, b.end_v.2.2);
  refine' ⟨ _, _ ⟩;
  exact b.walk.1.map ( show hexGraph →g hexGraph from { toFun := fun v => ( v.2.1, v.1, v.2.2 ), map_rel' := by
                                                          unfold hexGraph; aesop; } );
  all_goals norm_num [ hb ];
  · simp +decide [ SimpleGraph.Walk.isPath_def ];
    rw [ List.nodup_map_iff_inj_on ];
    · grind;
    · exact b.walk.2.support_nodup;
  · ring;
  · intro a a_1; constructor <;> intros <;> subst_vars <;> simp_all +decide [ PaperInfStrip ] ;
    · have := b.in_strip _ ‹_›; simp_all +decide [ PaperInfStrip ] ;
      grind +extAll;
    · have := b.in_strip _ ‹_›; simp_all +decide [ PaperInfStrip ] ;
      grind +splitImp

/-! ## Right and left bridges have different endpoints -/

lemma right_left_endpoints_ne (m₁ m₂ : ℕ) :
    ((↑m₁ : ℤ), -(↑m₁ : ℤ)-1, false) ≠ (-(↑m₂ : ℤ)-1, (↑m₂ : ℤ), false) := by
  intro h; simp at h; omega

/-! ## Partition function bounds -/

/-- paper_bridge_partition 1 xc ≤ 2xc/(1-xc²). -/
lemma paper_bridge_partition_1_le :
    paper_bridge_partition 1 xc ≤ 2 * xc / (1 - xc ^ 2) := by
  sorry

/-
paper_bridge_partition 1 xc ≥ 2xc/(1-xc²).
-/
lemma paper_bridge_partition_1_ge :
    2 * xc / (1 - xc ^ 2) ≤ paper_bridge_partition 1 xc := by
  rw [ div_le_iff₀ ( by linarith [xc_sq_lt_one] ) ];
  rw [ show paper_bridge_partition 1 xc = ∑' ( b : PaperBridge 1 ), xc ^ b.walk.1.length from rfl ];
  -- By definition of $paper_bridge_partition$, we know that
  have h_partition : (∑' (b : PaperBridge 1), xc ^ (b.walk.1.length)) ≥ (∑' (m : ℕ), xc ^ (2 * m + 1)) + (∑' (m : ℕ), xc ^ (2 * m + 1)) := by
    have h_sum : ∑' (m : ℕ), xc ^ (2 * m + 1) + ∑' (m : ℕ), xc ^ (2 * m + 1) ≤ ∑' (p : ℕ ⊕ ℕ), xc ^ (match p with | Sum.inl m => 2 * m + 1 | Sum.inr m => 2 * m + 1) := by
      rw [ Summable.tsum_sum ];
      · have h_sum : Summable (fun m : ℕ => xc ^ (2 * m + 1)) := by
          norm_num [ pow_add, pow_mul ];
          exact Summable.mul_right _ ( summable_geometric_of_lt_one ( by positivity ) ( by nlinarith [ xc_sq_lt_one ] ) );
        exact h_sum;
      · have h_summable : Summable (fun m : ℕ => xc ^ (2 * m + 1)) := by
          norm_num [ pow_add, pow_mul ];
          exact Summable.mul_right _ ( summable_geometric_of_lt_one ( by positivity ) ( by nlinarith [ xc_sq_lt_one ] ) );
        exact h_summable;
    have h_sum : ∑' (p : ℕ ⊕ ℕ), xc ^ (match p with | Sum.inl m => 2 * m + 1 | Sum.inr m => 2 * m + 1) ≤ ∑' (b : PaperBridge 1), xc ^ b.walk.1.length := by
      have h_inj : Function.Injective (fun p : ℕ ⊕ ℕ => match p with | Sum.inl m => (exists_right_bridge m).choose | Sum.inr m => (exists_left_bridge m).choose) := by
        intro p q h_eq;
        grind
      rw [ ← tsum_eq_tsum_of_ne_zero_bij ];
      use fun p => match p.val with | Sum.inl m => (exists_right_bridge m).choose | Sum.inr m => (exists_left_bridge m).choose;
      · exact fun p q h => Subtype.ext <| h_inj h;
      · intro b hb;
        by_cases h : strip1_pos b.end_v > 0;
        · obtain ⟨ m, hm ⟩ := paper_bridge_1_right_endpoint b h;
          use ⟨ Sum.inl m, by
            simp +decide [ Function.support, xc_pos.ne' ] ⟩
          generalize_proofs at *;
          exact paper_bridge_1_unique_by_endpoint _ _ ( by simpa [ hm ] using ( exists_right_bridge m |> Exists.choose_spec |> And.left ) );
        · by_cases h' : strip1_pos b.end_v < 0;
          · obtain ⟨ m, hm ⟩ := paper_bridge_1_left_endpoint b h';
            use ⟨ Sum.inr m, by
              exact ne_of_gt ( pow_pos ( by exact lt_of_le_of_lt ( by norm_num ) ( show xc > 0 from by exact lt_of_le_of_lt ( by norm_num ) ( show xc > 0 from by exact xc_pos ) ) ) _ ) ⟩
            generalize_proofs at *;
            exact paper_bridge_1_unique_by_endpoint _ _ ( by simpa [ hm ] using ( exists_left_bridge m |> Exists.choose_spec |> And.left ) );
          · have := b.end_right; simp_all +decide [ strip1_pos ] ;
            omega;
      · rintro ⟨ p, hp ⟩ ; rcases p with ( m | m ) <;> simp +decide [ hp ] ;
        · exact congr_arg _ ( mod_cast ( exists_right_bridge m |> Exists.choose_spec |> And.right ) );
        · exact congr_arg _ ( mod_cast ( exists_left_bridge m |> Exists.choose_spec |> And.right ) );
    exact le_trans ‹_› h_sum;
  norm_num [ pow_add, pow_mul, tsum_mul_left ] at *;
  rw [ tsum_mul_right, tsum_geometric_of_lt_one ( by positivity ) ( by nlinarith [ xc_sq_lt_one ] ) ] at h_partition ; nlinarith [ xc_pos, xc_sq_lt_one, mul_inv_cancel₀ ( by nlinarith [ xc_sq_lt_one ] : ( 1 - xc ^ 2 ) ≠ 0 ) ]

/-- paper_bridge_partition 1 xc = 2xc/(1-xc²). -/
theorem paper_bridge_partition_1_eq :
    paper_bridge_partition 1 xc = 2 * xc / (1 - xc ^ 2) :=
  le_antisymm paper_bridge_partition_1_le paper_bridge_partition_1_ge

end