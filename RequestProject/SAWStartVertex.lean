/-
# The vertex relation at the starting vertex

The discrete Stokes identity `stripSum_eq_bdrySum` reduces the boundary sum to
the parafermionic vertex sum at `paperStart`, the one vertex of the strip where
the vertex relation (`fresh_vertex_relation`) fails.  This file computes that
defect.

In Duminil-Copin & Smirnov a configuration starts at the boundary *mid-edge*
`a`, and the empty configuration contributes `F(a) = 1`.  Here a configuration
starts at the *vertex* `paperStart`, so the empty configuration is absent, while
the degenerate configuration that immediately steps back out along `a` is
present.  Both discrepancies live on the mid-edge `a = (paperStart, hexOrigin)`,
and the outcome is the clean identity

  `paperStart_vertex_defect :
     freshVertexSum T L paperStart + freshObs T L paperStart hexOrigin = 1`

from which `bdry_start_eval` follows at once.

## Structure of the computation

Writing `n₀ = hexOrigin`, `n₁ = (-1,0,false)`, `n₂ = (0,-1,false)` for the three
neighbours of `paperStart` and `dᵢ` for the corresponding directions
(`d₀ = -1`, `d₁ = e^{-iπ/3}`, `d₂ = e^{iπ/3}`):

* `freshObs T L hexOrigin paperStart = 0` — nothing can reach `hexOrigin`;
* since `d₀ = -1`, the `n₀` term of the vertex sum cancels the added
  `freshObs T L paperStart hexOrigin`, leaving
  `d₁(F(v,n₁) + F(n₁,v)) + d₂(F(v,n₂) + F(n₂,v))`;
* `F(v,nₖ)` for `k = 1,2` consists of the single *empty* configuration
  (`freshObs_paperStart_side`): a nonempty configuration returning to
  `paperStart` must use both edges `v–n₁` and `v–n₂`, so its free mid-edge is
  forced to be `a`;
* the two empty configurations give `d₁ x e^{iσπ/3} + d₂ x e^{-iσπ/3}
  = 2x cos(π/8) = 1` at `x = xc` (`paperStart_nil_triplet`) — this is exactly
  the local relation of Lemma 1, with the empty configuration at `a` playing the
  role of the root;
* the remaining configurations pair up and cancel
  (`paperStart_pair_cancel`) — this is the analogue at `paperStart` of the pair
  involution of Lemma 1.  The involution itself is constructed here
  (`equivP1`, `equivP2`); the two pinned winding values it needs
  (`paperStart_inner_winding_one`, `paperStart_inner_winding_two`) are the
  turning-number input and are the only statements of this file still stated
  with `sorry`.
-/

import Mathlib
import RequestProject.SAWStripBoundarySum
import RequestProject.SAWVEdgeCountAux

open Real Complex

noncomputable section

set_option maxHeartbeats 1600000

/-! ## The three neighbours of `paperStart` -/

lemma hexNbr_paperStart_zero : hexNeighbors3 paperStart 0 = hexOrigin := rfl

lemma hexNbr_paperStart_one :
    hexNeighbors3 paperStart 1 = ((-1, 0, false) : HexVertex) := rfl

lemma hexNbr_paperStart_two :
    hexNeighbors3 paperStart 2 = ((0, -1, false) : HexVertex) := rfl

lemma midEdgeDir_paperStart_zero : midEdgeDir paperStart 0 = -1 := by
  simp [midEdgeDir, hexNeighbors3, trueNeighbors, paperStart, correctHexEmbed,
    Complex.ext_iff]

lemma midEdgeDir_paperStart_one :
    midEdgeDir paperStart 1
      = Complex.cos ((-(Real.pi / 3) : ℝ)) + Complex.sin ((-(Real.pi / 3) : ℝ)) * Complex.I := by
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp [midEdgeDir, hexNeighbors3, trueNeighbors, paperStart, correctHexEmbed,
    Complex.ext_iff]
  norm_num [neg_div]

lemma midEdgeDir_paperStart_two :
    midEdgeDir paperStart 2
      = Complex.cos ((Real.pi / 3 : ℝ)) + Complex.sin ((Real.pi / 3 : ℝ)) * Complex.I := by
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp [midEdgeDir, hexNeighbors3, trueNeighbors, paperStart, correctHexEmbed,
    Complex.ext_iff]
  norm_num

lemma arg_midEdgeDir_paperStart_one :
    Complex.arg (midEdgeDir paperStart 1) = -(Real.pi / 3) := by
  rw [midEdgeDir_paperStart_one]
  exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

lemma arg_midEdgeDir_paperStart_two :
    Complex.arg (midEdgeDir paperStart 2) = Real.pi / 3 := by
  rw [midEdgeDir_paperStart_two]
  exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-! ## The configurations at the two inner mid-edges of `paperStart` -/

/-- The empty configuration at the mid-edge `(paperStart, nₖ)`. -/
def nilFreshTrail (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (k : Fin 3) :
    FreshTrail T L paperStart (hexNeighbors3 paperStart k) where
  walk := SimpleGraph.Walk.nil
  is_trail := by simp
  adj := hexNeighbors3_adj paperStart k
  fresh := by simp
  in_strip := by
    intro u hu
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
    subst hu
    exact paperStart_in_fin_strip T L hT hL

/-- **The only configuration at an inner mid-edge of `paperStart` is the empty
one.**  A nonempty configuration returns to `paperStart`, hence uses two of the
three edges at `paperStart`; the edge to `hexOrigin` is unusable, so it uses
both `v–n₁` and `v–n₂`, contradicting the freshness of `s(v, nₖ)`. -/
lemma paperStart_out_walk_length_zero {T L : ℕ} {k : Fin 3} (hk : k ≠ 0)
    (γ : FreshTrail T L paperStart (hexNeighbors3 paperStart k)) :
    γ.walk.length = 0 := by
  have hi : s(hexNeighbors3 paperStart 0, paperStart) ∉ γ.walk.edges :=
    freshTrail_start_edge_not_mem γ
  have hj : s(hexNeighbors3 paperStart k, paperStart) ∉ γ.walk.edges := by
    rw [Sym2.eq_swap]; exact γ.fresh
  have hle : vEdgeCount paperStart γ.walk ≤ 1 :=
    vEdgeCount_le_one_of_two_excluded (Ne.symm hk) γ.walk γ.is_trail hi hj
  have hpar := vEdgeCount_parity paperStart paperStart γ.walk paperStart
  simp only at hpar
  have h0 : vEdgeCount paperStart γ.walk = 0 := by omega
  exact walk_length_zero_of_vEdgeCount_zero γ.walk h0

lemma paperStart_out_eq_nil {T L : ℕ} {k : Fin 3} (hT : 1 ≤ T) (hL : 1 ≤ L) (hk : k ≠ 0)
    (γ : FreshTrail T L paperStart (hexNeighbors3 paperStart k)) :
    γ = nilFreshTrail T L hT hL k := by
  have h := paperStart_out_walk_length_zero hk γ
  obtain ⟨walk, is_trail, adj, fresh, in_strip⟩ := γ
  simp only at h
  have : walk = SimpleGraph.Walk.nil := by
    cases walk with
    | nil => rfl
    | cons hadj q => simp at h
  subst this
  rfl

/-! ## The weight of the empty configuration -/

lemma nilFreshTrail_len (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (k : Fin 3) :
    (nilFreshTrail T L hT hL k).len = 1 := rfl

lemma nilFreshTrail_winding (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (k : Fin 3) :
    (nilFreshTrail T L hT hL k).winding = Complex.arg (midEdgeDir paperStart k) := by
  show hexWalkWinding [hexOrigin, paperStart, hexNeighbors3 paperStart k] = _
  simp only [hexWalkWinding, correctHexEmbed_hexOrigin, correctHexEmbed_paperStart',
    midEdgeDir]
  norm_num

lemma nilFreshTrail_weight (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (k : Fin 3) :
    (nilFreshTrail T L hT hL k).weight
      = walkWeight (Complex.arg (midEdgeDir paperStart k)) 1 xc sigma := by
  rw [FreshTrail.weight, nilFreshTrail_winding, nilFreshTrail_len]

/-- The observable on an inner mid-edge of `paperStart`. -/
lemma freshObs_paperStart_side (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) {k : Fin 3} (hk : k ≠ 0) :
    freshObs T L paperStart (hexNeighbors3 paperStart k)
      = walkWeight (Complex.arg (midEdgeDir paperStart k)) 1 xc sigma := by
  haveI : Unique (FreshTrail T L paperStart (hexNeighbors3 paperStart k)) :=
    ⟨⟨nilFreshTrail T L hT hL k⟩, fun γ => paperStart_out_eq_nil hT hL hk γ⟩
  rw [freshObs, tsum_eq_single (nilFreshTrail T L hT hL k)
    (fun b hb => absurd (Subsingleton.elim b (nilFreshTrail T L hT hL k)) hb)]
  exact nilFreshTrail_weight T L hT hL k

/-! ## The local relation at the starting vertex -/

/-- **The empty-configuration triplet.**  The two empty configurations at the
inner mid-edges of `paperStart` contribute exactly `1`; this is the local
relation of Lemma 1 with the (absent) empty configuration at `a` as its root,
and it is where the critical value `xc = 1/(2 cos(π/8))` enters. -/
lemma paperStart_nil_triplet :
    midEdgeDir paperStart 1 * walkWeight (Complex.arg (midEdgeDir paperStart 1)) 1 xc sigma
      + midEdgeDir paperStart 2
        * walkWeight (Complex.arg (midEdgeDir paperStart 2)) 1 xc sigma = 1 := by
  rw [arg_midEdgeDir_paperStart_one, arg_midEdgeDir_paperStart_two,
    midEdgeDir_paperStart_one, midEdgeDir_paperStart_two, ← Complex.exp_mul_I,
    ← Complex.exp_mul_I]
  unfold walkWeight
  have h1 : Complex.exp (((-(Real.pi / 3) : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (-Complex.I * (sigma : ℂ) * ((-(Real.pi / 3) : ℝ) : ℂ)) * (xc : ℂ) ^ 1)
      = Complex.exp (((-(Real.pi / 8) : ℝ) : ℂ) * Complex.I) * (xc : ℂ) := by
    rw [pow_one, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast [sigma]
    ring
  have h2 : Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (-Complex.I * (sigma : ℂ) * ((Real.pi / 3 : ℝ) : ℂ)) * (xc : ℂ) ^ 1)
      = Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) * (xc : ℂ) := by
    rw [pow_one, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast [sigma]
    ring
  rw [h1, h2]
  have hcos : Complex.exp (((-(Real.pi / 8) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I)
      = 2 * ((Real.cos (Real.pi / 8) : ℝ) : ℂ) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hc : Real.cos (Real.pi / 8) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have hc' : ((Real.cos (Real.pi / 8) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hxc : ((xc : ℝ) : ℂ) = 1 / (2 * ((Real.cos (Real.pi / 8) : ℝ) : ℂ)) := by
    rw [show xc = 1 / (2 * Real.cos (Real.pi / 8)) from by
      unfold xc; rw [sqrt_two_add_sqrt_two_eq]]
    push_cast; ring
  calc Complex.exp (((-(Real.pi / 8) : ℝ) : ℂ) * Complex.I) * (xc : ℂ)
        + Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) * (xc : ℂ)
      = (Complex.exp (((-(Real.pi / 8) : ℝ) : ℂ) * Complex.I)
          + Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I)) * (xc : ℂ) := by ring
    _ = 2 * ((Real.cos (Real.pi / 8) : ℝ) : ℂ) * (1 / (2 * ((Real.cos (Real.pi / 8) : ℝ) : ℂ))) := by
        rw [hcos, hxc]
    _ = 1 := by field_simp

/-! ## The pair involution at the starting vertex -/

lemma FreshTrail.ext' {T L : ℕ} {p n : HexVertex} {γ₁ γ₂ : FreshTrail T L p n}
    (h : γ₁.walk = γ₂.walk) : γ₁ = γ₂ := by
  cases γ₁; cases γ₂; simp only at h; subst h; rfl

lemma paperStart_ne_one : paperStart ≠ hexNeighbors3 paperStart 1 := by decide
lemma paperStart_ne_two : paperStart ≠ hexNeighbors3 paperStart 2 := by decide
lemma nbr_one_ne_two : hexNeighbors3 paperStart 1 ≠ hexNeighbors3 paperStart 2 := by decide

/-- The inner part of a configuration at an inner mid-edge of `paperStart`: a
trail from `n₂` to `n₁` that avoids `paperStart` and stays in the strip. -/
def innerC (T L : ℕ) : Type :=
  { q : hexGraph.Walk (hexNeighbors3 paperStart 2) (hexNeighbors3 paperStart 1) //
      q.IsTrail ∧ paperStart ∉ q.support ∧ ∀ u ∈ q.support, PaperFinStrip T L u }

lemma innerC_edge_not_mem {T L : ℕ} (q : innerC T L) (x : HexVertex) :
    s(paperStart, x) ∉ q.1.edges := by
  intro hmem
  exact q.2.2.1 (q.1.fst_mem_support_of_mem_edges hmem)

lemma innerC_edge_not_mem' {T L : ℕ} (q : innerC T L) (x : HexVertex) :
    s(x, paperStart) ∉ q.1.edges := by
  rw [Sym2.eq_swap]; exact innerC_edge_not_mem q x

/-- Attaching `paperStart` through `n₂` gives a configuration at the mid-edge
`(n₁, paperStart)`. -/
def toP1 (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (q : innerC T L) :
    FreshTrail T L (hexNeighbors3 paperStart 1) paperStart where
  walk := SimpleGraph.Walk.cons (hexNeighbors3_adj paperStart 2) q.1
  is_trail := by
    rw [SimpleGraph.Walk.isTrail_cons]
    exact ⟨q.2.1, innerC_edge_not_mem q _⟩
  adj := (hexNeighbors3_adj paperStart 1).symm
  fresh := by
    rw [SimpleGraph.Walk.edges_cons]
    simp only [List.mem_cons, not_or]
    exact ⟨by decide, innerC_edge_not_mem' q _⟩
  in_strip := by
    intro u hu
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact paperStart_in_fin_strip T L hT hL
    · exact q.2.2.2 u hu

/-- Attaching `paperStart` through `n₁` to the reversed inner trail gives a
configuration at the mid-edge `(n₂, paperStart)`. -/
def toP2 (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (q : innerC T L) :
    FreshTrail T L (hexNeighbors3 paperStart 2) paperStart where
  walk := SimpleGraph.Walk.cons (hexNeighbors3_adj paperStart 1) q.1.reverse
  is_trail := by
    rw [SimpleGraph.Walk.isTrail_cons]
    refine ⟨q.2.1.reverse, ?_⟩
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
    exact innerC_edge_not_mem q _
  adj := (hexNeighbors3_adj paperStart 2).symm
  fresh := by
    rw [SimpleGraph.Walk.edges_cons]
    simp only [List.mem_cons, not_or]
    constructor
    · decide
    · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
      exact innerC_edge_not_mem' q _
  in_strip := by
    intro u hu
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact paperStart_in_fin_strip T L hT hL
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hu
      exact q.2.2.2 u hu

lemma toP1_len (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (q : innerC T L) :
    (toP1 T L hT hL q).len = q.1.length + 2 := by
  simp [FreshTrail.len, toP1]

lemma toP2_len (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (q : innerC T L) :
    (toP2 T L hT hL q).len = q.1.length + 2 := by
  simp [FreshTrail.len, toP2]

/-- The first step of a configuration at the mid-edge `(n₁, paperStart)` goes to
`n₂`, and the rest of it is an inner trail. -/
lemma toP1_surjective (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    Function.Surjective (toP1 T L hT hL) := by
  intro γ
  obtain ⟨u, hadj, p', hp'⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne paperStart_ne_one γ.walk
  have hfresh := γ.fresh
  rw [hp', SimpleGraph.Walk.edges_cons] at hfresh
  have htrail := γ.is_trail
  rw [hp', SimpleGraph.Walk.isTrail_cons] at htrail
  have hstrip := γ.in_strip
  rw [hp'] at hstrip
  have hu2 : u = hexNeighbors3 paperStart 2 := by
    have huin : PaperFinStrip T L u := by
      refine hstrip u ?_
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ p'.start_mem_support
    have hune0 : u ≠ hexOrigin := by
      rintro rfl; exact hexOrigin_not_in_strip T huin.1
    have hune1 : u ≠ hexNeighbors3 paperStart 1 := by
      rintro rfl
      exact hfresh (by rw [Sym2.eq_swap]; exact List.mem_cons_self ..)
    rcases hexNeighbors3_complete paperStart u hadj with h | h | h
    · exact absurd h hune0
    · exact absurd h hune1
    · exact h
  subst hu2
  have hps : paperStart ∉ p'.support := by
    intro hmem
    have h1 : vEdgeCount paperStart γ.walk = 1 :=
      freshTrail_vEdgeCount_start γ (Ne.symm paperStart_ne_one)
    have hsplit : vEdgeCount paperStart γ.walk = vEdgeCount paperStart p' + 1 := by
      rw [hp']; simp [vEdgeCount]
    have hpos : 0 < vEdgeCount paperStart p' :=
      vEdgeCount_pos_of_mem_support_ne_start p' paperStart hmem paperStart_ne_two
    omega
  refine ⟨⟨p', htrail.1, hps, fun u hu => hstrip u (by
    rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hu)⟩, ?_⟩
  exact FreshTrail.ext' (by rw [hp']; rfl)

lemma toP2_surjective (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    Function.Surjective (toP2 T L hT hL) := by
  intro γ
  obtain ⟨u, hadj, p', hp'⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne paperStart_ne_two γ.walk
  have hfresh := γ.fresh
  rw [hp', SimpleGraph.Walk.edges_cons] at hfresh
  have htrail := γ.is_trail
  rw [hp', SimpleGraph.Walk.isTrail_cons] at htrail
  have hstrip := γ.in_strip
  rw [hp'] at hstrip
  have hu1 : u = hexNeighbors3 paperStart 1 := by
    have huin : PaperFinStrip T L u := by
      refine hstrip u ?_
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ p'.start_mem_support
    have hune0 : u ≠ hexOrigin := by
      rintro rfl; exact hexOrigin_not_in_strip T huin.1
    have hune2 : u ≠ hexNeighbors3 paperStart 2 := by
      rintro rfl
      exact hfresh (by rw [Sym2.eq_swap]; exact List.mem_cons_self ..)
    rcases hexNeighbors3_complete paperStart u hadj with h | h | h
    · exact absurd h hune0
    · exact h
    · exact absurd h hune2
  subst hu1
  have hps : paperStart ∉ p'.support := by
    intro hmem
    have h1 : vEdgeCount paperStart γ.walk = 1 :=
      freshTrail_vEdgeCount_start γ (Ne.symm paperStart_ne_two)
    have hsplit : vEdgeCount paperStart γ.walk = vEdgeCount paperStart p' + 1 := by
      rw [hp']; simp [vEdgeCount]
    have hpos : 0 < vEdgeCount paperStart p' :=
      vEdgeCount_pos_of_mem_support_ne_start p' paperStart hmem paperStart_ne_one
    omega
  refine ⟨⟨p'.reverse, htrail.1.reverse, ?_, ?_⟩, ?_⟩
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]; exact hps
  · intro u hu
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hu
    exact hstrip u (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hu)
  · refine FreshTrail.ext' ?_
    show SimpleGraph.Walk.cons _ p'.reverse.reverse = γ.walk
    rw [SimpleGraph.Walk.reverse_reverse, hp']

lemma toP1_injective (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    Function.Injective (toP1 T L hT hL) := by
  intro q q' h
  have hw : (toP1 T L hT hL q).walk = (toP1 T L hT hL q').walk := by rw [h]
  refine Subtype.ext ?_
  simpa [toP1] using hw

lemma toP2_injective (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    Function.Injective (toP2 T L hT hL) := by
  intro q q' h
  have hw : (toP2 T L hT hL q).walk = (toP2 T L hT hL q').walk := by rw [h]
  have : q.1.reverse = q'.1.reverse := by simpa [toP2] using hw
  exact Subtype.ext (by simpa using congrArg SimpleGraph.Walk.reverse this)

/-- The configurations at the mid-edge `(n₁, paperStart)` are the inner trails. -/
def equivP1 (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    innerC T L ≃ FreshTrail T L (hexNeighbors3 paperStart 1) paperStart :=
  Equiv.ofBijective _ ⟨toP1_injective T L hT hL, toP1_surjective T L hT hL⟩

/-- The configurations at the mid-edge `(n₂, paperStart)` are the inner trails,
run backwards. -/
def equivP2 (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    innerC T L ≃ FreshTrail T L (hexNeighbors3 paperStart 2) paperStart :=
  Equiv.ofBijective _ ⟨toP2_injective T L hT hL, toP2_surjective T L hT hL⟩

/-! ### The winding of the paired configurations

The two configurations of a pair traverse the same simple loop through
`paperStart` in opposite directions.  By the Umlaufsatz that loop, which leaves
`hexOrigin` outside, is traversed clockwise in the first case and
counter-clockwise in the second, so the total turnings are `-4π/3` and `4π/3`.
(The value modulo `2π` is already given by `freshTrail_winding_angle`; what the
orientation argument supplies is the choice of representative.) -/

/-- **Geometric input.**  A configuration at the mid-edge `(n₁, paperStart)`
turns by `-4π/3`. -/
lemma paperStart_inner_winding_one (T L : ℕ)
    (γ : FreshTrail T L (hexNeighbors3 paperStart 1) paperStart) :
    γ.winding = -(4 * Real.pi / 3) := by
  sorry

/-- **Geometric input.**  A configuration at the mid-edge `(n₂, paperStart)`
turns by `4π/3`. -/
lemma paperStart_inner_winding_two (T L : ℕ)
    (γ : FreshTrail T L (hexNeighbors3 paperStart 2) paperStart) :
    γ.winding = 4 * Real.pi / 3 := by
  sorry

/-- The two members of a pair contribute opposite (purely imaginary) terms. -/
lemma paperStart_pair_term_zero (l : ℕ) :
    midEdgeDir paperStart 1 * walkWeight (-(4 * Real.pi / 3)) l xc sigma
      + midEdgeDir paperStart 2 * walkWeight (4 * Real.pi / 3) l xc sigma = 0 := by
  rw [midEdgeDir_paperStart_one, midEdgeDir_paperStart_two, ← Complex.exp_mul_I,
    ← Complex.exp_mul_I]
  unfold walkWeight
  have h1 : Complex.exp (((-(Real.pi / 3) : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (-Complex.I * (sigma : ℂ) * ((-(4 * Real.pi / 3) : ℝ) : ℂ))
            * (xc : ℂ) ^ l)
      = Complex.I * (xc : ℂ) ^ l := by
    rw [← mul_assoc, ← Complex.exp_add,
      show ((-(Real.pi / 3) : ℝ) : ℂ) * Complex.I
          + -Complex.I * (sigma : ℂ) * ((-(4 * Real.pi / 3) : ℝ) : ℂ)
        = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast [sigma]; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp
  have h2 : Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (-Complex.I * (sigma : ℂ) * ((4 * Real.pi / 3 : ℝ) : ℂ))
            * (xc : ℂ) ^ l)
      = -Complex.I * (xc : ℂ) ^ l := by
    rw [← mul_assoc, ← Complex.exp_add,
      show ((Real.pi / 3 : ℝ) : ℂ) * Complex.I
          + -Complex.I * (sigma : ℂ) * ((4 * Real.pi / 3 : ℝ) : ℂ)
        = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I by push_cast [sigma]; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp
  rw [h1, h2]
  ring

lemma toP1_weight (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (q : innerC T L) :
    (toP1 T L hT hL q).weight
      = walkWeight (-(4 * Real.pi / 3)) (q.1.length + 2) xc sigma := by
  rw [FreshTrail.weight, paperStart_inner_winding_one, toP1_len]

lemma toP2_weight (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (q : innerC T L) :
    (toP2 T L hT hL q).weight
      = walkWeight (4 * Real.pi / 3) (q.1.length + 2) xc sigma := by
  rw [FreshTrail.weight, paperStart_inner_winding_two, toP2_len]

/-! ## The pair cancellation at the starting vertex -/

/-- **The pair involution at `paperStart`.**  A configuration ending at the
mid-edge `(nᵢ, paperStart)` (`i = 1, 2`) leaves `paperStart` through the other
inner edge; reversing it and re-attaching `paperStart` through `nᵢ` produces a
configuration ending at the mid-edge `(nⱼ, paperStart)` of the same length, and
the two contributions cancel.

This is the exact analogue at `paperStart` of the pair part of Lemma 1
(`freshVertexSum_pair_part_zero_proved`), whose proof requires the same
turning-number input; it is the one remaining ingredient of the starting-vertex
computation. -/
lemma paperStart_pair_cancel (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    midEdgeDir paperStart 1 * freshObs T L (hexNeighbors3 paperStart 1) paperStart
      + midEdgeDir paperStart 2 * freshObs T L (hexNeighbors3 paperStart 2) paperStart
      = 0 := by
  rw [freshObs, freshObs, tsum_mul_left.symm, tsum_mul_left.symm,
    ← (equivP1 T L hT hL).tsum_eq (fun p => midEdgeDir paperStart 1 * p.weight),
    ← (equivP2 T L hT hL).tsum_eq (fun p => midEdgeDir paperStart 2 * p.weight)]
  simp only [equivP1, equivP2, Equiv.ofBijective_apply]
  have hkey : ∀ q : innerC T L,
      midEdgeDir paperStart 1 * (toP1 T L hT hL q).weight
        = -(midEdgeDir paperStart 2 * (toP2 T L hT hL q).weight) := by
    intro q
    have := paperStart_pair_term_zero (q.1.length + 2)
    rw [toP1_weight, toP2_weight]
    linear_combination this
  rw [tsum_congr (fun q => hkey q), tsum_neg]
  ring

/-! ## The defect of the vertex relation at `paperStart` -/

lemma freshObs_hexOrigin_paperStart (T L : ℕ) :
    freshObs T L (hexNeighbors3 paperStart 0) paperStart = 0 := by
  rw [hexNbr_paperStart_zero]
  exact freshObs_eq_zero_of_not_strip T L hexOrigin paperStart
    (fun h => hexOrigin_not_in_strip T h.1)

/-- **The defect of the vertex relation at the starting vertex.**  Adding the
observable on the mid-edge `a` restores the normalisation `F(a) = 1` of
Duminil-Copin & Smirnov. -/
theorem paperStart_vertex_defect (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    freshVertexSum T L paperStart + freshObs T L paperStart hexOrigin = 1 := by
  rw [freshVertexSum, Fin.sum_univ_three]
  rw [freshObs_hexOrigin_paperStart T L, midEdgeDir_paperStart_zero,
    freshObs_paperStart_side T L hT hL (k := 1) (by decide),
    freshObs_paperStart_side T L hT hL (k := 2) (by decide)]
  have hpair := paperStart_pair_cancel T L hT hL
  have htrip := paperStart_nil_triplet
  rw [hexNbr_paperStart_zero]
  linear_combination hpair + htrip

/-! ## The starting mid-edge and the strip identity -/

/-- **Starting mid-edge — the normalisation `F(a) = 1` of the paper.**

In Duminil-Copin & Smirnov the walk starts at the boundary mid-edge `a` and the
empty walk `a → a` contributes `1` to `F(a)`.  In the present formalisation a
walk always starts at the *vertex* `paperStart`, so this empty configuration is
absent while the degenerate configuration stepping straight back out along `a`
is present; `paperStart_vertex_defect` shows that the two discrepancies combine
into the paper's normalisation. -/
lemma bdry_start_eval (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (∑ p ∈ (bdryPairs T L).filter IsStartPair, bdryTerm T L p).re
      = (freshVertexSum T L paperStart).re - 1 := by
  rw [bdry_start_sum T L hT hL]
  have h := congrArg Complex.re (paperStart_vertex_defect T L hT hL)
  simp only [Complex.add_re, Complex.one_re, Complex.neg_re] at h ⊢
  linarith

/-- **Lemma 2** (strip identity), in the form actually delivered by the boundary
evaluation: the escape contribution is only known to be non-negative, since the
family of escape mid-edges is not in bijection with the walks counted by
`E_paper` (a walk can leave the strip through more than one mid-edge at a
corner). -/
theorem strip_identity_nonneg_rest (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ Erest : ℝ, 0 ≤ Erest ∧
      1 = c_alpha * A_paper T L xc + B_paper T L xc + Erest := by
  refine ⟨(∑ p ∈ (bdryPairs T L).filter (IsEPair T), bdryTerm T L p).re,
    bdry_E_re_nonneg T L, ?_⟩
  have h := congrArg Complex.re (bdry_split T L)
  rw [stripSum_eq_bdrySum T L hT hL] at h
  simp only [Complex.add_re] at h
  rw [bdry_start_eval T L hT hL, bdry_A_eval T L, bdry_B_eval T L] at h
  simp only [Complex.ofReal_re] at h
  linarith

end
