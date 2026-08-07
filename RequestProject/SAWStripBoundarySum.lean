/-
# The strip boundary sum

Applies the discrete Stokes cancellation of `SAWStokesSum.lean` to the concrete
domain `PaperFinStrip T L`, and organises the resulting boundary sum into the
four families of boundary mid-edges of Duminil-Copin & Smirnov 2012:

* the **starting** mid-edge `a` at `paperStart`;
* the **left boundary** `α`  (TRUE vertices with `x + y = 0`);
* the **right boundary** `β` (FALSE vertices with `x + y = -T`);
* the **escape boundary** `ε` (everything else leaving the strip).

## What is proved here

* `freshObs_eq_zero_of_not_strip` — the observable vanishes on a mid-edge whose
  *first* endpoint is outside the strip (no walk can even reach it);
* `stripSum_eq_bdrySum` — the discrete Stokes identity for the strip:
  `freshVertexSum T L paperStart = ∑ boundary mid-edges`;
* `bdry_split` — the boundary sum splits as `start + α + β + ε`.

## The boundary evaluation (Step 3 of the paper)

The three families of boundary mid-edges that do not contain the starting
mid-edge are evaluated here: `bdry_A_eval`, `bdry_B_eval` and
`bdry_E_re_nonneg`.  All three are proved, resting only on the single geometric
input `freshTrail_boundary_winding_bound` of `SAWBoundaryWindingBound.lean`.
The starting mid-edge is treated in `SAWStartVertex.lean`.
-/

import Mathlib
import RequestProject.SAWStokesSum
import RequestProject.SAWPairInvolutionProof
import RequestProject.SAWFreshTrailPath
import RequestProject.SAWFreshWindingAngle
import RequestProject.SAWBoundaryWindingBound

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## The strip as a finset -/

/-- The vertices of the finite strip, as a `Finset`. -/
def paperStripFinset (T L : ℕ) : Finset HexVertex := (paper_fin_strip_finite' T L).toFinset

lemma mem_paperStripFinset {T L : ℕ} {v : HexVertex} :
    v ∈ paperStripFinset T L ↔ PaperFinStrip T L v := by
  simp [paperStripFinset]

lemma paperStart_mem_paperStripFinset {T L : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) :
    paperStart ∈ paperStripFinset T L :=
  mem_paperStripFinset.2 (paperStart_in_fin_strip T L hT hL)

/-! ## The observable vanishes outside the strip -/

/-- If `w` is not in the strip there is no fresh trail ending at `w`, hence the
observable on the oriented mid-edge `(w, v)` vanishes. -/
lemma freshObs_eq_zero_of_not_strip (T L : ℕ) (w v : HexVertex)
    (hw : ¬ PaperFinStrip T L w) : freshObs T L w v = 0 := by
  have : IsEmpty (FreshTrail T L w v) := by
    constructor
    intro γ
    exact hw (γ.in_strip w γ.walk.end_mem_support)
  simp [freshObs, tsum_empty]

/-! ## The boundary sum -/

/-- The oriented mid-edges leaving the strip. -/
def bdryPairs (T L : ℕ) : Finset (HexVertex × HexVertex) :=
  (paperStripFinset T L).biUnion fun v => (nbrFinset v \ paperStripFinset T L).image (Prod.mk v)

lemma mem_bdryPairs {T L : ℕ} {p : HexVertex × HexVertex} :
    p ∈ bdryPairs T L ↔
      PaperFinStrip T L p.1 ∧ hexGraph.Adj p.1 p.2 ∧ ¬ PaperFinStrip T L p.2 := by
  obtain ⟨v, w⟩ := p
  simp only [bdryPairs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨u, hu, x, ⟨hx1, hx2⟩, rfl, rfl⟩
    exact ⟨mem_paperStripFinset.1 hu, (mem_nbrFinset_iff _ _).1 hx1,
      fun h => hx2 (mem_paperStripFinset.2 h)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨v, mem_paperStripFinset.2 h1,
      w, ⟨(mem_nbrFinset_iff _ _).2 h2, fun h => h3 (mem_paperStripFinset.1 h)⟩, rfl, rfl⟩

/-- The contribution of a boundary mid-edge. -/
def bdryTerm (T L : ℕ) (p : HexVertex × HexVertex) : ℂ :=
  midDir p.1 p.2 * freshObs T L p.1 p.2

/-- On a boundary mid-edge the symmetric observable reduces to a single term. -/
lemma stokesTerm_eq_bdryTerm (T L : ℕ) (v w : HexVertex)
    (hw : ¬ PaperFinStrip T L w) : stokesTerm T L v w = bdryTerm T L (v, w) := by
  simp [stokesTerm, bdryTerm, freshSym, freshObs_eq_zero_of_not_strip T L w v hw]

/-- The boundary sum, written as an iterated sum. -/
lemma bdrySum_eq_double (T L : ℕ) :
    ∑ p ∈ bdryPairs T L, bdryTerm T L p
      = ∑ v ∈ paperStripFinset T L, ∑ w ∈ nbrFinset v \ paperStripFinset T L, stokesTerm T L v w := by
  rw [bdryPairs, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.sum_image (by intro a _ b _ h; exact (Prod.mk.injEq .. ▸ h).2)]
    refine Finset.sum_congr rfl fun w hw => ?_
    exact (stokesTerm_eq_bdryTerm T L v w
      (fun h => (Finset.mem_sdiff.1 hw).2 (mem_paperStripFinset.2 h))).symm
  · intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_image]
    rintro p ⟨x, _, rfl⟩ ⟨y, _, hy⟩
    exact hab (congrArg Prod.fst hy).symm

/-- **Discrete Stokes for the strip.**  The whole boundary sum equals the
vertex sum at `paperStart`: every other strip vertex satisfies the vertex
relation. -/
theorem stripSum_eq_bdrySum (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∑ p ∈ bdryPairs T L, bdryTerm T L p = freshVertexSum T L paperStart := by
  rw [bdrySum_eq_double, ← stokes_boundary_sum]
  refine Finset.sum_eq_single_of_mem paperStart (paperStart_mem_paperStripFinset hT hL) ?_
  intro v hv hne
  exact fresh_vertex_relation T L v (mem_paperStripFinset.1 hv) hne

/-! ## Classification of boundary mid-edges -/

/-- The starting mid-edge `a`: the one leaving the strip at `paperStart`. -/
def IsStartPair (p : HexVertex × HexVertex) : Prop := p.1 = paperStart

/-- Left boundary (`α`) mid-edges: from a TRUE vertex on the diagonal `x+y = 0`
(other than `paperStart`) to the FALSE vertex with the same coordinates. -/
def IsAPair (p : HexVertex × HexVertex) : Prop :=
  p.1 ≠ paperStart ∧ p.1.2.2 = true ∧ p.1.1 + p.1.2.1 = 0 ∧
    p.2 = (p.1.1, p.1.2.1, false)

/-- Right boundary (`β`) mid-edges: from a FALSE vertex on the diagonal
`x+y = -T` to the TRUE vertex with the same coordinates. -/
def IsBPair (T : ℕ) (p : HexVertex × HexVertex) : Prop :=
  p.1.2.2 = false ∧ p.1.1 + p.1.2.1 = -(T : ℤ) ∧ p.2 = (p.1.1, p.1.2.1, true)

/-- Escape (`ε`) mid-edges: all remaining boundary mid-edges. -/
def IsEPair (T : ℕ) (p : HexVertex × HexVertex) : Prop :=
  ¬ IsStartPair p ∧ ¬ IsAPair p ∧ ¬ IsBPair T p

instance : DecidablePred IsStartPair := fun _ => by unfold IsStartPair; infer_instance
instance : DecidablePred IsAPair := fun _ => by unfold IsAPair; infer_instance
instance (T : ℕ) : DecidablePred (IsBPair T) := fun _ => by unfold IsBPair; infer_instance
instance (T : ℕ) : DecidablePred (IsEPair T) := fun _ => by unfold IsEPair; infer_instance

lemma not_isAPair_of_isStartPair {p : HexVertex × HexVertex} (h : IsStartPair p) :
    ¬ IsAPair p := fun ha => ha.1 h

lemma not_isBPair_of_isStartPair {T : ℕ} {p : HexVertex × HexVertex}
    (h : IsStartPair p) : ¬ IsBPair T p := by
  intro hb
  obtain ⟨hb1, -, -⟩ := hb
  rw [h] at hb1
  exact absurd hb1 (by simp [paperStart])

lemma not_isBPair_of_isAPair {T : ℕ} {p : HexVertex × HexVertex} (h : IsAPair p) :
    ¬ IsBPair T p := by
  intro hb
  obtain ⟨hb1, -, -⟩ := hb
  rw [h.2.1] at hb1
  exact absurd hb1 (by simp)

/-- The four families partition the boundary mid-edges. -/
lemma bdry_split (T L : ℕ) :
    ∑ p ∈ bdryPairs T L, bdryTerm T L p
      = (∑ p ∈ (bdryPairs T L).filter IsStartPair, bdryTerm T L p)
        + (∑ p ∈ (bdryPairs T L).filter IsAPair, bdryTerm T L p)
        + (∑ p ∈ (bdryPairs T L).filter (IsBPair T), bdryTerm T L p)
        + (∑ p ∈ (bdryPairs T L).filter (IsEPair T), bdryTerm T L p) := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hS : IsStartPair p
  · rw [if_pos hS, if_neg (not_isAPair_of_isStartPair hS),
      if_neg (not_isBPair_of_isStartPair hS),
      if_neg (fun h : IsEPair T p => h.1 hS)]
    ring
  · by_cases hA : IsAPair p
    · rw [if_neg hS, if_pos hA, if_neg (not_isBPair_of_isAPair hA),
        if_neg (fun h : IsEPair T p => h.2.1 hA)]
      ring
    · by_cases hB : IsBPair T p
      · rw [if_neg hS, if_neg hA, if_pos hB, if_neg (fun h : IsEPair T p => h.2.2 hB)]
        ring
      · rw [if_neg hS, if_neg hA, if_neg hB, if_pos ⟨hS, hA, hB⟩]
        ring

/-! ## Boundary evaluation — the remaining analytic input

Each of the following four lemmas concerns exactly one family of boundary
mid-edges.  Together with `stripSum_eq_bdrySum` and `bdry_split` they give the
strip identity.  They are the formal content of Step 3 ("boundary evaluation")
of the proof of Lemma 2 in Duminil-Copin & Smirnov 2012, and rely on the fact
that the winding of a hexagonal walk telescopes to the direction angle of its
final mid-edge. -/

/-! ### The two straight boundaries

The `α` and `β` families are in bijection with the strip vertices lying on the
left resp. right diagonal, each contributing a single mid-edge. -/

/-- The strip vertices on the left boundary diagonal (excluding `paperStart`). -/
def alphaVerts (T L : ℕ) : Finset HexVertex :=
  (paperStripFinset T L).filter
    (fun v => v ≠ paperStart ∧ v.2.2 = true ∧ v.1 + v.2.1 = 0)

/-- The strip vertices on the right boundary diagonal. -/
def betaVerts (T L : ℕ) : Finset HexVertex :=
  (paperStripFinset T L).filter (fun v => v.2.2 = false ∧ v.1 + v.2.1 = -(T : ℤ))

/-- The `0`-th neighbour of a TRUE vertex on the diagonal `x + y = 0` lies
outside the strip. -/
lemma alphaPair_out (T L : ℕ) (x y : ℤ) (h : x + y = 0) :
    ¬ PaperFinStrip T L ((x, y, false) : HexVertex) := by
  rintro ⟨hinf, -⟩
  simp only [PaperInfStrip] at hinf
  simp at hinf
  omega

/-- The `0`-th neighbour of a FALSE vertex on the diagonal `x + y = -T` lies
outside the strip. -/
lemma betaPair_out (T L : ℕ) (x y : ℤ) (h : x + y = -(T : ℤ)) :
    ¬ PaperFinStrip T L ((x, y, true) : HexVertex) := by
  rintro ⟨hinf, -⟩
  simp only [PaperInfStrip] at hinf
  simp at hinf
  omega

lemma APairs_eq (T L : ℕ) :
    (bdryPairs T L).filter IsAPair
      = (alphaVerts T L).image (fun v => (v, ((v.1, v.2.1, false) : HexVertex))) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_image, alphaVerts]
  constructor
  · rintro ⟨hp, hne, hb, hd, h2⟩
    rw [mem_bdryPairs] at hp
    exact ⟨p.1, ⟨mem_paperStripFinset.2 hp.1, hne, hb, hd⟩, by
      rw [← h2]⟩
  · rintro ⟨v, ⟨hv, hne, hb, hd⟩, rfl⟩
    obtain ⟨x, y, b⟩ := v
    simp only at hb hd
    subst hb
    refine ⟨mem_bdryPairs.2 ⟨mem_paperStripFinset.1 hv, ?_, alphaPair_out T L x y hd⟩,
      hne, rfl, hd, rfl⟩
    exact hexNeighbors3_adj (x, y, true) 0

lemma BPairs_eq (T L : ℕ) :
    (bdryPairs T L).filter (IsBPair T)
      = (betaVerts T L).image (fun v => (v, ((v.1, v.2.1, true) : HexVertex))) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_image, betaVerts]
  constructor
  · rintro ⟨hp, hb, hd, h2⟩
    rw [mem_bdryPairs] at hp
    exact ⟨p.1, ⟨mem_paperStripFinset.2 hp.1, hb, hd⟩, by rw [← h2]⟩
  · rintro ⟨v, ⟨hv, hb, hd⟩, rfl⟩
    obtain ⟨x, y, b⟩ := v
    simp only at hb hd
    subst hb
    refine ⟨mem_bdryPairs.2 ⟨mem_paperStripFinset.1 hv, ?_, betaPair_out T L x y hd⟩,
      rfl, hd, rfl⟩
    exact hexNeighbors3_adj (x, y, false) 0

/-- The `α` contribution is `-∑ F` over the left boundary vertices. -/
lemma bdry_A_sum (T L : ℕ) :
    ∑ p ∈ (bdryPairs T L).filter IsAPair, bdryTerm T L p
      = -∑ v ∈ alphaVerts T L, freshObs T L v (v.1, v.2.1, false) := by
  rw [APairs_eq, Finset.sum_image (by intro a _ b _ h; exact (Prod.mk.injEq .. ▸ h).1),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨x, y, b⟩ := v
  have hb : b = true := by
    simp only [alphaVerts, Finset.mem_filter] at hv
    exact hv.2.2.1
  subst hb
  simp [bdryTerm, midDir, true_dir1]

/-- The `β` contribution is `∑ F` over the right boundary vertices. -/
lemma bdry_B_sum (T L : ℕ) :
    ∑ p ∈ (bdryPairs T L).filter (IsBPair T), bdryTerm T L p
      = ∑ v ∈ betaVerts T L, freshObs T L v (v.1, v.2.1, true) := by
  rw [BPairs_eq, Finset.sum_image (by intro a _ b _ h; exact (Prod.mk.injEq .. ▸ h).1)]
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨x, y, b⟩ := v
  have hb : b = false := by
    simp only [betaVerts, Finset.mem_filter] at hv
    exact hv.2.1
  subst hb
  simp [bdryTerm, midDir, false_to_true_dir]

/-- The real part of a walk weight. -/
lemma walkWeight_re (W : ℝ) (len : ℕ) (x s : ℝ) :
    (walkWeight W len x s).re = Real.cos (s * W) * x ^ len := by
  unfold walkWeight
  rw [show (-Complex.I * (s : ℂ) * (W : ℂ)) = ((-(s * W) : ℝ) : ℂ) * Complex.I by
      push_cast; ring, ← Complex.ofReal_pow, Complex.mul_re]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, Real.cos_neg]
  ring

/-! ### The left boundary: fresh trails there are exactly the `A` walks -/

/-- A `true` vertex is adjacent to the `false` vertex with the same coordinates. -/
lemma true_to_false_adj (v : HexVertex) (hv : v.2.2 = true) :
    hexGraph.Adj v (v.1, v.2.1, false) :=
  Or.inr ⟨hv, rfl, Or.inl ⟨rfl, rfl⟩⟩

lemma alphaVerts_true {T L : ℕ} {v : HexVertex} (h : v ∈ alphaVerts T L) :
    v.2.2 = true := by
  simp only [alphaVerts, Finset.mem_filter] at h; exact h.2.2.1

lemma alphaVerts_diag {T L : ℕ} {v : HexVertex} (h : v ∈ alphaVerts T L) :
    v.1 + v.2.1 = 0 := by
  simp only [alphaVerts, Finset.mem_filter] at h; exact h.2.2.2

lemma alphaVerts_ne_paperStart {T L : ℕ} {v : HexVertex} (h : v ∈ alphaVerts T L) :
    v ≠ paperStart := by
  simp only [alphaVerts, Finset.mem_filter] at h; exact h.2.1

/-- `PaperSAW_A T L` is a finite type. -/
instance paperSAW_A_finite (T L : ℕ) : Finite (PaperSAW_A T L) := by
  have hN : ∀ s : PaperSAW_A T L,
      s.len ≤ (paper_fin_strip_finite' T L).toFinset.card :=
    fun s => paper_saw_length_bound' T L s.len s.saw s.in_strip
  exact Finite.of_injective
    (fun s : PaperSAW_A T L => (⟨⟨s.len,
      Nat.lt_add_one_iff.mpr (hN s)⟩, s.saw⟩ :
      Σ n : Fin ((paper_fin_strip_finite' T L).toFinset.card + 1),
        SAW paperStart n))
    (fun s t h => by cases s; cases t; aesop)

/-- The fresh trails ending on a left-boundary mid-edge, as a single type. -/
def alphaSigma (T L : ℕ) : Type :=
  Σ v : {v : HexVertex // v ∈ alphaVerts T L},
    FreshTrail T L v.1 (v.1.1, v.1.2.1, false)

instance alphaSigma_finite (T L : ℕ) : Finite (alphaSigma T L) := by
  unfold alphaSigma; infer_instance

/-- A fresh trail on an `α` mid-edge is an `A`-walk. -/
def alphaToSAW (T L : ℕ) (p : alphaSigma T L) : PaperSAW_A T L where
  len := p.2.walk.length
  saw := p.2.toSAW (alphaVerts_ne_paperStart p.1.2)
  end_left := ⟨alphaVerts_diag p.1.2, alphaVerts_true p.1.2,
    alphaVerts_ne_paperStart p.1.2⟩
  in_strip := p.2.in_strip

/-- An `A`-walk is a fresh trail on an `α` mid-edge. -/
def sawToAlpha (T L : ℕ) (s : PaperSAW_A T L) : alphaSigma T L :=
  ⟨⟨s.saw.w, by
      simp only [alphaVerts, Finset.mem_filter]
      exact ⟨mem_paperStripFinset.2 (s.in_strip _ s.saw.p.1.end_mem_support),
        s.end_left.2.2, s.end_left.2.1, s.end_left.1⟩⟩,
    { walk := s.saw.p.1
      is_trail := s.saw.p.2.isTrail
      adj := true_to_false_adj _ s.end_left.2.1
      fresh := by
        intro hmem
        exact alphaPair_out T L s.saw.w.1 s.saw.w.2.1 s.end_left.1
          (s.in_strip _ (s.saw.p.1.snd_mem_support_of_mem_edges hmem))
      in_strip := s.in_strip }⟩

/-- **The left-boundary bijection.** -/
def alphaEquiv (T L : ℕ) : alphaSigma T L ≃ PaperSAW_A T L where
  toFun := alphaToSAW T L
  invFun := sawToAlpha T L
  left_inv := by rintro ⟨⟨v, hv⟩, γ⟩; rfl
  right_inv := by rintro ⟨n, ⟨w, p, rfl⟩, h1, h2⟩; rfl

/-- The direction of an `α` mid-edge is `-1`, of angle `π`. -/
lemma alpha_lastDir_arg {v : HexVertex} (hv : v.2.2 = true) :
    Complex.arg (correctHexEmbed ((v.1, v.2.1, false) : HexVertex)
      - correctHexEmbed v) = Real.pi := by
  obtain ⟨x, y, b⟩ := v
  simp only at hv
  subst hv
  simp [correctHexEmbed, Complex.ext_iff, Complex.arg]

/-- The direction of a `β` mid-edge is `+1`, of angle `0`. -/
lemma beta_lastDir_arg {v : HexVertex} (hv : v.2.2 = false) :
    Complex.arg (correctHexEmbed ((v.1, v.2.1, true) : HexVertex)
      - correctHexEmbed v) = 0 := by
  obtain ⟨x, y, b⟩ := v
  simp only at hv
  subst hv
  simp [correctHexEmbed, Complex.ext_iff, Complex.arg]

/-- **The topological input for the left boundary.**  A configuration ending on
the left boundary of the strip makes no extra full turn.  This is where the
self-avoidance of the walk and the simple connectivity of the strip enter: the
winding modulo `2π` is already pinned by `freshTrail_winding_angle`. -/
lemma alphaTrail_winding_bound (T L : ℕ) (p : alphaSigma T L) :
    |p.2.winding| ≤ Real.pi :=
  freshTrail_boundary_winding_bound p.2 (alphaPair_out T L _ _ (alphaVerts_diag p.1.2))

/-- **The winding of a left-boundary walk is `±π`.**

The initial mid-edge `a` points to the right and the final mid-edge points to
the left, so a configuration joining them turns by exactly half a revolution,
in one direction or the other. -/
lemma alphaTrail_winding (T L : ℕ) (p : alphaSigma T L) :
    p.2.winding = Real.pi ∨ p.2.winding = -Real.pi := by
  have hangle : ((p.2.winding : Real.Angle)) = ((Real.pi : ℝ) : Real.Angle) := by
    rw [freshTrail_winding_angle p.2, alpha_lastDir_arg (alphaVerts_true p.1.2)]
  obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hangle
  have hb := alphaTrail_winding_bound T L p
  have hpi := Real.pi_pos
  rw [abs_le] at hb
  have hn0 : n = 0 ∨ n = -1 := by
    rcases lt_trichotomy n 0 with h | h | h
    · right
      by_contra hne
      have : (n : ℝ) ≤ -2 := by exact_mod_cast (by omega : n ≤ -2)
      nlinarith [hb.1]
    · left; exact h
    · left
      by_contra hne
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      nlinarith [hb.2]
  rcases hn0 with rfl | rfl
  · left; push_cast at hn; linarith
  · right; push_cast at hn; linarith

lemma alphaTrail_weight_re (T L : ℕ) (p : alphaSigma T L) :
    p.2.weight.re = -c_alpha * xc ^ ((alphaToSAW T L p).len + 1) := by
  have hlen : p.2.len = (alphaToSAW T L p).len + 1 := rfl
  have hcos : Real.cos (sigma * p.2.winding) = -c_alpha := by
    rcases alphaTrail_winding T L p with h | h <;> rw [h]
    · rw [show sigma * Real.pi = 5 * Real.pi / 8 by unfold sigma; ring]
      exact cos_five_pi_eight
    · rw [show sigma * -Real.pi = -(5 * Real.pi / 8) by unfold sigma; ring,
        Real.cos_neg]
      exact cos_five_pi_eight
  rw [FreshTrail.weight, walkWeight_re, hcos, hlen]

/-- The left-boundary sum, as a sum over `alphaSigma`. -/
lemma bdry_A_sum_sigma (T L : ℕ) :
    ∑ v ∈ alphaVerts T L, freshObs T L v (v.1, v.2.1, false)
      = ∑' (p : alphaSigma T L), p.2.weight := by
  rw [← Finset.tsum_subtype (alphaVerts T L)
    (fun v => freshObs T L v (v.1, v.2.1, false))]
  exact (Summable.tsum_sigma (f := fun p : alphaSigma T L => p.2.weight)
    Summable.of_finite).symm

/-- **Left boundary.**  On an `α` mid-edge the direction is `-1` and the winding
is `±π`, so the real part of the contribution is `cos(3π/8) = c_α` times the
generating function `A_paper`. -/
lemma bdry_A_eval (T L : ℕ) :
    (∑ p ∈ (bdryPairs T L).filter IsAPair, bdryTerm T L p).re
      = c_alpha * A_paper T L xc := by
  rw [bdry_A_sum, bdry_A_sum_sigma, Complex.neg_re]
  have h1 : (∑' (p : alphaSigma T L), p.2.weight).re
      = ∑' (s : PaperSAW_A T L), -c_alpha * xc ^ (s.len + 1) := by
    rw [← Complex.reCLM_apply, (Summable.of_finite).hasSum.mapL Complex.reCLM |>.tsum_eq.symm]
    simp only [Complex.reCLM_apply]
    rw [← (alphaEquiv T L).tsum_eq (fun s => -c_alpha * xc ^ (s.len + 1))]
    exact tsum_congr fun p => alphaTrail_weight_re T L p
  rw [h1, tsum_mul_left, A_paper]
  ring

/-! ### The right boundary: fresh trails there are exactly the `B` walks

`freshTrail_isPath` says that a fresh trail ending at a vertex other than
`paperStart` is a self-avoiding walk.  On the right boundary this gives an
explicit bijection `betaEquiv` between the fresh trails ending on a `β`
mid-edge and the walks counted by `B_paper`. -/

/-- A `false` vertex is adjacent to the `true` vertex with the same coordinates. -/
lemma false_to_true_adj (v : HexVertex) (hv : v.2.2 = false) :
    hexGraph.Adj v (v.1, v.2.1, true) :=
  Or.inl ⟨hv, rfl, Or.inl ⟨rfl, rfl⟩⟩

lemma betaVerts_false {T L : ℕ} {v : HexVertex} (h : v ∈ betaVerts T L) :
    v.2.2 = false := by
  simp only [betaVerts, Finset.mem_filter] at h; exact h.2.1

lemma betaVerts_diag {T L : ℕ} {v : HexVertex} (h : v ∈ betaVerts T L) :
    v.1 + v.2.1 = -(T : ℤ) := by
  simp only [betaVerts, Finset.mem_filter] at h; exact h.2.2

lemma betaVerts_ne_paperStart {T L : ℕ} {v : HexVertex} (h : v ∈ betaVerts T L) :
    v ≠ paperStart := by
  intro hv
  have hf := betaVerts_false h
  rw [hv] at hf
  exact absurd hf (by simp [paperStart])

/-- The fresh trails ending on a right-boundary mid-edge, as a single type. -/
def betaSigma (T L : ℕ) : Type :=
  Σ v : {v : HexVertex // v ∈ betaVerts T L},
    FreshTrail T L v.1 (v.1.1, v.1.2.1, true)

instance betaSigma_finite (T L : ℕ) : Finite (betaSigma T L) := by
  unfold betaSigma; infer_instance

/-- A fresh trail on a `β` mid-edge is a `B`-walk. -/
def betaToSAW (T L : ℕ) (p : betaSigma T L) : PaperSAW_B T L where
  len := p.2.walk.length
  saw := p.2.toSAW (betaVerts_ne_paperStart p.1.2)
  end_right := ⟨betaVerts_diag p.1.2, betaVerts_false p.1.2⟩
  in_strip := p.2.in_strip

/-- A `B`-walk is a fresh trail on a `β` mid-edge. -/
def sawToBeta (T L : ℕ) (s : PaperSAW_B T L) : betaSigma T L :=
  ⟨⟨s.saw.w, by
      simp only [betaVerts, Finset.mem_filter]
      exact ⟨mem_paperStripFinset.2 (s.in_strip _ s.saw.p.1.end_mem_support),
        s.end_right.2, s.end_right.1⟩⟩,
    { walk := s.saw.p.1
      is_trail := s.saw.p.2.isTrail
      adj := false_to_true_adj _ s.end_right.2
      fresh := by
        intro hmem
        exact betaPair_out T L s.saw.w.1 s.saw.w.2.1 s.end_right.1
          (s.in_strip _ (s.saw.p.1.snd_mem_support_of_mem_edges hmem))
      in_strip := s.in_strip }⟩

/-- **The right-boundary bijection.** -/
def betaEquiv (T L : ℕ) : betaSigma T L ≃ PaperSAW_B T L where
  toFun := betaToSAW T L
  invFun := sawToBeta T L
  left_inv := by rintro ⟨⟨v, hv⟩, γ⟩; rfl
  right_inv := by rintro ⟨n, ⟨w, p, rfl⟩, h1, h2⟩; rfl

/-- **The topological input for the right boundary.**  A configuration ending on
the right boundary of the strip makes no full turn.  This is where the
self-avoidance of the walk and the simple connectivity of the strip enter: the
winding modulo `2π` is already pinned by `freshTrail_winding_angle`. -/
lemma betaTrail_winding_bound (T L : ℕ) (p : betaSigma T L) :
    |p.2.winding| < 2 * Real.pi :=
  lt_of_le_of_lt
    (freshTrail_boundary_winding_bound p.2 (betaPair_out T L _ _ (betaVerts_diag p.1.2)))
    (by linarith [Real.pi_pos])

/-- **The winding of a right-boundary walk vanishes.**

The initial mid-edge `a` and the final mid-edge are both horizontal and point in
the same direction, so the total turning is a multiple of `2π`, and the
configuration makes no full turn. -/
lemma betaTrail_winding_zero (T L : ℕ) (p : betaSigma T L) :
    p.2.winding = 0 := by
  have hangle : ((p.2.winding : Real.Angle)) = ((0 : ℝ) : Real.Angle) := by
    rw [freshTrail_winding_angle p.2, beta_lastDir_arg (betaVerts_false p.1.2)]
  obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hangle
  have hb := betaTrail_winding_bound T L p
  have hpi := Real.pi_pos
  rw [abs_lt] at hb
  rw [sub_zero] at hn
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · exfalso
      have : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      nlinarith [hb.1]
    · exact h
    · exfalso
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      nlinarith [hb.2]
  rw [hn0] at hn
  simpa using hn

lemma betaTrail_weight (T L : ℕ) (p : betaSigma T L) :
    p.2.weight = (xc : ℂ) ^ ((betaToSAW T L p).len + 1) := by
  simp [FreshTrail.weight, walkWeight, betaTrail_winding_zero T L p,
    FreshTrail.len, betaToSAW]

/-- The right-boundary sum, as a sum over `betaSigma`. -/
lemma bdry_B_sum_sigma (T L : ℕ) :
    ∑ v ∈ betaVerts T L, freshObs T L v (v.1, v.2.1, true)
      = ∑' (p : betaSigma T L), p.2.weight := by
  rw [← Finset.tsum_subtype (betaVerts T L)
    (fun v => freshObs T L v (v.1, v.2.1, true))]
  exact (Summable.tsum_sigma (f := fun p : betaSigma T L => p.2.weight)
    Summable.of_finite).symm

/-- **Right boundary.**  On a `β` mid-edge the direction is `+1` and the winding
is `0`, so the contribution is exactly the generating function `B_paper`. -/
lemma bdry_B_eval (T L : ℕ) :
    ∑ p ∈ (bdryPairs T L).filter (IsBPair T), bdryTerm T L p
      = (B_paper T L xc : ℂ) := by
  rw [bdry_B_sum, bdry_B_sum_sigma]
  have h1 : ∑' (p : betaSigma T L), p.2.weight
      = ∑' (s : PaperSAW_B T L), (xc : ℂ) ^ (s.len + 1) := by
    rw [← (betaEquiv T L).tsum_eq (fun s => (xc : ℂ) ^ (s.len + 1))]
    exact tsum_congr fun p => betaTrail_weight T L p
  rw [h1, B_paper, Complex.ofReal_tsum]
  push_cast
  rfl

/-- **Escape boundary.**  Every boundary mid-edge contributes a term whose real
part is non-negative, because the combined direction/winding phase is
`exp(3iθ/8)` with `|θ| ≤ π` and `cos(3θ/8) > 0` (`boundary_cos_pos`). -/
lemma bdry_E_re_nonneg (T L : ℕ) :
    0 ≤ (∑ p ∈ (bdryPairs T L).filter (IsEPair T), bdryTerm T L p).re := by
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun p hp => ?_
  have hout : ¬ PaperFinStrip T L p.2 :=
    (mem_bdryPairs.1 (Finset.mem_filter.1 hp).1).2.2
  exact freshObs_dir_re_nonneg T L p.1 p.2 hout

/-! ### The starting mid-edge

The only mid-edge leaving the strip at `paperStart` is the mid-edge `a` towards
`hexOrigin`.  We first identify the starting family and its contribution
exactly; the remaining input is then the normalisation `F(a) = 1` of the paper,
in the form of `bdry_start_eval`. -/

/-- The two neighbours of `paperStart` other than `hexOrigin` are in the strip. -/
lemma paperStart_nbr_mem_strip (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (i : Fin 3)
    (hi : i ≠ 0) : PaperFinStrip T L (hexNeighbors3 paperStart i) := by
  have hT' : (1 : ℤ) ≤ (T : ℤ) := by exact_mod_cast hT
  have hL' : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
  fin_cases i
  · exact absurd rfl hi
  · refine ⟨?_, ?_⟩ <;>
      simp [hexNeighbors3, trueNeighbors, paperStart, PaperInfStrip] <;> omega
  · refine ⟨?_, ?_⟩ <;>
      simp [hexNeighbors3, trueNeighbors, paperStart, PaperInfStrip] <;> omega

lemma hexNeighbors3_paperStart_zero : hexNeighbors3 paperStart 0 = hexOrigin := rfl

/-- The starting family consists of the single mid-edge `a = (paperStart, hexOrigin)`. -/
lemma startPairs_eq (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (bdryPairs T L).filter IsStartPair = {(paperStart, hexOrigin)} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hs⟩
    rw [mem_bdryPairs] at hp
    obtain ⟨-, hadj, hout⟩ := hp
    rw [IsStartPair] at hs
    rw [hs] at hadj
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, p.2 = hexNeighbors3 paperStart i := by
      rcases hexNeighbors3_complete paperStart p.2 hadj with h | h | h
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
    have hi0 : i = 0 := by
      by_contra hne
      exact hout (hi ▸ paperStart_nbr_mem_strip T L hT hL i hne)
    rw [hi0, hexNeighbors3_paperStart_zero] at hi
    exact Prod.ext hs hi
  · rintro rfl
    refine ⟨mem_bdryPairs.2 ⟨paperStart_in_fin_strip T L hT hL, ?_, ?_⟩, rfl⟩
    · exact hexNeighbors3_adj paperStart 0
    · intro h
      exact hexOrigin_not_in_strip T h.1

/-- The contribution of the starting mid-edge is `-F(a)`. -/
lemma bdry_start_sum (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∑ p ∈ (bdryPairs T L).filter IsStartPair, bdryTerm T L p
      = -freshObs T L paperStart hexOrigin := by
  rw [startPairs_eq T L hT hL, Finset.sum_singleton, bdryTerm]
  simp [midDir, starting_direction]

/-! The remaining two statements of the boundary evaluation — the evaluation of
the starting mid-edge (`bdry_start_eval`) and the strip identity
(`strip_identity_nonneg_rest`) — are proved in `SAWStartVertex.lean`, which
computes the defect of the vertex relation at `paperStart`. -/

end
