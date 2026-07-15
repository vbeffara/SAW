import Mathlib

/-!
# Polygonal connectivity of open sets (infrastructure for the escape core)

This file develops a small, reusable, and genuinely-true topological brick used by
the discrete Hopf Umlaufsatz: in a normed plane, if two points `p, q` are joined
by a path lying entirely inside an *open* set `U`, then they are joined by a
*polyline* (a finite `List.IsChain` of straight segments) every segment of which
stays inside `U`.

This is exactly the shape the escape residue `vertex_escape_walk_core`
(`SAWUmlaufPolygon.lean`) needs: taking `U = ℂ \ K`, where `K` is the (closed)
union of the polygon edges not incident to the base vertex `x` together with the
forbidden diagonals, a segment lies in `U` iff it is `Disjoint` from every such
edge/diagonal.  The only genuinely-hard (Jordan-curve-theorem-level) content that
remains after this reduction is the *connectivity* fact that the base vertex `x`
and a far exterior point lie in the same path component of `U` — isolated here as
`JoinedIn`.

The proof of the main lemma is the standard Lebesgue-number sampling argument:
the path image is compact, cover it by balls contained in `U`, take a Lebesgue
number `δ`, sample the (extended) path at a spacing `< δ`, and observe that
consecutive samples lie in a common ball `⊆ U`, whose convexity puts the
connecting segment inside `U`.
-/

open scoped unitInterval
open Metric

namespace HexArea

/-- **Sampling a segment inside a ball.**  Two points of an open ball are joined
    by a segment lying in the ball (convexity of balls), hence in any superset. -/
lemma segment_subset_of_mem_ball {U : Set ℂ} {c : ℂ} {r : ℝ}
    (hball : Metric.ball c r ⊆ U) {a b : ℂ} (ha : a ∈ Metric.ball c r)
    (hb : b ∈ Metric.ball c r) :
    segment ℝ a b ⊆ U :=
  (subset_trans ((convex_ball c r).segment_subset ha hb) hball)

/-
**Polygonal (polyline) connectivity of an open set.**  If `p` and `q` are
    joined by a path inside the open set `U ⊆ ℂ`, then there is a finite polyline
    from `p` to `q` — a `List.IsChain` of the "segment stays in `U`" relation —
    ending at `q`.  Proved by the Lebesgue-number sampling of a connecting path.

    This is the reusable topological reduction target for the polygon-exterior
    escape core `vertex_escape_walk_core`.
-/
lemma exists_polyline_segments_subset_of_joinedIn (U : Set ℂ) (hU : IsOpen U)
    (p q : ℂ) (h : JoinedIn U p q) :
    ∃ zs : List ℂ, List.IsChain (fun a b => segment ℝ a b ⊆ U) (p :: zs) ∧
      zs.getLastD p = q := by
  revert h p q;
  intro p q hpq
  obtain ⟨γ, hγ⟩ := hpq
  let γ_ext := γ.extend
  have hγ_ext : Continuous γ_ext := by
    exact γ_ext.continuous
  have hγ_ext_zero : γ_ext 0 = p := by
    exact γ.extend_zero
  have hγ_ext_one : γ_ext 1 = q := by
    aesop
  have hγ_ext_U : ∀ t : ℝ, γ_ext t ∈ U := by
    intro t
    by_cases ht : t ≤ 0 ∨ t ≥ 1;
    · cases ht <;> have := hγ 0 <;> have := hγ 1 <;> aesop;
    · grind
  generalize_proofs at *;
  -- By the Lebesgue-number sampling argument, there exists a $\delta > 0$ such that for any $t_1, t_2 \in [0, 1]$, if $|t_1 - t_2| < \delta$, then $\gamma(t_1)$ and $\gamma(t_2)$ are connected by a segment in $U$.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ t1 t2 : ℝ, t1 ∈ Set.Icc 0 1 → t2 ∈ Set.Icc 0 1 → |t1 - t2| < δ → segment ℝ (γ_ext t1) (γ_ext t2) ⊆ U := by
    -- By the Lebesgue-number sampling argument, there exists a $\delta > 0$ such that for any $t \in [0, 1]$, the ball $B(\gamma(t), \delta)$ is contained in $U$.
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ t ∈ Set.Icc 0 1, Metric.ball (γ_ext t) δ ⊆ U := by
      -- By the Lebesgue-number lemma, there exists $\delta > 0$ such that for all $t \in [0,1]$, there exists $c_t \in U$ with $ball(c_t, \delta) \subseteq U$. Apply this lemma to the compact set $γ_ext '' Set.Icc 0 1$.
      have h_lebesgue : IsCompact (γ_ext '' Set.Icc 0 1) := by
        exact CompactIccSpace.isCompact_Icc.image hγ_ext
      generalize_proofs at *;
      have h_lebesgue : ∀ {S : Set ℂ}, IsCompact S → S ⊆ U → IsOpen U → ∃ δ > 0, ∀ x ∈ S, Metric.ball x δ ⊆ U := by
        intros S hS hSU hU; exact (by
        have := Metric.isOpen_iff.mp hU;
        choose! ε hε_pos hε using this;
        have := hS.elim_nhds_subcover ( fun x => Metric.ball x ( ε x / 2 ) ) fun x hx => Metric.ball_mem_nhds _ ( half_pos ( hε_pos x ( hSU hx ) ) );
        obtain ⟨ t, ht₁, ht₂ ⟩ := this;
        -- Let $\delta = \min_{x \in t} \frac{\epsilon(x)}{2}$.
        obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ t, δ ≤ ε x / 2 := by
          by_cases ht : t.Nonempty;
          · exact ⟨ Finset.min' ( t.image fun x => ε x / 2 ) ⟨ _, Finset.mem_image_of_mem _ ht.choose_spec ⟩, by have := Finset.min'_mem ( t.image fun x => ε x / 2 ) ⟨ _, Finset.mem_image_of_mem _ ht.choose_spec ⟩ ; aesop, fun x hx => Finset.min'_le _ _ <| Finset.mem_image_of_mem _ hx ⟩;
          · exact ⟨ 1, zero_lt_one, fun x hx => False.elim <| ht ⟨ x, hx ⟩ ⟩;
        use δ;
        simp_all +decide [ Set.subset_def ];
        intro x hx y hy; obtain ⟨ i, hi, hi' ⟩ := ht₂ x hx; exact hε i ( hSU i ( ht₁ i hi ) ) y ( by linarith [ hδ i hi, dist_triangle y x i ] ) ;);
      generalize_proofs at *;
      exact h_lebesgue ‹_› ( Set.image_subset_iff.mpr fun t ht => hγ_ext_U t ) hU |> fun ⟨ δ, hδ₁, hδ₂ ⟩ => ⟨ δ, hδ₁, fun t ht => hδ₂ _ <| Set.mem_image_of_mem _ ht ⟩
    generalize_proofs at *; (
    -- By the continuity of $\gamma$, there exists a $\delta' > 0$ such that for any $t_1, t_2 \in [0, 1]$, if $|t_1 - t_2| < \delta'$, then $|\gamma(t_1) - \gamma(t_2)| < \delta$.
    obtain ⟨δ', hδ'_pos, hδ'⟩ : ∃ δ' > 0, ∀ t1 t2 : ℝ, t1 ∈ Set.Icc 0 1 → t2 ∈ Set.Icc 0 1 → |t1 - t2| < δ' → dist (γ_ext t1) (γ_ext t2) < δ := by
      have h_unif_cont : UniformContinuousOn γ_ext (Set.Icc 0 1) := by
        exact ( isCompact_Icc.uniformContinuousOn_of_continuous hγ_ext.continuousOn )
      generalize_proofs at *; (
      exact Metric.uniformContinuousOn_iff.mp h_unif_cont δ hδ_pos |> Exists.imp fun δ' hδ' => by tauto;)
    generalize_proofs at *; (
    refine' ⟨ δ', hδ'_pos, fun t1 t2 ht1 ht2 h => _ ⟩
    generalize_proofs at *; (
    refine' segment_subset_of_mem_ball _ _ _;
    exacts [ γ_ext t1, δ, hδ t1 ht1, by simpa using hδ_pos, by simpa [ dist_comm ] using hδ' t1 t2 ht1 ht2 h ])))
  generalize_proofs at *; (
  -- Choose $N$ such that $1/N < \delta$.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N > 0 ∧ 1 / (N : ℝ) < δ := by
    exact ⟨ ⌊δ⁻¹⌋₊ + 1, Nat.succ_pos _, by simpa using inv_lt_of_inv_lt₀ hδ_pos <| Nat.lt_floor_add_one _ ⟩
  generalize_proofs at *; (
  refine' ⟨ List.map ( fun i : ℕ => γ_ext ( ( i + 1 : ℝ ) / N ) ) ( List.range N ), _, _ ⟩ <;> simp_all +decide [ List.isChain_iff_getElem ];
  · intro i hi; rcases i with ( _ | i ) <;> simp_all +decide [ List.getElem_cons ] ;
    · simpa [ hγ_ext_zero ] using hδ 0 ( ( N : ℝ ) ⁻¹ ) ( by norm_num ) ( by norm_num ) ( by positivity ) ( inv_le_one_of_one_le₀ <| mod_cast hi ) <| by simpa [ abs_of_nonneg ] using hN;
    · convert hδ _ _ _ _ _ _ _ using 1 <;> ring <;> norm_num [ hN.1.ne' ];
      · positivity;
      · nlinarith [ show ( i : ℝ ) + 1 + 1 ≤ N by norm_cast, mul_inv_cancel₀ ( by norm_cast; linarith : ( N : ℝ ) ≠ 0 ) ];
      · positivity;
      · nlinarith [ show ( i : ℝ ) + 1 + 1 ≤ N by norm_cast, inv_mul_cancel₀ ( by norm_cast; linarith : ( N : ℝ ) ≠ 0 ) ];
      · linarith;
  · rw [List.getLast?_range, if_neg hN.1.ne']
    simp only [Option.map_some, Option.getD_some]
    have hone : ((↑(N-1) + 1) / (N:ℝ)) = 1 := by
      have hcast : (↑(N-1) : ℝ) + 1 = N := by
        rw [Nat.cast_sub hN.1]; ring
      rw [hcast, div_self (by exact_mod_cast hN.1.ne')]
    rw [hone, hγ_ext_one]))

/-- **Abstract polygon-escape polyline from a path in the complement.**  Given a
    finite list `forb` of forbidden segments, if the base point `x` is joined to a
    target `q` by a path inside the *complement* of the union of the forbidden
    segments, and `q` lies outside a set `hull`, then there is a polyline from `x`
    (a `List.IsChain` of the "segment avoids every forbidden segment" relation)
    ending outside `hull`.

    This is the exact shape needed by the polygon-exterior escape residue
    `vertex_escape_walk_core` (`SAWUmlaufPolygon.lean`): take `forb` to be the
    polygon edges not incident to `x` together with the forbidden diagonals, and
    `hull := convexHull ℝ (W.toFinset)`.  After this reduction the only remaining
    (Jordan-curve-theorem-level) content is the *connectivity* hypothesis
    `JoinedIn` — that the boundary vertex `x` reaches a far exterior point without
    crossing any forbidden segment. -/
lemma exists_escape_polyline_of_joinedIn (forb : List (ℂ × ℂ)) (x q : ℂ)
    (hull : Set ℂ) (hq : q ∉ hull)
    (hjoin : JoinedIn ((⋃ s ∈ forb, segment ℝ s.1 s.2)ᶜ) x q) :
    ∃ zs : List ℂ,
      List.IsChain (fun a b => ∀ s ∈ forb,
          Disjoint (segment ℝ a b) (segment ℝ s.1 s.2)) (x :: zs) ∧
      zs.getLastD x ∉ hull := by
  set U : Set ℂ := (⋃ s ∈ forb, segment ℝ s.1 s.2)ᶜ with hUdef
  have hKclosed : IsClosed (⋃ s ∈ forb, segment ℝ s.1 s.2) := by
    apply Set.Finite.isClosed_biUnion forb.finite_toSet
    intro s _
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hUopen : IsOpen U := by rw [hUdef]; exact hKclosed.isOpen_compl
  obtain ⟨zs, hchain, hlast⟩ :=
    exists_polyline_segments_subset_of_joinedIn U hUopen x q hjoin
  refine ⟨zs, ?_, ?_⟩
  · refine hchain.imp ?_
    intro a b hab s hs
    rw [← Set.subset_compl_iff_disjoint_right]
    refine hab.trans ?_
    apply Set.compl_subset_compl.mpr
    exact fun y hy => Set.mem_biUnion hs hy
  · rw [hlast]; exact hq

end HexArea