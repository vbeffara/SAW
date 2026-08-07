/-
# The loop of a pair walk and its turning number

This file is the geometric route to `pair_winding_relation` (the last remaining
input of Lemma 1 of Duminil-Copin–Smirnov).  It sits *upstream* of
`RequestProject.SAWPairCancellation` (which is why the definitional part of the
pair involution was split off into `RequestProject.SAWPairInvolDefs`).

## The picture

Let `γ` be a `FreshIncomingPair T L v k`: a fresh trail from `paperStart` to
`n_k := hexNeighbors3 v k` that uses exactly two edges at `v`.  Writing
`m := pairArriveIdx`, `e := pairExitIdx`, the walk decomposes as

  `paperStart → ⋯ → n_m → v → n_e → ⋯ (inner) ⋯ → n_k`   (`pairDecomp`)

and the *observable* path additionally traverses the mid-edge `n_k → v`.  So the
full support of `γ` is a prefix `paperStart → ⋯ → v` followed by the **closed
loop**

  `pairLoopList = v :: inner.support ++ [v]`.

Since the hexagonal lattice is 3-regular, the three indices `m`, `e`, `k` are
pairwise distinct, the three edges at `v` are all used (two by the loop, one by
the prefix), and the loop is a *simple* closed hex trail.

The pair involution reverses `inner`, i.e. it traverses the same loop backwards.

## The three ingredients

1. **Winding split** (`pair_winding_split`, `pair_winding_split_rev`):
   `W(γ) = W(prefix) + τ_in + W(loop)` where `τ_in` is the turn at `v` from the
   prefix into the loop.
2. **Umlaufsatz** (`pair_loop_umlauf`): the loop is a simple closed hex trail,
   so `W(loop) + τ_corner = ±2π`, where `τ_corner` is the turn of the loop at
   `v` itself.  This consumes `hex_closed_trail_turning_number`, whose proof was
   completed in `RequestProject.SAWUmlaufGaussBonnet`.
3. **Corner orientation** (`pair_loop_turning_eq`): the sign of `±2π` is the
   sign of `τ_corner`, equivalently `W(loop) = 5 · τ_corner`.  This is the only
   remaining gap.  Mathematically it holds because the third edge `v → n_m` at a
   honeycomb vertex always lies on the *reflex* side of the corner formed by the
   two loop edges; the prefix reaches `v` from `paperStart`, which is outside
   the loop, so the corner cannot be reflex for the loop's interior, i.e. the
   loop turns at `v` in the direction of its own orientation.

Given these, the assembly `pair_winding_relation_geom` is pure arithmetic with
`W_common = hexWalkWinding (pairPrefix γ).support`.
-/

import Mathlib
import RequestProject.SAWWindingDecomp
import RequestProject.SAWPairWindingProof
import RequestProject.SAWUmlaufGaussBonnet

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## A handshake bound: `2 · count ≤ vEdgeCount + endpoints` -/

/-- Handshake at a vertex of a walk: each interior visit of `v` uses two
    incident edges, each endpoint visit uses one.  (No trail hypothesis is
    needed: `vEdgeCount` counts edge *occurrences*.) -/
lemma walk_two_mul_count_le_vEdgeCount :
    ∀ {s t : HexVertex} (w : hexGraph.Walk s t) (v : HexVertex),
      2 * w.support.count v ≤
        vEdgeCount v w + (if v = s then 1 else 0) + (if v = t then 1 else 0) := by
  intro s t w
  induction w with
  | nil =>
    intro v
    simp only [SimpleGraph.Walk.support_nil, List.count_cons, List.count_nil, vEdgeCount,
      SimpleGraph.Walk.edges_nil, List.filter_nil, List.length_nil]
    split_ifs with h1 h2 <;> simp_all
  | @cons a b c hab w ih =>
    intro v
    have hne : ¬ (a = b) := hab.ne
    have h1 : (SimpleGraph.Walk.cons hab w).support.count v
        = (if v = a then 1 else 0) + w.support.count v := by
      rw [SimpleGraph.Walk.support_cons]
      by_cases h : v = a
      · subst h; simp; omega
      · simp [h, Ne.symm h]
    have h2 : vEdgeCount v (SimpleGraph.Walk.cons hab w)
        = (if v = a ∨ v = b then 1 else 0) + vEdgeCount v w := by
      simp only [vEdgeCount, SimpleGraph.Walk.edges_cons, List.filter_cons]
      by_cases h : v = a ∨ v = b
      · rcases h with h | h <;> subst h <;> simp [Sym2.mem_iff] <;> omega
      · push_neg at h
        simp [Sym2.mem_iff, h.1, h.2]
    have hIH := ih v
    rw [h1, h2]
    by_cases hva : v = a <;> by_cases hvb : v = b <;> by_cases hvc : v = c <;>
      simp_all <;> omega

/-! ## The winding split lemma for lists -/

/-- Splitting the winding of a vertex list at a two-vertex overlap. -/
lemma hexWalkWinding_split_two :
    ∀ (M : List HexVertex) (a b : HexVertex) (Ltail : List HexVertex),
      hexWalkWinding (M ++ a :: b :: Ltail) =
        hexWalkWinding (M ++ [a, b]) + hexWalkWinding (a :: b :: Ltail) := by
  intro M
  induction M with
  | nil => intro a b Ltail; simp [hexWalkWinding]
  | cons x M ih =>
    intro a b Ltail
    cases M with
    | nil =>
      have := ih a b Ltail
      simp only [List.nil_append] at this
      simp only [List.cons_append, List.nil_append]
      rw [hexWalkWinding_cons3 x a b Ltail]
      simp [hexWalkWinding]
    | cons y M' =>
      cases M' with
      | nil =>
        have h := ih a b Ltail
        simp only [List.cons_append, List.nil_append] at h ⊢
        rw [hexWalkWinding_cons3 x y a (b :: Ltail), hexWalkWinding_cons3 x y a [b], h]
        ring
      | cons z M'' =>
        have h := ih a b Ltail
        simp only [List.cons_append] at h ⊢
        rw [hexWalkWinding_cons3 x y z (M'' ++ a :: b :: Ltail),
            hexWalkWinding_cons3 x y z (M'' ++ [a, b]), h]
        ring

/-! ## Two small list facts -/

lemma list_getLast!_concat {α : Type*} [Inhabited α] (l : List α) (y : α) :
    (l ++ [y]).getLast! = y := by
  cases l with
  | nil => simp [List.getLast!]
  | cons a t =>
    rw [List.cons_append, List.getLast!_cons_eq_getLastD]
    simp [List.getLastD_eq_getLast?]

lemma list_split_last_two {α : Type*} [Inhabited α] : ∀ (l : List α), 2 ≤ l.length →
    l = l.dropLast.dropLast ++ [l.dropLast.getLast!, l.getLast!] := by
  intro l
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x _ =>
    intro h
    induction l using List.reverseRecOn with
    | nil => simp at h
    | append_singleton l y _ =>
      rw [List.dropLast_concat, List.dropLast_concat, list_getLast!_concat,
        list_getLast!_concat, List.append_assoc]
      rfl

lemma hex_walk_support_getLast! :
    ∀ {u w : HexVertex} (p : hexGraph.Walk u w), p.support.getLast! = w := by
  intro u w p
  induction p with
  | nil => simp [List.getLast!]
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.support_cons]
    cases hs : p.support with
    | nil => exact absurd hs p.support_ne_nil
    | cons x t =>
      rw [hs] at ih
      simp only [List.getLast!_cons_eq_getLastD, List.getLastD_eq_getLast?] at ih ⊢
      cases t with
      | nil => simpa using ih
      | cons y s => simpa using ih

/-! ## The arrival index -/

variable {T L : ℕ} {v : HexVertex} {k : Fin 3}

/-- The index of the neighbour of `v` from which the prefix arrives at `v`. -/
noncomputable def pairArriveIdx (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) : Fin 3 :=
  (prefix_penultimate_is_neighbor hv_ne γ).choose

lemma pairArriveIdx_spec (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    (pairPrefix hv_ne γ).support.dropLast.getLast! =
      hexNeighbors3 v (pairArriveIdx hv_ne γ) ∧
    pairArriveIdx hv_ne γ ≠ k ∧
    pairArriveIdx hv_ne γ ≠ pairExitIdx hv_ne γ :=
  (prefix_penultimate_is_neighbor hv_ne γ).choose_spec

lemma pairArriveIdx_ne_k (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    pairArriveIdx hv_ne γ ≠ k := (pairArriveIdx_spec hv_ne γ).2.1

lemma pairArriveIdx_ne_exit (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    pairArriveIdx hv_ne γ ≠ pairExitIdx hv_ne γ := (pairArriveIdx_spec hv_ne γ).2.2

/-- The prefix support ends with `[n_m, v]`. -/
lemma pairPrefix_length_pos (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    0 < (pairPrefix hv_ne γ).length := by
  rcases Nat.eq_zero_or_pos (pairPrefix hv_ne γ).length with h | h
  · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h).symm hv_ne
  · exact h

lemma pairPrefix_support_split (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    (pairPrefix hv_ne γ).support =
      (pairPrefix hv_ne γ).support.dropLast.dropLast ++
        [hexNeighbors3 v (pairArriveIdx hv_ne γ), v] := by
  have hlen : 2 ≤ (pairPrefix hv_ne γ).support.length := by
    rw [SimpleGraph.Walk.length_support]
    have := pairPrefix_length_pos hv_ne γ
    omega
  have h := list_split_last_two (pairPrefix hv_ne γ).support hlen
  rw [hex_walk_support_getLast!, (pairArriveIdx_spec hv_ne γ).1] at h
  exact h

/-! ## The loop -/

/-- The closed loop that the pair walk cuts out at `v`:
    `v → n_e → ⋯ → n_k → v`. -/
noncomputable def pairLoopList (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) : List HexVertex :=
  v :: ((pairInner hv_ne γ).support ++ [v])

/-- The reversed loop, traversed by the paired walk. -/
noncomputable def pairLoopListRev (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) : List HexVertex :=
  v :: ((pairInner hv_ne γ).reverse.support ++ [v])

lemma pairInner_support_head (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    (pairInner hv_ne γ).support =
      hexNeighbors3 v (pairExitIdx hv_ne γ) :: (pairInner hv_ne γ).support.tail := by
  exact SimpleGraph.Walk.support_eq_cons _

/-- The loop, in the shape used by `SAWWindingDecomp`. -/
lemma pairLoopList_eq (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    pairLoopList hv_ne γ =
      [v] ++ [hexNeighbors3 v (pairExitIdx hv_ne γ)] ++
        (pairInner hv_ne γ).support.tail ++ [v] := by
  unfold pairLoopList
  rw [pairInner_support_head hv_ne γ]
  simp

lemma pairInner_rev_support_head (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInner hv_ne γ).reverse.support =
      hexNeighbors3 v k :: (pairInner hv_ne γ).reverse.support.tail :=
  SimpleGraph.Walk.support_eq_cons _

lemma pairLoopListRev_eq (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    pairLoopListRev hv_ne γ =
      [v] ++ [hexNeighbors3 v k] ++
        (pairInner hv_ne γ).reverse.support.tail ++ [v] := by
  unfold pairLoopListRev
  rw [pairInner_rev_support_head hv_ne γ]
  simp

/-! ### The loop is a simple closed hex trail -/

/-- The exit neighbour and the arrival neighbour of the loop are distinct
    vertices. -/
lemma pairInner_endpoints_ne (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    hexNeighbors3 v (pairExitIdx hv_ne γ) ≠ hexNeighbors3 v k := by
  intro h
  exact pairExitIdx_ne hv_ne γ (hexNeighbors3_injective v h)

/-- The edges of `pairInner` at a vertex, plus the edge `v – n_e`, are edges of
    the whole walk. -/
lemma pairInner_vEdgeCount_le (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k)
    (x : HexVertex) :
    vEdgeCount x (pairInner hv_ne γ) +
        (if x ∈ (s(v, hexNeighbors3 v (pairExitIdx hv_ne γ)) : Sym2 HexVertex) then 1 else 0)
      ≤ vEdgeCount x γ.1.walk := by
  have hdec := pairDecomp hv_ne γ
  have hcons :
      (SimpleGraph.Walk.cons (hexNeighbors3_adj v (pairExitIdx hv_ne γ)) (pairInner hv_ne γ))
        = (SimpleGraph.Walk.cons (hexNeighbors3_adj v (pairExitIdx hv_ne γ))
            SimpleGraph.Walk.nil).append (pairInner hv_ne γ) := by simp
  rw [hdec, hcons, vEdgeCount_append, vEdgeCount_append, vEdgeCount_cons_nil]
  omega

/-- At most three edges of the walk meet any vertex. -/
lemma pair_walk_vEdgeCount_le_three (γ : FreshIncomingPair T L v k) (x : HexVertex) :
    vEdgeCount x γ.1.walk ≤ 3 :=
  hex_edges_incident_le_three γ.1.walk γ.1.is_trail x

/-- At the far endpoint `n_k` of the loop only two edges of the walk can be
    used: the third one is the fresh mid-edge `n_k – v`. -/
lemma pair_walk_vEdgeCount_nk_le_two (γ : FreshIncomingPair T L v k) :
    vEdgeCount (hexNeighbors3 v k) γ.1.walk ≤ 2 := by
  have hadj : hexGraph.Adj (hexNeighbors3 v k) v := (hexNeighbors3_adj v k).symm
  have hcomp := hexNeighbors3_complete (hexNeighbors3 v k) v hadj
  have hfresh : s(hexNeighbors3 v k, v) ∉ γ.1.walk.edges := γ.1.fresh
  rcases hcomp with h | h | h
  · exact vEdgeCount_le_two_excluding _ 0 γ.1.walk γ.1.is_trail
      (by rw [← h, Sym2.eq_swap]; exact hfresh)
  · exact vEdgeCount_le_two_excluding _ 1 γ.1.walk γ.1.is_trail
      (by rw [← h, Sym2.eq_swap]; exact hfresh)
  · exact vEdgeCount_le_two_excluding _ 2 γ.1.walk γ.1.is_trail
      (by rw [← h, Sym2.eq_swap]; exact hfresh)

/-- `pairInner` is a path: its vertices are pairwise distinct.

    This is where 3-regularity of the honeycomb enters: a second visit to an
    interior vertex would need four edges there, a second visit to `n_e` would
    need four (three inside `inner` plus `v – n_e`), and a second visit to `n_k`
    would need three — but only two are available, since the mid-edge
    `n_k – v` is fresh. -/
lemma pairInner_support_nodup (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    (pairInner hv_ne γ).support.Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro x
  have hhand := walk_two_mul_count_le_vEdgeCount (pairInner hv_ne γ) x
  have hle := pairInner_vEdgeCount_le hv_ne γ x
  have h3 := pair_walk_vEdgeCount_le_three γ x
  have hnene := pairInner_endpoints_ne hv_ne γ
  by_cases hx : x = hexNeighbors3 v (pairExitIdx hv_ne γ)
  · have hmem : x ∈ (s(v, hexNeighbors3 v (pairExitIdx hv_ne γ)) : Sym2 HexVertex) := by
      rw [hx]; simp
    have hxk : ¬ (x = hexNeighbors3 v k) := by rw [hx]; exact hnene
    rw [if_pos hmem] at hle
    rw [if_pos hx, if_neg hxk] at hhand
    omega
  · by_cases hy : x = hexNeighbors3 v k
    · have h2 : vEdgeCount x γ.1.walk ≤ 2 := by
        rw [hy]; exact pair_walk_vEdgeCount_nk_le_two γ
      rw [if_neg hx, if_pos hy] at hhand
      omega
    · rw [if_neg hx, if_neg hy] at hhand
      omega

lemma pairLoopList_length (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    (pairLoopList hv_ne γ).length = (pairInner hv_ne γ).length + 3 := by
  simp [pairLoopList, SimpleGraph.Walk.length_support]

lemma pairInner_length_pos (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    0 < (pairInner hv_ne γ).length := by
  rcases Nat.eq_zero_or_pos (pairInner hv_ne γ).length with h | h
  · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h)
      (pairInner_endpoints_ne hv_ne γ)
  · exact h

/-! ## The three turns at `v`

`turnInto e` is the turn from the incoming prefix direction `v - n_m` to the
outgoing direction `n_e - v`; `pairCornerTurn` is the turn of the *loop* at `v`,
from `v - n_k` to `n_e - v`.  All of them have the shape
`arg (- midEdgeDir v x / midEdgeDir v y)`, which is `∓π/3` by
`turning_angle_k` / `turning_angle_l`. -/

/-- The turn at `v` from the prefix into the loop. -/
noncomputable def pairEntryTurn (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) : ℝ :=
  Complex.arg (-midEdgeDir v (pairExitIdx hv_ne γ) / midEdgeDir v (pairArriveIdx hv_ne γ))

/-- The turn at `v` from the prefix into the *reversed* loop. -/
noncomputable def pairEntryTurnRev (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) : ℝ :=
  Complex.arg (-midEdgeDir v k / midEdgeDir v (pairArriveIdx hv_ne γ))

/-- The turn of the loop at its base point `v`. -/
noncomputable def pairCornerTurn (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) : ℝ :=
  Complex.arg (-midEdgeDir v (pairExitIdx hv_ne γ) / midEdgeDir v k)

/-! ## Step 1: the winding split -/

lemma pair_winding_split (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    γ.1.rawWinding =
      hexWalkWinding (pairPrefix hv_ne γ).support + pairEntryTurn hv_ne γ +
        hexWalkWinding (pairLoopList hv_ne γ) := by
  have hpre := pairPrefix_support_split hv_ne γ
  set M := (pairPrefix hv_ne γ).support.dropLast.dropLast with hM
  set nm := hexNeighbors3 v (pairArriveIdx hv_ne γ) with hnm
  set nex := hexNeighbors3 v (pairExitIdx hv_ne γ) with hnex
  set tl := (pairInner hv_ne γ).support.tail with htl
  have hfull : γ.1.fullSupport = M ++ nm :: v :: (nex :: (tl ++ [v])) := by
    rw [original_fullSupport_eq hv_ne γ]
    rw [hpre]
    simp only [List.append_assoc, List.cons_append, List.nil_append, ← hnex, ← htl]
  have hloop : pairLoopList hv_ne γ = v :: nex :: (tl ++ [v]) := by
    rw [pairLoopList_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append, ← hnex, ← htl]
  have hturn : Complex.arg ((correctHexEmbed nex - correctHexEmbed v) /
      (correctHexEmbed v - correctHexEmbed nm)) = pairEntryTurn hv_ne γ := by
    have hsub : correctHexEmbed v - correctHexEmbed nm
        = -(correctHexEmbed nm - correctHexEmbed v) := by ring
    simp only [pairEntryTurn, midEdgeDir, ← hnm, ← hnex, hsub, div_neg, neg_div]
  show hexWalkWinding γ.1.fullSupport = _
  rw [hfull, hexWalkWinding_split_two M nm v (nex :: (tl ++ [v])),
    hexWalkWinding_cons3 nm v nex (tl ++ [v]), ← hpre, hloop, hturn]
  ring

lemma pair_winding_split_rev (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInvol hv hv_ne γ).1.rawWinding =
      hexWalkWinding (pairPrefix hv_ne γ).support + pairEntryTurnRev hv_ne γ +
        hexWalkWinding (pairLoopListRev hv_ne γ) := by
  have hpre := pairPrefix_support_split hv_ne γ
  set M := (pairPrefix hv_ne γ).support.dropLast.dropLast with hM
  set nm := hexNeighbors3 v (pairArriveIdx hv_ne γ) with hnm
  set nk := hexNeighbors3 v k with hnk
  set tl := (pairInner hv_ne γ).reverse.support.tail with htl
  have hfull : (pairInvol hv hv_ne γ).1.fullSupport = M ++ nm :: v :: (nk :: (tl ++ [v])) := by
    rw [paired_fullSupport_eq hv hv_ne γ]
    rw [hpre]
    simp only [List.append_assoc, List.cons_append, List.nil_append, ← hnk, ← htl]
  have hloop : pairLoopListRev hv_ne γ = v :: nk :: (tl ++ [v]) := by
    rw [pairLoopListRev_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append, ← hnk, ← htl]
  have hturn : Complex.arg ((correctHexEmbed nk - correctHexEmbed v) /
      (correctHexEmbed v - correctHexEmbed nm)) = pairEntryTurnRev hv_ne γ := by
    have hsub : correctHexEmbed v - correctHexEmbed nm
        = -(correctHexEmbed nm - correctHexEmbed v) := by ring
    simp only [pairEntryTurnRev, midEdgeDir, ← hnm, ← hnk, hsub, div_neg, neg_div]
  show hexWalkWinding (pairInvol hv hv_ne γ).1.fullSupport = _
  rw [hfull, hexWalkWinding_split_two M nm v (nk :: (tl ++ [v])),
    hexWalkWinding_cons3 nm v nk (tl ++ [v]), ← hpre, hloop, hturn]
  ring

/-- Reversing the loop negates its winding. -/
lemma pairLoopListRev_winding (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    hexWalkWinding (pairLoopListRev hv_ne γ) = -hexWalkWinding (pairLoopList hv_ne γ) := by
  rw [pairLoopList_eq, pairLoopListRev_eq]
  exact pair_suffix_winding_neg hv_ne γ

/-! ## Step 2: the Umlaufsatz for the loop -/

/-- The discrete Umlaufsatz in the shape needed here: a simple closed hex trail
    presented as `u :: ((nex :: Mt) ++ [u])`, whose inner part is `Nodup` and
    ends at `nk`, has total turning `±2π`, the closing turn at `u` being
    `arg ((nex - u) / (u - nk))`. -/
lemma hex_closed_loop_turning (u nex nk : HexVertex) (Mt : List HexVertex)
    (hM1 : 1 ≤ Mt.length)
    (hlast : (nex :: Mt).getLast (List.cons_ne_nil _ _) = nk)
    (htrail : HexTrailList (u :: ((nex :: Mt) ++ [u])))
    (hnodup : (nex :: Mt).Nodup) :
    hexWalkWinding (u :: ((nex :: Mt) ++ [u])) +
      Complex.arg ((correctHexEmbed nex - correctHexEmbed u) /
        (correctHexEmbed u - correctHexEmbed nk)) = 2 * Real.pi ∨
    hexWalkWinding (u :: ((nex :: Mt) ++ [u])) +
      Complex.arg ((correctHexEmbed nex - correctHexEmbed u) /
        (correctHexEmbed u - correctHexEmbed nk)) = -(2 * Real.pi) := by
  have hlen : (u :: ((nex :: Mt) ++ [u])).length = Mt.length + 3 := by simp
  have hL4 : 4 ≤ (u :: ((nex :: Mt) ++ [u])).length := by rw [hlen]; omega
  have hcat : (u :: ((nex :: Mt) ++ [u])) = (u :: nex :: Mt) ++ [u] := rfl
  have hclosed : (u :: ((nex :: Mt) ++ [u])).head?
      = (u :: ((nex :: Mt) ++ [u])).getLast? := by
    have hg : (u :: ((nex :: Mt) ++ [u])).getLast? = some u := by
      rw [hcat, List.getLast?_concat]
    rw [hg]
    rfl
  have hsimple : (u :: ((nex :: Mt) ++ [u])).tail.dropLast.Nodup := by
    have htl : (u :: ((nex :: Mt) ++ [u])).tail = (nex :: Mt) ++ [u] := rfl
    rw [htl, List.dropLast_concat]
    exact hnodup
  have h := hex_closed_trail_turning_number (u :: ((nex :: Mt) ++ [u])) hL4 htrail hclosed hsimple
  have e0 : (u :: ((nex :: Mt) ++ [u])).get ⟨0, by omega⟩ = u := rfl
  have e1 : (u :: ((nex :: Mt) ++ [u])).get ⟨1, by omega⟩ = nex := rfl
  have e2 : (u :: ((nex :: Mt) ++ [u])).get
      ⟨(u :: ((nex :: Mt) ++ [u])).length - 2, by rw [hlen]; omega⟩ = nk := by
    have h1 : (u :: ((nex :: Mt) ++ [u])).length - 2 = Mt.length + 1 := by rw [hlen]; omega
    simp only [List.get_eq_getElem, h1, List.getElem_cons_succ]
    have hgo : ((nex :: Mt) ++ [u])[Mt.length]'(by simp) = nk := by
      rw [List.getElem_append_left (by simp)]
      rw [← hlast, List.getLast_eq_getElem]
      congr 1
    exact hgo
  simp only [e0, e1, e2] at h
  exact h

/-- The loop is a simple closed hex trail, so its total turning is `±2π`. -/
lemma pair_loop_umlauf (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    hexWalkWinding (pairLoopList hv_ne γ) + pairCornerTurn hv_ne γ = 2 * Real.pi ∨
    hexWalkWinding (pairLoopList hv_ne γ) + pairCornerTurn hv_ne γ = -(2 * Real.pi) := by
  set nex := hexNeighbors3 v (pairExitIdx hv_ne γ) with hnex
  set tl := (pairInner hv_ne γ).support.tail with htl
  have hsupp : (pairInner hv_ne γ).support = nex :: tl := pairInner_support_head hv_ne γ
  have hsuppLen : (pairInner hv_ne γ).support.length = (pairInner hv_ne γ).length + 1 :=
    SimpleGraph.Walk.length_support _
  have hM1 : 1 ≤ tl.length := by
    have h := pairInner_length_pos hv_ne γ
    have : (nex :: tl).length = (pairInner hv_ne γ).length + 1 := by rw [← hsupp]; exact hsuppLen
    simp only [List.length_cons] at this
    omega
  have hlast : (nex :: tl).getLast (List.cons_ne_nil _ _) = hexNeighbors3 v k := by
    have h0 := SimpleGraph.Walk.getLast_support (pairInner hv_ne γ)
    simp only [← hsupp]
    exact h0
  have htrail : HexTrailList (v :: ((nex :: tl) ++ [v])) := by
    have h1 := pair_suffix_hex_trail hv_ne γ
    rw [← pairLoopList_eq] at h1
    rw [pairLoopList, hsupp] at h1
    exact h1
  have hnodup : (nex :: tl).Nodup := by
    have h1 := pairInner_support_nodup hv_ne γ
    rwa [hsupp] at h1
  have h := hex_closed_loop_turning v nex (hexNeighbors3 v k) tl hM1 hlast htrail hnodup
  have hloop : pairLoopList hv_ne γ = v :: ((nex :: tl) ++ [v]) := by
    rw [pairLoopList, hsupp]
  have hcorner : Complex.arg
      ((correctHexEmbed nex - correctHexEmbed v) /
        (correctHexEmbed v - correctHexEmbed (hexNeighbors3 v k)))
      = pairCornerTurn hv_ne γ := by
    have hsub : correctHexEmbed v - correctHexEmbed (hexNeighbors3 v k)
        = -(correctHexEmbed (hexNeighbors3 v k) - correctHexEmbed v) := by ring
    simp only [pairCornerTurn, midEdgeDir, ← hnex, hsub, div_neg, neg_div]
  rw [hcorner] at h
  rw [hloop]
  exact h

end
