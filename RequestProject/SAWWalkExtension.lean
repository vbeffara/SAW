/-
# Walk extension and retraction for the vertex relation

Key combinatorial operations for the pair/triplet partition
in the vertex relation (Lemma 1 of Duminil-Copin & Smirnov).
-/

import Mathlib

open SimpleGraph

/-! ## Walk extension by one step -/

/-- Extend a walk by one step to a new neighbor. -/
def walkExtend {V : Type*} {G : SimpleGraph V} {v w u : V}
    (p : G.Walk v w) (h : G.Adj w u) : G.Walk v u :=
  p.append (.cons h .nil)

@[simp] lemma walkExtend_length {V : Type*} {G : SimpleGraph V} {v w u : V}
    (p : G.Walk v w) (h : G.Adj w u) :
    (walkExtend p h).length = p.length + 1 := by
  simp [walkExtend]

/-- The support of an extended walk. -/
lemma walkExtend_support {V : Type*} {G : SimpleGraph V} {v w u : V}
    (p : G.Walk v w) (h : G.Adj w u) :
    (walkExtend p h).support = p.support ++ [u] := by
  simp [walkExtend, Walk.support_append]

/-- Extending a path by a vertex not in the support gives a path. -/
lemma walkExtend_isPath {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {v w u : V} (p : G.Walk v w) (hp : p.IsPath) (h : G.Adj w u)
    (hu : u ∉ p.support) :
    (walkExtend p h).IsPath := by
  rw [Walk.isPath_def] at hp ⊢
  rw [walkExtend_support]
  exact List.Nodup.append hp (List.nodup_singleton u)
    (by intro x hx₁ hx₂; simp at hx₂; subst hx₂; exact hu hx₁)

/-- The new vertex u is in the extended walk's support. -/
lemma walkExtend_mem {V : Type*} {G : SimpleGraph V}
    {v w u : V} (p : G.Walk v w) (h : G.Adj w u) :
    u ∈ (walkExtend p h).support := by
  rw [walkExtend_support]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-! ## Walk retraction (removing last step) -/

/-- Remove the last edge from a walk of length ≥ 1. Returns the
    second-to-last vertex, the shorter walk, and the adjacency. -/
noncomputable def walkRetract {V : Type*} {G : SimpleGraph V}
    {v w : V} : (p : G.Walk v w) → 0 < p.length →
    (u : V) × G.Walk v u × PLift (G.Adj u w)
  | .cons h₁ .nil, _ => ⟨v, .nil, .up h₁⟩
  | .cons h₁ (.cons h₂ q), _ =>
    let ⟨u, r, hadj⟩ := walkRetract (.cons h₂ q) (by simp)
    ⟨u, .cons h₁ r, hadj⟩

/-
The retraction has length one less.
-/
lemma walkRetract_length {V : Type*} {G : SimpleGraph V}
    {v w : V} (p : G.Walk v w) (h : 0 < p.length) :
    (walkRetract p h).2.1.length = p.length - 1 := by
  -- We prove this by induction on the length of the walk.
  induction' p with v w p h ih;
  · contradiction;
  · cases ‹G.Walk p _› <;> simp_all +decide [ walkRetract ]

/-
Retracting a path gives a path.
-/
lemma walkRetract_isPath {V : Type*} {G : SimpleGraph V}
    {v w : V} (p : G.Walk v w) (hp : p.IsPath) (h : 0 < p.length) :
    (walkRetract p h).2.1.IsPath := by
  -- The retracted walk is a subwalk of the original path, which is a path by assumption.
  have h_subwalk : (walkRetract p h).snd.1.support.Sublist p.support := by
    induction' p with p hp;
    · contradiction;
    · rename_i h₁ h₂ h₃;
      cases h₂ <;> simp_all +decide [ walkRetract ];
  rw [ SimpleGraph.Walk.isPath_def ] at *;
  exact h_subwalk.nodup hp

/-
Retracting then extending gives back the original walk.
-/
lemma walkRetract_extend {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {v w : V} (p : G.Walk v w) (hp : p.IsPath) (h : 0 < p.length) :
    let ⟨u, q, hadj⟩ := walkRetract p h
    walkExtend q hadj.down = p := by
  rcases p with ( _ | ⟨ h, p ⟩ ) <;> simp_all +decide;
  · contradiction;
  · induction' p with w p hp ih generalizing v;
    · rfl;
    · rename_i h₁ h₂ h₃;
      convert congr_arg ( fun x => Walk.cons h₃ x ) ( h₂ _ _ _ ) using 1;
      aesop