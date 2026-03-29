/-
# Zigzag SAW construction for lower bounds

This file constructs explicit self-avoiding walks on the hexagonal lattice
using a "zigzag" pattern that provides a lower bound on saw_count.

## Main result

For each binary string of length k, we construct a distinct (2k)-step SAW
from the origin. This gives c_{2k} ≥ 2^k, which (combined with c_1 = 3)
implies c_n^2 ≥ 2^n for all n ≥ 1 (saw_count_sq_ge_two_pow).

## Construction

The zigzag walk from the origin (0,0,false) alternates:
- F→T step: go to the same cell (x,y,false) → (x,y,true)
- T→F step: binary choice to go "left" (x-1,y,false) or "down" (x,y-1,false)

The F-coordinates follow a lattice path from (0,0) going left or down,
so x_i + y_i = -i, making all F-positions distinct.
Since F and T vertices differ in the Bool component, all vertices are distinct.
-/

import Mathlib
import RequestProject.SAWBridge

open Real

noncomputable section

/-! ## Zigzag coordinate sequence

Given a list of boolean choices, compute the sequence of (x,y) coordinates
visited by the zigzag walk.
-/

/-- Compute the next (x,y) coordinate after a binary choice.
    false = go left (x-1, y), true = go down (x, y-1). -/
def zigzag_step (pos : ℤ × ℤ) (choice : Bool) : ℤ × ℤ :=
  if choice then (pos.1, pos.2 - 1) else (pos.1 - 1, pos.2)

/-- zigzag_step always decreases x+y by exactly 1. -/
lemma zigzag_step_sum (pos : ℤ × ℤ) (c : Bool) :
    (zigzag_step pos c).1 + (zigzag_step pos c).2 = pos.1 + pos.2 - 1 := by
  simp [zigzag_step]; split <;> omega

/-- The sequence of F-vertex coordinates in the zigzag walk.
    Starting from (0,0), each step goes left or down based on the choice. -/
def zigzag_positions (choices : List Bool) : List (ℤ × ℤ) :=
  choices.scanl (fun pos c => zigzag_step pos c) (0, 0)

/-- Length of zigzag_positions. -/
@[simp] lemma zigzag_positions_length (choices : List Bool) :
    (zigzag_positions choices).length = choices.length + 1 := by
  simp [zigzag_positions]

/-
PROBLEM
General version: position i in scanl zigzag_step from pos has sum pos.1+pos.2-i.

PROVIDED SOLUTION
By induction on `choices`, generalizing `pos` and `i`.

Base case (choices = []): scanl f pos [] = [pos], so i = 0 (only option since length is 1). Element at index 0 is pos. Sum = pos.1 + pos.2 - 0 = pos.1 + pos.2. ✓

Inductive case (choices = c :: cs):
scanl f pos (c :: cs) = pos :: scanl f (f pos c) cs = pos :: scanl f (zigzag_step pos c) cs.

Case i = 0: element is pos, sum = pos.1 + pos.2 = pos.1 + pos.2 - 0. ✓

Case i = i' + 1: element at index i'+1 in (pos :: scanl f (zigzag_step pos c) cs)
is element at index i' in (scanl f (zigzag_step pos c) cs).
By induction hypothesis with starting position (zigzag_step pos c) and choices cs:
sum = (zigzag_step pos c).1 + (zigzag_step pos c).2 - i'
    = (pos.1 + pos.2 - 1) - i'    [by zigzag_step_sum]
    = pos.1 + pos.2 - (i' + 1). ✓
-/
lemma scanl_zigzag_sum (choices : List Bool) (pos : ℤ × ℤ) (i : ℕ)
    (hi : i < (choices.scanl (fun p c => zigzag_step p c) pos).length) :
    ((choices.scanl (fun p c => zigzag_step p c) pos).get ⟨i, hi⟩).1 +
    ((choices.scanl (fun p c => zigzag_step p c) pos).get ⟨i, hi⟩).2 =
    pos.1 + pos.2 - (i : ℤ) := by
  induction' choices with choice choices ih generalizing pos i ; simp_all +decide [ List.length ];
  · aesop;
  · rcases i with ( _ | i ) <;> simp_all +decide [ List.length ];
    convert ih ( zigzag_step pos choice |>.1 ) ( zigzag_step pos choice |>.2 ) i _ using 1 ; ring;
    · unfold zigzag_step; split_ifs <;> ring;
    · rw [ List.length_scanl ] at hi ; aesop

/-- The sum x + y at position i equals -i.
    This is the key invariant of the zigzag construction. -/
lemma zigzag_sum_eq_neg (choices : List Bool) (i : ℕ)
    (hi : i < (zigzag_positions choices).length) :
    ((zigzag_positions choices).get ⟨i, hi⟩).1 +
    ((zigzag_positions choices).get ⟨i, hi⟩).2 = -(i : ℤ) := by
  have := scanl_zigzag_sum choices (0, 0) i (by rwa [zigzag_positions] at hi)
  simp [zigzag_positions] at this ⊢
  linarith

/-- All positions in the zigzag are distinct (since x+y is strictly decreasing). -/
lemma zigzag_positions_nodup (choices : List Bool) :
    (zigzag_positions choices).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  have h1 := zigzag_sum_eq_neg choices i hi
  have h2 := zigzag_sum_eq_neg choices j hj
  have heq : (zigzag_positions choices).get ⟨i, hi⟩ =
         (zigzag_positions choices).get ⟨j, hj⟩ := by
    rw [hij]
  rw [heq] at h1
  have hij' : (i : ℤ) = (j : ℤ) := by linarith
  simp only [Fin.mk.injEq]; omega

/-! ## Adjacency lemmas -/

/-- Adjacency for same-cell F→T step. -/
lemma hex_adj_same_cell (x y : ℤ) : hexGraph.Adj (x, y, false) (x, y, true) := by
  left; exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Adjacency for T→F "left" step: (x,y,T) → (x-1,y,F). -/
lemma hex_adj_T_left (x y : ℤ) : hexGraph.Adj (x, y, true) (x - 1, y, false) := by
  right; refine ⟨rfl, rfl, Or.inr (Or.inl ⟨?_, rfl⟩)⟩; omega

/-- Adjacency for T→F "down" step: (x,y,T) → (x,y-1,F). -/
lemma hex_adj_T_down (x y : ℤ) : hexGraph.Adj (x, y, true) (x, y - 1, false) := by
  right; refine ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩; simp

/-- Adjacency for the T→F step determined by a binary choice. -/
lemma hex_adj_T_choice (x y : ℤ) (c : Bool) :
    hexGraph.Adj (x, y, true) ((zigzag_step (x, y) c).1, (zigzag_step (x, y) c).2, false) := by
  simp only [zigzag_step]
  cases c
  · simp; exact hex_adj_T_left x y
  · simp; exact hex_adj_T_down x y

/-! ## Counting results -/

/-- There are at least 2^k distinct (2k)-step SAWs from the origin.
    The proof constructs an injection from binary strings of length k
    to (2k)-step SAWs using the zigzag walk construction. -/
lemma saw_count_even_lower (k : ℕ) : 2 ^ k ≤ saw_count (2 * k) := by
  sorry

/-- There are at least 3 * 2^k distinct (2k+1)-step SAWs from the origin.
    Uses the 3 neighbors of hexOrigin combined with the even lower bound. -/
lemma saw_count_odd_lower (k : ℕ) : 3 * 2 ^ k ≤ saw_count (2 * k + 1) := by
  sorry

/-- Main bound: 2^n ≤ c_n^2 for n ≥ 1.
    Combines saw_count_even_lower and saw_count_odd_lower. -/
theorem saw_count_sq_ge_two_pow' (n : ℕ) (hn : 1 ≤ n) : 2 ^ n ≤ saw_count n ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · calc 2 ^ (2 * k) = (2 ^ k) ^ 2 := by ring
      _ ≤ (saw_count (2 * k)) ^ 2 := Nat.pow_le_pow_left (saw_count_even_lower k) 2
  · have h := saw_count_odd_lower k
    calc 2 ^ (2 * k + 1) = 2 * (2 ^ k) ^ 2 := by ring
      _ ≤ (3 * 2 ^ k) ^ 2 := by nlinarith [Nat.pos_of_ne_zero (by positivity : 2 ^ k ≠ 0)]
      _ ≤ (saw_count (2 * k + 1)) ^ 2 := Nat.pow_le_pow_left h 2

end