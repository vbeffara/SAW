/-
# Discrete Stokes Theorem for the Strip Identity

This file provides the abstract double-counting / discrete Stokes lemma.
-/

import Mathlib

open Finset

/-
Abstract discrete Stokes theorem for finite graphs with symmetric adjacency.

Given a finite set V, symmetric neighbor function N, and antisymmetric f,
if ∑_{w∈N(v)} f(v,w) = 0 for each v ∈ V, then ∑_{v∈V} ∑_{w∈N(v)\V} f(v,w) = 0.
-/
theorem discrete_stokes_abstract
    {α : Type*} [DecidableEq α]
    (V : Finset α) (N : α → Finset α)
    (f : α → α → ℂ)
    (h_sym_N : ∀ v w, w ∈ N v → v ∈ N w)
    (h_antisym : ∀ v w, f v w = -f w v)
    (h_vertex : ∀ v ∈ V, ∑ w ∈ N v, f v w = 0) :
    ∑ v ∈ V, ∑ w ∈ (N v).filter (· ∉ V), f v w = 0 := by
  -- To prove the equality, we can use the fact that pairs $(v, w)$ with $v \in V$ and $w \in V$ cancel out in the sum.
  have h_symm : ∑ v ∈ V, ∑ w ∈ N v with w ∈ V, f v w = 0 := by
    have h_sum_zero : ∑ v ∈ V, ∑ w ∈ N v with w ∈ V, f v w = ∑ v ∈ V, ∑ w ∈ N v with w ∈ V, -f v w := by
      rw [ Finset.sum_sigma', Finset.sum_sigma' ];
      apply Finset.sum_bij (fun x _ => ⟨x.snd, x.fst⟩);
      · simp +contextual [ h_sym_N ];
      · grind;
      · simp +contextual;
        exact fun b hb₁ hb₂ hb₃ => ⟨ _, _, ⟨ hb₃, h_sym_N _ _ hb₂, hb₁ ⟩, rfl ⟩;
      · exact fun a ha => h_antisym _ _;
    norm_num at *; linear_combination h_sum_zero / 2;
  convert congr_arg₂ ( · - · ) ( Finset.sum_congr rfl h_vertex ) h_symm using 1;
  · simp +decide [ Finset.sum_ite, Finset.filter_not ];
  · norm_num