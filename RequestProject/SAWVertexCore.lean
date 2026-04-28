/-
# Vertex relation core infrastructure
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-- Extend a walk by one adjacent step. -/
def walkExtend {v w u : HexVertex} (p : hexGraph.Walk v w) (h : hexGraph.Adj w u) :
    hexGraph.Walk v u :=
  p.append (.cons h .nil)

lemma walkExtend_length {v w u : HexVertex} (p : hexGraph.Walk v w) (h : hexGraph.Adj w u) :
    (walkExtend p h).length = p.length + 1 := by
  unfold walkExtend; simp [SimpleGraph.Walk.length_append]

lemma walkExtend_support {v w u : HexVertex} (p : hexGraph.Walk v w) (h : hexGraph.Adj w u) :
    (walkExtend p h).support = p.support ++ [u] := by
  unfold walkExtend; simp [SimpleGraph.Walk.support_append]

lemma walkExtend_isPath {v w u : HexVertex} (p : hexGraph.Walk v w) (hp : p.IsPath)
    (h : hexGraph.Adj w u) (hu : u ∉ p.support) :
    (walkExtend p h).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, walkExtend_support]
  rw [List.nodup_append]
  exact ⟨hp.support_nodup, List.nodup_singleton u,
    fun a ha b hb => by simp only [List.mem_singleton] at hb; subst hb; exact (fun h => hu (h ▸ ha))⟩

def pathExtend {v w u : HexVertex} (p : hexGraph.Path v w) (h : hexGraph.Adj w u)
    (hu : u ∉ p.1.support) : hexGraph.Path v u :=
  ⟨walkExtend p.1 h, walkExtend_isPath p.1 p.2 h hu⟩

lemma pathExtend_length {v w u : HexVertex} (p : hexGraph.Path v w) (h : hexGraph.Adj w u)
    (hu : u ∉ p.1.support) : (pathExtend p h hu).1.length = p.1.length + 1 :=
  walkExtend_length p.1 h

lemma pathExtend_support {v w u : HexVertex} (p : hexGraph.Path v w) (h : hexGraph.Adj w u)
    (hu : u ∉ p.1.support) : (pathExtend p h hu).1.support = p.1.support ++ [u] :=
  walkExtend_support p.1 h

def sawExtend {start : HexVertex} {n : ℕ} (s : SAW start n)
    {u : HexVertex} (h : hexGraph.Adj s.w u) (hu : u ∉ s.p.1.support) :
    SAW start (n + 1) where
  w := u
  p := pathExtend s.p h hu
  l := by simp [pathExtend_length, s.l]

lemma sawExtend_in_strip {start : HexVertex} {n : ℕ} {T : ℕ} (s : SAW start n)
    {u : HexVertex} (h : hexGraph.Adj s.w u) (hu : u ∉ s.p.1.support)
    (hs : ∀ v ∈ s.p.1.support, PaperInfStrip T v) (hu_strip : PaperInfStrip T u) :
    ∀ v ∈ (sawExtend s h hu).p.1.support, PaperInfStrip T v := by
  intro v hv
  simp only [sawExtend, pathExtend_support] at hv
  rw [List.mem_append] at hv
  rcases hv with h1 | h1
  · exact hs v h1
  · simp only [List.mem_singleton] at h1; subst h1; exact hu_strip

/-! ## Adjacency lemmas -/

lemma false_adj_true_same (x y : ℤ) :
    hexGraph.Adj (x, y, false) (x, y, true) := by
  simp +decide [hexGraph]

lemma false_adj_true_right (x y : ℤ) :
    hexGraph.Adj (x, y, false) (x + 1, y, true) := by
  simp +decide [hexGraph]

lemma false_adj_true_up (x y : ℤ) :
    hexGraph.Adj (x, y, false) (x, y + 1, true) := by
  simp +decide [hexGraph]

lemma true_adj_false_same (x y : ℤ) :
    hexGraph.Adj (x, y, true) (x, y, false) := by
  simp +decide [hexGraph]

lemma true_adj_false_left (x y : ℤ) :
    hexGraph.Adj (x, y, true) (x - 1, y, false) := by
  simp +decide [hexGraph]

lemma true_adj_false_down (x y : ℤ) :
    hexGraph.Adj (x, y, true) (x, y - 1, false) := by
  simp +decide [hexGraph]

end
