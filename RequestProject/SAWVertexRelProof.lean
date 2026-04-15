/-
# Vertex Relation — Algebraic Components

Algebraic lemmas needed for the vertex relation (Lemma 1 of the paper).

Reference: Section 2 of Duminil-Copin & Smirnov (2012).
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-! ## Triplet and pair cancellation in vertex-relation form -/

/-- Triplet cancellation for the vertex relation. -/
theorem triplet_for_vertex_relation :
    (1 : ℂ) + (xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam = 0 :=
  triplet_cancellation

/-- Pair cancellation for the vertex relation. -/
theorem pair_for_vertex_relation :
    j * conj lam ^ 4 + conj j * lam ^ 4 = (0 : ℂ) :=
  pair_cancellation

/-! ## Direction factor algebraic properties -/

/-- Direction from FALSE to same-cell TRUE is 1. -/
lemma false_dir_same' (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = (1 : ℂ) :=
  false_to_true_dir x y

/-- Interior edge cancellation. -/
theorem interior_edge_cancel (v w : HexVertex) :
    (correctHexEmbed w - correctHexEmbed v) +
    (correctHexEmbed v - correctHexEmbed w) = 0 := by
  ring

/-- Direction sum at FALSE vertex is zero. -/
lemma false_vertex_dir_sum' (x y : ℤ) :
    (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) +
    (correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false)) +
    (correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false)) = 0 :=
  false_vertex_dir_sum x y

/-- Direction sum at TRUE vertex is zero. -/
lemma true_vertex_dir_sum' (x y : ℤ) :
    (correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)) +
    (correctHexEmbed (x - 1, y, false) - correctHexEmbed (x, y, true)) +
    (correctHexEmbed (x, y - 1, false) - correctHexEmbed (x, y, true)) = 0 :=
  true_vertex_dir_sum x y

end
