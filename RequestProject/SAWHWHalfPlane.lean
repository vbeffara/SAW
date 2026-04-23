/-
# Half-Plane Walk Decomposition Infrastructure

Formalizes helper lemmas for the Hammersley-Welsh bridge decomposition
from Section 3 of Duminil-Copin & Smirnov (2012).
-/

import Mathlib
import RequestProject.SAWHWCore
import RequestProject.SAWHWDecompProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk width via diagCoord -/

/-- Width of a walk = max diagCoord - min diagCoord over all vertices. -/
def walkWidthDiag {v w : HexVertex} (p : hexGraph.Walk v w) : ℕ :=
  (walkMaxDiagCoord p - walkMinDiagCoord p).toNat

/-- walkMaxDiagCoord ≥ walkMinDiagCoord for any walk. -/
lemma walkMax_ge_walkMin {v w : HexVertex} (p : hexGraph.Walk v w) :
    walkMinDiagCoord p ≤ walkMaxDiagCoord p := by
  have hv := walkMinDiagCoord_le p v p.start_mem_support
  have hv' := walkMaxDiagCoord_ge p v p.start_mem_support
  linarith

/-
Walk width ≤ walk length: each step changes diagCoord by at most 1.
-/
lemma walkWidthDiag_le_length {v w : HexVertex} (p : hexGraph.Walk v w) :
    walkWidthDiag p ≤ p.length := by
  -- We'll use the fact that the walk width is the difference between the maximum and minimum diagonal coordinates, which are integers.
  have h_int_bounds : walkMaxDiagCoord p - walkMinDiagCoord p ≤ p.length := by
    obtain ⟨u_max, hu_max⟩ : ∃ u_max ∈ p.support, diagCoordZ u_max = walkMaxDiagCoord p := walkMaxDiagCoord_achieved p
    obtain ⟨u_min, hu_min⟩ : ∃ u_min ∈ p.support, diagCoordZ u_min = walkMinDiagCoord p := walkMinDiagCoord_achieved p;
    obtain ⟨q₁, q₂, hq⟩ : ∃ q₁ : hexGraph.Walk v u_min, ∃ q₂ : hexGraph.Walk u_min w, p = q₁.append q₂ := by
      exact ⟨ p.takeUntil u_min hu_min.1, p.dropUntil u_min hu_min.1, by simp +decide ⟩;
    by_cases hu_max_q₂ : u_max ∈ q₂.support;
    · have h_walk_q2 : diagCoordZ u_max - diagCoordZ u_min ≤ q₂.length := by
        have := walk_diagCoordZ_bound q₂ u_max hu_max_q₂; aesop;
      simp_all +decide [ walkMaxDiagCoord, walkMinDiagCoord ];
      linarith;
    · obtain ⟨q₁', q₂', hq'⟩ : ∃ q₁' : hexGraph.Walk v u_max, ∃ q₂' : hexGraph.Walk u_max u_min, q₁ = q₁'.append q₂' := by
        exact ⟨ q₁.takeUntil u_max ( by aesop ), q₁.dropUntil u_max ( by aesop ), by aesop ⟩;
      have := walk_diagCoordZ_bound q₂' u_min; simp_all +decide ;
      linarith;
  exact Int.toNat_le.mpr h_int_bounds

/-- A SAW from paperStart of length n has walk width ≤ n. -/
lemma saw_width_le_length (n : ℕ) (s : SAW paperStart n) :
    walkWidthDiag s.p.1 ≤ n := by
  calc walkWidthDiag s.p.1 ≤ s.p.1.length := walkWidthDiag_le_length s.p.1
    _ = n := s.l

/-! ## Prefix/suffix diagCoord bounds -/

/-
In a walk split at a vertex u, the minimum diagCoord of the prefix
    is at most the minimum diagCoord of the full walk.
-/
lemma takeUntil_min_le_full {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support) :
    walkMinDiagCoord p ≤ walkMinDiagCoord (p.takeUntil u hu) := by
  obtain ⟨ z, hz₁, hz₂ ⟩ := walkMinDiagCoord_achieved ( p.takeUntil u hu );
  convert walkMinDiagCoord_le p z _;
  · exact hz₂.symm;
  · convert SimpleGraph.Walk.support_takeUntil_subset p hu hz₁ using 1

/-- Every vertex in a walk's prefix (takeUntil) is also in the full walk. -/
lemma takeUntil_support_subset {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support) :
    ∀ z ∈ (p.takeUntil u hu).support, z ∈ p.support :=
  SimpleGraph.Walk.support_takeUntil_subset p hu

/-- Every vertex in a walk's suffix (dropUntil) is also in the full walk. -/
lemma dropUntil_support_subset {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support) :
    ∀ z ∈ (p.dropUntil u hu).support, z ∈ p.support :=
  SimpleGraph.Walk.support_dropUntil_subset p hu

/-! ## Key property: suffix after last-min vertex is a half-plane walk

If we split a walk at the LAST vertex with minimum diagCoord,
the suffix has all vertices with diagCoord strictly greater than
the minimum. In particular, the first vertex of the suffix
has diagCoord = minDiagCoord + 1, making it a half-plane walk. -/

/-- Vertices after the last minimum have diagCoord > minimum.
    This is the key combinatorial fact for the HW decomposition. -/
lemma suffix_diagCoord_gt_min {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hp : p.IsPath)
    (hu : u ∈ p.support)
    (hu_min : diagCoordZ u = walkMinDiagCoord p)
    (hu_last : ∀ z ∈ (p.dropUntil u hu).support, z ≠ u →
      diagCoordZ z > walkMinDiagCoord p) :
    ∀ z ∈ (p.dropUntil u hu).support, z ≠ u →
      diagCoordZ z ≥ walkMinDiagCoord p + 1 := by
  intro z hz hne
  linarith [hu_last z hz hne]

/-
On the hex lattice, adjacent vertices have diagCoord differing by at most 1.
    If the walk minimum is m and a vertex has diagCoord ≥ m + 1 (not = m),
    then the vertex after it also has diagCoord ≥ m + 1 or = m.
    But if we're past the last vertex with diagCoord = m, it must be ≥ m + 1.
-/
lemma adj_diagCoord_step {v w : HexVertex} (h : hexGraph.Adj v w) :
    diagCoordZ w ∈ ({diagCoordZ v - 1, diagCoordZ v, diagCoordZ v + 1} : Set ℤ) := by
  unfold diagCoordZ; rcases v with ⟨ x₁, y₁, b₁ ⟩ ; rcases w with ⟨ x₂, y₂, b₂ ⟩ ; simp_all +decide [ hexGraph ] ;
  omega

end