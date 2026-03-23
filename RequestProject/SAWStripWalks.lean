/-
# Walks restricted to strip domains

Formalization of self-avoiding walks restricted to strip domains S_T,
connecting the abstract partition functions to concrete SAW counts.

This is the key infrastructure needed to bridge the gap between:
- The abstract strip identity (proved in SAWProof/SAWDecomp)
- The concrete partition function Z(x) = Σ c_n · x^n

## Reference

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the hexagonal lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

1. **Strip domain predicates**: Membership in S_T
2. **Restricted walks**: SAWs that stay within a strip
3. **Boundary classification**: Left (α), right (β) boundaries
4. **Partition functions**: B_T as sums over restricted walks
5. **Connection to saw_count**: Restricted walks inject into all SAWs
-/

import RequestProject.SAWBridgeFix

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Strip domain predicates

The strip domain S_T consists of all hex vertices with x-coordinate in [0,T].
-/

/-- A vertex is in the strip S_T if its first coordinate is in [0, T]. -/
def inStripT (T : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T

instance (T : ℕ) (v : HexVertex) : Decidable (inStripT T v) :=
  inferInstanceAs (Decidable (0 ≤ v.1 ∧ v.1 ≤ T))

/-- A walk stays in the strip S_T if all vertices have x-coordinate in [0,T]. -/
def walkInStripT {v w : HexVertex} (p : hexGraph.Walk v w) (T : ℕ) : Prop :=
  ∀ u ∈ p.support, inStripT T u

/-! ## Restricted SAWs

A SAW from hexOrigin restricted to the strip S_T is characterized by
where it ends: left boundary (x=0), right boundary (x=T), or interior.
-/

/-- A SAW from hexOrigin that stays within the strip S_T and ends on the
    right boundary (x = T). This corresponds to the paper's B_T. -/
structure StripBridgeSAW (T : ℕ) where
  /-- The length of the walk -/
  len : ℕ
  /-- The underlying SAW -/
  saw : SAW hexOrigin len
  /-- Endpoint is on right boundary -/
  end_right : saw.w.1 = T
  /-- All vertices stay in the strip -/
  in_strip : ∀ v ∈ saw.p.1.support, inStripT T v

/-! ## Connection: StripBridgeSAW injects into SAW

Each StripBridgeSAW is a particular SAW from hexOrigin, so
the total weight of StripBridgeSAWs is bounded by Z(xc).
-/

/-- StripBridgeSAWs inject into SAWs: different strip bridges
    give different SAWs (since they are literally the same walk). -/
lemma stripBridgeSAW_injective (T : ℕ) :
    Function.Injective (fun (s : StripBridgeSAW T) => (⟨s.len, s.saw⟩ : Σ n, SAW hexOrigin n)) := by
  intro s₁ s₂ h
  simp only [Sigma.mk.inj_iff] at h
  obtain ⟨h_len, h_saw⟩ := h
  cases s₁; cases s₂
  simp_all

/-- Strip bridges of different widths are disjoint: they end at different
    x-coordinates, so the underlying SAWs are different. -/
theorem strip_bridges_disjoint {T₁ T₂ : ℕ} (hT : T₁ ≠ T₂)
    (s₁ : StripBridgeSAW T₁) (s₂ : StripBridgeSAW T₂) :
    s₁.saw.w ≠ s₂.saw.w := by
  intro h
  have h1 := s₁.end_right  -- s₁.saw.w.1 = T₁
  have h2 := s₂.end_right  -- s₂.saw.w.1 = T₂
  rw [h] at h1
  omega

/-! ## Connection: OriginBridge ↔ StripBridgeSAW

An OriginBridge T is essentially the same as a StripBridgeSAW T:
both are SAWs from hexOrigin staying in [0,T] and ending at x=T.
-/

/-- Convert a StripBridgeSAW to an OriginBridge. -/
def stripBridgeToOriginBridge {T : ℕ} (s : StripBridgeSAW T) : OriginBridge T :=
  ⟨⟨hexOrigin, s.saw.w, s.saw.p, by simp [hexOrigin], s.end_right,
    fun v hv => ⟨(s.in_strip v hv).1, (s.in_strip v hv).2⟩⟩, rfl⟩

/-! ## The paper's argument in detail

### From the paper (Section 3, proof of Theorem 1):

"We start by proving that Z(x_c) = +∞, and hence μ ≥ √(2+√2).
Suppose that for some T, E_T^{x_c} > 0. As noted before,
E_{T,L}^{x_c} decreases in L and so
  Z(x_c) ≥ Σ_{L>0} E_{T,L}^{x_c} ≥ Σ_{L>0} E_T^{x_c} = +∞,
which completes the proof."

"Assuming on the contrary that E_T^{x_c} = 0 for all T, we simplify
equation (5) to 1 = c_α·A_T + B_T."

"It follows easily by induction that
  B_T^{x_c} ≥ min[B_1^{x_c}, 1/(c_α·x_c)] / T
for every T ≥ 1, and therefore
  Z(x_c) ≥ Σ_{T>0} B_T^{x_c} = +∞."

### The abstract version is fully proved:
- Case 2 divergence: SAWDecomp.case2_divergence
- Quadratic recurrence: SAWDecomp.quadratic_recurrence_lower_bound
- Harmonic divergence: SAWDecomp.harmonic_not_summable

### The remaining connection:
Show that the concrete StripBridgeSAW partition function equals
the abstract B_T from the strip identity, and that the abstract
strip identity holds for the concrete partition functions.
-/

end
