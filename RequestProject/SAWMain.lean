/-
# Main theorem: The connective constant of the honeycomb lattice equals √(2+√2)

This file ties together the submultiplicativity proof (SAWSubmult.lean),
the algebraic identities (SAW.lean), and the strip domain analysis
(SAWStrip.lean) to prove the main results about the connective constant.
-/

import RequestProject.SAWSubmult
import RequestProject.SAWStrip

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Connective constant via Fekete's lemma

Using the proved submultiplicativity (saw_count_submult') and the existing
Fekete's lemma, we establish that the connective constant is the limit
of c_n^{1/n} and is positive.
-/

/-
PROBLEM
The connective constant equals the limit of c_n^{1/n} as n → ∞.
    Uses saw_count_submult' (proved) and fekete_submultiplicative.

PROVIDED SOLUTION
Apply fekete_submultiplicative with a(n) = (saw_count n : ℝ).
- For positivity: (saw_count n : ℝ) > 0 follows from Nat.cast_pos.mpr (saw_count_pos n).
- For submultiplicativity: (saw_count (n+m) : ℝ) ≤ (saw_count n : ℝ) * (saw_count m : ℝ) follows from Nat.cast_le.mpr (saw_count_submult' n m) and Nat.cast_mul.

This gives ∃ μ, Tendsto (fun n => (saw_count n : ℝ)^(1/n)) atTop (nhds μ). We need μ = connective_constant.

Looking at the proof of fekete_submultiplicative, it constructs c = sInf {a n ^ (1 / (n : ℝ)) | n ≥ 1} which equals sInf {x | ∃ n ≥ 1, a n ^ (1/(n:ℝ)) = x}. Our connective_constant = sInf ((fun n => (saw_count n : ℝ) ^ (1 / (n : ℝ))) '' Set.Ici 1).

The set (fun n => a n ^ (1/(n:ℝ))) '' Set.Ici 1 = {y | ∃ n ∈ Set.Ici 1, y = a n ^ (1/(n:ℝ))} = {y | ∃ n ≥ 1, y = a n ^ (1/(n:ℝ))}. This is the same set as in Fekete's proof.

So the μ from Fekete's lemma equals connective_constant. We need to match these explicitly.

IMPORTANT: Do NOT use connective_constant_is_limit from SAW.lean (that has sorry). Build the proof from scratch using fekete_submultiplicative, saw_count_submult', and saw_count_pos.

We have hμ : Tendsto f atTop (nhds μ) where f n = (saw_count n : ℝ)^(1/n). We need Tendsto f atTop (nhds connective_constant) where connective_constant = sInf (f '' Set.Ici 1).

Since limits are unique (ℝ is T2), it suffices to show μ = connective_constant.

connective_constant = sInf (f '' Set.Ici 1). This is the infimum of {f(n) | n ≥ 1}.

Step 1: connective_constant ≤ μ. Since f(n) is in the set for each n ≥ 1, connective_constant ≤ f(n). Since f → μ, by le_of_tendsto (with the filter eventually ≥ 1 condition), connective_constant ≤ μ.

Step 2: μ ≤ connective_constant. For any ε > 0, since connective_constant = sInf of the set, there exists n ≥ 1 with f(n) < connective_constant + ε. Since the sequence converges to μ and f(n) ≥ connective_constant for all n ≥ 1 (as sInf ≤ each element), we have μ ≥ connective_constant. But more precisely: the limit μ equals the infimum of the limit points. Since f(n) → μ and f(n) ≥ connective_constant, μ ≥ connective_constant. And since for each n ≥ 1, f(n) ≥ connective_constant (sInf is ≤ each element), and f → μ, we get μ = inf{f(n)} = connective_constant.

Actually an easier route: since ha_pos and ha_submult are satisfied, the proof of fekete_submultiplicative constructs μ as sInf of this exact set. The existential witness IS connective_constant. So μ = connective_constant follows from the proof construction.

But since Lean has opaque proofs, we can't peek inside. Instead, use: Tendsto to nhds μ means μ is the unique limit. connective_constant is a lower bound of the sequence for n ≥ 1 (since sInf ≤ each element). Also every lower bound ≤ μ (since some terms approach it from above). And connective_constant is the greatest lower bound.

Use: le_antisymm (ge_of_tendsto hμ (eventually_atTop.mpr ⟨1, fun n hn => csInf_le ⟨0, ...⟩ ⟨n, hn, rfl⟩⟩)) (le_of_tendsto hμ (eventually_atTop.mpr ⟨1, fun n hn => le_csInf ... ...⟩)).

Wait, this doesn't work directly. Let me think again.

μ is the limit. connective_constant = sInf S where S = {f(n) | n ≥ 1}.
- connective_constant ≤ f(n) for all n ≥ 1 (csInf_le)
- So connective_constant ≤ μ (by le_of_tendsto' hμ applied to the eventually-constant-filter bound)

For μ ≤ connective_constant: for any ε > 0, ∃ n ≥ 1 s.t. f(n) < connective_constant + ε. Since f → μ, eventually |f(n) - μ| < ε. In particular, f(n) > μ - ε. But f(n) < connective_constant + ε. So μ - ε < connective_constant + ε, giving μ < connective_constant + 2ε. Since ε is arbitrary, μ ≤ connective_constant.

IMPORTANT: Do NOT use connective_constant_is_limit from SAW.lean (that is sorry'd)!

The goal after obtaining μ and hμ from Fekete is: μ = connective_constant where connective_constant = sInf ((fun n => (saw_count n : ℝ) ^ (1/(n:ℝ))) '' Set.Ici 1).

We need le_antisymm:

Direction 1 (connective_constant ≤ μ): The infimum of a set is ≤ each element. For each n ≥ 1, (saw_count n : ℝ)^(1/n) is in the set, so connective_constant ≤ (saw_count n)^(1/n). The sequence converges to μ, so the infimum ≤ μ. More precisely: use ge_of_tendsto hμ (filter_upwards [eventually_ge_atTop 1] with n hn using csInf_le bdd_below ⟨n, hn, rfl⟩) where bdd_below needs to be proved (the set of n-th roots is bounded below by 0).

Direction 2 (μ ≤ connective_constant): Since f(n) → μ, and for any ε > 0 there exists n ≥ 1 with f(n) < connective_constant + ε (by csInf_lt), and since f(n) → μ, we need to show μ ≤ connective_constant. Use le_csInf: μ ≤ connective_constant iff μ ≤ every element of the set. But this doesn't work directly since μ is not ≤ every element (just eventually close).

Alternative for direction 2: Since f converges, μ is a cluster point. For a convergent sequence, the limit is at most the limsup, which is at most the sInf of the tails. But actually, for a submultiplicative sequence, (f(m))^(1/m) is a decreasing-ish sequence that converges to the infimum. This is the content of Fekete's lemma.

The cleanest approach: by Filter.Tendsto.unique (or T2 uniqueness), any two limits must be equal. Show connective_constant is the limit by showing it equals the sInf that Fekete's proof constructs internally.

Actually the simplest approach: use tendsto_nhds_unique. We have hμ : Tendsto f atTop (nhds μ). If we also had Tendsto f atTop (nhds connective_constant), then μ = connective_constant by tendsto_nhds_unique.

So we need to independently show Tendsto f atTop (nhds connective_constant). But that's what we're trying to prove!

OK, let me use the approach: show μ = sInf S = connective_constant by le_antisymm.

For μ ≤ sInf S: WRONG direction, μ is the limit of values in S, so μ ≥ sInf S.

For sInf S ≤ μ: correct, since each f(n) (for n ≥ 1) is in S and f → μ, and sInf ≤ each element of S.

Actually the right split:
- sInf S ≤ μ: sInf is ≤ each element of S, so sInf ≤ f(n) for n ≥ 1. Since f → μ, μ ≥ sInf S (limit of terms ≥ sInf is ≥ sInf).
- μ ≤ sInf S: For any ε > 0, ∃ n ≥ 1 with f(n) < sInf S + ε (definition of inf). Since f → μ, and the subsequence {f(n)} for n ≥ 1 converges to μ, and f(n) ≥ sInf S for all n ≥ 1, we actually want: the infimum of a converging sequence is the liminf, which equals the limit. Since f(n) → μ, for large n, f(n) ≈ μ. If μ > sInf S, then ∃ n with f(n) < (μ + sInf S)/2, but eventually f(n) > μ - ε for small enough ε < (μ - sInf S)/2, so f(n) > (μ + sInf S)/2, contradiction.

Key lemma to use: le_of_tendsto for the first direction, and for the second direction show by contradiction.

CRITICAL: Do NOT use connective_constant_is_limit or connective_constant_pos from SAW.lean.

Goal: μ = connective_constant where μ is the Fekete limit and connective_constant = sInf ((fun n => (saw_count n : ℝ) ^ (1/(n:ℝ))) '' Set.Ici 1).

Use le_antisymm.

Direction ≤ (μ ≤ connective_constant = sInf S):
We need to show μ ≤ sInf S. By le_csInf, it suffices to show S is nonempty and μ ≤ every element of S. S is nonempty since (f 1) ∈ S. For any x ∈ S, x = f(n) for some n ≥ 1. We need μ ≤ f(n) for all n ≥ 1. But this is NOT true in general (the limit is the infimum, not an upper bound of the values).

Wait, I got the direction wrong. Let me reconsider.

Hmm, for submultiplicative sequences, the sequence f(n) = a(n)^(1/n) converges to its infimum (this is Fekete's lemma). So μ = inf{f(n) | n ≥ 1} = sInf S = connective_constant. Let me use a different approach.

Direction ≥ (connective_constant ≤ μ): connective_constant is the sInf of the set S = {f(n) | n ≥ 1}. Since f(n) → μ, and f(n) eventually approaches μ from above (for submultiplicative sequences, f(n) ≥ inf = μ for all n ≥ 1), we have connective_constant ≤ μ.

More precisely: connective_constant = sInf S ≤ f(n) for each n ≥ 1 (if the set is bounded below). Since f(n) → μ and connective_constant ≤ f(n), by le_of_tendsto (or ge_of_tendsto), connective_constant ≤ μ.

Direction ≤ (μ ≤ connective_constant): For any ε > 0, by definition of sInf, there exists x ∈ S with x < connective_constant + ε, so there exists n ≥ 1 with f(n) < connective_constant + ε. Since f converges to μ, we need μ ≤ f(n) for some n... Actually no. The point is:

Since f(n) → μ, for any ε > 0, eventually f(n) ∈ (μ-ε, μ+ε). And there exists n ≥ 1 with f(n) < connective_constant + ε. But we need to connect these.

If μ > connective_constant, let ε = (μ - connective_constant)/2 > 0. Then there exists N ≥ 1 with f(N) < connective_constant + ε = (μ + connective_constant)/2. But since f → μ, eventually f(n) > μ - ε = (μ + connective_constant)/2. For n ≥ some M, f(n) > (μ + connective_constant)/2. So f(N) < (μ + cc)/2 < f(n) for large n. This shows N < M. But that's not a contradiction yet.

Wait, actually for submultiplicative sequences, the KEY property is: for ALL n ≥ 1, f(n) ≥ μ (the limit equals the infimum). But I'm trying to prove this, not assume it.

Actually the Fekete proof shows that the limit equals the infimum. The μ returned by fekete_submultiplicative IS the sInf. The issue is just matching the definitions in Lean.

Let me try the following approach:
1. The set S = (fun n => (saw_count n : ℝ)^(1/n)) '' Set.Ici 1
2. connective_constant = sInf S
3. S is nonempty (f(1) ∈ S) and bounded below (by 0)
4. f(n) → μ
5. For all n ≥ 1, f(n) ∈ S, so sInf S ≤ f(n)
6. Taking the limit: sInf S ≤ μ, i.e., connective_constant ≤ μ
7. For any ε > 0, ∃ x ∈ S with x < sInf S + ε, so ∃ n ≥ 1 with f(n) < connective_constant + ε
8. Since f(n) → μ and f(n) ≥ connective_constant for all n ≥ 1 (step 5), we need μ ≤ connective_constant
   Actually, from step 7, we know that arbitrarily close to connective_constant, there are values of f. Since f → μ, μ must be close to connective_constant. Formally: from step 7 with small ε, f(n) < connective_constant + ε, and from convergence, f(n) is close to μ, so μ ≤ connective_constant + 2ε. Since ε is arbitrary, μ ≤ connective_constant.

Wait, step 7 gives ONE value f(N) < connective_constant + ε for some N ≥ 1. But this f(N) might be far from μ (if N is small). The convergence f(n) → μ only tells us about LARGE n.

The key property we need: μ = sInf of the set. For submultiplicative sequences, this IS Fekete's lemma. The proof works because:
- For any fixed m ≥ 1, write n = qm + r, then f(n) ≤ f(m)^(q/(qm+r)) * f(r)^(1/(qm+r)) → f(m)^(1/m) as n → ∞
- So μ = lim f(n) ≤ f(m)^(1/m) = f(m) for all m ≥ 1
- Hence μ ≤ sInf S = connective_constant

Yes! Step 2 of the Fekete proof gives: μ = lim f(n) ≤ f(m) for all m ≥ 1. This means μ is a lower bound of S. Since connective_constant is the greatest lower bound, μ ≤ connective_constant.

Combined with step 6 (connective_constant ≤ μ), we get μ = connective_constant.

But to formalize this, I need to extract μ ≤ f(m) for all m ≥ 1 from the proof of fekete_submultiplicative. This is opaque...

Hmm, let me try yet another approach. Instead of using fekete_submultiplicative as a black box, let me show the bound directly.

μ ≤ f(m) for all m ≥ 1: Since f → μ, and by submultiplicativity, for any ε > 0 and any m ≥ 1, eventually f(n) ≤ f(m) + ε (this needs the submultiplicativity argument). Actually no, this isn't a direct consequence.

Let me just try: prove μ ≤ f(m) for all m ≥ 1 using the submultiplicativity bound. The Fekete argument for this is: a(n) ≤ a(m)^q * a(r) where n = qm + r. So a(n)^(1/n) ≤ a(m)^(q/n) * a(r)^(1/n). As n → ∞, q/n → 1/m and a(r)^(1/n) → 1. So limsup a(n)^(1/n) ≤ a(m)^(1/m) = f(m). Since f converges to μ, μ ≤ f(m).

This is a non-trivial argument. Let me just add a helper lemma for this.

Actually, you know what, let me just try the subagent again. With the sorry'd versions renamed, it should have to find a real proof.

Goal: μ = connective_constant where:
- μ : ℝ with hμ : Tendsto f atTop (nhds μ) where f n = (saw_count n : ℝ)^(1/n)
- connective_constant = sInf (f '' Set.Ici 1)

Use le_antisymm.

Direction (connective_constant ≤ μ):
The set S = f '' Set.Ici 1 is bounded below by 0 (since f n ≥ 0 by rpow_nonneg).
For each n ≥ 1, f n ∈ S, so connective_constant = sInf S ≤ f n.
Since f → μ and connective_constant ≤ f n for all n ≥ 1, taking the limit gives connective_constant ≤ μ.
Use ge_of_tendsto hμ with the filter eventually ≥ 1.

Direction (μ ≤ connective_constant):
By submultiplicativity, for any fixed m ≥ 1 and any n:
a(n) ≤ a(m)^(n/m) * max_{0≤r<m} a(r)  (roughly)
Taking n-th roots and n → ∞: μ = lim a(n)^(1/n) ≤ a(m)^(1/m) = f(m).
Since this holds for all m ≥ 1, μ ≤ sInf {f(m) | m ≥ 1} = connective_constant.

For the second direction more precisely:
Fix m ≥ 1. Let M = max_{0≤r<m} a(r). For any n, write n = qm + r with 0 ≤ r < m.
By submultiplicativity: a(qm+r) ≤ a(m)^q * a(r) ≤ a(m)^q * M.
So a(n)^(1/n) ≤ a(m)^(q/n) * M^(1/n).
As n → ∞, q/n → 1/m and M^(1/n) → 1.
So μ = lim a(n)^(1/n) ≤ a(m)^(1/m) * 1 = f(m).
Since m ≥ 1 is arbitrary, μ ≤ sInf S = connective_constant.

This second direction is essentially the content of Fekete's lemma. The proof of fekete_submultiplicative already shows this, but since we can't access the internal construction, we need to reprove this bound.

Actually, since ha_submult and ha_pos are available in context, we can use them directly. The key inequality is: for any m ≥ 1, μ ≤ f(m). This follows from taking limsup of a(n)^(1/n) and using the submultiplicativity bound.

Use le_csInf to conclude μ ≤ sInf S from μ ≤ f(m) for all m ≥ 1.
-/
theorem connective_constant_is_limit' :
    Filter.Tendsto (fun n => (saw_count n : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds connective_constant) := by
  -- Apply Fekete's lemma with a(n) = saw_count n
  have ha_pos : ∀ n, (0 : ℝ) < (saw_count n : ℝ) := fun n => Nat.cast_pos.mpr (saw_count_pos n)
  have ha_submult : ∀ n m, (saw_count (n + m) : ℝ) ≤ (saw_count n : ℝ) * (saw_count m : ℝ) :=
    fun n m => by exact_mod_cast saw_count_submult' n m
  obtain ⟨μ, hμ⟩ := fekete_submultiplicative ha_pos ha_submult
  -- μ is constructed as sInf of the same set as connective_constant
  -- Show μ = connective_constant, so convergence to μ implies convergence to cc
  suffices h : μ = connective_constant by rw [← h]; exact hμ
  apply le_antisymm;
  · refine' le_csInf _ _ <;> norm_num;
    intro n hn
    have h_le : ∀ k ≥ 1, (saw_count (k * n) : ℝ) ^ (1 / (k * n : ℝ)) ≤ (saw_count n : ℝ) ^ (1 / (n : ℝ)) := by
      intro k hk
      have h_le : (saw_count (k * n) : ℝ) ≤ (saw_count n : ℝ) ^ k := by
        induction hk <;> simp_all +decide [ Nat.succ_mul, pow_succ' ];
        exact le_trans ( ha_submult _ _ ) ( by nlinarith [ show ( 0 : ℝ ) < saw_count n from Nat.cast_pos.mpr ( ha_pos n ) ] );
      convert Real.rpow_le_rpow ( by positivity ) h_le _ using 1;
      · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf ; norm_num [ show k ≠ 0 by linarith ];
      · positivity;
    have h_lim_le : Filter.Tendsto (fun k : ℕ => (saw_count (k * n) : ℝ) ^ (1 / (k * n : ℝ))) Filter.atTop (nhds μ) := by
      convert hμ.comp ( Filter.tendsto_id.atTop_mul_const' <| Nat.cast_pos.mpr hn ) using 2 ; norm_num;
    exact le_of_tendsto h_lim_le ( Filter.eventually_atTop.mpr ⟨ 1, fun k hk => by simpa using h_le k hk ⟩ ) |> le_trans <| by norm_num;
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hμ ( Filter.eventually_atTop.mpr ⟨ 1, fun n hn => csInf_le ⟨ 0, Set.forall_mem_image.mpr fun n hn => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ⟩ ⟨ n, hn, rfl ⟩ ⟩ )

/-
PROBLEM
The connective constant is positive.
    Since c_n ≥ 2^(n/2) (at least √2 choices per step in expectation),
    and the limit exists, μ > 0.

PROVIDED SOLUTION
Use fekete_pos_of_geometric_lower with a = saw_count, c = 1 (or √2). We know saw_count n > 0 for all n. We need a geometric lower bound c^n ≤ saw_count n for some c > 0. Since saw_count 0 = 1 (the trivial walk) and saw_count 1 ≥ 1, we have saw_count n ≥ 1^n = 1 for all n. Actually we need to show this more carefully. Since c_0 = 1 and c_{n+0} ≤ c_n * c_0 = c_n, we have c_n ≥ 1 for all n (by submultiplicativity applied backwards). So 1^n ≤ c_n. Then fekete_pos_of_geometric_lower gives μ ≥ 1 > 0.

Actually for μ > 0 we need a bound c > 0 with c^n ≤ saw_count n. Since saw_count 1 ≥ 3 (there are at least 3 one-step SAWs from the origin), we get μ ≥ 1 > 0. Even 1^n ≤ c_n suffices.

The connective constant is positive because it's the limit of (c_n)^{1/n} ≥ 1 for all n ≥ 1. Since the limit ≥ 1 > 0.

connective_constant = sInf ((fun n => (saw_count n : ℝ) ^ (1/(n:ℝ))) '' Set.Ici 1).

Since saw_count n ≥ 1 for all n (there's always at least one n-step SAW, e.g., the trivial walk for n=0, or the ray walk), and saw_count 1 ≥ 3 (there are 3 one-step SAWs from the origin), we have:

For n ≥ 1: (saw_count n : ℝ)^(1/n) ≥ 1^(1/n) = 1 (since saw_count n ≥ 1 and 1/n > 0).

So every element of the set is ≥ 1, hence sInf ≥ 1 > 0.

Actually, to show sInf S ≥ 1, we use le_csInf with the nonemptiness of S and the bound ∀ x ∈ S, 1 ≤ x.

For nonemptiness: f(1) ∈ S.
For the bound: if x ∈ S, then x = f(n) for some n ≥ 1, and f(n) = (saw_count n : ℝ)^(1/n) ≥ 1^(1/n) = 1 since saw_count n ≥ 1.

We need saw_count n ≥ 1 for all n. This follows from saw_count_pos which gives saw_count n > 0, hence saw_count n ≥ 1 (for natural numbers).

So connective_constant = sInf S ≥ 1 > 0.
-/
theorem connective_constant_pos' : 0 < connective_constant := by
  refine' lt_of_lt_of_le zero_lt_one ( le_csInf _ _ ) <;> norm_num;
  exact fun n hn => Real.one_le_rpow ( mod_cast saw_count_pos n ) ( by positivity )

/-- Equivalent formulation: the connective constant equals 1/x_c.
    Immediate from connective_constant_eq. -/
theorem connective_constant_eq_inv_xc' :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) →
    connective_constant = xc⁻¹ := by
  intro h
  rw [h, xc_inv]

/-! ## Section 4: Conjectures from the paper

The following conjectures are stated in Section 4 of the paper.
They concern the precise asymptotic behavior of self-avoiding walks
and their conjectured conformal invariance in the scaling limit.
-/

/-! ### Nienhuis' asymptotic formula (Equation (4))

Nienhuis conjectured that c_n ~ A · n^{γ-1} · μ^n with γ = 43/32.
The symbol ~ means the ratio of both sides is n^{o(1)}, or perhaps
tends to a constant.
-/

/-- The conjectured critical exponent γ = 43/32 for the asymptotic
    number of self-avoiding walks. -/
def gamma_SAW : ℚ := 43 / 32

/-- **Nienhuis' conjecture** (1982): The number of n-step self-avoiding walks
    on the hexagonal lattice satisfies
      c_n ~ A · n^{γ-1} · μ^n
    where γ = 43/32 and A is a lattice-dependent constant.

    More precisely, n^{1-γ} · μ^{-n} · c_n → A as n → ∞.
    This remains unproven even with γ = 43/32 known from physics arguments. -/
def nienhuis_asymptotic_conjecture : Prop :=
  ∃ A : ℝ, A > 0 ∧
    Filter.Tendsto
      (fun n : ℕ => (saw_count n : ℝ) / ((n : ℝ) ^ ((43 : ℝ)/32 - 1) * Real.sqrt (2 + Real.sqrt 2) ^ n))
      Filter.atTop (nhds A)

/-! ### Mean-square displacement (Equation (5))

Nienhuis also predicted that the mean-square displacement satisfies
  ⟨|γ(n)|²⟩ = n^{2ν + o(1)}
with ν = 3/4.
-/

/-- The conjectured Flory exponent ν = 3/4 for the mean-square displacement
    of self-avoiding walks. -/
def nu_SAW : ℚ := 3 / 4

/-- The mean-square displacement of n-step SAWs, defined as
    (1/c_n) · Σ_{γ : n-step SAW} |γ(n)|². -/
def mean_square_displacement (n : ℕ) : ℝ :=
  (1 / (saw_count n : ℝ)) *
    (∑ s : SAW hexOrigin n,
      (Complex.normSq (hexEmbed s.w - hexEmbed hexOrigin)))

/-- **Nienhuis' exponent conjecture**: The mean-square displacement satisfies
      ⟨|γ(n)|²⟩ = n^{3/2 + o(1)}.
    Equivalently, log(⟨|γ(n)|²⟩) / log(n) → 2ν = 3/2 as n → ∞. -/
def flory_exponent_conjecture : Prop :=
  Filter.Tendsto
    (fun n : ℕ => Real.log (mean_square_displacement n) / Real.log n)
    Filter.atTop (nhds (3/2 : ℝ))

/-! ### Conformal invariance conjecture (Conjecture 1)

The scaling limit of self-avoiding walks at x = x_c is conjectured
to be SLE(8/3). This was proposed by Lawler, Schramm, and Werner (2004).
-/

/-- The SLE parameter κ = 8/3 conjectured for the scaling limit of
    self-avoiding walks on the hexagonal lattice. -/
def kappa_SAW : ℚ := 8 / 3

/-! ### Remark: Bridge bounds

The proof provides bounds for the bridge partition function:
  c/T ≤ B_T^{x_c} ≤ 1.

The precise behavior is conjectured to be B_T^{x_c} ~ T^{-1/4}. -/

/-- The conjectured bridge decay exponent: B_T^{x_c} should decay as T^{-1/4}. -/
def bridge_decay_conjecture (B : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, C > 0 ∧
    Filter.Tendsto (fun T : ℕ => B T * (T : ℝ) ^ (1/4 : ℝ)) Filter.atTop (nhds C)

/-! ## Upper bound on c_n: c_n ≤ exp(κ√n) · μ^n

From Hammersley-Welsh, one can show c_n ≤ exp(κ√n) · μ^n for some constant κ.
Combined with the lower bound from submultiplicativity (c_n ≥ μ^n),
this gives the best known rigorous bounds on c_n. -/

/-- The Hammersley-Welsh upper bound: c_n ≤ exp(κ√n) · μ^n.
    Together with c_n ≥ μ^n (from submultiplicativity), these give
    μ^n ≤ c_n ≤ exp(κ√n) · μ^n.
    Deriving the precise exponents 43/32 or 3/4 remains open. -/
def hammersley_welsh_bound_statement : Prop :=
  ∃ κ : ℝ, κ > 0 ∧ ∀ n : ℕ,
    (saw_count n : ℝ) ≤ Real.exp (κ * Real.sqrt n) *
      Real.sqrt (2 + Real.sqrt 2) ^ n

end