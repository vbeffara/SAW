/-
# The connective constant of the honeycomb lattice equals √(2+√2)

Formalization of the key algebraic and analytic results from:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653–1665, 2012.

## Overview

The paper proves that the connective constant μ of the hexagonal (honeycomb)
lattice satisfies μ = √(2+√2). The value was conjectured by B. Nienhuis in 1982
using Coulomb gas methods from theoretical physics.

The proof introduces a *parafermionic observable* F(z) for self-avoiding walks,
weighted by a complex phase depending on the winding, and shows that at the
critical fugacity x_c = 1/√(2+√2) and spin σ = 5/8, this observable satisfies
a discrete contour-integral relation (Lemma 1). The relation is then used
in strip domains to bound the partition function from above and below.

## Structure of this file

We formalize:
1. The key constants: x_c, λ, j, σ, c_α, c_ε
2. Basic algebraic properties of these constants
3. The two algebraic identities at the heart of Lemma 1 (the vertex relation):
   - Pair cancellation:   j * conj(λ)⁴ + conj(j) * λ⁴ = 0
   - Triplet cancellation: 1 + x_c * j * conj(λ) + x_c * conj(j) * λ = 0
4. The identity x_c⁻¹ = 2 * cos(π/8)
5. Properties of the boundary coefficients c_α and c_ε
-/

import Mathlib

open Real Complex

noncomputable section

/-! ## Key constants -/

/-- The critical fugacity x_c = 1/√(2+√2), the reciprocal of the connective constant. -/
def xc : ℝ := 1 / Real.sqrt (2 + Real.sqrt 2)

/-- The complex phase λ = exp(-i·5π/24), encoding the weight per turn at σ = 5/8. -/
def lam : ℂ := Complex.exp (-Complex.I * (5 * Real.pi / 24))

/-- The cube root of unity j = exp(i·2π/3), encoding the 120° rotation between
    mid-edges around a vertex of the hexagonal lattice. -/
def j : ℂ := Complex.exp (Complex.I * (2 * Real.pi / 3))

/-- The spin parameter σ = 5/8. -/
def sigma : ℝ := 5 / 8

/-- The boundary coefficient c_α = cos(3π/8) for the left boundary of the strip. -/
def c_alpha : ℝ := Real.cos (3 * Real.pi / 8)

/-- The boundary coefficient c_ε = cos(π/4) = √2/2 for the top/bottom boundaries. -/
def c_eps : ℝ := Real.cos (Real.pi / 4)

/-! ## Basic properties of the constants -/

/-
2 + √2 is positive.
-/
lemma two_add_sqrt_two_pos : (0 : ℝ) < 2 + Real.sqrt 2 := by
  positivity

/-
x_c is positive.
-/
lemma xc_pos : 0 < xc := by
  exact one_div_pos.mpr <| Real.sqrt_pos.mpr <| by positivity;

/-
PROBLEM
The connective constant √(2+√2) equals 2·cos(π/8).
    This identity is used in the triplet cancellation.

PROVIDED SOLUTION
We need √(2+√2) = 2cos(π/8). By the half-angle formula, cos(π/8) = cos(π/4 / 2) = √((1+cos(π/4))/2) = √((1+√2/2)/2) = √((2+√2)/4). So 2cos(π/8) = 2√((2+√2)/4) = √(4·(2+√2)/4) = √(2+√2). Equivalently, square both sides: (2+√2) vs 4cos²(π/8) = 4·(1+cos(π/4))/2 = 2(1+√2/2) = 2+√2.
-/
lemma sqrt_two_add_sqrt_two_eq : Real.sqrt (2 + Real.sqrt 2) = 2 * Real.cos (Real.pi / 8) := by
  rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> norm_num [ mul_div ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg ( 2 + Real.sqrt 2 ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ 2 + Real.sqrt 2 by positivity ) ] ;
  positivity

/-
x_c⁻¹ = √(2+√2).
-/
lemma xc_inv : xc⁻¹ = Real.sqrt (2 + Real.sqrt 2) := by
  unfold xc; norm_num;

/-
c_α is positive.
-/
lemma c_alpha_pos : 0 < c_alpha := by
  exact Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩

/-
c_ε is positive.
-/
lemma c_eps_pos : 0 < c_eps := by
  exact Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩

/-
c_ε = √2/2.
-/
lemma c_eps_eq : c_eps = Real.sqrt 2 / 2 := by
  exact Real.cos_pi_div_four

/-! ## The two key algebraic identities (Lemma 1 of the paper)

These identities are the computational heart of the proof that the parafermionic
observable satisfies the vertex relation (equation (2) in the paper).

Walks contributing to the vertex relation are partitioned into:
- **Pairs**: walks visiting all three mid-edges around a vertex, grouped by
  reversing the loop direction. Their contributions cancel by Identity 1.
- **Triplets**: a walk visiting one mid-edge paired with its two one-step
  extensions. Their contributions cancel by Identity 2.
-/

/-
PROBLEM
**Pair cancellation identity.**
    j · conj(λ)⁴ + conj(j) · λ⁴ = 0.

    This identity ensures that pairs of walks visiting all three mid-edges
    around a vertex v contribute zero to the vertex relation.
    The factor j·conj(λ)⁴ arises from the 120° rotation (j) between mid-edges
    and the winding phase (conj(λ)⁴ = exp(i·5π/6) for a ±4π/3 loop).

PROVIDED SOLUTION
Use the already proved lemmas j_mul_conj_lam_pow_four and conj_j_mul_lam_pow_four. We have j * conj(λ)^4 = -I and conj(j) * λ^4 = I, so their sum is -I + I = 0.
-/
theorem pair_cancellation : j * starRingEnd ℂ lam ^ 4 + starRingEnd ℂ j * lam ^ 4 = 0 := by
  simp +decide [ show j = Complex.exp ( Complex.I * ( 2 * Real.pi / 3 ) ) from rfl, show lam = Complex.exp ( -Complex.I * ( 5 * Real.pi / 24 ) ) from rfl, ← Complex.exp_nat_mul, ← Complex.exp_conj ] ; ring;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring_nf ; norm_num [ mul_div ] ;
  rw [ show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring, show Real.pi * 5 / 6 = Real.pi - Real.pi / 6 by ring ] ; norm_num ; ring;

/-
PROBLEM
**Triplet cancellation identity.**
    1 + x_c · j · conj(λ) + x_c · conj(j) · λ = 0.

    This identity ensures that triplets of walks (one visiting one mid-edge,
    two visiting two mid-edges) contribute zero to the vertex relation.
    This is the *only* place where the critical value x_c = 1/√(2+√2) is used.

    The identity follows from x_c = 1/(2·cos(π/8)) and the expansion:
      j·conj(λ) + conj(j)·λ = 2·Re(j·conj(λ))
        = 2·cos(2π/3 + 5π/24) = 2·cos(7π/8) = -2·cos(π/8).

PROVIDED SOLUTION
Use j_conj_lam_sum which gives j*conj(λ) + conj(j)*λ = ↑(-2*cos(π/8)), and then xc_inv which gives xc⁻¹ = √(2+√2), and sqrt_two_add_sqrt_two_eq which gives √(2+√2) = 2*cos(π/8). So xc = 1/(2*cos(π/8)), and thus xc * (-2*cos(π/8)) = -1. Hence 1 + xc*(j*conj(λ) + conj(j)*λ) = 1 + xc*(-2*cos(π/8)) = 1 - 1 = 0. Rewrite using mul_add to distribute xc.
-/
theorem triplet_cancellation :
    1 + (xc : ℂ) * j * starRingEnd ℂ lam + (xc : ℂ) * starRingEnd ℂ j * lam = 0 := by
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] at * ; ring;
  unfold j lam xc; norm_num [ Complex.exp_re, Complex.exp_im ] ; ring;
  rw [ show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring, show Real.pi * ( 5 / 24 ) = Real.pi / 3 - Real.pi / 8 by ring ] ; norm_num [ Real.sin_sub, Real.cos_sub ] ; ring ; norm_num;
  rw [ mul_inv_cancel₀ ( by positivity ) ] ; ring

/-! ## Intermediate algebraic facts -/

/-
PROBLEM
j · conj(λ)⁴ = -I (used in pair cancellation).

PROVIDED SOLUTION
j·conj(λ)⁴ = exp(i·2π/3)·exp(i·5π/24)⁴ = exp(i·2π/3)·exp(i·20π/24) = exp(i·2π/3)·exp(i·5π/6) = exp(i·(2π/3 + 5π/6)) = exp(i·(4π/6 + 5π/6)) = exp(i·9π/6) = exp(i·3π/2) = -i.
-/
lemma j_mul_conj_lam_pow_four : j * starRingEnd ℂ lam ^ 4 = -Complex.I := by
  -- We know that $j = \exp(i \cdot 2\pi/3)$ and $\lambda = \exp(-i \cdot 5\pi/24)$.
  have h_j : j = Complex.exp (Complex.I * (2 * Real.pi / 3)) := by
    exact?
  have h_lam : lam = Complex.exp (-Complex.I * (5 * Real.pi / 24)) := by
    exact?
  have h_conj_lam : starRingEnd ℂ lam = Complex.exp (Complex.I * (5 * Real.pi / 24)) := by
    norm_num [ h_lam, Complex.ext_iff, Complex.exp_re, Complex.exp_im ]
  rw [h_j, h_conj_lam] at *; ring_nf at *; norm_num [Complex.ext_iff, Complex.exp_re, Complex.exp_im] at *; (
  rw [ ← Complex.exp_nat_mul ] ; ring_nf ; norm_num [ Complex.exp_re, Complex.exp_im, mul_div ] ; ring_nf ; norm_num [ mul_div ] ;
  rw [ show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring, show Real.pi * 5 / 6 = Real.pi - Real.pi / 6 by ring ] ; norm_num ; ring ; norm_num;);

/-
PROBLEM
conj(j) · λ⁴ = I (used in pair cancellation).

PROVIDED SOLUTION
conj(j)·λ⁴ = exp(-i·2π/3)·exp(-i·5π/24)⁴ = exp(-i·2π/3)·exp(-i·20π/24) = exp(-i·2π/3)·exp(-i·5π/6) = exp(-i·(2π/3+5π/6)) = exp(-i·3π/2) = i.
-/
lemma conj_j_mul_lam_pow_four : starRingEnd ℂ j * lam ^ 4 = Complex.I := by
  unfold lam j; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, ← Complex.exp_nat_mul ] ; ring;
  rw [ show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring, show Real.pi * ( 5 / 6 ) = Real.pi - Real.pi / 6 by ring ] ; norm_num ; ring ; norm_num;

/-
PROBLEM
The real part identity: Re(j · conj(λ)) = cos(2π/3 + 5π/24) = cos(7π/8) = -cos(π/8).
    This is the key computation for the triplet cancellation.

PROVIDED SOLUTION
j·conj(λ) = exp(i·2π/3)·exp(i·5π/24) = exp(i·(2π/3 + 5π/24)) = exp(i·(16π/24 + 5π/24)) = exp(i·21π/24) = exp(i·7π/8). So Re(j·conj(λ)) = cos(7π/8) = -cos(π/8).
-/
lemma re_j_conj_lam :
    (j * starRingEnd ℂ lam).re = -Real.cos (Real.pi / 8) := by
  unfold j lam; norm_num [ Complex.exp_re, Complex.exp_im ] ; ring; norm_num [ mul_div ] ;
  rw [ ← Real.cos_add ] ; ring_nf ; norm_num [ mul_div ] ; ring_nf ; (
  rw [ show Real.pi * ( 7 / 8 ) = Real.pi - Real.pi / 8 by ring, Real.cos_pi_sub ] ; norm_num [ Real.sqrt_div_self ] ; ring;);

/-
PROBLEM
j · conj(λ) + conj(j) · λ = -2 · cos(π/8).
    Since conj(j·conj(λ)) = conj(j)·λ, the sum is twice the real part.

PROVIDED SOLUTION
Since conj(j * conj(λ)) = conj(j) * λ, the sum j*conj(λ) + conj(j)*λ = 2 * Re(j*conj(λ)). By re_j_conj_lam, Re(j*conj(λ)) = -cos(π/8). So the sum = 2*(-cos(π/8)) = -2*cos(π/8). Cast to complex.
-/
lemma j_conj_lam_sum :
    j * starRingEnd ℂ lam + starRingEnd ℂ j * lam = ↑(-2 * Real.cos (Real.pi / 8)) := by
  convert congr_arg ( fun x : ℝ => x : ℝ → ℂ ) ( show 2 * ( j * ( starRingEnd ℂ ) lam |> Complex.re ) = -2 * Real.cos ( Real.pi / 8 ) from ?_ ) using 1;
  · norm_num [ Complex.ext_iff ] at *; constructor <;> linarith;
  · rw [ re_j_conj_lam ] ; ring

/-! ## Submultiplicativity and existence of the connective constant

The number c_n of n-step self-avoiding walks satisfies c_{n+m} ≤ c_n · c_m
(submultiplicativity), from which Fekete's lemma gives the existence of
μ = lim_{n→∞} c_n^{1/n}. We state this as a general fact about submultiplicative
sequences.
-/

/-
PROBLEM
**Fekete's lemma** (submultiplicative version): If a sequence satisfies
    a(n+m) ≤ a(n) · a(m) and a(n) > 0 for all n, m, then a(n)^{1/n} converges.

    This is the standard result guaranteeing existence of the connective constant
    for any lattice. When additionally a(1) > 1 (as for SAW counts), the limit
    is positive.

    Note: the limit equals inf_{n≥1} a(n)^{1/n}.

PROVIDED SOLUTION
Set b(n) = log(a(n)). Then b is subadditive: b(n+m) ≤ b(n) + b(m). By Fekete's subadditive lemma, b(n)/n → L = inf{b(n)/n : n ≥ 1} (which could be -∞, but since a is submultiplicative with a(n)>0, b(n)/n is bounded below by b(1) + ... so actually L is finite because b(n) ≤ n*b(1)). Then a(n)^(1/n) = exp(b(n)/n) → exp(L). The key challenge is that Fekete's subadditive lemma may not be directly in Mathlib. Alternative approach: show the sequence a(n)^(1/n) is eventually monotone decreasing or use subsequence arguments. Actually, the classical proof: for any m ≥ 1, write n = qm + r with 0 ≤ r < m. Then b(n) ≤ q*b(m) + b(r), so b(n)/n ≤ q*b(m)/n + b(r)/n. As n → ∞, q/n → 1/m and b(r)/n → 0, so limsup b(n)/n ≤ b(m)/m. Since m is arbitrary, limsup ≤ inf, and liminf ≥ inf trivially, so the limit exists.
-/
theorem fekete_submultiplicative {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n)
    (ha_submult : ∀ n m, a (n + m) ≤ a n * a m) :
    ∃ μ : ℝ, Filter.Tendsto (fun n => a n ^ (1 / (n : ℝ))) Filter.atTop (nhds μ) := by
  -- Let $c = \inf_{n \geq 1} a(n)^{1/n}$.
  set c := sInf {a n ^ (1 / (n : ℝ)) | n ≥ 1} with hc_def;
  -- We need to show that $c \leq a(n)^{1/n} \leq c + \epsilon$ for any $\epsilon > 0$ and sufficiently large $n$.
  have h_bounds : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, c ≤ a n ^ (1 / (n : ℝ)) ∧ a n ^ (1 / (n : ℝ)) ≤ c + ε := by
    -- Fix an arbitrary $\epsilon > 0$.
    intro ε hε_pos;
    -- Choose $m$ such that $a(m)^{1/m} < c + \epsilon / 2$.
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧ a m ^ (1 / (m : ℝ)) < c + ε / 2 := by
      exact by rcases exists_lt_of_csInf_lt ( show { x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ a n ^ ( 1 / ( n : ℝ ) ) = x }.Nonempty from ⟨ _, ⟨ 1, by norm_num, rfl ⟩ ⟩ ) ( lt_add_of_pos_right _ <| half_pos hε_pos ) with ⟨ x, ⟨ n, hn, rfl ⟩, hx ⟩ ; exact ⟨ n, hn, hx ⟩ ;;
    -- By submultiplicativity, we have $a(n) \leq a(m)^q \cdot a(r)$ where $n = qm + r$ and $0 \leq r < m$.
    have h_submult : ∀ n : ℕ, n ≥ m → a n ≤ a m ^ (n / m : ℕ) * a (n % m) := by
      intro n hn; rw [ ← Nat.div_add_mod n m ] ; induction' n / m with k hk IH <;> simp_all +decide [ pow_succ, mul_assoc ] ;
      convert le_trans ( ha_submult ( m * k + n % m ) m ) ( mul_le_mul_of_nonneg_right hk ( le_of_lt ( ha_pos m ) ) ) using 1 ; ring;
      rw [ show ( m * ( k + 1 ) + n % m ) / m = ( m * k + n % m ) / m + 1 from Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith [ Nat.div_add_mod ( m * k + n % m ) m, Nat.mod_lt ( m * k + n % m ) hm.1, Nat.mod_lt n hm.1 ] ) ( Nat.le_div_iff_mul_le hm.1 |>.2 <| by linarith [ Nat.div_mul_le_self ( m * k + n % m ) m, Nat.mod_lt ( m * k + n % m ) hm.1, Nat.mod_lt n hm.1 ] ) ] ; ring;
    -- Taking the $n$-th root of both sides of the inequality $a(n) \leq a(m)^q \cdot a(r)$, we get $a(n)^{1/n} \leq a(m)^{q/n} \cdot a(r)^{1/n}$.
    have h_root : ∀ n : ℕ, n ≥ m → a n ^ (1 / (n : ℝ)) ≤ a m ^ ((n / m : ℕ) / (n : ℝ)) * a (n % m) ^ (1 / (n : ℝ)) := by
      intros n hn
      have h_root : a n ^ (1 / (n : ℝ)) ≤ (a m ^ (n / m : ℕ) * a (n % m)) ^ (1 / (n : ℝ)) := by
        exact Real.rpow_le_rpow ( le_of_lt ( ha_pos _ ) ) ( h_submult _ hn ) ( by positivity );
      convert h_root using 1 ; rw [ Real.mul_rpow ( pow_nonneg ( le_of_lt ( ha_pos _ ) ) _ ) ( le_of_lt ( ha_pos _ ) ) ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( le_of_lt ( ha_pos _ ) ) ] ; ring;
    -- As $n \to \infty$, $(n / m) / n \to 1 / m$ and $a(r)^{1/n} \to 1$ for any fixed $r$.
    have h_lim : Filter.Tendsto (fun n : ℕ => a m ^ ((n / m : ℕ) / (n : ℝ))) Filter.atTop (nhds (a m ^ (1 / (m : ℝ)))) ∧ ∀ r : ℕ, r < m → Filter.Tendsto (fun n : ℕ => a r ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
      constructor;
      · -- We'll use the fact that $(n / m) / n \to 1 / m$ as $n \to \infty$.
        have h_frac : Filter.Tendsto (fun n : ℕ => (n / m : ℕ) / (n : ℝ)) Filter.atTop (nhds (1 / (m : ℝ))) := by
          -- We can use the fact that $(n / m : ℕ) / (n : ℝ) = 1 / m - (n % m : ℕ) / (n : ℝ) * (1 / m)$.
          have h_div : ∀ n : ℕ, n ≥ m → (n / m : ℕ) / (n : ℝ) = 1 / m - (n % m : ℕ) / (n : ℝ) * (1 / m) := by
            intro n hn; rw [ div_mul_eq_mul_div, div_sub_div, div_eq_div_iff ] <;> ring <;> norm_num [ show n ≠ 0 by linarith, show m ≠ 0 by linarith ] ;
            rw [ ← Nat.mod_add_div n m ] ; norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hm.1 ) ] ; ring;
            norm_num [ Nat.add_mul_div_left _ _ ( by linarith : 0 < m ) ] ; ring;
          -- Since $(n % m : ℕ) / (n : ℝ) \to 0$ as $n \to \infty$, we have $(n / m : ℕ) / (n : ℝ) \to 1 / m$.
          have h_mod : Filter.Tendsto (fun n : ℕ => (n % m : ℕ) / (n : ℝ)) Filter.atTop (nhds 0) := by
            exact squeeze_zero ( fun n => by positivity ) ( fun n => mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Nat.le_of_lt <| Nat.mod_lt _ <| by linarith ) <| by positivity ) <| tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop;
          rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem ( Filter.Ici_mem_atTop m ) h_div ) ] ; simpa using tendsto_const_nhds.sub ( h_mod.mul_const _ ) ;
        exact Filter.Tendsto.rpow tendsto_const_nhds h_frac <| Or.inl <| ne_of_gt <| ha_pos m;
      · exact fun r hr => by simpa using tendsto_const_nhds.rpow tendsto_inv_atTop_nhds_zero_nat ( Or.inl <| ne_of_gt <| ha_pos r ) ;
    -- Using the limits, we can find $N$ such that for all $n \geq N$, $a(m)^{(n/m)/n} \cdot a(r)^{1/n} < c + \epsilon$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, a m ^ ((n / m : ℕ) / (n : ℝ)) * a (n % m) ^ (1 / (n : ℝ)) < c + ε := by
      have h_lim_prod : Filter.Tendsto (fun n : ℕ => a m ^ ((n / m : ℕ) / (n : ℝ)) * a (n % m) ^ (1 / (n : ℝ))) Filter.atTop (nhds (a m ^ (1 / (m : ℝ)) * 1)) := by
        refine' Filter.Tendsto.mul h_lim.1 _;
        rw [ Metric.tendsto_nhds ] at *;
        intro ε hε_pos; simp_all +decide [ Nat.mod_eq_of_lt ] ;
        choose! N hN using fun r hr => Metric.tendsto_atTop.mp ( h_lim.2 r hr ) ε hε_pos;
        exact ⟨ Finset.sup ( Finset.range m ) N, fun n hn => hN _ ( Nat.mod_lt _ hm.1 ) _ ( le_trans ( Finset.le_sup ( f := N ) ( Finset.mem_range.mpr ( Nat.mod_lt _ hm.1 ) ) ) hn ) ⟩;
      simpa using h_lim_prod.eventually ( gt_mem_nhds <| by linarith );
    exact ⟨ Max.max m N, fun n hn => ⟨ by exact csInf_le ⟨ 0, by rintro x ⟨ k, hk₁, rfl ⟩ ; exact Real.rpow_nonneg ( le_of_lt ( ha_pos k ) ) _ ⟩ ⟨ n, by linarith [ le_max_left m N ], rfl ⟩, le_trans ( h_root n ( by linarith [ le_max_left m N ] ) ) ( le_of_lt ( hN n ( by linarith [ le_max_right m N ] ) ) ) ⟩ ⟩;
  exact ⟨ c, Metric.tendsto_atTop.mpr fun ε ε_pos => by rcases h_bounds ( ε / 2 ) ( half_pos ε_pos ) with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => abs_lt.mpr ⟨ by linarith [ hN n hn ], by linarith [ hN n hn ] ⟩ ⟩ ⟩

/-
PROBLEM
When a submultiplicative sequence has a geometric lower bound a(n) ≥ c^n
    for some c > 0, the connective constant μ = lim a(n)^{1/n} is at least c.
    For SAW on the hexagonal lattice, c_n ≥ (√2)^n, giving μ ≥ √2 > 0.

PROVIDED SOLUTION
By fekete_submultiplicative, there exists μ with a(n)^(1/n) → μ. We need μ ≥ c. Since c^n ≤ a(n), we get c = (c^n)^(1/n) ≤ a(n)^(1/n) (for n ≥ 1). Since a(n)^(1/n) → μ, and a(n)^(1/n) ≥ c for all n ≥ 1, by the limit comparison μ ≥ c.
-/
theorem fekete_pos_of_geometric_lower {a : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (ha_pos : ∀ n, 0 < a n)
    (ha_submult : ∀ n m, a (n + m) ≤ a n * a m)
    (ha_lower : ∀ n, c ^ n ≤ a n) :
    ∃ μ : ℝ, μ ≥ c ∧ Filter.Tendsto (fun n => a n ^ (1 / (n : ℝ))) Filter.atTop (nhds μ) := by
  obtain ⟨ μ, hμ ⟩ := fekete_submultiplicative ha_pos ha_submult;
  refine' ⟨ μ, le_of_tendsto_of_tendsto tendsto_const_nhds hμ _, hμ ⟩;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using le_trans ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( by positivity ), Real.rpow_one ] ) ( Real.rpow_le_rpow ( by positivity ) ( ha_lower n ) ( by positivity ) )

/-! ## The identity for the strip domain (Lemma 2)

When we sum the vertex relation over all vertices in the strip domain S_{T,L},
the interior contributions cancel telescopically, leaving a boundary identity:

  1 = c_α · A^{x_c}_{T,L} + B^{x_c}_{T,L} + c_ε · E^{x_c}_{T,L}

where A, B, E are partition functions for walks ending on the left, right,
and top/bottom boundaries respectively, all with positive coefficients.

This identity is the bridge between the algebraic vertex relation and the
analytic bounds on the partition function.
-/

/-
The boundary identity (Lemma 2 of the paper) expressed abstractly:
    For any non-negative reals A, B, E satisfying the strip identity,
    we have B ≤ 1 (since all terms are non-negative and c_α, c_ε > 0).

    This is the key bound: the bridge partition function B^{x_c}_T ≤ 1
    for all strip widths T.
-/
theorem bridge_bound_of_strip_identity {A B E : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hid : 1 = c_alpha * A + B + c_eps * E) : B ≤ 1 := by
  -- Since $c_\alpha$ and $c_\varepsilon$ are positive, the terms $c_\alpha \cdot A$ and $c_\varepsilon \cdot E$ are non-negative. Therefore, $B$ must be less than or equal to 1 because adding positive terms to $B$ can't make the sum exceed 1.
  have h_pos : 0 ≤ c_alpha * A ∧ 0 ≤ c_eps * E := by
    exact ⟨ mul_nonneg ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ) hA, mul_nonneg ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ) hE ⟩;
  linarith

/-! ## Lower bound: μ ≥ √(2+√2)

The proof of Z(x_c) = ∞ proceeds by cases:
- If E^{x_c}_T > 0 for some T, then Z(x_c) ≥ Σ_L E^{x_c}_{T,L} = ∞.
- If E^{x_c}_T = 0 for all T, then 1 = c_α · A_T + B_T, and a recurrence
  relation A_{T+1} - A_T ≤ x_c · B_{T+1}² gives B_T ≥ c/T, so
  Z(x_c) ≥ Σ_T B_T = ∞.
-/

/-
PROBLEM
In the case E_T = 0, the recurrence gives B_T ≥ c/T.
    More precisely, if c_α · x_c · B² + B ≥ B' for all consecutive values,
    and B₁ ≥ δ > 0, then B_T ≥ min(δ, 1/(c_α·x_c)) / T.

PROVIDED SOLUTION
By induction on T. The recurrence B_n ≤ c_α·x_c·B_{n+1}² + B_{n+1} means B_{n+1} ≥ B_n / (1 + c_α·x_c·B_{n+1}). Since B_T ≤ 1 by bridge_bound, we have c_α·x_c·B_{n+1} ≤ c_α·x_c, so the denominator is at most 1 + c_α·x_c. One can show by induction that if B_T ≥ δ₀/T where δ₀ = min(δ, 1/(c_α·x_c)), then using the quadratic recurrence B_{T+1} ≥ 1/(c_α·x_c·(T+1)) follows. The key idea: from c_α·x_c·u² + u ≥ v, if v ≥ δ₀/T then u ≥ δ₀/(T+1).
-/
theorem bridge_lower_bound {B : ℕ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hB1 : δ ≤ B 1)
    (hB_pos : ∀ n, 0 < B n)
    (hrec : ∀ n, B n ≤ c_alpha * xc * B (n + 1) ^ 2 + B (n + 1)) :
    ∀ T, 1 ≤ T → min δ (1 / (c_alpha * xc)) / T ≤ B T := by
  intro T hT1
  induction' T, hT1 using Nat.le_induction with T hT ih
  aesop;
  rw [ div_le_iff₀ ( by positivity ) ] at *;
  by_contra h_contra;
  -- By the properties of the minimum function and the recurrence relation, we can derive that $B (T + 1) \geq \frac{1}{c_alpha \cdot xc \cdot (T + 1)}$.
  have h_B_succ : B (T + 1) ≥ 1 / (c_alpha * xc * (T + 1)) := by
    rw [ ge_iff_le, div_le_iff₀ ] <;> norm_num at *;
    · cases ih <;> nlinarith [ hrec T, hB_pos T, hB_pos ( T + 1 ), show 0 < c_alpha * xc from mul_pos ( show 0 < c_alpha from c_alpha_pos ) ( show 0 < xc from xc_pos ) ];
    · exact mul_pos ( mul_pos ( c_alpha_pos ) ( xc_pos ) ) ( by positivity );
  norm_num [ mul_assoc, mul_comm, mul_left_comm ] at *;
  nlinarith [ inv_mul_cancel_left₀ ( by positivity : ( T : ℝ ) + 1 ≠ 0 ) ( c_alpha⁻¹ * xc⁻¹ ) ]

/-! ## Upper bound: μ ≤ √(2+√2)

The upper bound uses the Hammersley-Welsh bridge decomposition:
any self-avoiding walk can be uniquely decomposed into a sequence of bridges
with strictly monotone widths. Combined with B^{x_c}_T ≤ 1, this gives
B^x_T ≤ (x/x_c)^T for x < x_c, and hence:

  Z(x) ≤ 2 · ∏_{T>0} (1 + B^x_T)² < ∞   for x < x_c.
-/

/-
For x < x_c, the bridge partition function decays exponentially.
    Since a bridge of width T has length ≥ T and B^{x_c}_T ≤ 1, we get
    B^x_T ≤ (x/x_c)^T.
-/
theorem bridge_exponential_decay {x : ℝ} (hx : 0 < x) (hxxc : x < xc)
    {BT_xc : ℝ} (hBT : BT_xc ≤ 1) (hBT_pos : 0 ≤ BT_xc) (T : ℕ) :
    (x / xc) ^ T * BT_xc ≤ (x / xc) ^ T := by
  exact mul_le_of_le_one_right ( pow_nonneg ( div_nonneg hx.le ( le_of_lt ( show 0 < xc from by rw [ show xc = 1 / Real.sqrt ( 2 + Real.sqrt 2 ) by rfl ] ; positivity ) ) ) _ ) hBT

/-
PROBLEM
The product ∏_{T≥1} (1 + r^T) converges for 0 ≤ r < 1. This ensures the
    Hammersley-Welsh decomposition gives a finite bound on Z(x) for x < x_c.

PROVIDED SOLUTION
Since 0 ≤ r < 1, the series Σ r^T converges. By the standard result that if Σ aₙ converges with aₙ ≥ 0 then ∏(1+aₙ) converges, we get the result. Try using hasSum_geometric_of_lt_one and relating products to sums via logarithms or direct Mathlib API.
-/
theorem prod_one_add_geometric_converges {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ P : ℝ, 0 < P ∧
      Filter.Tendsto (fun N => ∏ T ∈ Finset.range N, (1 + r ^ (T + 1)))
        Filter.atTop (nhds P) := by
  -- The logarithm of the product is the sum of the logarithms, and since $\sum_{T=1}^\infty r^T$ converges, the sum of the logarithms also converges.
  have h_log_prod : Summable (fun T : ℕ => Real.log (1 + r ^ (T + 1))) := by
    exact Summable.of_nonneg_of_le ( fun n => Real.log_nonneg ( by linarith [ pow_nonneg hr0 ( n + 1 ) ] ) ) ( fun n => Real.log_le_sub_one_of_pos ( by linarith [ pow_nonneg hr0 ( n + 1 ) ] ) ) ( by simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_of_lt_one hr0 hr1 );
  have h_exp_log_prod : Filter.Tendsto (fun N => Real.exp (∑ T ∈ Finset.range N, Real.log (1 + r ^ (T + 1)))) Filter.atTop (nhds (Real.exp (∑' T, Real.log (1 + r ^ (T + 1))))) := by
    exact Real.continuous_exp.continuousAt.tendsto.comp h_log_prod.hasSum.tendsto_sum_nat;
  exact ⟨ _, Real.exp_pos _, h_exp_log_prod.congr fun N => by rw [ Real.exp_sum, Finset.prod_congr rfl fun _ _ => Real.exp_log ( by positivity ) ] ⟩

end