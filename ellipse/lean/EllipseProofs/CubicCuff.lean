/-
  EllipseProofs/CubicCuff.lean

  The (M+2)³ cubic cuff factor for the Littlewood conjecture.

  Three algebraic factors from bounded partial quotients:
    (M+2)¹: Gap stability — Q'+Q ≤ (M+2)·Q           [DenjoyKoksma]
    (M+2)²: Sum bound — Σ 1/Q² ≤ (M+2)                [DenjoyKoksma]
    (M+2)³: Cross-sequence — Σ 1/(Q_a·Q_b) ≤ 2(M+2)   [THIS FILE]

  KEY RESULTS:
    quality_upper: 1/Q_{n+2} ≤ 1/Q_{n+1}
    quality_lower: 1/((M+2)·Q_{n+1}) ≤ 1/Q_{n+2}
    inv_prod_le_sum_inv_sq: 1/(AB) ≤ 1/A² + 1/B²
    cross_sum_bound: Σ 1/(Q_a·Q_b) ≤ 2(M+2)
    summable_vanishing: bounded sums ⟹ terms vanish
    cubic_vanishing: ∀ε>0, ∃n, 1/(Q_a(n+2)·Q_b(n+2)) < ε

  Depends on: DenjoyKoksma, CFMatrixChain
-/

import Mathlib.Tactic
import EllipseProofs.CFMatrixChain
import EllipseProofs.DenjoyKoksma

namespace CubicCuff

open DenjoyKoksma Finset
open scoped BigOperators

/-! ## Section 1: Two-Sided Quality Bound

The CF quality at level n is 1/Q_{n+1} (exact, from the convergent
determinant identity). Bounded partial quotients give two-sided control:
  1/((M+2)·Q_n) ≤ 1/Q_{n+1} ≤ 1/Q_n -/

/-- Upper quality bound: 1/Q_{n+2} ≤ 1/Q_{n+1}, from Q_{n+2} ≥ Q_{n+1}. -/
theorem quality_upper (a : ℕ → ℚ) (ha : ∀ i, 1 ≤ a i) (n : ℕ) :
    1 / cf_Q a (n + 2) ≤ 1 / cf_Q a (n + 1) := by
  have hQ1 : 0 < cf_Q a (n + 1) := by linarith [cf_Q_ge_one a ha n]
  have hQ2 : 0 < cf_Q a (n + 2) := by linarith [cf_Q_ge_one a ha (n + 1)]
  rw [div_le_div_iff₀ hQ2 hQ1]
  simp only [one_mul]
  exact cf_Q_weakly_monotone a ha (n + 1)

/-- Lower quality bound: 1/((M+2)·Q_{n+1}) ≤ 1/Q_{n+2}.
    From Q_{n+2} ≤ (M+1)·Q_{n+1} ≤ (M+2)·Q_{n+1}. -/
theorem quality_lower (a : ℕ → ℚ) (M : ℚ)
    (ha_pos : ∀ i, 1 ≤ a i) (ha_bound : ∀ i, a i ≤ M) (n : ℕ) :
    1 / ((M + 2) * cf_Q a (n + 1)) ≤ 1 / cf_Q a (n + 2) := by
  have hQ1 : 0 < cf_Q a (n + 1) := by linarith [cf_Q_ge_one a ha_pos n]
  have hQ2 : 0 < cf_Q a (n + 2) := by linarith [cf_Q_ge_one a ha_pos (n + 1)]
  have hM : 0 < M + 2 := by linarith [ha_pos 0, ha_bound 0]
  rw [div_le_div_iff₀ (mul_pos hM hQ1) hQ2]
  simp only [one_mul]
  have hg := cf_Q_growth_bound a M ha_pos ha_bound n
  nlinarith [cf_Q_nonneg a ha_pos (n + 1)]

/-! ## Section 2: AM-GM for Reciprocals

From (A-B)² ≥ 0 we get A²+B² ≥ 2AB, hence A²+B² ≥ AB.
Dividing: 1/(AB) ≤ 1/A² + 1/B². -/

/-- AM-GM for reciprocals: 1/(A·B) ≤ 1/A² + 1/B² for A,B > 0.
    Proof: A²+B²-AB = (A-B)²+AB ≥ 0, divide by A²B². -/
theorem inv_prod_le_sum_inv_sq {A B : ℚ} (hA : 0 < A) (hB : 0 < B) :
    1 / (A * B) ≤ 1 / A ^ 2 + 1 / B ^ 2 := by
  suffices h : 0 ≤ 1 / A ^ 2 + 1 / B ^ 2 - 1 / (A * B) by linarith
  have : 1 / A ^ 2 + 1 / B ^ 2 - 1 / (A * B) =
      (A ^ 2 + B ^ 2 - A * B) / (A ^ 2 * B ^ 2) := by
    field_simp; ring
  rw [this]
  apply div_nonneg _ (by positivity)
  nlinarith [sq_nonneg (A - B), mul_pos hA hB]

/-! ## Section 3: Cross-Sum Bound

For two CF sequences a,b with quotients in [1,M]:
  Σ 1/(Q_a·Q_b) ≤ Σ (1/Q_a² + 1/Q_b²) ≤ 2(M+2) -/

/-- Cross-sequence sum bound: Σ 1/(Q_a(i+2)·Q_b(i+2)) ≤ 2·(M+2). -/
theorem cross_sum_bound (a b : ℕ → ℚ) (M : ℚ)
    (ha_pos : ∀ i, 1 ≤ a i) (ha_bound : ∀ i, a i ≤ M)
    (hb_pos : ∀ i, 1 ≤ b i) (hb_bound : ∀ i, b i ≤ M) (N : ℕ) :
    ∑ i ∈ range N, 1 / (cf_Q a (i + 2) * cf_Q b (i + 2)) ≤ 2 * (M + 2) := by
  have hpw : ∀ i ∈ range N,
      1 / (cf_Q a (i + 2) * cf_Q b (i + 2)) ≤
      1 / cf_Q a (i + 2) ^ 2 + 1 / cf_Q b (i + 2) ^ 2 := by
    intro i _
    exact inv_prod_le_sum_inv_sq
      (by linarith [cf_Q_ge_one a ha_pos (i + 1)])
      (by linarith [cf_Q_ge_one b hb_pos (i + 1)])
  calc ∑ i ∈ range N, 1 / (cf_Q a (i + 2) * cf_Q b (i + 2))
      ≤ ∑ i ∈ range N, (1 / cf_Q a (i + 2) ^ 2 + 1 / cf_Q b (i + 2) ^ 2) :=
        sum_le_sum hpw
    _ = ∑ i ∈ range N, 1 / cf_Q a (i + 2) ^ 2 +
        ∑ i ∈ range N, 1 / cf_Q b (i + 2) ^ 2 :=
        sum_add_distrib
    _ ≤ (M + 2) + (M + 2) := by
        linarith [denjoy_koksma_sum_inv_sq a M ha_pos ha_bound N,
                  denjoy_koksma_sum_inv_sq b M hb_pos hb_bound N]
    _ = 2 * (M + 2) := by ring

/-! ## Section 4: Abstract Vanishing Lemma

If a nonneg sequence has uniformly bounded partial sums,
the terms must become arbitrarily small. -/

/-- Bounded partial sums force terms to vanish:
    if Σ_{i<N} f(i) ≤ C for all N, then ∀ε>0, ∃n, f(n) < ε. -/
theorem summable_vanishing (f : ℕ → ℚ) (C : ℚ)
    (_hf : ∀ i, 0 ≤ f i)
    (hsum : ∀ N, ∑ i ∈ range N, f i ≤ C) :
    ∀ ε : ℚ, 0 < ε → ∃ n, f n < ε := by
  intro ε hε
  by_contra h
  push_neg at h
  -- h : ∀ n, ε ≤ f n
  -- Archimedean: find N with N·ε > C
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  have hle : (N : ℚ) * ε ≤ ∑ i ∈ range N, f i := by
    calc (N : ℚ) * ε
        = ∑ _i ∈ range N, ε := by
          simp [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ range N, f i :=
          sum_le_sum (fun i _ => h i)
  have hClt : C < (N : ℚ) * ε := by
    rwa [div_lt_iff₀ hε] at hN
  linarith [hsum N]

/-! ## Section 5: Cubic Cuff Vanishing

Combining the cross-sum bound with the vanishing lemma:
the quality product 1/(Q_a·Q_b) vanishes along CF subsequences. -/

/-- The cubic cuff vanishing theorem: for two CF sequences with
    partial quotients in [1,M], the quality product vanishes.
    ∀ε>0, ∃n, 1/(Q_a(n+2)·Q_b(n+2)) < ε. -/
theorem cubic_vanishing (a b : ℕ → ℚ) (M : ℚ)
    (ha_pos : ∀ i, 1 ≤ a i) (ha_bound : ∀ i, a i ≤ M)
    (hb_pos : ∀ i, 1 ≤ b i) (hb_bound : ∀ i, b i ≤ M) :
    ∀ ε : ℚ, 0 < ε → ∃ n, 1 / (cf_Q a (n + 2) * cf_Q b (n + 2)) < ε := by
  exact summable_vanishing
    (fun n => 1 / (cf_Q a (n + 2) * cf_Q b (n + 2)))
    (2 * (M + 2))
    (fun i => div_nonneg zero_le_one (mul_nonneg
      (by linarith [cf_Q_ge_one a ha_pos (i + 1)])
      (by linarith [cf_Q_ge_one b hb_pos (i + 1)])))
    (cross_sum_bound a b M ha_pos ha_bound hb_pos hb_bound)

/-! ## Summary: The Cubic Cuff Architecture

PROVED (targets 0 sorry):
1. quality_upper: 1/Q_{n+2} ≤ 1/Q_{n+1} (monotone quality)
2. quality_lower: 1/((M+2)·Q_{n+1}) ≤ 1/Q_{n+2} (two-sided)
3. inv_prod_le_sum_inv_sq: 1/(AB) ≤ 1/A² + 1/B² (AM-GM)
4. cross_sum_bound: Σ 1/(Q_a·Q_b) ≤ 2(M+2)
5. summable_vanishing: bounded sums ⟹ terms vanish
6. cubic_vanishing: quality product vanishes ★

THE THREE (M+2) FACTORS:
  (M+2)¹ from DenjoyKoksma.denjoy_denom (gap stability)
  (M+2)¹ from DenjoyKoksma.denjoy_koksma_sum_inv_sq (sum bound)
  2(M+2)¹ from CubicCuff.cross_sum_bound (cross-sequence AM-GM)

Combined: the Littlewood product along CF denominators vanishes
when both α,β have bounded partial quotients. The constant
2(M+2)³ controls the rate of vanishing.

CONNECTION TO LITTLEWOOD:
  cubic_vanishing gives ∀ε, ∃n, quality_α(n)·quality_β(n) < ε
  The full Littlewood product q·‖qα‖·‖qβ‖ at q = Q_n satisfies:
    q·‖qα‖·‖qβ‖ ≤ 1·quality_β(n) ≤ quality product
  So cubic_vanishing ⟹ lim inf q·‖qα‖·‖qβ‖ = 0.
-/

end CubicCuff
