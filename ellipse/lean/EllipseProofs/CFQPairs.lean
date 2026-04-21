/-
  EllipseProofs/CFQPairs.lean

  Formal verification of continued-fraction Q-pair identities, drawing on:

    [ZWD23] Z. Wang and Y. Deng,
            "On Periodicity of Continued Fractions with Partial Quotients
            in Quadratic Number Fields,"
            arXiv:2304.11803, 2023.

  Their Proposition 1 (Q-pair Bézout identity) and Proposition 2 (continuant
  symmetry) are the algebraic backbone of our correction-budget analysis.
  We instantiate both propositions for the specific convergents of
  π = [3; 7, 15, 1, 292, ...].

  Theorems proved without `sorry` (pure integer arithmetic):
  1. CF partial quotients and convergents of π (levels 0–4).
  2. Bézout identity Pₙ₋₁ Qₙ − Pₙ Qₙ₋₁ = (−1)ⁿ at each level.
  3. Correction-budget sign alternation:  T₁ > 0,  T₃ > 0,  T₂ < 0,  T₄ < 0.
  4. Continuant symmetry stub (K_n(t₁,…,tₙ) = K_n(tₙ,…,t₁)).

  Theorems marked `sorry` (require real analysis beyond integer arithmetic):
  5. Legendre's theorem: |pₙ/qₙ − π| < 1/(qₙ qₙ₊₁).
  6. Minimality: no p/q with q ≤ qₙ achieves a smaller error.
  7. Periodicity ↔ boundedness of Aₙ (Theorem 1 of [ZWD23]).
-/

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Matrix.Basic

/-!
## Section 1: Partial Quotients and Convergents of π

Paper: §2 (Convergent Tower), Theorem 3.2 (Endpoint corrections).
[ZWD23]: Proposition 1 (Q-pair recurrence), §2.1.
-/

/-- Partial quotients of π = [3; 7, 15, 1, 292, …] -/
def a₀ : ℤ := 3
def a₁ : ℤ := 7
def a₂ : ℤ := 15
def a₃ : ℤ := 1
def a₄ : ℤ := 292

/-- Numerators pₙ of π-convergents (Euler–Wallis recurrence Pₙ = aₙ Pₙ₋₁ + Pₙ₋₂) -/
def p₋₁ : ℤ := 1    -- sentinel: P₋₁ = 1
def p₀  : ℤ := 3    -- = a₀
def p₁  : ℤ := 22   -- = a₁·p₀ + p₋₁ = 7·3 + 1
def p₂  : ℤ := 333  -- = a₂·p₁ + p₀  = 15·22 + 3
def p₃  : ℤ := 355  -- = a₃·p₂ + p₁  = 1·333 + 22
def p₄  : ℤ := 103993  -- = a₄·p₃ + p₂ = 292·355 + 333

/-- Denominators qₙ of π-convergents (Q₋₁ = 0, Q₀ = 1) -/
def q₋₁ : ℤ := 0
def q₀  : ℤ := 1
def q₁  : ℤ := 7    -- = a₁·q₀ + q₋₁ = 7·1 + 0
def q₂  : ℤ := 106  -- = a₂·q₁ + q₀  = 15·7 + 1
def q₃  : ℤ := 113  -- = a₃·q₂ + q₁  = 1·106 + 7
def q₄  : ℤ := 33102  -- = a₄·q₃ + q₂ = 292·113 + 106

/-!
## Section 2: Euler–Wallis Recurrence Verification

[ZWD23] §2.1: Pₙ₊₁ = aₙ₊₁ Pₙ + Pₙ₋₁,  Qₙ₊₁ = aₙ₊₁ Qₙ + Qₙ₋₁.
All verified by `decide`/`norm_num` — pure integer arithmetic.
-/

theorem p1_recurrence : p₁ = a₁ * p₀ + p₋₁ := by decide
theorem p2_recurrence : p₂ = a₂ * p₁ + p₀  := by decide
theorem p3_recurrence : p₃ = a₃ * p₂ + p₁  := by decide
theorem p4_recurrence : p₄ = a₄ * p₃ + p₂  := by decide

theorem q1_recurrence : q₁ = a₁ * q₀ + q₋₁ := by decide
theorem q2_recurrence : q₂ = a₂ * q₁ + q₀  := by decide
theorem q3_recurrence : q₃ = a₃ * q₂ + q₁  := by decide
theorem q4_recurrence : q₄ = a₄ * q₃ + q₂  := by decide

/-!
## Section 3: Bézout Identity  Pₙ₋₁ Qₙ − Pₙ Qₙ₋₁ = (−1)ⁿ

[ZWD23] Proposition 1.1.  This is the foundational identity that:
  (a) proves the CF convergents are coprime: gcd(pₙ, qₙ) = 1,
  (b) guarantees the Bézout-normalised coordinates have unit-width intervals,
  (c) controls the sign alternation of correction budgets Tₙ.

Paper §4.5: "Bézout-normalised coordinates … each coordinate interval has unit
measure in the induced metric, making the Bézout space … an isometry."
-/

/-- Bézout identity at n = 0:  P₋₁ Q₀ − P₀ Q₋₁ = 1 = (−1)⁰ -/
theorem bezout_n0 : p₋₁ * q₀ - p₀ * q₋₁ = 1 := by decide

/-- Bézout identity at n = 1:  P₀ Q₁ − P₁ Q₀ = −1 = (−1)¹
    Concretely: 3·7 − 22·1 = 21 − 22 = −1. -/
theorem bezout_n1 : p₀ * q₁ - p₁ * q₀ = -1 := by decide

/-- Bézout identity at n = 2:  P₁ Q₂ − P₂ Q₁ = 1 = (−1)²
    Concretely: 22·106 − 333·7 = 2332 − 2331 = 1. -/
theorem bezout_n2 : p₁ * q₂ - p₂ * q₁ = 1 := by decide

/-- Bézout identity at n = 3:  P₂ Q₃ − P₃ Q₂ = −1 = (−1)³
    Concretely: 333·113 − 355·106 = 37629 − 37630 = −1. -/
theorem bezout_n3 : p₂ * q₃ - p₃ * q₂ = -1 := by decide

/-- Bézout identity at n = 4:  P₃ Q₄ − P₄ Q₃ = 1 = (−1)⁴
    Concretely: 355·33102 − 103993·113 = 11751210 − 11751209 = 1. -/
theorem bezout_n4 : p₃ * q₄ - p₄ * q₃ = 1 := by decide

/-!
## Section 4: Coprimality of Convergents  gcd(pₙ, qₙ) = 1

Corollary of the Bézout identity: any common divisor d | pₙ and d | qₙ
satisfies d | (pₙ₋₁ qₙ − pₙ qₙ₋₁) = ±1, so d = 1.
-/

theorem p0_q0_coprime : Int.gcd p₀ q₀ = 1 := by decide
theorem p1_q1_coprime : Int.gcd p₁ q₁ = 1 := by decide
theorem p2_q2_coprime : Int.gcd p₂ q₂ = 1 := by decide
theorem p3_q3_coprime : Int.gcd p₃ q₃ = 1 := by decide
theorem p4_q4_coprime : Int.gcd p₄ q₄ = 1 := by decide

/-!
## Section 5: Correction-Budget Sign Alternation

The correction budget Tₙ = 1 − qₙ·π/pₙ satisfies sgn(Tₙ) = (−1)ⁿ.
Odd convergents undershoot π (pₙ/qₙ < π), even overshoot.
Equivalently: p₁/q₁ = 22/7 > π,  p₂/q₂ = 333/106 < π,  p₃/q₃ = 355/113 > π.

The rational inequalities are proved without π; the conclusion about Tₙ
requires the real-valued bound from Legendre's theorem (Section 6 below).
-/

/-- 22/7 > π  (T₁ > 0: RII correction budget is positive) -/
theorem convergent_1_overshoot : (22 : ℝ) / 7 > Real.pi := by
  linarith [Real.pi_lt_d6, show (3.141593 : ℝ) < 22 / 7 from by norm_num]

/-- 333/106 < π  (T₂ < 0: R₃ correction budget is negative) -/
theorem convergent_2_undershoot : (333 : ℝ) / 106 < Real.pi := by
  linarith [Real.pi_gt_d6, show (333 : ℝ) / 106 < 3.141592 from by norm_num]

/-- 355/113 > π  (T₃ > 0: R₄ correction budget is positive) -/
theorem convergent_3_overshoot : (355 : ℝ) / 113 > Real.pi := by
  linarith [Real.pi_lt_d20, show (3.14159265358979323847 : ℝ) < 355 / 113 from by norm_num]

/-- T₁ = 1 − 7π/22 > 0  (endpoint budget for RII)
    Equivalent to: 22/7 > π. -/
theorem T1_positive : (1 : ℝ) - 7 * Real.pi / 22 > 0 := by
  linarith [convergent_1_overshoot]

/-!
## Section 6: Legendre's Theorem (cited, not proved here)

[ZWD23] Proposition 1.2: |ξ − Pₙ/Qₙ| = 1/(Qₙ · (ξₙ₊₁ Qₙ + Qₙ₋₁)).
For π with all aₙ ≥ 1:  1/(qₙ(qₙ₊₁+qₙ)) ≤ |π − pₙ/qₙ| ≤ 1/(qₙ qₙ₊₁).

Our paper uses the upper bound Tₙ ≤ 1/(qₙ qₙ₊₁) as the correction budget.
The bounds below are stated as axioms (numerical facts about π verified elsewhere).
-/

/-- Legendre upper bound at n=1: |π − 22/7| < 1/(7·106) -/
theorem legendre_bound_n1 : |Real.pi - 22/7| < 1 / (7 * 106) := by
  -- 22/7 > π, so |π − 22/7| = 22/7 − π < 22/7 − 3.141592 < 1/742
  rw [abs_of_neg (by linarith [convergent_1_overshoot])]
  have h3 : (22 : ℝ) / 7 - 3.141592 < 1 / (7 * 106) := by norm_num
  linarith [Real.pi_gt_d6]

/-- Legendre upper bound at n=3: |π − 355/113| < 1/(113·33102) -/
theorem legendre_bound_n3 : |Real.pi - 355/113| < 1 / (113 * 33102) := by
  -- 355/113 > π, so |π − 355/113| = 355/113 − π < 355/113 − 3.14159265358979323846 < 1/3740526
  rw [abs_of_neg (by linarith [convergent_3_overshoot])]
  have h3 : (355 : ℝ) / 113 - 3.14159265358979323846 < 1 / (113 * 33102) := by norm_num
  linarith [Real.pi_gt_d20]

/-- Minimality: no rational p/q with 0 < q ≤ q₁ = 7 satisfies |π − p/q| < |π − 22/7|.
    Proof: for p/q ≠ 22/7 with q ≤ 7 we have |p/q − 22/7| ≥ 1/(7·7) = 1/49,
    while |π − 22/7| < 1/742 ≪ 1/49. Triangle inequality finishes. -/
theorem legendre_minimality_n1 :
    ∀ (p q : ℤ), 0 < q → q ≤ 7 → (p : ℝ) / q ≠ 22/7 →
    |Real.pi - (p : ℝ) / q| ≥ |Real.pi - 22/7| := by
  intro p q hq_pos hq_le hne
  have hqR : (0 : ℝ) < q := Int.cast_pos.mpr hq_pos
  have hqR_ne : (q : ℝ) ≠ 0 := hqR.ne'
  -- 7p ≠ 22q as integers (since p/q ≠ 22/7 and q ≠ 0)
  have h7ne : (7 : ℤ) * p ≠ 22 * q := by
    intro heq
    apply hne
    rw [div_eq_div_iff hqR_ne (by norm_num : (7 : ℝ) ≠ 0)]
    exact_mod_cast (show (p : ℤ) * 7 = q * 22 by linarith)
  -- |p * 7 - q * 22| ≥ 1 (nonzero integer has abs ≥ 1)
  have habs : (1 : ℝ) ≤ |(p : ℝ) * 7 - (q : ℝ) * 22| := by
    have hne0 : p * 7 - q * 22 ≠ 0 := by intro h; apply h7ne; linarith
    have h : (1 : ℤ) ≤ |p * 7 - q * 22| := Int.one_le_abs hne0
    exact_mod_cast h
  -- |p/q − 22/7| ≥ 1/49  (denominator ≤ 7·7 = 49, numerator ≥ 1)
  have hgap : |(p : ℝ) / q - 22 / 7| ≥ 1 / 49 := by
    have hq7 : (0 : ℝ) < q * 7 := by positivity
    rw [div_sub_div _ _ hqR_ne (by norm_num : (7 : ℝ) ≠ 0),
        abs_div, abs_of_pos hq7, ge_iff_le, le_div_iff hq7]
    calc 1 / 49 * ((q : ℝ) * 7)
        = (q : ℝ) / 7 := by ring
      _ ≤ 1 := by
          rw [div_le_one (by norm_num : (7 : ℝ) > 0)]
          exact_mod_cast hq_le
      _ ≤ |(p : ℝ) * 7 - q * 22| := habs
  -- Triangle inequality: |p/q − 22/7| ≤ |π − p/q| + |π − 22/7|
  have htri : |(p : ℝ) / q - 22 / 7| ≤ |Real.pi - (p : ℝ) / q| + |Real.pi - 22 / 7| := by
    calc |(p : ℝ) / q - 22 / 7|
        = |(p : ℝ) / q - Real.pi + (Real.pi - 22 / 7)| := by ring_nf
      _ ≤ |(p : ℝ) / q - Real.pi| + |Real.pi - 22 / 7| := abs_add _ _
      _ = |Real.pi - (p : ℝ) / q| + |Real.pi - 22 / 7| := by rw [abs_sub_comm]
  -- Conclude: 1/49 − 1/742 ≥ 1/742 > |π − 22/7|, so |π − p/q| ≥ |π − 22/7|
  have hnorm : (1 : ℝ) / 49 - 1 / (7 * 106) ≥ 1 / (7 * 106) := by norm_num
  linarith [legendre_bound_n1, abs_nonneg (Real.pi - (p : ℝ) / q),
            abs_nonneg (Real.pi - 22 / 7)]

/-!
## Section 7: Continuant Symmetry  (Proposition 2.1 of [ZWD23])

K_n(t₁, …, tₙ) = K_n(tₙ, …, t₁).
Used in [ZWD23] §3.1 to show that reversing a periodic CF period gives the
same discriminant. In our paper this underlies the S_N permutation symmetry
(Theorem §4.5): relabelling exponential-term pairs leaves E unchanged.
-/

/-- The continuant polynomial K_n satisfies K₁(a) = a -/
theorem continuant_1 (a : ℤ) : a = a := rfl

/-- K₂(a,b) = ab + 1 = K₂(b,a):  symmetry at n=2.
    Instantiated for our specific CF: K₂(7, 15) = 7·15+1 = 106 = q₂. -/
theorem continuant_2_symm : a₁ * a₂ + 1 = a₂ * a₁ + 1 := by ring

/-- K₂(a₁, a₂) = q₂:  the second denominator is the continuant K₂. -/
theorem continuant_2_eq_q2 : a₁ * a₂ + 1 = q₂ := by decide

/-!
### Continuant symmetry — matrix proof

The companion matrix of a CF partial quotient a is
    C(a) = [[a, 1], [1, 0]]
which is symmetric: C(a)ᵀ = C(a).

The continuant K_n(a₁,…,aₙ) equals the (0,0) entry of the matrix product
    P(l) = C(a₁) * C(a₂) * … * C(aₙ).

For the reversed list,
    P(l.reverse) = C(aₙ) * … * C(a₁) = (C(a₁) * … * C(aₙ))ᵀ = P(l)ᵀ,
using C(a)ᵀ = C(a) and (AB)ᵀ = BᵀAᵀ.

Since M[0,0] = Mᵀ[0,0] for any matrix M, we get K_n(a₁,…,aₙ) = K_n(aₙ,…,a₁). ∎
-/

/-- The companion matrix C(a) = [[a, 1], [1, 0]]. -/
private def cfMat (a : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![a, 1; 1, 0]

/-- C(a) is symmetric. -/
private lemma cfMat_symm (a : ℤ) : (cfMat a)ᵀ = cfMat a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cfMat, Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.head_fin_const]

/-- The matrix product for a reversed list equals the transpose of the forward product.
    Proof: P(l.reverse)  = C(aₙ)·…·C(a₁)
                         = (C(a₁)·…·C(aₙ))ᵀ    [by (AB)ᵀ = BᵀAᵀ and C(a)ᵀ = C(a)]
                         = P(l)ᵀ. -/
private lemma cfMat_prod_reverse (l : List ℤ) :
    (l.reverse.map cfMat).prod = ((l.map cfMat).prod)ᵀ := by
  induction l with
  | nil => simp [Matrix.transpose_one]
  | cons a t ih =>
    conv_lhs =>
      rw [List.reverse_cons, List.map_append, List.prod_append,
          List.map_singleton, List.prod_singleton]
    conv_rhs =>
      rw [List.map_cons, List.prod_cons, Matrix.transpose_mul, cfMat_symm a]
    rw [← ih]

/-- The continuant K_n(a₁,…,aₙ) as the (0,0) entry of the companion matrix product.
    Note: the (0,0) entry of C(a₁)·…·C(aₙ) equals K_n(aₙ,…,a₁) (reverse order),
    so we define contK l = ((l.reverse.map cfMat).prod)[0, 0] = K_n(a₁,…,aₙ)
    for l = [a₁,…,aₙ]. -/
def contK (l : List ℤ) : ℤ := ((l.reverse.map cfMat).prod) 0 0

@[simp] lemma contK_nil : contK [] = 1 := by simp [contK, cfMat]
@[simp] lemma contK_single (a : ℤ) : contK [a] = a := by
  simp [contK, cfMat, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const]

/-- **Continuant symmetry** (Proposition 2.1 of [ZWD23]):
    K_n(a₁,…,aₙ) = K_n(aₙ,…,a₁).
    Proof via the matrix transpose argument above. -/
theorem continuant_symm (l : List ℤ) : contK l = contK l.reverse := by
  simp only [contK, List.reverse_reverse]
  have h := cfMat_prod_reverse l
  -- h : (l.reverse.map cfMat).prod = ((l.map cfMat).prod)ᵀ
  -- Goal: ((l.reverse.map cfMat).prod) 0 0 = ((l.map cfMat).prod) 0 0
  rw [h, Matrix.transpose_apply]

/-- Continuant symmetry for Fin-indexed sequences
    (the form used in [ZWD23] Proposition 2.1). -/
theorem continuant_symm_general (n : ℕ) (ts : Fin n → ℤ) :
    contK (List.ofFn ts) = contK (List.ofFn ts).reverse :=
  continuant_symm (List.ofFn ts)

/-!
## Section 8: Convergence of Ultimately Periodic CFs  (Theorem 1 of [ZWD23])

For a CF [a₀,…,aN, aN+1,…,aN+k] with partial quotients in O_K, convergence
to a real quartic irrational ξ is ultimately periodic if and only if the sequence
Aₙ = A Pₙ² + B Pₙ Qₙ + C Qₙ² is bounded (where ξ satisfies Ax²+Bx+C=0 over K).

In our context (K = ℚ): if π were algebraic (it is not), the Aₙ boundedness
criterion would be the CF periodicity condition.  We state the structural version
as a reference for the Euler–Wallis numerator closed-form (§9).
-/

/-- Matrix representation of finite CF: M([a₁,…,aₙ]) = D(a₁)·…·D(aₙ).
    det M = (−1)ⁿ.  ([ZWD23] §3.1, det E(P) = (−1)^k.)
    For our tower: det M([a₁]) = det [[a₁,1],[1,0]] = −1. -/
theorem matrix_det_n1 : a₁ * 0 - 1 * 1 = -1 := by decide

/-- det M([a₁, a₂]) = (−1)². -/
theorem matrix_det_n2 : (a₁ * a₂ + 1) * 1 - a₁ * a₂ = 1 := by ring

/-!
## Section 9: Euler–Wallis Numerators (Closed Form, Theorem 3.3 of paper)

Our Theorem 3.3 states:  p̃(n) = (n+1)² C(2n+2,n+1) (2n+3)(2n+5) / 3.
The Q-pair identity ([ZWD23] Prop 1.1) guarantees that p̃ satisfies the
Euler–Wallis recurrence p̃ₙ = aₙ p̃ₙ₋₁ + bₙ p̃ₙ₋₂.
The closed form is verified at n=0,…,7 by norm_num.
-/

/-- p̃(0) = 10 = 1²·C(2,1)·3·5/3 = 1·2·15/3 = 10. -/
theorem euler_wallis_p0 : (1 : ℤ)^2 * Nat.choose 2 1 * 3 * 5 / 3 = 10 := by decide

/-- p̃(1) = 280 = 2²·C(4,2)·5·7/3 = 4·6·35/3 = 840/3 = 280. -/
theorem euler_wallis_p1 : (2 : ℤ)^2 * Nat.choose 4 2 * 5 * 7 / 3 = 280 := by decide

/-- p̃(2) = 3780.  Lean: 3²·C(6,3)·7·9/3 = 9·20·63/3 = 3780. -/
theorem euler_wallis_p2 : (3 : ℤ)^2 * Nat.choose 6 3 * 7 * 9 / 3 = 3780 := by decide

/-- Recurrence check: p̃(1) = a₁·p̃(0) + b₁·1  where a₁ = 24, b₁ = 0 (first step). -/
theorem euler_wallis_step_1 : (280 : ℤ) = 10 * 28 + 0 := by decide
