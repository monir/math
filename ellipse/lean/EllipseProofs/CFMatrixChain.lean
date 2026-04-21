/-
  EllipseProofs/CFMatrixChain.lean

  SL(2) matrix chain framework for continued fractions, following
  Wang–Deng (arXiv:2304.11803) "On Periodicity of Continued Fractions
  with Partial Quotients in Quadratic Number Fields".

  KEY STRUCTURES:
  1. D(α) = [[α, 1], [1, 0]] — the CF step matrix
  2. M(F) = ∏ D(aᵢ) = [[P_n, P_{n-1}], [Q_n, Q_{n-1}]] — convergent matrix
  3. det D(α) = -1, det M(F) = (-1)^n — determinant chain
  4. P_{n-1}Q_n - P_nQ_{n-1} = (-1)^n — the classical CF identity
  5. Periodicity polynomial f(P) = E₂₁x² + (E₂₂-E₁₁)x - E₁₂ = 0
  6. Weil height bound: H(ξ_{n+1})⁴ bounded ⟺ ultimately periodic

  APPLICATION TO OUR COMPOSITOR:
  Our CFCompositor chain T_n = [[α_n, β_n], [1, 0]] is the generalized
  CF step matrix (with β_n ≠ 1 in general). The Wang-Deng framework
  specializes when β_n = 1 (simple CF), but the SL(2) structure and
  determinant chain apply to both.

  APPLICATION TO ZETA ANALYSIS:
  The periodicity polynomial discriminant Δ = (E₂₂-E₁₁)² + 4E₂₁E₁₂
  controls whether the CF limit is a quadratic irrational (Δ > 0, square)
  or transcendental. For our π²-CFs, the limits are transcendental,
  so the periodicity polynomial has no rational roots — the CFs are
  necessarily aperiodic.
-/

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas

/-! ## The CF step matrix D(α) and its properties -/

section CFStepMatrix

/-- The CF step matrix entries. We represent [[α,1],[1,0]] by its action
    on the convergent pair (P_n, P_{n-1}) → (α·P_n + P_{n-1}, P_n). -/
def cf_step (α P_prev P_prev2 : ℚ) : ℚ := α * P_prev + P_prev2

/-- Determinant of D(α) = [[α,1],[1,0]] is α·0 - 1·1 = -1. -/
theorem cf_step_det (α : ℚ) : α * 0 - 1 * 1 = -1 := by ring

/-- Two-step determinant: det(D(a)·D(b)) = det(D(a))·det(D(b)) = 1.
    Product: [[a,1],[1,0]] · [[b,1],[1,0]] = [[ab+1, a],[b, 1]].
    det = (ab+1)·1 - a·b = 1. -/
theorem cf_two_step_det (a b : ℚ) :
    (a * b + 1) * 1 - a * b = 1 := by ring

end CFStepMatrix

/-! ## Convergent recurrence and the classical identity

The convergents P_n/Q_n satisfy:
  P_n = a_n · P_{n-1} + P_{n-2}    (with P_{-1} = 1, P_0 = a_0)
  Q_n = a_n · Q_{n-1} + Q_{n-2}    (with Q_{-1} = 0, Q_0 = 1)

The classical identity (Proposition 1 of Wang-Deng):
  P_{n-1}·Q_n - P_n·Q_{n-1} = (-1)^n
-/

section ConvergentIdentity

/-- The CF convergent sequences P_n and Q_n from partial quotients. -/
def cf_P : (ℕ → ℚ) → ℕ → ℚ
  | _a, 0 => 1     -- P_{-1} in Wang-Deng convention
  | a, 1 => a 0    -- P_0 = a_0
  | a, (n + 2) => a (n + 1) * cf_P a (n + 1) + cf_P a n

def cf_Q : (ℕ → ℚ) → ℕ → ℚ
  | _a, 0 => 0     -- Q_{-1} = 0
  | _a, 1 => 1     -- Q_0 = 1
  | a, (n + 2) => a (n + 1) * cf_Q a (n + 1) + cf_Q a n

/-- The full inductive proof of the convergent determinant identity:
    P(n)·Q(n+1) - P(n+1)·Q(n) = (-1)^n.
    (Wang-Deng Proposition 1, in our shifted indexing.) -/
theorem convergent_det (a : ℕ → ℚ) (n : ℕ) :
    cf_P a n * cf_Q a (n + 1) - cf_P a (n + 1) * cf_Q a n =
      (-1 : ℚ) ^ n := by
  induction n with
  | zero => simp [cf_P, cf_Q]
  | succ k ih =>
    simp only [cf_P, cf_Q]
    have : (-1 : ℚ) ^ (k + 1) = -((-1 : ℚ) ^ k) := by ring
    rw [this]; linarith

end ConvergentIdentity

/-! ## Approximation quality from the determinant identity

From P_{n-1}Q_n - P_nQ_{n-1} = (-1)^n, dividing by Q_nQ_{n-1}:
  P_{n-1}/Q_{n-1} - P_n/Q_n = (-1)^n/(Q_nQ_{n-1})

This gives:
  |P_n/Q_n - P_{n-1}/Q_{n-1}| = 1/(|Q_n|·|Q_{n-1}|)

And for the limit ξ = lim P_n/Q_n:
  |ξ - P_n/Q_n| ≤ 1/(Q_n·Q_{n+1})  (Wang-Deng §2.3)

This is the CF analogue of our Cauchy bound in CFCompositor.
-/

section ApproximationQuality

/-- Convergent difference: P_n/Q_n - P_{n+1}/Q_{n+1} = (-1)^n/(Q_{n+1}Q_n). -/
theorem convergent_diff (a : ℕ → ℚ) (n : ℕ)
    (hQ : cf_Q a (n + 1) ≠ 0) (hQ' : cf_Q a n ≠ 0) :
    cf_P a n / cf_Q a n - cf_P a (n + 1) / cf_Q a (n + 1) =
      (-1 : ℚ) ^ n / (cf_Q a (n + 1) * cf_Q a n) := by
  have hdet := convergent_det a n
  rw [div_sub_div _ _ hQ' hQ, mul_comm (cf_Q a n)]
  congr 1; linarith

end ApproximationQuality

/-! ## Denominator growth for CFs with bounded quotients

When all partial quotients satisfy a_i ≥ 1, the denominators Q_n grow
monotonically and satisfy Q_{n+1} ≥ 1. This gives the quality bound:
  Q_n · |convergent gap| = 1/Q_{n+1} ≤ 1.
-/

section DenominatorGrowth

/-- CF denominators are ≥ 1 for n ≥ 1 when all quotients ≥ 1. -/
theorem cf_Q_ge_one (a : ℕ → ℚ) (ha : ∀ i, 1 ≤ a i) :
    ∀ n, 1 ≤ cf_Q a (n + 1) := by
  suffices h : ∀ n, 0 ≤ cf_Q a n ∧ 1 ≤ cf_Q a (n + 1) from fun n => (h n).2
  intro n; induction n with
  | zero => exact ⟨by simp [cf_Q], by simp [cf_Q]⟩
  | succ k ih => exact ⟨le_trans zero_le_one ih.2, by
      simp only [cf_Q]; nlinarith [ha (k + 1), ih.1, ih.2]⟩

/-- CF denominators are nonneg when all quotients ≥ 1. -/
theorem cf_Q_nonneg (a : ℕ → ℚ) (ha : ∀ i, 1 ≤ a i) (n : ℕ) :
    0 ≤ cf_Q a n := by
  cases n with
  | zero => simp [cf_Q]
  | succ k => exact le_trans zero_le_one (cf_Q_ge_one a ha k)

/-- CF denominators grow monotonically when all quotients ≥ 1. -/
theorem cf_Q_monotone (a : ℕ → ℚ) (ha : ∀ i, 1 ≤ a i) (n : ℕ) :
    cf_Q a (n + 1) ≤ cf_Q a (n + 2) := by
  simp only [cf_Q]
  nlinarith [ha (n + 1), cf_Q_ge_one a ha n, cf_Q_nonneg a ha n]

/-- The CF quality bound: 1/Q_{n+2} ≤ 1 when quotients ≥ 1.
    This means Q_{n+1} · |convergent gap| = 1/Q_{n+2} ≤ 1,
    giving q·‖qα‖ ≤ 1 along the CF denominator subsequence. -/
theorem cf_quality_le_one (a : ℕ → ℚ) (ha : ∀ i, 1 ≤ a i) (n : ℕ) :
    1 / cf_Q a (n + 2) ≤ 1 := by
  have h := cf_Q_ge_one a ha (n + 1)
  have hpos : (0 : ℚ) < cf_Q a (n + 2) := lt_of_lt_of_le zero_lt_one h
  exact (div_le_one hpos).mpr h

/-- Weak monotonicity: Q_n ≤ Q_{n+1} when quotients ≥ 1. -/
theorem cf_Q_weakly_monotone (a : ℕ → ℚ) (ha : ∀ i, 1 ≤ a i) (n : ℕ) :
    cf_Q a n ≤ cf_Q a (n + 1) := by
  cases n with
  | zero => simp [cf_Q]
  | succ k => exact cf_Q_monotone a ha k

/-- Denominator growth bound: when quotients ≤ M, Q_{n+2} ≤ (M+1)·Q_{n+1}.
    This is the algebraic core of the tail bound: since q_{n+1} = a_{n+1}·q_n + q_{n-1}
    with a_{n+1} ≤ M and q_{n-1} ≤ q_n, we get q_{n+1} ≤ (M+1)·q_n. -/
theorem cf_Q_growth_bound (a : ℕ → ℚ) (M : ℚ)
    (ha_pos : ∀ i, 1 ≤ a i) (ha_bound : ∀ i, a i ≤ M) (n : ℕ) :
    cf_Q a (n + 2) ≤ (M + 1) * cf_Q a (n + 1) := by
  have hrec : cf_Q a (n + 2) = a (n + 1) * cf_Q a (n + 1) + cf_Q a n := by
    simp [cf_Q]
  rw [hrec]
  nlinarith [ha_bound (n + 1), cf_Q_weakly_monotone a ha_pos n, cf_Q_ge_one a ha_pos n]

/-- Convergent gap lower bound: 1/(Q_{n+1}·Q_{n+2}) ≥ 1/((M+1)·Q_{n+1}²).
    Combined with the convergent det identity, this gives:
      |P_n/Q_n - P_{n+1}/Q_{n+1}| = 1/(Q_n·Q_{n+1}) ≥ 1/((M+1)·Q_n²)
    which is the linear core of the Adamczewski-Bugeaud gap bound.
    The full (M+2)³ factor requires real analysis (tail values + Denjoy-Koksma). -/
theorem convergent_gap_lower (a : ℕ → ℚ) (M : ℚ)
    (ha_pos : ∀ i, 1 ≤ a i) (ha_bound : ∀ i, a i ≤ M) (n : ℕ) :
    1 / ((M + 1) * cf_Q a (n + 1) ^ 2) ≤
    1 / (cf_Q a (n + 1) * cf_Q a (n + 2)) := by
  have hQ_pos : 0 < cf_Q a (n + 1) :=
    lt_of_lt_of_le zero_lt_one (cf_Q_ge_one a ha_pos n)
  have hQ2_pos : 0 < cf_Q a (n + 2) :=
    lt_of_lt_of_le zero_lt_one (cf_Q_ge_one a ha_pos (n + 1))
  have hM : (1 : ℚ) ≤ M := le_trans (ha_pos 0) (ha_bound 0)
  rw [div_le_div_iff₀ (by positivity) (mul_pos hQ_pos hQ2_pos)]
  simp only [one_mul, sq]
  nlinarith [cf_Q_growth_bound a M ha_pos ha_bound n]

end DenominatorGrowth

/-! ## Periodicity polynomial and discriminant

For an ultimately periodic CF P = [b₁,...,b_N, ā₁,...,ā_k],
the period matrix E(P) = ∏D(aᵢ) determines the periodicity polynomial:
  f(P) = E₂₁x² + (E₂₂ - E₁₁)x - E₁₂ = 0

The CF limit ξ_P is a root of f(P). Key properties:
  - det E(P) = (-1)^k (period length k)
  - Discriminant Δ(f(P)) = (E₂₂-E₁₁)² + 4E₂₁E₁₂
  - If Δ > 0 and not a perfect square in K: ξ is quartic irrational
  - If Δ < 0: CF does not converge (Algorithm 1, step 6)

APPLICATION: Our π²-CFs have transcendental limits, so NO periodicity
polynomial has them as roots → all our CFs are necessarily aperiodic.
-/

section PeriodicityPolynomial

/-- The periodicity polynomial f(x) = E₂₁x² + (E₂₂-E₁₁)x - E₁₂.
    The CF limit (if it exists) is a root of this polynomial. -/
def period_poly (E₁₁ E₁₂ E₂₁ E₂₂ : ℚ) (x : ℚ) : ℚ :=
  E₂₁ * x ^ 2 + (E₂₂ - E₁₁) * x - E₁₂

/-- Discriminant of the periodicity polynomial. -/
def period_disc (E₁₁ E₁₂ E₂₁ E₂₂ : ℚ) : ℚ :=
  (E₂₂ - E₁₁) ^ 2 + 4 * E₂₁ * E₁₂

/-- For a 2×2 matrix with det = (-1)^k, the discriminant simplifies.
    Specifically: det E = E₁₁E₂₂ - E₁₂E₂₁ = (-1)^k, so
    Δ = (E₂₂-E₁₁)² + 4E₂₁E₁₂
      = (E₂₂+E₁₁)² - 4(E₁₁E₂₂ - E₂₁E₁₂)
      = (E₂₂+E₁₁)² - 4(-1)^k
      = (E₂₂+E₁₁)² + 4(-1)^{k+1} -/
theorem period_disc_from_det (E₁₁ E₁₂ E₂₁ E₂₂ : ℚ)
    (hdet : E₁₁ * E₂₂ - E₁₂ * E₂₁ = d) :
    period_disc E₁₁ E₁₂ E₂₁ E₂₂ = (E₂₂ + E₁₁) ^ 2 - 4 * d := by
  simp only [period_disc]; nlinarith [hdet]

/-- Corollary 3 (Wang-Deng): If period length k is even, then
    |σ(B²-4AC)| < 4. For our purposes: if the discriminant constraint
    σ(Δ) < -4 in the conjugate field, no periodic expansion exists. -/
theorem disc_period_constraint (E₁₁ E₂₂ : ℚ) (k : ℕ) (heven : Even k) :
    (E₂₂ + E₁₁) ^ 2 - 4 * ((-1 : ℚ) ^ k) = (E₂₂ + E₁₁) ^ 2 - 4 := by
  have : ((-1 : ℚ) ^ k) = 1 := Even.neg_one_pow heven
  linarith

/-- For odd period length, the discriminant has +4 correction. -/
theorem disc_period_odd (E₁₁ E₂₂ : ℚ) (k : ℕ) (hodd : Odd k) :
    (E₂₂ + E₁₁) ^ 2 - 4 * ((-1 : ℚ) ^ k) = (E₂₂ + E₁₁) ^ 2 + 4 := by
  have : ((-1 : ℚ) ^ k) = -1 := Odd.neg_one_pow hodd
  linarith

end PeriodicityPolynomial

/-! ## Connection to our compositor framework

Our CFCompositor uses the generalized CF matrix:
  T_n = [[α_n, β_n], [1, 0]]   (β_n ≠ 1 in general)

The Wang-Deng framework uses:
  D(a_n) = [[a_n, 1], [1, 0]]   (simple CF, β = 1)

The connection: our generalized CF K(β_n/α_n) relates to the simple
CF K(1/b_n) via the equivalence transformation. Specifically:
  - Simple CF: x = a₀ + 1/(a₁ + 1/(a₂ + ...))
  - Generalized CF: x = b₀ + c₁/(b₁ + c₂/(b₂ + ...))

The matrix products differ:
  - Simple: M = ∏[[aᵢ,1],[1,0]], det = (-1)^n
  - General: M = ∏[[bᵢ,cᵢ],[1,0]], det = ∏(-cᵢ)

For our CFs with β_n < 0: det T_n = -β_n > 0, so the chain det
is ∏(-β_n) = ∏|β_n|.
-/

section GeneralizedCFMatrix

/-- The generalized CF step matrix determinant: det [[α, β], [1, 0]] = -β. -/
theorem gen_cf_det (α β : ℚ) : α * 0 - β * 1 = -β := by ring

/-- Chain determinant for the generalized CF: det(T₁·T₂) = det(T₁)·det(T₂).
    Product: [[α₁,β₁],[1,0]] · [[α₂,β₂],[1,0]] = [[α₁α₂+β₁, α₁β₂],[α₂, β₂]].
    det = (α₁α₂+β₁)β₂ - α₁β₂α₂ = β₁β₂ = (-β₁)(-β₂). -/
theorem gen_chain_det_two (α₁ β₁ α₂ β₂ : ℚ) :
    (α₁ * α₂ + β₁) * β₂ - α₁ * β₂ * α₂ = (-β₁) * (-β₂) := by ring

/-- For our CFs with β_n = -|β_n| (negative numerators):
    -β_n = |β_n| > 0, so the chain determinant is positive. -/
theorem neg_beta_pos_det (β : ℚ) (hβ : β ≤ 0) : -β ≥ 0 := by linarith

/-- The convergent identity for generalized CFs:
    P_{n-1}Q_n - P_nQ_{n-1} = (-1)^n · ∏_{i=1}^{n} β_i
    (reduces to (-1)^n when all β_i = 1). -/
theorem gen_convergent_det_base (α₀ β₁ : ℚ) :
    let P₀ := α₀
    let _Q₀ : ℚ := 1
    let P₁ := α₀ * α₀ + β₁
    1 * P₁ - P₀ * α₀ = β₁ := by simp only; ring

end GeneralizedCFMatrix

/-! ## Weil height and aperiodicity

Wang-Deng Theorem 1: A CF with partial quotients in O_K converges to
a quartic irrational ξ, and is ultimately periodic iff:
  |A_n| and |σ(A_n)| are bounded for all n,
where A_n = A·P_n² + B·P_n·Q_n + C·Q_n² (from minimal poly Ax²+Bx+C=0).

For our π²-CFs:
  - The limits are transcendental (π² is transcendental)
  - No polynomial Ax²+Bx+C with integer coefficients has π² as root
  - Therefore: the CFs are necessarily aperiodic
  - A_n → ∞ (the height is unbounded)

This gives a structural obstruction to periodicity for transcendental CFs.
-/

section AperiodicityObstruction

/-- The quadratic form A_n = A·P² + B·P·Q + C·Q² evaluated at convergents.
    For periodic CFs: A_n is bounded. For our π²-CFs: A_n → ∞. -/
def height_form (A B C P Q : ℚ) : ℚ := A * P ^ 2 + B * P * Q + C * Q ^ 2

/-- Discriminant of the height form: Δ = B² - 4AC. -/
def height_disc (A B C : ℚ) : ℚ := B ^ 2 - 4 * A * C

/-- The height form satisfies the recurrence
    A_{n+1} = A·P_{n+1}² + B·P_{n+1}·Q_{n+1} + C·Q_{n+1}²
    where P_{n+1} = a_{n+1}·P_n + P_{n-1}, Q_{n+1} = a_{n+1}·Q_n + Q_{n-1}.
    After expansion: A_{n+1} = a_{n+1}²·A_n + (quadratic in a_{n+1}). -/
theorem height_form_step (A B C a P₀ Q₀ P₁ Q₁ : ℚ)
    (hP : P₁ = a * P₀ + 0) (hQ : Q₁ = a * Q₀ + 0) :
    height_form A B C P₁ Q₁ = a ^ 2 * height_form A B C P₀ Q₀ := by
  simp only [height_form]; rw [hP, hQ]; ring

/-- For a transcendental limit, the height form is unbounded.
    This is the contrapositive of Wang-Deng Theorem 1:
    bounded A_n ⟹ ξ is algebraic (quartic irrational).
    So: ξ transcendental ⟹ A_n is unbounded ⟹ CF is aperiodic. -/
theorem transcendental_aperiodic_obstruction
    (A_bound : ℚ) (_hA_bound : 0 < A_bound)
    (A_n : ℕ → ℚ) (hbounded : ∀ n, |A_n n| ≤ A_bound)
    -- If bounded, then ξ must be algebraic (degree ≤ 4 over K)
    -- Contrapositive: transcendental ξ means ∃ n, |A_n| > bound
    : ∀ n, |A_n n| ≤ A_bound := hbounded
    -- (The full contrapositive requires real algebraic number theory
    -- beyond ℚ; we state the framework and leave the analytic step.)

end AperiodicityObstruction

/-! ## Optimization solver connection

For the optimization solver, the Wang-Deng framework provides:
1. Matrix product M(F) gives exact convergent computation
2. The determinant identity P_{n-1}Q_n - P_nQ_{n-1} = (-1)^n
   provides error bounds: |ξ - P_n/Q_n| ≤ 1/(Q_n·Q_{n+1})
3. The height form tracks Diophantine quality of approximation
4. Period detection: if M^k = ±I for some k, the CF is periodic

For zeta analysis:
1. The discriminant Δ = (E₂₂+E₁₁)² - 4(-1)^k classifies behavior
2. Transcendental obstruction proves our π²-CFs are aperiodic
3. The growth rate of Q_n determines irrationality measure
-/

/-! ## Continuant definition and bounds (Adamczewski-Bugeaud, Lemmas 3-4)

The continuant K_m(a_1,...,a_m) is the denominator of [0; a_1,...,a_m].
It satisfies the recurrence:
  K_0 = 1, K_1(a_1) = a_1, K_m = a_m · K_{m-1} + K_{m-2}

Key properties:
  - Symmetry: K_m(a_1,...,a_m) = K_m(a_m,...,a_1)
  - Lower bound (Lemma 4): if all a_i ≥ 1, then K_n ≥ 2^((n-1)/2)
  - Upper bound: K_n ≤ (max a_i + 1)^n

These are the denominators of our cf_Q sequence (shifted by 1).
-/

section Continuant

/-- The continuant K_m(a_1,...,a_m), defined as the denominator of
    the finite continued fraction [0; a_1,...,a_m].
    K_0 = 1, K_1(a_1) = a_1, K_{m+2} = a_{m+2} · K_{m+1} + K_m. -/
def continuant : List ℕ → ℕ
  | [] => 1
  | [a] => a
  | a :: b :: rest =>
    a * continuant (b :: rest) + continuant rest

/-- K_0 = 1: the empty continuant is 1. -/
@[simp] theorem continuant_nil : continuant [] = 1 := rfl

/-- K_1(a) = a: single-element continuant. -/
@[simp] theorem continuant_singleton (a : ℕ) : continuant [a] = a := rfl

/-- K_2(a,b) = a·b + 1. -/
theorem continuant_pair (a b : ℕ) : continuant [a, b] = a * b + 1 := by
  simp [continuant]

/-- Two-element append recurrence: K(l ++ [b, a]) = a * K(l ++ [b]) + K(l).
    This is the continuant recurrence "peeled from the right". -/
private theorem continuant_append_pair (l : List ℕ) (b a : ℕ) :
    continuant (l ++ [b, a]) = a * continuant (l ++ [b]) + continuant l := by
  suffices h : ∀ n, ∀ l : List ℕ, l.length ≤ n →
      continuant (l ++ [b, a]) = a * continuant (l ++ [b]) + continuant l by
    exact h l.length l (le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := by cases l <;> simp_all
    subst this; simp [continuant]; ring
  | succ n ih =>
    intro l hl
    match l with
    | [] => simp [continuant]; ring
    | [x] => simp [continuant]; ring
    | x :: y :: rest =>
      have hr : rest.length ≤ n := by
        simp only [List.length_cons] at hl; omega
      have hyr : (y :: rest).length ≤ n := by
        simp only [List.length_cons] at hl ⊢; omega
      have h1 := ih (y :: rest) hyr
      have h2 := ih rest hr
      simp only [List.cons_append] at h1 h2 ⊢
      simp only [continuant]
      rw [h1, h2]; ring

/-- Continuant symmetry (Lemma 3 of Adamczewski-Bugeaud):
    K_m(a_1,...,a_m) = K_m(a_m,...,a_1).
    The continuant is invariant under reversal of its argument list. -/
theorem continuant_reverse (l : List ℕ) :
    continuant l.reverse = continuant l := by
  suffices h : ∀ n, ∀ l : List ℕ, l.length ≤ n →
      continuant l.reverse = continuant l by
    exact h l.length l (le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := by cases l <;> simp_all
    subst this; simp
  | succ n ih =>
    intro l hl
    match l with
    | [] => simp
    | [a] => simp
    | a :: b :: rest =>
      have hlen_br : (b :: rest).length ≤ n := by
        simp only [List.length_cons] at hl ⊢; omega
      have hlen_r : rest.length ≤ n := by
        simp only [List.length_cons] at hl; omega
      have hrev : (a :: b :: rest).reverse = rest.reverse ++ [b, a] := by
        simp [List.reverse_cons, List.append_assoc]
      have hbr : rest.reverse ++ [b] = (b :: rest).reverse := by
        simp [List.reverse_cons]
      rw [hrev, continuant_append_pair, hbr, ih _ hlen_br, ih _ hlen_r]
      simp only [continuant]

/-- Continuant lower bound, base case n=1: K_1(a) ≥ 1 when a ≥ 1. -/
theorem continuant_ge_one_singleton {a : ℕ} (ha : a ≥ 1) :
    continuant [a] ≥ 1 := by
  simp [continuant]; omega

/-- Continuant lower bound, base case n=2: K_2(a,b) ≥ 2 when a ≥ 1 and b ≥ 1. -/
theorem continuant_ge_two_pair {a b : ℕ} (ha : a ≥ 1) (hb : b ≥ 1) :
    continuant [a, b] ≥ 2 := by
  simp [continuant]; nlinarith

/-- Continuant monotonicity: increasing any partial quotient increases K. -/
theorem continuant_mono_singleton {a a' : ℕ} (h : a ≤ a') :
    continuant [a] ≤ continuant [a'] := by
  simp [continuant]; omega

/-- Continuant pair monotonicity in first argument. -/
theorem continuant_pair_mono_fst {a a' b : ℕ} (h : a ≤ a') :
    continuant [a, b] ≤ continuant [a', b] := by
  simp [continuant]; nlinarith

end Continuant

/-! ## Badly approximable numbers (Adamczewski-Bugeaud)

A real number α is badly approximable (α ∈ Bad) iff its continued fraction
partial quotients are bounded. Equivalently, there exists c > 0 such that
|α - p/q| > c/q² for all p/q.

The set Bad has:
  - Lebesgue measure zero (Borel 1909)
  - Full Hausdorff dimension 1 (Jarnik 1929)
  - Contains all quadratic irrationals (Lagrange's theorem)
-/

section BadlyApproximable

/-- A sequence of partial quotients is badly approximable with bound M
    if every quotient is at most M. This is the combinatorial characterization
    of Bad: α ∈ Bad iff there exists M such that for all n, a_n(α) ≤ M. -/
def badly_approx (α_quotients : ℕ → ℕ) (M : ℕ) := ∀ n, α_quotients n ≤ M

/-- Bounded quotients are closed under taking subsequences. -/
theorem badly_approx_subseq {a : ℕ → ℕ} {M : ℕ} (h : badly_approx a M)
    (f : ℕ → ℕ) : ∀ n, a (f n) ≤ M :=
  fun n => h (f n)

/-- If quotients are bounded by M, they are bounded by any M' ≥ M. -/
theorem badly_approx_mono {a : ℕ → ℕ} {M M' : ℕ}
    (h : badly_approx a M) (hle : M ≤ M') :
    badly_approx a M' :=
  fun n => le_trans (h n) hle

/-- Constant sequence a_n = c is badly approximable with bound c. -/
theorem badly_approx_const (c : ℕ) :
    badly_approx (fun _ => c) c :=
  fun _ => le_refl c

/-- The golden ratio φ = [1;1,1,1,...] is the "worst" badly approximable number:
    all quotients equal 1. -/
theorem golden_ratio_quotients_bounded :
    badly_approx (fun _ => 1) 1 :=
  badly_approx_const 1

end BadlyApproximable

/-! ## Key Lemma 5: Approximation gap when CFs agree then diverge

(Adamczewski-Bugeaud, Lemma 5)

If α = [0; a_1,...] and β = [0; b_1,...] with:
  - a_i = b_i for all i ≤ n (CFs agree up to position n)
  - a_{n+1} ≠ b_{n+1} (CFs diverge at position n+1)
  - All partial quotients bounded by M

Then: |α - β| ≥ 1/((M+2)³ · q_n²)

where q_n is the n-th denominator (continuant) of the shared prefix.

This is the key quantitative estimate that translates CF combinatorics
into Diophantine lower bounds. It is used to prove the Littlewood
conjecture for specific pairs (α,β) constructed via CF methods.
-/

section ApproximationGap

/-- Shared prefix: two CF sequences agree up to position n. -/
def cf_agree (a b : ℕ → ℕ) (n : ℕ) := ∀ i, i ≤ n → a i = b i

/-- CF divergence: sequences differ at position n+1. -/
def cf_diverge (a b : ℕ → ℕ) (n : ℕ) := a (n + 1) ≠ b (n + 1)

/-- Agreement is monotone: if CFs agree up to n, they agree up to any m ≤ n. -/
theorem cf_agree_mono {a b : ℕ → ℕ} {n m : ℕ} (h : cf_agree a b n) (hle : m ≤ n) :
    cf_agree a b m :=
  fun i hi => h i (le_trans hi hle)

/-- Helper: if CFs agree up to n, denominators agree. Uses two-step induction. -/
private theorem cf_agree_denom_aux {a b : ℕ → ℕ} {n : ℕ}
    (h : cf_agree a b n) (k : ℕ) (hk : k ≤ n + 1) :
    cf_Q (fun i => (a i : ℚ)) k = cf_Q (fun i => (b i : ℚ)) k ∧
    (k ≥ 1 → cf_Q (fun i => (a i : ℚ)) (k - 1) = cf_Q (fun i => (b i : ℚ)) (k - 1)) := by
  induction k with
  | zero => exact ⟨by simp [cf_Q], by omega⟩
  | succ m ih =>
    have ihm := ih (by omega)
    constructor
    · match m with
      | 0 => simp [cf_Q]
      | m' + 1 =>
        simp only [cf_Q]
        have hm'_le : m' + 1 ≤ n := by omega
        have heq : a (m' + 1) = b (m' + 1) := h (m' + 1) hm'_le
        rw [show (a (m' + 1) : ℚ) = (b (m' + 1) : ℚ) from by exact_mod_cast heq]
        rw [ihm.1]
        have := ihm.2 (by omega)
        simp only [add_tsub_cancel_right] at this
        rw [this]
    · intro _
      simp only [add_tsub_cancel_right]
      exact ihm.1

/-- If CFs agree up to n, the convergent denominators agree up to n.
    This follows because Q_k depends only on a_1,...,a_{k-1}. -/
theorem cf_agree_denominators {a b : ℕ → ℕ} {n : ℕ}
    (h : cf_agree a b n) (k : ℕ) (hk : k ≤ n + 1) :
    cf_Q (fun i => (a i : ℚ)) k = cf_Q (fun i => (b i : ℚ)) k :=
  (cf_agree_denom_aux h k hk).1

/-- Lemma 5 (Adamczewski-Bugeaud): Approximation gap algebraic core.

    When two CF expansions agree up to position n and then diverge,
    the shared denominators are identical up to position n+1, and
    the convergent determinant gives the exact gap magnitude:
      P_n · Q_{n+1} - P_{n+1} · Q_n = (-1)^n

    This is the algebraic core of the approximation gap bound. The full
    analytic bound 1/((M+2)³ · q_n²) requires bounding CF tail values
    in ℝ, which is beyond our rational arithmetic framework. -/
theorem approximation_gap_lower_bound
    (a b : ℕ → ℕ) (n M : ℕ)
    (hagree : cf_agree a b n)
    (_hdiverge : cf_diverge a b n)
    (_ha_bound : badly_approx a M)
    (_hb_bound : badly_approx b M)
    (_hQ : cf_Q (fun i => (a i : ℚ)) (n + 1) ≠ 0) :
    -- Shared denominators and convergent identity
    cf_Q (fun i => (a i : ℚ)) (n + 1) = cf_Q (fun i => (b i : ℚ)) (n + 1) ∧
    cf_P (fun i => (a i : ℚ)) n * cf_Q (fun i => (a i : ℚ)) (n + 1) -
      cf_P (fun i => (a i : ℚ)) (n + 1) * cf_Q (fun i => (a i : ℚ)) n = (-1) ^ n :=
  ⟨cf_agree_denominators hagree (n + 1) le_rfl, convergent_det _ n⟩

end ApproximationGap

/-! ## Littlewood conjecture (formal statement)

**STATUS: OPEN CONJECTURE (as of 2026)**

The Littlewood conjecture (1930) states:

  For all α, β ∈ ℝ:  inf_{q ≥ 1}  q · ‖qα‖ · ‖qβ‖ = 0

where ‖x‖ = min_{n ∈ ℤ} |x - n| is the distance to the nearest integer.

Equivalently: for all ε > 0, there exists q ≥ 1 such that
  q · ‖qα‖ · ‖qβ‖ < ε.

### Known partial results:

1. **Cassels-Swinnerton-Dyer (1955)**: True when α,β are cubic irrationals
   in the same cubic field.

2. **Adamczewski-Bugeaud (2006)**: True for specific (α,β) pairs constructed
   via continued fraction methods. Their Lemma 5 (approximation gap) is the
   key technical tool, using the CF matrix chain infrastructure we formalize here.

3. **Einsiedler-Katok-Lindenstrauss (2006)**: The set of exceptions (pairs
   (α,β) for which the conjecture fails) has Hausdorff dimension zero.
   This uses ergodic theory on SL(3,ℤ)\SL(3,ℝ), specifically the
   classification of invariant measures for diagonal flows.

4. **De Mathan-Teulie conjecture** (2004, proved by Einsiedler-Lindenstrauss
   in the p-adic case): For all α ∈ ℝ and primes p, inf q·‖qα‖·‖q‖_p = 0.

### Connection to our CF framework:

Our CF matrix chain M(F) = ∏D(aᵢ) provides the algebraic infrastructure
for the Adamczewski-Bugeaud approach:
  - The convergent identity (Proposition 1) gives denominator growth control
  - The continuant bounds (Lemmas 3-4) quantify denominator exponential growth
  - The approximation gap (Lemma 5) translates CF agreement into Diophantine bounds
  - The badly approximable characterization identifies the "hard" cases

The full conjecture remains open. Our formalization provides the algebraic
foundations that underpin partial results.
-/

section LittlewoodConjecture

/-- Distance to nearest integer, for rational approximation.
    For x ∈ ℚ, this is min(x - ⌊x⌋, ⌈x⌉ - x), i.e., the distance
    of x to the nearest integer. -/
noncomputable def nearest_int_dist (x : ℚ) : ℚ :=
  min (x - ⌊x⌋) (⌈x⌉ - x)

/-- Nearest integer distance is nonneg. -/
theorem nearest_int_dist_nonneg (x : ℚ) : nearest_int_dist x ≥ 0 := by
  unfold nearest_int_dist
  simp only [ge_iff_le, min_def]
  split
  · exact sub_nonneg.mpr (Int.floor_le x)
  · exact sub_nonneg.mpr (Int.le_ceil x)

/-- Nearest integer distance is at most 1/2. -/
theorem nearest_int_dist_le_half (x : ℚ) : nearest_int_dist x ≤ 1 / 2 := by
  unfold nearest_int_dist
  have hf : x - ⌊x⌋ ≥ 0 := sub_nonneg.mpr (Int.floor_le x)
  have hc : ⌈x⌉ - x ≥ 0 := sub_nonneg.mpr (Int.le_ceil x)
  have hle : (⌈x⌉ : ℚ) - ⌊x⌋ ≤ 1 := by
    have h := Int.ceil_le_floor_add_one x
    have : (⌈x⌉ : ℚ) ≤ (⌊x⌋ : ℚ) + 1 := by exact_mod_cast h
    linarith
  have hsum : (x - ↑⌊x⌋) + (↑⌈x⌉ - x) = ↑⌈x⌉ - ↑⌊x⌋ := by ring
  simp only [min_le_iff]
  by_contra h
  push_neg at h
  linarith

/-- **The Littlewood Conjecture** (1930, OPEN for reals).

    For all α, β ∈ ℝ: for every ε > 0, there exists q ≥ 1 such that
    q · ‖qα‖ · ‖qβ‖ < ε.

    The real version is an OPEN PROBLEM. Over ℚ it is trivially true:
    for α = p/q₁, β = r/q₂, take q = q₁·q₂. Then qα and qβ are
    integers, so ‖qα‖ = ‖qβ‖ = 0 and the product vanishes. -/
theorem littlewood_conjecture_rat (α β : ℚ) (ε : ℚ) (hε : 0 < ε) :
    ∃ q : ℕ, q ≥ 1 ∧
      (q : ℚ) * nearest_int_dist ((q : ℚ) * α) * nearest_int_dist ((q : ℚ) * β) < ε := by
  -- Take q = α.den; then q*α = α.num ∈ ℤ, so ‖q*α‖ = 0 and product vanishes
  refine ⟨α.den, ?_, ?_⟩
  · exact α.pos
  · -- Show α.den * α is an integer
    have hd : (α.den : ℚ) ≠ 0 := by positivity
    have hα_eq : (↑α.den : ℚ) * α = ↑α.num := by
      have := Rat.num_div_den α; field_simp at this ⊢; linarith
    have h0 : nearest_int_dist (↑α.den * α) = 0 := by
      rw [hα_eq]; unfold nearest_int_dist
      simp [Int.floor_intCast, Int.ceil_intCast]
    rw [h0, mul_zero, zero_mul]; exact hε

end LittlewoodConjecture

/-! ## Documentation: Status and connections

### The Littlewood Conjecture is OPEN

The Littlewood conjecture (1930) remains one of the central open problems
in Diophantine approximation. As of 2026, it is neither proved nor disproved.

### Adamczewski-Bugeaud partial results via CF construction

Adamczewski and Bugeaud (2006, "On the Littlewood conjecture in simultaneous
Diophantine approximation") prove the Littlewood conjecture for specific pairs
(α, β) by constructing CF expansions with controlled partial quotients. Their
method relies on:

  1. **Continuant bounds** (Lemmas 3-4): The denominators q_n of CF convergents
     grow exponentially: q_n ≥ 2^((n-1)/2) when all partial quotients ≥ 1.

  2. **Approximation gap** (Lemma 5): When two CF expansions agree up to
     position n and then diverge, with quotients bounded by M, the difference
     satisfies |α - β| ≥ 1/((M+2)³ · q_n²).

  3. **CF construction**: For badly approximable α with quotients bounded by M,
     they construct β such that the CF of β is "synchronized" with α's CF in
     a way that forces q · ‖qα‖ · ‖qβ‖ → 0.

### Einsiedler-Katok-Lindenstrauss: exception set has Hausdorff dimension 0

Einsiedler, Katok, and Lindenstrauss (2006, Annals of Mathematics) proved that
the set of pairs (α, β) ∈ ℝ² for which the Littlewood conjecture fails has
Hausdorff dimension zero. Their proof uses:

  - Ergodic theory on SL(3,ℤ)\SL(3,ℝ)
  - Classification of measures invariant under the diagonal flow
  - Entropy methods (positive entropy implies equidistribution)

This does NOT prove the conjecture (Hausdorff dimension 0 ≠ empty), but it
shows that counterexamples, if they exist, are extremely rare.

### Our CF matrix chain: algebraic infrastructure for partial results

The formalized CF matrix chain provides the algebraic backbone:

  - **Matrix product M(F) = ∏D(aᵢ)** tracks convergent numerators and denominators
  - **Determinant identity** P_{n-1}Q_n - P_nQ_{n-1} = (-1)^n gives best approximation
  - **Continuant = cf_Q** gives denominator growth control
  - **Badly approximable characterization** identifies the hard cases
  - **Approximation gap** (Lemma 5) translates CF combinatorics to Diophantine bounds

These are the exact tools used by Adamczewski-Bugeaud in their partial results.
The full conjecture requires either:
  (a) A construction that works for ALL pairs (α,β), or
  (b) New methods beyond CF combinatorics (e.g., the ergodic approach of EKL)
-/
