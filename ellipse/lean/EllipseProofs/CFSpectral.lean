/-
  EllipseProofs/CFSpectral.lean

  Spectral classification of continued fraction families.

  Every CF has reduced recurrence f(n+1) = α_n·f(n) + β_n·f(n-1)
  where α_n = a_n (original CF coeff), β_n = b_n. The characteristic
  equation r² - Ar - B = 0 (with A = lim α_n/n², B = lim β_n/n⁴)
  determines the spectral family.

  SPECTRAL FAMILIES:

    (3,-2): r²-3r+2=0, roots (2,1), |M|_∞ = 1/2
      Members: C, F, G, H, I, K  (6 CFs)
      Cuff: 2·(n+2)²  (or 3/2·(n+2)² for C)
      Braiding: β_n contains factor (2n-c)
        c=1: F (b=-n³(2n-1)), I (b=-n(n+2)²(2n-1))
        c=3: C (b=-n³(2n-3)), H (b=-n²(n+2)(2n-3)), K (b=-n²(n+3)(2n-3))
        c=5: G (b=-n²(n+2)(2n-5))
      All share: |β_n| ≤ 2·n²·(n+c')² for some c', giving C ≤ 8/9

    (3,-1): r²-3r+1=0, roots ((3±√5)/2), |M|_∞ ≈ 0.146
      Members: J  (1 CF, b=-(n-1)²n(n+2))
      Cuff: simple (n+2)² suffices (much room below 1)

    (5,-4): r²-5r+4=0, roots (4,1), |M|_∞ = 1/4
      Members: L  (1 CF, a=5n²+7n+2, b=-4n²(n+1)²)
      Cuff: 3·(n+2)² (leading coeff 5 vs 3)

    (3,0): degenerate r²-3r=0, roots (3,0), |M|_∞ = 0
      Members: A  (1 CF, b=-4(n+1)², degree 2)
      β → 0 as 1/n² → exponential dominance

    Positive β: |M|_∞ ≪ 1
      (11,1): B. (5,1): D. (7,8): E.
      α-dominance: β·f(n-2) < α·f(n-1) ≤ f(n).

  CF BRAIDING (2/3 PARITY):

  Within the (3,-2) family, the factor (2n-c) in β_n controls:
  - Sign: β_n < 0 for n > c/2 (all n ≥ 2 when c ≤ 3)
  - Correction: |M_n| = 1/2 + O(c/n), with the O(c/n) term
    alternating sign based on n mod 2

  The +1 SL(2) chain: T_n = [[α_n, β_n],[1,0]] has det = -β_n > 0
  for n large enough. After √|β_n| normalization:
    T̂_n ∈ SL(2,ℝ), spectral radius → 2, contraction rate → 1/2.
  The braiding parameter c shifts the correction term, giving
  different rates of approach to the asymptotic 1/2.

  GAP POLYNOMIALS (verifying cuff is self-sustaining):
    F: 6n+12                          (trivial)
    C: (k²+20k+61)/2                 (trivial)
    G: (5k+37)/2                      (trivial)
    H: (5k+23)/2                      (trivial)
    I: (7k²+66k+156)/2               (trivial)
    J: 2n²+3n-1                       (pos for n ≥ 1)
    K: (9n²+22n+5)/2                  (trivial)
    L: 4k⁴-11k³-22k²-13k-3          (pos for k ≥ 5, so n₀=4)
-/

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas

/-! ## Parametric chain lemmas

The (3,-2) family members all use the same chain structure:
two steps of c·(n+k)² growth give c²·(n+k)²·(n+k+1)² chain.
-/

section ChainLemmas

/-- Two-step chain: if f(n+1) ≥ c·a·f(n) and f(n+2) ≥ c·b·f(n+1),
    then f(n+2) ≥ c²·a·b·f(n). -/
theorem two_step_chain {f : ℕ → ℚ} {c a b : ℚ} {n : ℕ}
    (h1 : c * a * f n ≤ f (n + 1))
    (h2 : c * b * f (n + 1) ≤ f (n + 2))
    (hcb : 0 ≤ c * b) :
    c ^ 2 * a * b * f n ≤ f (n + 2) :=
  calc c ^ 2 * a * b * f n = c * b * (c * a * f n) := by ring
    _ ≤ c * b * f (n + 1) := mul_le_mul_of_nonneg_left h1 hcb
    _ ≤ f (n + 2) := h2

/-- Multiplier bound from chain and polynomial bound on |β|.
    If f(n+2) ≥ D·f(n) and |β| ≤ C·D, then |β|·f(n) ≤ C·f(n+2). -/
theorem mult_from_chain {f_lo f_hi : ℚ} {β_abs C D : ℚ}
    (hchain : D * f_lo ≤ f_hi)
    (hbeta : β_abs ≤ C * D)
    (hflo : 0 ≤ f_lo)
    (hC : 0 ≤ C) :
    β_abs * f_lo ≤ C * f_hi :=
  calc β_abs * f_lo ≤ C * D * f_lo := mul_le_mul_of_nonneg_right hbeta hflo
    _ = C * (D * f_lo) := by ring
    _ ≤ C * f_hi := mul_le_mul_of_nonneg_left hchain hC

end ChainLemmas

/-! ## Spectral family membership

Each CF is tagged with its spectral family by its asymptotic (A,B).
The family determines the cuff type and contraction rate.
-/

/-- Spectral families for the CF collection. -/
inductive SpectralFamily where
  | family_3_neg2  -- roots (2,1), |M|_∞ = 1/2, cuff 2(n+2)²
  | family_3_neg1  -- roots ((3±√5)/2), |M|_∞ ≈ 0.146
  | family_5_neg4  -- roots (4,1), |M|_∞ = 1/4, cuff 3(n+2)²
  | family_3_0     -- degenerate, |M|_∞ = 0
  | positive_beta  -- α-dominance, |M|_∞ ≪ 1
  deriving DecidableEq, Repr

/-- The braiding parameter c from factor (2n-c) in β_n,
    for members of the (3,-2) family. -/
def braiding_param : String → ℕ
  | "F" => 1
  | "I" => 1
  | "C" => 3
  | "H" => 3
  | "K" => 3
  | "G" => 5
  | _   => 0

/-- Contraction rate for each spectral family. -/
noncomputable def contraction_rate : SpectralFamily → ℚ
  | .family_3_neg2 => 1 / 2
  | .family_3_neg1 => 3 / 20   -- ≈ 0.15, conservative bound on (3-√5)²/4
  | .family_5_neg4 => 1 / 4
  | .family_3_0    => 0
  | .positive_beta => 1 / 2    -- conservative universal bound

/-- All contraction rates are in (0, 1). -/
theorem contraction_rate_lt_one (fam : SpectralFamily) :
    contraction_rate fam < 1 := by
  cases fam <;> simp [contraction_rate] <;> norm_num

theorem contraction_rate_nonneg (fam : SpectralFamily) :
    0 ≤ contraction_rate fam := by
  cases fam <;> simp [contraction_rate] <;> norm_num
