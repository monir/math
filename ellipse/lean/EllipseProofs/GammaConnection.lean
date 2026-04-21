/-
  EllipseProofs/GammaConnection.lean

  The Gauss connection coefficient: Gamma(1)^2 / (Gamma(3/2) * Gamma(1/2)) = 2/pi.

  Uses three Mathlib facts:
    Real.Gamma_one         : Gamma 1 = 1
    Real.Gamma_one_half_eq : Gamma (1/2) = sqrt pi
    Real.Gamma_add_one     : s != 0 -> Gamma (s+1) = s * Gamma s

  Paper reference: Theorem 2.4 (Gauss connection coefficient)
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

open Real

noncomputable section

/-- Gamma(3/2) = sqrt(pi) / 2, from the functional equation at s = 1/2. -/
lemma Gamma_three_halves : Gamma (3 / 2 : ℝ) = √π / 2 := by
  have h1 : (3 : ℝ) / 2 = 1 / 2 + 1 := by norm_num
  rw [h1, Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), Gamma_one_half_eq]
  ring

/-- The Gauss connection coefficient:
    Gamma(1)^2 / (Gamma(3/2) * Gamma(1/2)) = 2/pi.

    Proof: Gamma(1) = 1, Gamma(1/2) = sqrt(pi), Gamma(3/2) = sqrt(pi)/2.
    So 1^2 / ((sqrt(pi)/2) * sqrt(pi)) = 1 / (pi/2) = 2/pi.

    Paper: Theorem 2.4 -/
theorem gauss_connection_coefficient :
    Gamma 1 ^ 2 / (Gamma (3 / 2 : ℝ) * Gamma (1 / 2 : ℝ)) = 2 / π := by
  rw [Gamma_one, Gamma_three_halves, Gamma_one_half_eq, one_pow,
    div_mul_eq_mul_div, mul_self_sqrt pi_pos.le, one_div_div]

end
