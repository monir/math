/-
  SnowCrystalProofs.CosPiOverSix
  ================================
  Theorem T8 from the snow-crystal splitting v4 proof audit:

    cos(π/6) = √3/2

  This identity underlies the hexagonal renormalization factor
  R_hex = 4 / (4 + 2·cos(π/6)) = 4 / (4 + √3).

  Mathlib provides `Real.cos_pi_div_six : Real.cos (π/6) = √3/2`
  (in Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic).
  We restate it for our namespace and derive a couple of useful
  corollaries.

  Companion:
    research_scripts/snow_crystal_v4_proof_v3.py (T8)

  Registered: 2026-04-13.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace SnowCrystal.CosPiOverSix

open Real

/-- THE MAIN IDENTITY: cos(π/6) = √3/2 (from Mathlib). -/
theorem cos_pi_over_six : Real.cos (π / 6) = Real.sqrt 3 / 2 :=
  Real.cos_pi_div_six

/-- cos²(π/6) = 3/4 (squared form — useful for the hexagonal factor). -/
theorem cos_sq_pi_over_six : (Real.cos (π / 6))^2 = 3 / 4 := by
  rw [cos_pi_over_six]
  rw [div_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- 2·cos(π/6) = √3. -/
theorem two_cos_pi_over_six : 2 * Real.cos (π / 6) = Real.sqrt 3 := by
  rw [cos_pi_over_six]
  ring

/-- 4 + 2·cos(π/6) = 4 + √3 (the denominator of R_hex). -/
theorem denom_hex : 4 + 2 * Real.cos (π / 6) = 4 + Real.sqrt 3 := by
  rw [two_cos_pi_over_six]

/-- cos(π/6) is positive. -/
theorem cos_pi_over_six_pos : 0 < Real.cos (π / 6) := by
  rw [cos_pi_over_six]
  apply div_pos
  · exact Real.sqrt_pos.mpr (by norm_num)
  · norm_num

/-- cos(π/6) < 1 (it equals √3/2 ≈ 0.866). -/
theorem cos_pi_over_six_lt_one : Real.cos (π / 6) < 1 := by
  rw [cos_pi_over_six]
  have h_sq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h_nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  nlinarith

end SnowCrystal.CosPiOverSix
