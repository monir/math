/-
  SnowCrystalProofs.HexagonalFactor
  ===================================
  Theorem T3 from the snow-crystal splitting v4 proof audit:

    R_hex = 4 / (4 + √3) = (16 - 4√3) / 13

  This is the HEXAGONAL RENORMALIZATION FACTOR that reduces the bare
  cluster H-bond splitting (12.52 cm⁻¹) to the observed face splitting
  (~8.8 cm⁻¹). It arises from the C₆ᵥ geometry of Ice Ih.

  The identity is a rationalization:
    multiply num & denom by (4 - √3):
    4(4 - √3) / ((4 + √3)(4 - √3)) = (16 - 4√3) / (16 - 3) = (16 - 4√3) / 13

  The core algebraic fact is:
    (16 - 4√3) × (4 + √3) = 52    [product of conjugates]
  which is verified in `hex_rationalize_product`.

  Companion:
    research_scripts/snow_crystal_v4_proof_v3.py (T3, T10)
    research_findings/HEXAGONAL_RENORMALIZATION_PROGRAM_2026-04-12.md

  Registered: 2026-04-13.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace SnowCrystal.HexagonalFactor

open Real

/-- √3 is positive. -/
theorem sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

/-- √3 ≠ 0. -/
theorem sqrt3_ne_zero : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt3_pos

/-- The square of √3 is 3 (when 3 ≥ 0). -/
theorem sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)

/-- 4 + √3 is positive (so the denominator in R_hex is nonzero). -/
theorem denom_pos : (0 : ℝ) < 4 + Real.sqrt 3 := by
  have : (0 : ℝ) < 4 := by norm_num
  linarith [sqrt3_pos]

/-- 4 + √3 is nonzero. -/
theorem denom_ne_zero : (4 : ℝ) + Real.sqrt 3 ≠ 0 := ne_of_gt denom_pos

/-- The core rationalization identity:
    (16 - 4√3) × (4 + √3) = 52

    This is the algebraic fact underlying the hexagonal factor's closed form.
    Proof: expand and substitute √3 · √3 = 3. -/
theorem hex_rationalize_product :
    (16 - 4 * Real.sqrt 3) * (4 + Real.sqrt 3) = 52 := by
  have h : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq
  have expand : (16 - 4 * Real.sqrt 3) * (4 + Real.sqrt 3) =
                64 - 4 * (Real.sqrt 3 * Real.sqrt 3) := by ring
  rw [expand, h]
  norm_num

/-- Equivalently: (4 - √3)(4 + √3) = 16 - 3 = 13.
    Conjugate product — individual piece of the rationalization. -/
theorem conjugate_expand : (4 - Real.sqrt 3) * (4 + Real.sqrt 3) = 13 := by
  have h : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt3_sq
  have expand : (4 - Real.sqrt 3) * (4 + Real.sqrt 3) =
                16 - Real.sqrt 3 * Real.sqrt 3 := by ring
  rw [expand, h]
  norm_num

/-- THE MAIN THEOREM:
    R_hex := 4 / (4 + √3) = (16 - 4√3) / 13.

    Proof: cross-multiply using denom ≠ 0 and the rationalization identity. -/
theorem R_hex_closed_form :
    4 / (4 + Real.sqrt 3) = (16 - 4 * Real.sqrt 3) / 13 := by
  rw [div_eq_div_iff denom_ne_zero (by norm_num : (13 : ℝ) ≠ 0)]
  -- Goal: 4 * 13 = (16 - 4 * Real.sqrt 3) * (4 + Real.sqrt 3)
  rw [hex_rationalize_product]
  norm_num

/-- R_hex is a positive real number less than 1 (as expected for a
    renormalization factor that REDUCES the bare splitting). -/
theorem R_hex_pos : 0 < (4 : ℝ) / (4 + Real.sqrt 3) := by
  apply div_pos
  · norm_num
  · exact denom_pos

/-- R_hex < 1: the hexagonal renormalization REDUCES the splitting. -/
theorem R_hex_lt_one : (4 : ℝ) / (4 + Real.sqrt 3) < 1 := by
  rw [div_lt_one denom_pos]
  linarith [sqrt3_pos]

end SnowCrystal.HexagonalFactor
