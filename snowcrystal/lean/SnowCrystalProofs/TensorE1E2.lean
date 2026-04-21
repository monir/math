/-
  SnowCrystalProofs.TensorE1E2
  ==============================
  Theorem T9 from the snow-crystal splitting v4 proof audit:

    E₁ ⊗ E₂ = B₁ ⊕ B₂ ⊕ E₁   (decomposition in C₆ᵥ)

  The character of E₁ ⊗ E₂ is the pointwise PRODUCT:
    χ(E₁ ⊗ E₂)(g) = χ(E₁)(g) · χ(E₂)(g)

  For C₆ᵥ:
    χ(E₁) = (2, 1, -1, -2, 0, 0)
    χ(E₂) = (2, -1, -1, 2, 0, 0)
    χ(E₁ ⊗ E₂) = (4, -1, 1, -4, 0, 0)

  Decomposition (via inner products):
    B₁:  1
    B₂:  1
    E₁:  1
    (others: 0)
    Total dim: 1 + 1 + 2 = 4  ✓  (= dim E₁ × dim E₂ = 2 × 2)

  Physical meaning: if lower cluster modes are E₁ and upper are E₂,
  their COUPLING (needed for inter-cluster Raman processes) transforms
  as B₁ + B₂ + E₁.

  Companion:
    research_scripts/snow_crystal_v4_proof_v3.py (T9)

  Registered: 2026-04-13.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import SnowCrystalProofs.C6vOrthogonality

namespace SnowCrystal.TensorE1E2

open SnowCrystal.C6vOrthogonality

/-- The E₁ ⊗ E₂ tensor character (pointwise product). -/
def E1_tensor_E2 : C6vChar := ⟨4, -1, 1, -4, 0, 0⟩

/-- Verification that E1_tensor_E2 equals the pointwise product. -/
theorem E1_tensor_E2_is_product :
    E1_tensor_E2.e  = E1.e  * E2.e  ∧
    E1_tensor_E2.c6 = E1.c6 * E2.c6 ∧
    E1_tensor_E2.c3 = E1.c3 * E2.c3 ∧
    E1_tensor_E2.c2 = E1.c2 * E2.c2 ∧
    E1_tensor_E2.sv = E1.sv * E2.sv ∧
    E1_tensor_E2.sd = E1.sd * E2.sd := by
  unfold E1_tensor_E2 E1 E2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Integer inner products (multiplying through by |G| = 12) -/

theorem int_E1E2_A1 : innerInt E1_tensor_E2 A1 = 0 := by
  unfold innerInt E1_tensor_E2 A1; decide

theorem int_E1E2_A2 : innerInt E1_tensor_E2 A2 = 0 := by
  unfold innerInt E1_tensor_E2 A2; decide

theorem int_E1E2_B1 : innerInt E1_tensor_E2 B1 = 12 := by
  unfold innerInt E1_tensor_E2 B1; decide

theorem int_E1E2_B2 : innerInt E1_tensor_E2 B2 = 12 := by
  unfold innerInt E1_tensor_E2 B2; decide

theorem int_E1E2_E1 : innerInt E1_tensor_E2 E1 = 12 := by
  unfold innerInt E1_tensor_E2 E1; decide

theorem int_E1E2_E2 : innerInt E1_tensor_E2 E2 = 0 := by
  unfold innerInt E1_tensor_E2 E2; decide

/-! ## Rational multiplicities -/

theorem mult_A1 : innerProd E1_tensor_E2 A1 = 0 := by
  unfold innerProd; rw [int_E1E2_A1]; norm_num

theorem mult_A2 : innerProd E1_tensor_E2 A2 = 0 := by
  unfold innerProd; rw [int_E1E2_A2]; norm_num

theorem mult_B1 : innerProd E1_tensor_E2 B1 = 1 := by
  unfold innerProd; rw [int_E1E2_B1]; norm_num

theorem mult_B2 : innerProd E1_tensor_E2 B2 = 1 := by
  unfold innerProd; rw [int_E1E2_B2]; norm_num

theorem mult_E1 : innerProd E1_tensor_E2 E1 = 1 := by
  unfold innerProd; rw [int_E1E2_E1]; norm_num

theorem mult_E2 : innerProd E1_tensor_E2 E2 = 0 := by
  unfold innerProd; rw [int_E1E2_E2]; norm_num

/-! ## THE MAIN THEOREM -/

/-- THE E₁ ⊗ E₂ DECOMPOSITION: B₁ ⊕ B₂ ⊕ E₁ -/
theorem E1_tensor_E2_decomposition :
    innerProd E1_tensor_E2 A1 = 0 ∧
    innerProd E1_tensor_E2 A2 = 0 ∧
    innerProd E1_tensor_E2 B1 = 1 ∧
    innerProd E1_tensor_E2 B2 = 1 ∧
    innerProd E1_tensor_E2 E1 = 1 ∧
    innerProd E1_tensor_E2 E2 = 0 :=
  ⟨mult_A1, mult_A2, mult_B1, mult_B2, mult_E1, mult_E2⟩

/-- Dimension check: 1·(B₁) + 1·(B₂) + 2·(E₁) = 4 = 2·2 = dim(E₁)·dim(E₂). -/
theorem E1_tensor_E2_dim :
    1 * innerProd E1_tensor_E2 B1 +
    1 * innerProd E1_tensor_E2 B2 +
    2 * innerProd E1_tensor_E2 E1 = 4 := by
  rw [mult_B1, mult_B2, mult_E1]; norm_num

end SnowCrystal.TensorE1E2
