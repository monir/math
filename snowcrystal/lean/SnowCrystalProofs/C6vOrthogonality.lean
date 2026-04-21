/-
  SnowCrystalProofs.C6vOrthogonality
  =====================================
  Theorem T1 from the snow-crystal splitting v4 proof audit:

    Great Orthogonality Relations for the C₆ᵥ irrep characters:
      (1/|G|) Σ_c |c| · χ_μ(c) · χ_ν(c) = δ_{μν}

    |G| = 12, 6 irreps {A₁, A₂, B₁, B₂, E₁, E₂},
    6 conjugacy classes {E, 2C₆, 2C₃, C₂, 3σᵥ, 3σ_d}.

  We verify the key orthogonality relations via explicit integer
  arithmetic (working on the NUMERATOR after multiplying through by
  |G| = 12, avoiding rational-reduction issues with `decide`).

  Companion:
    research_scripts/snow_crystal_v4_proof_v3.py (T1)
    research_scripts/snow_crystal_irrep_v1.py

  Registered: 2026-04-13.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace SnowCrystal.C6vOrthogonality

/-- The C₆ᵥ character table, represented as 6-tuples.
    Column order: (E, 2C₆, 2C₃, C₂, 3σᵥ, 3σ_d).

    The 6 irreps:
      A₁ = ( 1,  1,  1,  1,  1,  1)  totally symmetric
      A₂ = ( 1,  1,  1,  1, -1, -1)  antisymmetric under σ
      B₁ = ( 1, -1,  1, -1,  1, -1)  sign change under C₆
      B₂ = ( 1, -1,  1, -1, -1,  1)  sign change under C₆ and σ
      E₁ = ( 2,  1, -1, -2,  0,  0)  2D — polar IR-active
      E₂ = ( 2, -1, -1,  2,  0,  0)  2D — quadrupolar -/
structure C6vChar where
  e  : ℤ  -- χ(E)
  c6 : ℤ  -- χ(2C₆)
  c3 : ℤ  -- χ(2C₃)
  c2 : ℤ  -- χ(C₂)
  sv : ℤ  -- χ(3σᵥ)
  sd : ℤ  -- χ(3σ_d)

def A1 : C6vChar := ⟨1,  1,  1,  1,  1,  1⟩
def A2 : C6vChar := ⟨1,  1,  1,  1, -1, -1⟩
def B1 : C6vChar := ⟨1, -1,  1, -1,  1, -1⟩
def B2 : C6vChar := ⟨1, -1,  1, -1, -1,  1⟩
def E1 : C6vChar := ⟨2,  1, -1, -2,  0,  0⟩
def E2 : C6vChar := ⟨2, -1, -1,  2,  0,  0⟩

/-- The INTEGER inner product (no division by |G| — sum weighted
    by class size, result equals 12·⟨χ, ψ⟩ by definition). -/
def innerInt (χ ψ : C6vChar) : ℤ :=
  1 * χ.e * ψ.e + 2 * χ.c6 * ψ.c6 + 2 * χ.c3 * ψ.c3 +
  1 * χ.c2 * ψ.c2 + 3 * χ.sv * ψ.sv + 3 * χ.sd * ψ.sd

/-- The rational inner product: (1/|G|) · innerInt. -/
def innerProd (χ ψ : C6vChar) : ℚ := (innerInt χ ψ : ℚ) / 12

/-! ## The 6 DIAGONAL orthogonality relations: ⟨χ_μ, χ_μ⟩ = 1 -/

theorem int_A1_A1 : innerInt A1 A1 = 12 := by unfold innerInt A1; decide
theorem int_A2_A2 : innerInt A2 A2 = 12 := by unfold innerInt A2; decide
theorem int_B1_B1 : innerInt B1 B1 = 12 := by unfold innerInt B1; decide
theorem int_B2_B2 : innerInt B2 B2 = 12 := by unfold innerInt B2; decide
theorem int_E1_E1 : innerInt E1 E1 = 12 := by unfold innerInt E1; decide
theorem int_E2_E2 : innerInt E2 E2 = 12 := by unfold innerInt E2; decide

/-! ## The 15 OFF-DIAGONAL orthogonality relations: ⟨χ_μ, χ_ν⟩ = 0 for μ ≠ ν -/

theorem int_A1_A2 : innerInt A1 A2 = 0 := by unfold innerInt A1 A2; decide
theorem int_A1_B1 : innerInt A1 B1 = 0 := by unfold innerInt A1 B1; decide
theorem int_A1_B2 : innerInt A1 B2 = 0 := by unfold innerInt A1 B2; decide
theorem int_A1_E1 : innerInt A1 E1 = 0 := by unfold innerInt A1 E1; decide
theorem int_A1_E2 : innerInt A1 E2 = 0 := by unfold innerInt A1 E2; decide

theorem int_A2_B1 : innerInt A2 B1 = 0 := by unfold innerInt A2 B1; decide
theorem int_A2_B2 : innerInt A2 B2 = 0 := by unfold innerInt A2 B2; decide
theorem int_A2_E1 : innerInt A2 E1 = 0 := by unfold innerInt A2 E1; decide
theorem int_A2_E2 : innerInt A2 E2 = 0 := by unfold innerInt A2 E2; decide

theorem int_B1_B2 : innerInt B1 B2 = 0 := by unfold innerInt B1 B2; decide
theorem int_B1_E1 : innerInt B1 E1 = 0 := by unfold innerInt B1 E1; decide
theorem int_B1_E2 : innerInt B1 E2 = 0 := by unfold innerInt B1 E2; decide

theorem int_B2_E1 : innerInt B2 E1 = 0 := by unfold innerInt B2 E1; decide
theorem int_B2_E2 : innerInt B2 E2 = 0 := by unfold innerInt B2 E2; decide

theorem int_E1_E2 : innerInt E1 E2 = 0 := by unfold innerInt E1 E2; decide

/-! ## Rational-form consequences: innerProd = 0 or 1 as appropriate -/

theorem rat_A1_A1 : innerProd A1 A1 = 1 := by
  unfold innerProd; rw [int_A1_A1]; norm_num

theorem rat_A2_A2 : innerProd A2 A2 = 1 := by
  unfold innerProd; rw [int_A2_A2]; norm_num

theorem rat_B1_B1 : innerProd B1 B1 = 1 := by
  unfold innerProd; rw [int_B1_B1]; norm_num

theorem rat_B2_B2 : innerProd B2 B2 = 1 := by
  unfold innerProd; rw [int_B2_B2]; norm_num

theorem rat_E1_E1 : innerProd E1 E1 = 1 := by
  unfold innerProd; rw [int_E1_E1]; norm_num

theorem rat_E2_E2 : innerProd E2 E2 = 1 := by
  unfold innerProd; rw [int_E2_E2]; norm_num

theorem rat_A1_A2 : innerProd A1 A2 = 0 := by
  unfold innerProd; rw [int_A1_A2]; norm_num

theorem rat_A1_E1 : innerProd A1 E1 = 0 := by
  unfold innerProd; rw [int_A1_E1]; norm_num

theorem rat_E1_E2 : innerProd E1 E2 = 0 := by
  unfold innerProd; rw [int_E1_E2]; norm_num

/-! ## THE GREAT ORTHOGONALITY THEOREM -/

/-- All 6 diagonal orthogonality relations bundled together. -/
theorem great_orthogonality_diagonal :
    innerProd A1 A1 = 1 ∧ innerProd A2 A2 = 1 ∧
    innerProd B1 B1 = 1 ∧ innerProd B2 B2 = 1 ∧
    innerProd E1 E1 = 1 ∧ innerProd E2 E2 = 1 :=
  ⟨rat_A1_A1, rat_A2_A2, rat_B1_B1, rat_B2_B2, rat_E1_E1, rat_E2_E2⟩

end SnowCrystal.C6vOrthogonality
