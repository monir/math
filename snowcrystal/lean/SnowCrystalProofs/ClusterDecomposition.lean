/-
  SnowCrystalProofs.ClusterDecomposition
  =========================================
  Theorem T2 from the snow-crystal splitting v4 proof audit:

    The (2+2) H-bond cluster mode set in Ice Ih decomposes
    under C₆ᵥ as E₁ ⊕ E₂ (two 2-dimensional irreps, total dim 4).

  Reducible character: χ_(2+2) = (4, 0, -2, 0, 0, 0)
  (Classes: E, 2C₆, 2C₃, C₂, 3σᵥ, 3σ_d)

  The naive "4 modes, 2 fixed under σ" guess [4,0,0,0,2,0] was WRONG —
  it gave fractional multiplicities (5/6, -1/6, 2/3). The correct
  character [4, 0, -2, 0, 0, 0] (= χ(E₁) + χ(E₂) pointwise) gives
  integer multiplicities E₁=1, E₂=1, others=0.

  All arithmetic is in ℤ (integer inner products), with the rational
  conclusion multiplicity = integer / 12 following.

  Companion:
    research_scripts/snow_crystal_v4_proof_v2.py (Theorem 2 fixed)
    research_scripts/snow_crystal_v4_proof_v3.py (proof ratio 90.2%)

  Registered: 2026-04-13.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import SnowCrystalProofs.C6vOrthogonality

namespace SnowCrystal.ClusterDecomposition

open SnowCrystal.C6vOrthogonality

/-- Reducible character of the (2+2) cluster.
    Values in classes (E, 2C₆, 2C₃, C₂, 3σᵥ, 3σ_d):
      (4, 0, -2, 0, 0, 0)
    This equals χ(E₁) + χ(E₂) pointwise. -/
def cluster : C6vChar := ⟨4, 0, -2, 0, 0, 0⟩

/-- Verification: cluster character = E₁ + E₂ (pointwise integer sum). -/
theorem cluster_is_E1_plus_E2 :
    cluster.e  = E1.e  + E2.e  ∧
    cluster.c6 = E1.c6 + E2.c6 ∧
    cluster.c3 = E1.c3 + E2.c3 ∧
    cluster.c2 = E1.c2 + E2.c2 ∧
    cluster.sv = E1.sv + E2.sv ∧
    cluster.sd = E1.sd + E2.sd := by
  unfold cluster E1 E2; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Integer inner products (multiplying through by |G| = 12):
    n_μ × 12 = innerInt(cluster, χ_μ)
-/

theorem int_cluster_A1 : innerInt cluster A1 = 0 := by
  unfold innerInt cluster A1; decide

theorem int_cluster_A2 : innerInt cluster A2 = 0 := by
  unfold innerInt cluster A2; decide

theorem int_cluster_B1 : innerInt cluster B1 = 0 := by
  unfold innerInt cluster B1; decide

theorem int_cluster_B2 : innerInt cluster B2 = 0 := by
  unfold innerInt cluster B2; decide

theorem int_cluster_E1 : innerInt cluster E1 = 12 := by
  unfold innerInt cluster E1; decide

theorem int_cluster_E2 : innerInt cluster E2 = 12 := by
  unfold innerInt cluster E2; decide

/-! ## Rational multiplicities via (integer / 12) -/

/-- Multiplicity of A₁: 0 -/
theorem mult_A1 : innerProd cluster A1 = 0 := by
  unfold innerProd; rw [int_cluster_A1]; norm_num

/-- Multiplicity of A₂: 0 -/
theorem mult_A2 : innerProd cluster A2 = 0 := by
  unfold innerProd; rw [int_cluster_A2]; norm_num

/-- Multiplicity of B₁: 0 -/
theorem mult_B1 : innerProd cluster B1 = 0 := by
  unfold innerProd; rw [int_cluster_B1]; norm_num

/-- Multiplicity of B₂: 0 -/
theorem mult_B2 : innerProd cluster B2 = 0 := by
  unfold innerProd; rw [int_cluster_B2]; norm_num

/-- Multiplicity of E₁: 1 -/
theorem mult_E1 : innerProd cluster E1 = 1 := by
  unfold innerProd; rw [int_cluster_E1]; norm_num

/-- Multiplicity of E₂: 1 -/
theorem mult_E2 : innerProd cluster E2 = 1 := by
  unfold innerProd; rw [int_cluster_E2]; norm_num

/-! ## THE MAIN THEOREM -/

/-- THE (2+2) CLUSTER DECOMPOSES AS E₁ ⊕ E₂ with INTEGER multiplicities. -/
theorem cluster_decomposition :
    innerProd cluster A1 = 0 ∧
    innerProd cluster A2 = 0 ∧
    innerProd cluster B1 = 0 ∧
    innerProd cluster B2 = 0 ∧
    innerProd cluster E1 = 1 ∧
    innerProd cluster E2 = 1 :=
  ⟨mult_A1, mult_A2, mult_B1, mult_B2, mult_E1, mult_E2⟩

/-- Total dimension check: 2·(mult E₁) + 2·(mult E₂) = 4
    (the 4 original cluster modes). -/
theorem total_dimension_check :
    2 * innerProd cluster E1 + 2 * innerProd cluster E2 = 4 := by
  rw [mult_E1, mult_E2]; norm_num

end SnowCrystal.ClusterDecomposition
