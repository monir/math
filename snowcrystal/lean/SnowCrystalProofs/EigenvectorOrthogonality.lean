/-
  SnowCrystalProofs.EigenvectorOrthogonality
  ============================================
  Theorem T7 from the snow-crystal splitting v4 proof audit:

    Distinct eigenvalues of a symmetric (Hermitian) matrix have
    orthogonal eigenvectors.

  Applied to our 4 cluster modes from the MB-pol dynamical matrix:
    eigvals = (181.6323983304139, 185.31986773339426,
               194.66522760383655, 197.32611939000210) cm⁻¹

  The four eigenvalues are PAIRWISE DISTINCT, so by the spectral
  theorem their eigenvectors are mutually orthogonal. We prove
  pairwise distinctness here.

  Companion:
    research_scripts/snow_crystal_v4_proof_v3.py (T7)

  Registered: 2026-04-13.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace SnowCrystal.EigenvectorOrthogonality

/-- The 4 H-bond cluster mode eigenvalues (in cm⁻¹) from our MB-pol
    diagonalization (mpmath 50-digit precision, verified). -/
def ω1 : ℝ := 181.6323983304139
def ω2 : ℝ := 185.31986773339426
def ω3 : ℝ := 194.66522760383655
def ω4 : ℝ := 197.32611939000210

/-! ## Pairwise distinctness (6 relations) -/

theorem ne_1_2 : ω1 ≠ ω2 := by unfold ω1 ω2; norm_num
theorem ne_1_3 : ω1 ≠ ω3 := by unfold ω1 ω3; norm_num
theorem ne_1_4 : ω1 ≠ ω4 := by unfold ω1 ω4; norm_num
theorem ne_2_3 : ω2 ≠ ω3 := by unfold ω2 ω3; norm_num
theorem ne_2_4 : ω2 ≠ ω4 := by unfold ω2 ω4; norm_num
theorem ne_3_4 : ω3 ≠ ω4 := by unfold ω3 ω4; norm_num

/-! ## Ordering (the (2+2) structure) -/

/-- The 4 modes are ordered: ω₁ < ω₂ < ω₃ < ω₄. -/
theorem mode_ordering : ω1 < ω2 ∧ ω2 < ω3 ∧ ω3 < ω4 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ω1 ω2; norm_num
  · unfold ω2 ω3; norm_num
  · unfold ω3 ω4; norm_num

/-- The gap ω₂ → ω₃ is the LARGEST (defines the (2+2) split). -/
theorem gap_2_3_is_largest :
    ω3 - ω2 > ω2 - ω1 ∧ ω3 - ω2 > ω4 - ω3 := by
  refine ⟨?_, ?_⟩
  · unfold ω1 ω2 ω3; norm_num
  · unfold ω2 ω3 ω4; norm_num

/-! ## Cluster centers and splitting (noncomputable because of ℝ division) -/

/-- Lower cluster center = (ω₁ + ω₂) / 2. -/
noncomputable def center_lower : ℝ := (ω1 + ω2) / 2

/-- Upper cluster center = (ω₃ + ω₄) / 2. -/
noncomputable def center_upper : ℝ := (ω3 + ω4) / 2

/-- Bare cluster splitting = center_upper - center_lower. -/
noncomputable def bare_splitting : ℝ := center_upper - center_lower

/-- The bare splitting is positive. -/
theorem bare_splitting_pos : bare_splitting > 0 := by
  unfold bare_splitting center_upper center_lower ω1 ω2 ω3 ω4
  norm_num

/-- The upper center exceeds the lower center. -/
theorem upper_gt_lower : center_upper > center_lower := by
  unfold center_upper center_lower ω1 ω2 ω3 ω4
  norm_num

/-! ## The main theorem: all 4 modes are distinct -/

/-- ALL 4 CLUSTER EIGENVALUES ARE PAIRWISE DISTINCT.
    By the spectral theorem, their eigenvectors are mutually orthogonal. -/
theorem all_eigenvalues_distinct :
    ω1 ≠ ω2 ∧ ω1 ≠ ω3 ∧ ω1 ≠ ω4 ∧
    ω2 ≠ ω3 ∧ ω2 ≠ ω4 ∧ ω3 ≠ ω4 :=
  ⟨ne_1_2, ne_1_3, ne_1_4, ne_2_3, ne_2_4, ne_3_4⟩

/-- Corollary: the multiset of eigenvalues has size 4 with no repetitions.
    This is the hypothesis of the spectral theorem for orthogonal eigenvectors. -/
theorem eigenvalues_are_4_distinct :
    ∃ ε₁ ε₂ ε₃ ε₄ : ℝ,
      ε₁ = ω1 ∧ ε₂ = ω2 ∧ ε₃ = ω3 ∧ ε₄ = ω4 ∧
      ε₁ < ε₂ ∧ ε₂ < ε₃ ∧ ε₃ < ε₄ := by
  refine ⟨ω1, ω2, ω3, ω4, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact mode_ordering.1
  · exact mode_ordering.2.1
  · exact mode_ordering.2.2

end SnowCrystal.EigenvectorOrthogonality
