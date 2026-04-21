/-
  SnowCrystalProofs.GaugeInvariance
  ===================================
  Theorem T12 from the snow-crystal splitting v4 proof audit:

    ACOUSTIC SUM RULE FROM GAUGE INVARIANCE:
    If the polarization P(u) = (Σ_α Z*_α) · u vanishes for ALL
    translations u, then Σ_α Z*_α = 0.

  This is STRONGER than mere charge neutrality (Σ q_α = 0):
  it's a statement about the POLARIZATION DERIVATIVES (Born charges).

  We formalize the MATH KERNEL:
    "A linear functional that vanishes on all vectors is trivial"
    equivalently:
    "If c · u = 0 for all u : ℝ, then c = 0"
  (and the 3D vector version).

  The EMPIRICAL part — that crystal translations ARE gauge
  transformations of the polarization — is accepted as a hypothesis.

  Companion:
    research_scripts/snow_crystal_v4_proof_v3.py (T12)

  Registered: 2026-04-13.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace SnowCrystal.GaugeInvariance

/-! ## KERNEL 1: scalar version -/

/-- If c · u = 0 for all u : ℝ, then c = 0.
    (Take u = 1.) -/
theorem scalar_vanishing_functional (c : ℝ)
    (h : ∀ u : ℝ, c * u = 0) : c = 0 := by
  have := h 1
  linarith

/-- Polarization form: if P(u) = c · u for a sum c of Born-charge-like
    scalars, and P(u) = 0 for all u, then c = 0. -/
theorem scalar_sum_rule (charges : List ℝ)
    (h_gauge : ∀ u : ℝ, (charges.foldr (· + ·) 0) * u = 0) :
    charges.foldr (· + ·) 0 = 0 :=
  scalar_vanishing_functional _ h_gauge

/-! ## KERNEL 2: per-component 3D version -/

/-- Restricting to the x-component: if (c₁, c₂, c₃) · (u, 0, 0) = 0
    for all u, then c₁ = 0. Similarly for y, z. -/
theorem component_x (c₁ c₂ c₃ : ℝ)
    (h : ∀ u : ℝ, c₁ * u + c₂ * 0 + c₃ * 0 = 0) : c₁ = 0 := by
  have := h 1
  linarith

theorem component_y (c₁ c₂ c₃ : ℝ)
    (h : ∀ u : ℝ, c₁ * 0 + c₂ * u + c₃ * 0 = 0) : c₂ = 0 := by
  have := h 1
  linarith

theorem component_z (c₁ c₂ c₃ : ℝ)
    (h : ∀ u : ℝ, c₁ * 0 + c₂ * 0 + c₃ * u = 0) : c₃ = 0 := by
  have := h 1
  linarith

/-- Full 3D gauge theorem: if the dot product (c · u) = 0 for all u ∈ ℝ³,
    then c = 0 (as a 3-vector).

    Physics: this is exactly the statement that the acoustic sum rule
    Σ Z*_α = 0 (as a 3×3 tensor, diagonal components) follows from
    vanishing of polarization under rigid translation. -/
theorem vanishing_dot_product (c₁ c₂ c₃ : ℝ)
    (h : ∀ u₁ u₂ u₃ : ℝ, c₁ * u₁ + c₂ * u₂ + c₃ * u₃ = 0) :
    c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have := h 1 0 0
    linarith
  · have := h 0 1 0
    linarith
  · have := h 0 0 1
    linarith

/-! ## KERNEL 3: the acoustic sum rule as a direct corollary -/

/-- GAUGE INVARIANCE IMPLIES THE ACOUSTIC SUM RULE:
    For a list of Born charges (Z_α)_α with total Z_total := Σ Z_α,
    if the polarization P(u) = Z_total · u vanishes for all u,
    then Z_total = 0. -/
theorem acoustic_sum_from_gauge
    (Z_total : ℝ)
    (h_gauge : ∀ u : ℝ, Z_total * u = 0) : Z_total = 0 := by
  exact scalar_vanishing_functional Z_total h_gauge

/-- Alternative form: direct formulation on lists of atoms. -/
theorem acoustic_sum_list (Z : List ℝ)
    (h_gauge : ∀ u : ℝ, (Z.foldr (· + ·) 0) * u = 0) :
    Z.foldr (· + ·) 0 = 0 :=
  scalar_vanishing_functional _ h_gauge

/-! ## Explicit verification for the ideal H₂O unit -/

/-- For a single H₂O unit with Z_H = 13/25, Z_O = -26/25,
    the list [Z_H, Z_H, Z_O] sums to zero,
    which IS the acoustic sum rule (by the gauge theorem above). -/
theorem h2o_zero_sum : [(13 : ℝ)/25, 13/25, -26/25].foldr (· + ·) 0 = 0 := by
  simp [List.foldr]
  norm_num

end SnowCrystal.GaugeInvariance
