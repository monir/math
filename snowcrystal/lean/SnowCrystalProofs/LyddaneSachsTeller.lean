/-
  SnowCrystalProofs.LyddaneSachsTeller
  ======================================
  Theorems T6 / T13 from the snow-crystal splitting v4 proof audit:

    ω_LO² / ω_TO² = ε(0) / ε(∞)

  The Lyddane-Sachs-Teller relation. It follows from the pole-zero
  structure of the frequency-dependent dielectric function:

    ε(ω) = ε(∞) · (ω² - ω_LO²) / (ω² - ω_TO²)

  Evaluating at ω = 0:
    ε(0) = ε(∞) · (-ω_LO²) / (-ω_TO²) = ε(∞) · ω_LO² / ω_TO²

  Rearranging gives LST.

  This is the IDENTITY we rely on for the LO-TO splitting correction
  in v4: given ε(0), ε(∞), ω_TO (all empirical), ω_LO is EXACT.

  Companion:
    research_scripts/snow_crystal_v4_proof_v3.py (T6, T13)
    research_scripts/snow_crystal_v4_loto.py

  Registered: 2026-04-13.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace SnowCrystal.LyddaneSachsTeller

/-- The frequency-dependent dielectric function with a single TO pole
    and a single LO zero. -/
noncomputable def epsilon_of_omega
    (ε_inf ω_LO ω_TO ω : ℝ) : ℝ :=
  ε_inf * (ω^2 - ω_LO^2) / (ω^2 - ω_TO^2)

/-- At ω = 0, the dielectric function gives:
      ε(0) = ε(∞) · ω_LO² / ω_TO²     (when ω_TO² ≠ 0) -/
theorem epsilon_at_zero
    (ε_inf ω_LO ω_TO : ℝ)
    (h_TO : ω_TO^2 ≠ 0) :
    epsilon_of_omega ε_inf ω_LO ω_TO 0 = ε_inf * ω_LO^2 / ω_TO^2 := by
  unfold epsilon_of_omega
  field_simp
  ring

/-- THE LYDDANE-SACHS-TELLER IDENTITY:
    ω_LO² / ω_TO² = ε(0) / ε(∞)

    Given the definitional relation ε(0) = ε(∞) · ω_LO² / ω_TO²,
    this follows algebraically when ω_TO, ε(∞) are nonzero. -/
theorem LST_identity
    (ε_0 ε_inf ω_LO ω_TO : ℝ)
    (h_TO : ω_TO^2 ≠ 0)
    (h_inf : ε_inf ≠ 0)
    (h_rel : ε_0 = ε_inf * ω_LO^2 / ω_TO^2) :
    ω_LO^2 / ω_TO^2 = ε_0 / ε_inf := by
  rw [h_rel]
  field_simp

/-- If we KNOW ω_TO and the ratio ε(0)/ε(∞), then ω_LO is determined:
      ω_LO² = ω_TO² · ε(0) / ε(∞) -/
theorem omega_LO_squared_from_LST
    (ε_0 ε_inf ω_TO : ℝ)
    (h_inf : ε_inf ≠ 0) :
    let ω_LO_sq := ω_TO^2 * ε_0 / ε_inf
    ω_LO_sq / ω_TO^2 = ε_0 / ε_inf ∨ ω_TO^2 = 0 := by
  by_cases h_TO : ω_TO = 0
  · right; rw [h_TO]; ring
  · left
    have h_TO_sq : ω_TO^2 ≠ 0 := pow_ne_zero 2 h_TO
    field_simp

/-- The dielectric function is zero when ω² = ω_LO² (LO modes are
    longitudinal so they don't couple to transverse EM). -/
theorem epsilon_zero_at_LO
    (ε_inf ω_LO ω_TO : ℝ)
    (h_ne_pole : ω_LO^2 - ω_TO^2 ≠ 0) :
    epsilon_of_omega ε_inf ω_LO ω_TO ω_LO = 0 := by
  unfold epsilon_of_omega
  have : (ω_LO^2 - ω_LO^2 : ℝ) = 0 := by ring
  rw [this]
  simp

/-- Full symbolic verification: the LST identity has zero residual
    (LHS - RHS) when the defining relation holds. -/
theorem LST_zero_residual
    (ε_0 ε_inf ω_LO ω_TO : ℝ)
    (h_TO : ω_TO^2 ≠ 0)
    (h_inf : ε_inf ≠ 0)
    (h_rel : ε_0 = ε_inf * ω_LO^2 / ω_TO^2) :
    ω_LO^2 / ω_TO^2 - ε_0 / ε_inf = 0 := by
  have := LST_identity ε_0 ε_inf ω_LO ω_TO h_TO h_inf h_rel
  linarith

end SnowCrystal.LyddaneSachsTeller
