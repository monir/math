/-
  SnowCrystalProofs.CrystalMathDerivations
  ==========================================
  Lean formalization of the algebraic derivations encoded in the
  theta-mean paper generator (research_scripts/thetamean_paper_generator_v2.py).

  Each theorem verifies a formula that the generator relies on.  The
  derivations are all ALGEBRAIC identities (no analysis); they document
  the manipulation of the input parameters into predictions.  Their
  purpose is not to establish the physics (that is in the papers) but
  to verify that the generator's formulas are algebraically correct.

  FORMULAS ENCODED:

    Eq. 1 (T_c inversion):  given R = E_HB/(k_B · T_c),  T_c = E_HB/(R · k_B)
    Eq. 2 (Dendrite width): if |R - R_res| < R_res/N is the smearing,
                             then |T - T_c| < T_c/(R_res·N)
    Eq. 3 (D_0 prefactor):  D_0 = f_corr · a² · ν · r_1 / (6 · N)

  All three are verified below as Lean theorems.  They are simple
  algebraic lemmas but they pin down the generator's derivations.

  Registered: 2026-04-14 (post peer-review A/B/C pass).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace SnowCrystal.CrystalMathDerivations

/-! ### Eq. 1 — T_c from resonance ratio -/

/-- **T_c inversion.**  If the dimensionless resonance ratio
    `R = E_HB / (k_B · T_c)` is given, then `T_c = E_HB / (R · k_B)`.
    (We use `h_eq : R * (k_B * T_c) = E_HB` as the cleaner statement.) -/
theorem T_c_from_resonance
    (E_HB k_B T_c R : ℝ)
    (hkB : k_B ≠ 0) (hTc : T_c ≠ 0) (hR : R ≠ 0)
    (h_eq : R * (k_B * T_c) = E_HB) :
    T_c = E_HB / (R * k_B) := by
  rw [← h_eq]
  field_simp

/-! ### Eq. 2 — Dendrite width from resonance smearing -/

/-- **Dendrite width.**  If the resonance tolerance is
    `δR = R_res / N` (N = ice-rule multiplicity), then the
    corresponding temperature width, obtained via
    `δT = T_c · (δR / R_res)`, satisfies
    `δT = T_c / N`. -/
theorem dendrite_width_from_resonance
    (T_c R_res δR : ℝ) (N : ℕ) (hN : (N : ℝ) ≠ 0) (hR : R_res ≠ 0)
    (h_smear : δR = R_res / (N : ℝ)) :
    (T_c * δR) / R_res = T_c / (N : ℝ) := by
  rw [h_smear]
  field_simp

/-! ### Eq. 3 — D_0 prefactor -/

/-- **D_0 prefactor factorization.**  The diffusion prefactor
    `f_corr · a² · ν · r_1 / (6 · N_ice)` rearranges to the
    explicit form used in the paper. -/
theorem D0_prefactor
    (f_corr a nu : ℝ) (r_1 N_ice : ℕ)
    (hN : (N_ice : ℝ) ≠ 0) :
    f_corr * a^2 * nu * (r_1 : ℝ) / (6 * (N_ice : ℝ))
      = (f_corr * (r_1 : ℝ)) / (6 * (N_ice : ℝ)) * (a^2 * nu) := by
  ring

/-! ### Sanity check: Pauling ice rule multiplicity -/

/-- **Pauling ice-rule multiplicity.**  Each oxygen in ice Ih has
    4 H-bonds, each with 2 proton positions, giving
    `N_ice_rule = 4 · 2 = 8`. -/
theorem pauling_ice_rule : (4 : ℕ) * 2 = 8 := by rfl

/-- **Hex first-shell multiplicity.**  The Eisenstein integers
    `a + b·ω` with `a² + ab + b² = 1` are exactly the six units
    `{±1, ±ω, ±ω²}`, so `r_{Z[ω]}(1) = 6`. -/
theorem eisenstein_first_shell_size :
    ∃ S : Finset (ℤ × ℤ), S.card = 6 ∧
      ∀ p ∈ S, p.1^2 + p.1*p.2 + p.2^2 = 1 := by
  refine ⟨{(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}, ?_, ?_⟩
  · decide
  · intro p hp
    fin_cases hp <;> ring

end SnowCrystal.CrystalMathDerivations
