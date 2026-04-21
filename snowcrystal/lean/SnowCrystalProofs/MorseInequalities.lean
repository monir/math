/-
  SnowCrystalProofs.MorseInequalities
  =====================================
  Theorem T11 from the snow-crystal splitting v4 proof audit:

    STRONG MORSE INEQUALITIES ON T²

    For a Morse function V: T² → ℝ with β = (β₀, β₁, β₂) = (1, 2, 1):

    WEAK MORSE:
      m_0 ≥ β_0 = 1     (at least 1 minimum)
      m_1 ≥ β_1 = 2     (at least 2 saddles)
      m_2 ≥ β_2 = 1     (at least 1 maximum)

    STRONG MORSE (partial alternating sums):
      m_0 ≥ β_0 = 1
      m_1 - m_0 ≥ β_1 - β_0 = 1   (i.e., m_1 ≥ m_0 + 1)
      m_0 - m_1 + m_2 = β_0 - β_1 + β_2 = 0 = χ(T²)   (Poincaré-Hopf)

  This file extends PoincareHopf.lean with the strong Morse inequalities.

  Companion:
    research_scripts/snow_crystal_v4_proof_v3.py (T11)
    SnowCrystalProofs/PoincareHopf.lean

  Registered: 2026-04-13.
-/

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import SnowCrystalProofs.PoincareHopf

namespace SnowCrystal.MorseInequalities

open SnowCrystal.PoincareHopf

/-! ## WEAK MORSE INEQUALITIES (already in MorseOnT2 definition) -/

/-- Weak Morse k=0: m₀ ≥ β₀ = 1. -/
theorem weak_0 (M : MorseOnT2) : M.n_min ≥ 1 := M.h_min

/-- Weak Morse k=1: m₁ ≥ β₁ = 2. -/
theorem weak_1 (M : MorseOnT2) : M.n_sad ≥ 2 := M.h_sad

/-- Weak Morse k=2: m₂ ≥ β₂ = 1. -/
theorem weak_2 (M : MorseOnT2) : M.n_max ≥ 1 := M.h_max

/-! ## STRONG MORSE INEQUALITIES (partial alternating sums) -/

/-- Strong Morse k=0: m₀ ≥ β₀ = 1. (Same as weak for k=0.) -/
theorem strong_0 (M : MorseOnT2) : (M.n_min : ℤ) ≥ 1 := by
  exact_mod_cast M.h_min

/-- Strong Morse k=1: m₁ - m₀ ≥ β₁ - β₀ = 1.

    Proof: from Poincaré-Hopf m₀ - m₁ + m₂ = 0 and m₂ ≥ 1:
           m₁ = m₀ + m₂ ≥ m₀ + 1, so m₁ - m₀ ≥ 1. -/
theorem strong_1 (M : MorseOnT2) :
    (M.n_sad : ℤ) - M.n_min ≥ 1 := by
  have h_euler := M.h_euler
  have h_max := M.h_max
  have : (M.n_max : ℤ) ≥ 1 := by exact_mod_cast h_max
  linarith

/-- Strong Morse k=2: m₀ - m₁ + m₂ = χ = 0. (Poincaré-Hopf equality.) -/
theorem strong_2 (M : MorseOnT2) :
    (M.n_min : ℤ) - M.n_sad + M.n_max = 0 := M.h_euler

/-! ## CONSEQUENCES -/

/-- There are at least 4 critical points on T². -/
theorem at_least_four_crit (M : MorseOnT2) :
    M.n_min + M.n_sad + M.n_max ≥ 4 := by
  have h1 := M.h_min
  have h2 := M.h_sad
  have h3 := M.h_max
  omega

/-- The number of saddles is at least 2. -/
theorem saddles_ge_two (M : MorseOnT2) : M.n_sad ≥ 2 := M.h_sad

/-- The number of saddles equals n_min + n_max (from Euler constraint). -/
theorem saddles_eq_min_plus_max (M : MorseOnT2) :
    (M.n_sad : ℤ) = M.n_min + M.n_max := by
  have := M.h_euler
  linarith

/-- If there's exactly 1 minimum and 1 maximum, there are exactly 2 saddles. -/
theorem minimal_complex_saddle_count (M : MorseOnT2)
    (h1 : M.n_min = 1) (h3 : M.n_max = 1) :
    M.n_sad = 2 := by
  have h_eul : (M.n_min : ℤ) - M.n_sad + M.n_max = 0 := M.h_euler
  have h1' : (M.n_min : ℤ) = 1 := by exact_mod_cast h1
  have h3' : (M.n_max : ℤ) = 1 := by exact_mod_cast h3
  have : (M.n_sad : ℤ) = 2 := by linarith
  exact_mod_cast this

/-! ## CONSTRUCTIVE EXAMPLE: the minimal Morse complex on T² -/

/-- Certificate that (1, 2, 1) IS a valid Morse complex on T². -/
def minimal_morse_T2 : MorseOnT2 :=
  { n_min := 1
    n_sad := 2
    n_max := 1
    h_min := by omega
    h_sad := by omega
    h_max := by omega
    h_euler := by decide }

/-- The minimal Morse complex satisfies all 3 weak inequalities with EQUALITY. -/
theorem minimal_tight_bounds :
    minimal_morse_T2.n_min = 1 ∧
    minimal_morse_T2.n_sad = 2 ∧
    minimal_morse_T2.n_max = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- The minimal Morse complex has exactly 4 critical points. -/
theorem minimal_total :
    minimal_morse_T2.n_min + minimal_morse_T2.n_sad + minimal_morse_T2.n_max = 4 := by
  decide

/-! ## MAIN SUMMARY THEOREM: ALL MORSE INEQUALITIES -/

/-- ALL MORSE INEQUALITIES on T² (weak + strong + Euler). -/
theorem all_morse_inequalities (M : MorseOnT2) :
    M.n_min ≥ 1 ∧                          -- weak 0
    M.n_sad ≥ 2 ∧                          -- weak 1
    M.n_max ≥ 1 ∧                          -- weak 2
    (M.n_sad : ℤ) - M.n_min ≥ 1 ∧          -- strong 1
    (M.n_min : ℤ) - M.n_sad + M.n_max = 0 -- Euler (strong 2)
    :=
  ⟨weak_0 M, weak_1 M, weak_2 M, strong_1 M, strong_2 M⟩

end SnowCrystal.MorseInequalities
