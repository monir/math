/-
  EllipseProofs/LittlewoodObstruction.lean

  Counterexample and negative lemma for the exact divisibility steering
  strategy in the Littlewood conjecture.

  The ToricLittlewood module proves constructive residue surjectivity:
  given M ≥ p, one can *choose* partial quotients a_i ∈ {1,...,M}
  such that the resulting continuants hit any target mod p.

  This does NOT imply that a *given* α's CF denominators hit all
  residue classes. This file provides:

  1. A concrete counterexample: α = [0; 1, 2, 2, 2, ...] has all
     continuants odd, so q_n ≠ 0 (mod 2) for all n.

  2. A negative lemma: no proof requiring exact divisibility of
     continuants by arbitrary moduli can work in general.

  3. The correct weakening is approximate nullspace penetration in
     SL(3,ℝ)/SL(3,ℤ), not exact modular steering.

  See also: LittlewoodNotes.md in research_findings/ for the
  SL(3) lattice framework that replaces the broken path.
-/

import Mathlib.Tactic

namespace LittlewoodObstruction

/-! ## The counterexample CF: α = [0; 1, 2, 2, 2, ...]

The continuant denominators satisfy q₀ = 1, q₁ = 1, qₙ₊₂ = 2qₙ₊₁ + qₙ.
Every term is odd, blocking exact divisibility by 2.
-/

/-- The denominator recurrence for the continued fraction `[0; 1, 2, 2, 2, ...]`.
    This is the continuant sequence q₀ = 1, q₁ = 1, qₙ₊₂ = 2qₙ₊₁ + qₙ. -/
def q (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * q (n + 1) + q n

@[simp] theorem q_zero : q 0 = 1 := rfl
@[simp] theorem q_one : q 1 = 1 := rfl
theorem q_step (n : Nat) : q (n + 2) = 2 * q (n + 1) + q n := rfl

/-- Modulo 2, the recurrence collapses to qₙ₊₂ ≡ qₙ. -/
theorem q_step_mod_two (n : Nat) : q (n + 2) % 2 = q n % 2 := by
  rw [q_step]
  rw [Nat.add_mod, Nat.mul_mod]
  simp

/-- Every denominator in this sequence is odd.
    This blocks the claim "∀ m, ∃ n, q n ≡ 0 (mod m)" at m = 2. -/
theorem q_mod_two_eq_one : ∀ n : Nat, q n % 2 = 1
  | 0 => by simp [q]
  | 1 => by simp [q]
  | n + 2 => by
      rw [q_step_mod_two]
      exact q_mod_two_eq_one n

theorem q_not_zero_mod_two (n : Nat) : q n % 2 ≠ 0 := by
  have h : q n % 2 = 1 := q_mod_two_eq_one n
  simp [h]

/-- All continuants are positive. -/
theorem q_pos : ∀ n : Nat, 0 < q n
  | 0 => by simp [q]
  | 1 => by simp [q]
  | n + 2 => by rw [q_step]; have := q_pos (n + 1); have := q_pos n; omega

/-! ## Negative Lemmas -/

/-- Concrete counterexample to the steering claim:
    the continuant denominators of [0; 1, 2, 2, 2, ...] never hit 0 mod 2. -/
theorem continuants_not_globally_surjective :
    ∃ m : Nat, 1 < m ∧ ∀ n : Nat, q n % m ≠ 0 := by
  refine ⟨2, by decide, ?_⟩
  intro n
  simpa using q_not_zero_mod_two n

/-- Negative lemma for the proposed proof strategy.
    Any argument that requires exact divisibility q_n ≡ 0 (mod m) for all
    moduli m fails already for this single continued fraction. -/
theorem no_exact_divisibility_steering :
    ¬ (∀ m : Nat, 1 < m → ∃ n : Nat, q n % m = 0) := by
  intro h
  rcases h 2 (by decide) with ⟨n, hn⟩
  exact q_not_zero_mod_two n hn

/-! ## The obstruction is structural, not incidental

The parity obstruction arises because the CF [0; 1, 2, 2, 2, ...] has
all even partial quotients after the first. The recurrence
qₙ₊₂ = (even)·qₙ₊₁ + qₙ preserves parity. More generally:

- If all partial quotients after some point are even, continuant parity is
  eventually constant.
- If all partial quotients are ≡ 0 mod p, then qₙ mod p is periodic with
  period dividing 2.

This is not an exotic edge case. Any α whose CF quotients lie in a proper
ideal coset of ℤ/mℤ will have continuants avoiding some residue class.
-/

/-- The recurrence preserves parity when the quotient is even:
    if a is even, then (a·x + y) mod 2 = y mod 2. -/
theorem even_step_parity (a x y : Nat) (ha : a % 2 = 0) :
    (a * x + y) % 2 = y % 2 := by
  rw [Nat.add_mod, Nat.mul_mod, ha]
  simp

/-- For any even partial quotient a, the CF step (x,y) ↦ (ax+y, x)
    sends parity(new first) = parity(old second). In particular,
    if both components have the same parity, it is preserved forever. -/
theorem even_quotient_parity_cycle (a x y : Nat)
    (ha : a % 2 = 0) (hxy : x % 2 = y % 2) :
    (a * x + y) % 2 = x % 2 := by
  rw [even_step_parity a x y ha, hxy]

end LittlewoodObstruction
