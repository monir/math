/-
  EllipseProofs/CFInstances.lean

  Instantiations of CFData for the seven CF theorems.
  Each provides closed-form solutions, recurrence proofs,
  non-vanishing, multiplier bounds, and convergence via compositor.

  Paper reference: cfproof_strip13.tex, Theorems A through G
-/

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import EllipseProofs.CFCompositor

open Finset

/-! ## Theorem F: 8/π²

Closed form f_n = 2^n(n+1)(2n+1).
Multiplier: M_n = n²/((n+1)(2n+1)) ≤ 1/2.
-/

section TheoremF_Instance

def f_F (n : ℕ) : ℚ := 2 ^ n * ((n : ℚ) + 1) * (2 * n + 1)

theorem f_F_pos (n : ℕ) : 0 < f_F n := by simp only [f_F]; positivity
theorem f_F_ne_zero (n : ℕ) : f_F n ≠ 0 := ne_of_gt (f_F_pos n)

-- No separate power lemmas needed — we use k-based indexing to avoid ℕ subtraction

noncomputable def α_F (n : ℕ) : ℚ :=
  if n < 2 then 0
  else 2 * (3 * (n : ℚ) ^ 2 + 3 * n + 1) / ((n : ℚ) * (2 * n - 1))

noncomputable def β_F (n : ℕ) : ℚ :=
  if n < 2 then 0
  else -4 * (n : ℚ) ^ 2 / (((n : ℚ) - 1) * (2 * n - 3))

-- Recurrence proof for the closed form (using k+2 to avoid ℕ subtraction)
theorem f_F_rec (n : ℕ) (hn : n ≥ 2) :
    f_F n = α_F n * f_F (n - 1) + β_F n * f_F (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  -- Now n = k+2, n-1 = k+1, n-2 = k
  simp only [show k + 2 - 1 = k + 1 from by omega, show k + 2 - 2 = k from by omega]
  simp only [f_F, α_F, β_F, if_neg (show ¬k + 2 < 2 by omega)]
  -- All terms are k, k+1, k+2 with no ℕ subtraction
  have h1 : (k : ℚ) + 2 ≠ 0 := by positivity
  have h2 : 2 * ((k : ℚ) + 2) - 1 ≠ 0 := by
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k; linarith
  have h3 : (1 : ℚ) + (k : ℚ) ≠ 0 := by positivity
  have h4 : 2 * ((k : ℚ) + 2) - 3 ≠ 0 := by
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k; linarith
  have hp2 : (2 : ℚ) ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
  have hp1 : (2 : ℚ) ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
  rw [hp2, hp1]; push_cast; field_simp
  -- field_simp leaves (1+↑k)⁻¹ terms; close via linear_combination
  have hmul := mul_inv_cancel₀ h3
  linear_combination (96 + 400 * (k : ℚ) + 584 * (k : ℚ) ^ 2 + 396 * (k : ℚ) ^ 3 +
    128 * (k : ℚ) ^ 4 + 16 * (k : ℚ) ^ 5) * hmul

-- The multiplier in closed form
theorem M_F_eq (n : ℕ) (hn : n ≥ 2) :
    β_F n * (f_F (n - 2) / f_F n) =
      -(n : ℚ) ^ 2 / (((n : ℚ) + 1) * (2 * n + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 2 = k from by omega]
  simp only [β_F, f_F, if_neg (show ¬k + 2 < 2 by omega)]
  have hp : (2 : ℚ) ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
  rw [hp]; push_cast
  have hk1 : (1 : ℚ) + (k : ℚ) ≠ 0 := by positivity
  have hk2 : 2 * (k : ℚ) + 1 ≠ 0 := by have := Nat.cast_nonneg (α := ℚ) k; linarith
  have hk3 : (k : ℚ) + 3 ≠ 0 := by positivity
  have hk5 : 2 * (k : ℚ) + 5 ≠ 0 := by positivity
  have h2k : (2 : ℚ) ^ k ≠ 0 := (pow_pos (by norm_num : (0:ℚ) < 2) k).ne'
  have hprod : (1 : ℚ) + ↑k * 3 + ↑k ^ 2 * 2 ≠ 0 := by positivity
  field_simp [hk1, hk2, hk3, hk5, h2k]
  -- Goal: -(a * x * 3) + ... = -1 where x = (1+3k+2k²)⁻¹
  -- This is just -(1+3k+2k²) * (1+3k+2k²)⁻¹ = -1
  have h := mul_inv_cancel₀ hprod
  linear_combination -h

theorem M_F_bound (n : ℕ) (hn : n ≥ 2) :
    |β_F n * (f_F (n - 2) / f_F n)| ≤ 1 / 2 := by
  rw [M_F_eq n hn]
  rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg _),
      abs_of_pos (by positivity : (0 : ℚ) < ((n : ℚ) + 1) * (2 * n + 1))]
  exact multiplier_bound_8_rat n (by omega)

-- Second solution (recursive)
noncomputable def g_F : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_F (n + 2) * g_F (n + 1) + β_F (n + 2) * g_F n

theorem g_F_rec (n : ℕ) (hn : n ≥ 2) :
    g_F n = α_F n * g_F (n - 1) + β_F n * g_F (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp [g_F]

/-- **CFData for Theorem F (8/π²).** -/
noncomputable def cfData_F : CFData where
  α := α_F
  β := β_F
  f := f_F
  g := g_F
  hf_rec := f_F_rec
  hg_rec := g_F_rec
  hf_ne_zero := f_F_ne_zero
  C := 1 / 2
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 2
  hn₀ := le_refl _
  h_mult := M_F_bound

/-- **Convergence of 8/π² CF.** -/
theorem cf_F_converges (N : ℕ) (hN : N ≥ 2) (M : ℕ) :
    |cfData_F.z (N + M) - cfData_F.z N| ≤
      |cfData_F.Delta N| * (1 / 2 / (1 - 1 / 2)) :=
  cfData_F.cauchy_bound N hN M

/-- Simplified: tail bound is |Δ_N| (since C/(1-C) = 1 for C=1/2). -/
theorem cf_F_tail (N : ℕ) (hN : N ≥ 2) (M : ℕ) :
    |cfData_F.z (N + M) - cfData_F.z N| ≤ |cfData_F.Delta N| := by
  have h := cf_F_converges N hN M
  have : (1 : ℚ) / 2 / (1 - 1 / 2) = 1 := by norm_num
  linarith [abs_nonneg (cfData_F.Delta N)]

/-- SL(2) chain contraction for Theorem F. -/
theorem cf_F_contractive :
    ∀ n, n ≥ 2 → |cfData_F.Delta (n + 1)| ≤ 1 / 2 * |cfData_F.Delta n| :=
  cfData_F.chain_is_contractive

end TheoremF_Instance

/-! ## Theorems B, E: Positive b_n (non-vanishing by induction)

β ≥ 0 always, so f_n = α·f_{n-1} + β·f_{n-2} > 0 by induction.
-/

section PositiveBeta

-- Helper: non-vanishing for recurrences with non-negative β
private theorem pos_recurrence_pos
    (f : ℕ → ℚ) (α β : ℕ → ℚ)
    (hf0 : 0 < f 0) (hf1 : 0 < f 1)
    (hf_rec : ∀ n, f (n + 2) = α (n + 2) * f (n + 1) + β (n + 2) * f n)
    (hα_pos : ∀ n, 0 < α (n + 2))
    (hβ_nn : ∀ n, 0 ≤ β (n + 2)) :
    ∀ n, 0 < f n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact hf0
    | 1 => exact hf1
    | n + 2 =>
      rw [hf_rec n]
      linarith [mul_pos (hα_pos n) (ih (n + 1) (by omega)),
                mul_nonneg (hβ_nn n) (ih n (by omega)).le]

end PositiveBeta

section TheoremB_Instance

def α_B (n : ℕ) : ℚ := 11 * (n : ℚ) ^ 2 + 11 * n + 3
def β_B (n : ℕ) : ℚ := (n : ℚ) ^ 4

noncomputable def f_B : ℕ → ℚ
  | 0 => 1
  | 1 => 3
  | (n + 2) => α_B (n + 2) * f_B (n + 1) + β_B (n + 2) * f_B n

noncomputable def g_B : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_B (n + 2) * g_B (n + 1) + β_B (n + 2) * g_B n

theorem f_B_rec (n : ℕ) (hn : n ≥ 2) :
    f_B n = α_B n * f_B (n - 1) + β_B n * f_B (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [f_B]

theorem g_B_rec (n : ℕ) (hn : n ≥ 2) :
    g_B n = α_B n * g_B (n - 1) + β_B n * g_B (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [g_B]

theorem f_B_pos : ∀ n, 0 < f_B n :=
  pos_recurrence_pos f_B α_B β_B (by norm_num [f_B]) (by norm_num [f_B])
    (fun n => by simp only [f_B])
    (fun n => by simp only [α_B]; positivity)
    (fun n => by simp only [β_B]; positivity)

theorem f_B_ne_zero (n : ℕ) : f_B n ≠ 0 := ne_of_gt (f_B_pos n)

-- Multiplier: β(n)·f(n-2)/f(n) ≤ 1/2.
-- Strategy: suffices β(n)·f(n-2) ≤ α(n)·f(n-1), then use recurrence.
-- n=2: direct. n≥3: chain f(n-1) ≥ α(n-1)·f(n-2) then poly ineq.
theorem M_B_bound (n : ℕ) (hn : n ≥ 2) :
    |β_B n * (f_B (n - 2) / f_B n)| ≤ 1 / 2 := by
  have hfn := f_B_pos n
  have hfn2 := f_B_pos (n - 2)
  rw [abs_of_nonneg (mul_nonneg (by simp [β_B]) (div_nonneg hfn2.le hfn.le)),
      ← mul_div_assoc, div_le_iff₀ hfn, f_B_rec n hn]
  -- Goal: β_B n * f_B (n-2) ≤ 1/2 * (α_B n * f_B (n-1) + β_B n * f_B (n-2))
  suffices h : β_B n * f_B (n - 2) ≤ α_B n * f_B (n - 1) by linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  match k with
  | 0 => simp [f_B, α_B, β_B]; norm_num
  | k + 1 =>
    -- n = k+3 ≥ 3
    simp only [show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega,
               show k + 2 - 1 = k + 1 from by omega, show k + 2 - 2 = k from by omega]
    have hlb : α_B (k + 2) * f_B (k + 1) ≤ f_B (k + 2) := by
      change α_B (k+2) * f_B (k+1) ≤ α_B (k+2) * f_B (k+1) + β_B (k+2) * f_B k
      linarith [mul_nonneg (show 0 ≤ β_B (k+2) from by simp [β_B]; positivity) (f_B_pos k).le]
    calc β_B (k + 3) * f_B (k + 1)
        ≤ (α_B (k + 3) * α_B (k + 2)) * f_B (k + 1) := by
          apply mul_le_mul_of_nonneg_right _ (f_B_pos (k+1)).le
          simp only [α_B, β_B]; push_cast
          nlinarith [sq_nonneg ((k : ℚ) + 3), Nat.cast_nonneg (α := ℚ) k]
      _ = α_B (k + 3) * (α_B (k + 2) * f_B (k + 1)) := by ring
      _ ≤ α_B (k + 3) * f_B (k + 2) :=
          mul_le_mul_of_nonneg_left hlb (by simp [α_B]; positivity)

noncomputable def cfData_B : CFData where
  α := α_B
  β := β_B
  f := f_B
  g := g_B
  hf_rec := f_B_rec
  hg_rec := g_B_rec
  hf_ne_zero := f_B_ne_zero
  C := 1 / 2
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 2
  hn₀ := le_refl _
  h_mult := M_B_bound

end TheoremB_Instance

section TheoremE_Instance

def α_E (n : ℕ) : ℚ := 7 * (n : ℚ) ^ 2 + 7 * n + 2
def β_E (n : ℕ) : ℚ := 8 * (n : ℚ) ^ 4

noncomputable def f_E : ℕ → ℚ
  | 0 => 1
  | 1 => 2
  | (n + 2) => α_E (n + 2) * f_E (n + 1) + β_E (n + 2) * f_E n

noncomputable def g_E : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_E (n + 2) * g_E (n + 1) + β_E (n + 2) * g_E n

theorem f_E_rec (n : ℕ) (hn : n ≥ 2) :
    f_E n = α_E n * f_E (n - 1) + β_E n * f_E (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [f_E]

theorem g_E_rec (n : ℕ) (hn : n ≥ 2) :
    g_E n = α_E n * g_E (n - 1) + β_E n * g_E (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [g_E]

theorem f_E_pos : ∀ n, 0 < f_E n :=
  pos_recurrence_pos f_E α_E β_E (by norm_num [f_E]) (by norm_num [f_E])
    (fun n => by simp only [f_E])
    (fun n => by simp only [α_E]; positivity)
    (fun n => by simp only [β_E]; positivity)

theorem f_E_ne_zero (n : ℕ) : f_E n ≠ 0 := ne_of_gt (f_E_pos n)

-- |M_E(2)| = 128/216 > 1/2, so we start at n₀ = 3.
theorem M_E_bound (n : ℕ) (hn : n ≥ 3) :
    |β_E n * (f_E (n - 2) / f_E n)| ≤ 1 / 2 := by
  have hfn := f_E_pos n
  rw [abs_of_nonneg (mul_nonneg (by simp only [β_E]; positivity)
        (div_nonneg (f_E_pos (n-2)).le hfn.le)),
      ← mul_div_assoc, div_le_iff₀ hfn, f_E_rec n (by omega)]
  suffices h : β_E n * f_E (n - 2) ≤ α_E n * f_E (n - 1) by linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  match k with
  | 0 =>
    simp only [show (3 : ℕ) - 2 = 1 from by omega, show (3 : ℕ) - 1 = 2 from by omega]
    simp [f_E, α_E, β_E]; norm_num
  | k + 1 =>
    simp only [show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega]
    have hlb : α_E (k + 3) * f_E (k + 2) ≤ f_E (k + 3) := by
      change α_E (k+3) * f_E (k+2) ≤ α_E (k+3) * f_E (k+2) + β_E (k+3) * f_E (k+1)
      linarith [mul_nonneg (show 0 ≤ β_E (k+3) from by simp only [β_E]; positivity)
                  (f_E_pos (k+1)).le]
    calc β_E (k + 4) * f_E (k + 2)
        ≤ (α_E (k + 4) * α_E (k + 3)) * f_E (k + 2) := by
          apply mul_le_mul_of_nonneg_right _ (f_E_pos (k+2)).le
          simp only [α_E, β_E]; push_cast
          nlinarith [sq_nonneg ((k : ℚ) + 4), Nat.cast_nonneg (α := ℚ) k]
      _ = α_E (k + 4) * (α_E (k + 3) * f_E (k + 2)) := by ring
      _ ≤ α_E (k + 4) * f_E (k + 3) :=
          mul_le_mul_of_nonneg_left hlb (by simp [α_E]; positivity)

noncomputable def cfData_E : CFData where
  α := α_E
  β := β_E
  f := f_E
  g := g_E
  hf_rec := f_E_rec
  hg_rec := g_E_rec
  hf_ne_zero := f_E_ne_zero
  C := 1 / 2
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 3
  hn₀ := by norm_num
  h_mult := M_E_bound

end TheoremE_Instance

/-! ## Theorem D: 18/π²

b_n = n²(n+1)(n-1) = n²(n²-1) ≥ 0 for n ≥ 1, and b_0 = 0, b_1 = 0.
So β ≥ 0 and non-vanishing by induction.
-/

section TheoremD_Instance

def α_D (n : ℕ) : ℚ := 5 * (n : ℚ) ^ 2 + 6 * n + 2
def β_D (n : ℕ) : ℚ := (n : ℚ) ^ 2 * ((n : ℚ) + 1) * ((n : ℚ) - 1)

noncomputable def f_D : ℕ → ℚ
  | 0 => 1
  | 1 => 2
  | (n + 2) => α_D (n + 2) * f_D (n + 1) + β_D (n + 2) * f_D n

noncomputable def g_D : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_D (n + 2) * g_D (n + 1) + β_D (n + 2) * g_D n

theorem f_D_rec (n : ℕ) (hn : n ≥ 2) :
    f_D n = α_D n * f_D (n - 1) + β_D n * f_D (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [f_D]

theorem g_D_rec (n : ℕ) (hn : n ≥ 2) :
    g_D n = α_D n * g_D (n - 1) + β_D n * g_D (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [g_D]

-- β_D(n+2) = (n+2)²(n+3)(n+1) ≥ 0 for all n
theorem f_D_pos : ∀ n, 0 < f_D n :=
  pos_recurrence_pos f_D α_D β_D (by norm_num [f_D]) (by norm_num [f_D])
    (fun n => by simp only [f_D])
    (fun n => by simp only [α_D]; positivity)
    (fun n => by
      simp only [β_D]
      -- Goal: 0 ≤ ↑(n+2)^2 * (↑(n+2)+1) * (↑(n+2)-1)
      -- All factors ≥ 0 since n+2 ≥ 2
      have h2 : (2 : ℚ) ≤ ↑(n + 2) := by exact_mod_cast (show 2 ≤ n + 2 by omega)
      apply mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith))

theorem f_D_ne_zero (n : ℕ) : f_D n ≠ 0 := ne_of_gt (f_D_pos n)

theorem M_D_bound (n : ℕ) (hn : n ≥ 2) :
    |β_D n * (f_D (n - 2) / f_D n)| ≤ 1 / 2 := by
  have hfn := f_D_pos n
  have hβ : 0 ≤ β_D n := by
    simp only [β_D]
    have h2 : (2 : ℚ) ≤ ↑n := by exact_mod_cast (show 2 ≤ n by omega)
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
  rw [abs_of_nonneg (mul_nonneg hβ (div_nonneg (f_D_pos (n-2)).le hfn.le)),
      ← mul_div_assoc, div_le_iff₀ hfn, f_D_rec n hn]
  suffices h : β_D n * f_D (n - 2) ≤ α_D n * f_D (n - 1) by linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  match k with
  | 0 => simp [f_D, α_D, β_D]; norm_num
  | k + 1 =>
    simp only [show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega]
    have hlb : α_D (k + 2) * f_D (k + 1) ≤ f_D (k + 2) := by
      change α_D (k+2) * f_D (k+1) ≤ α_D (k+2) * f_D (k+1) + β_D (k+2) * f_D k
      have hβk : 0 ≤ β_D (k + 2) := by
        simp only [β_D]
        have h2 : (2 : ℚ) ≤ ↑(k + 2) := by exact_mod_cast (show 2 ≤ k + 2 by omega)
        apply mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
      linarith [mul_nonneg hβk (f_D_pos k).le]
    calc β_D (k + 3) * f_D (k + 1)
        ≤ (α_D (k + 3) * α_D (k + 2)) * f_D (k + 1) := by
          apply mul_le_mul_of_nonneg_right _ (f_D_pos (k+1)).le
          simp only [α_D, β_D]; push_cast
          nlinarith [sq_nonneg ((k : ℚ) + 3), Nat.cast_nonneg (α := ℚ) k,
                     sq_nonneg ((k : ℚ) + 2)]
      _ = α_D (k + 3) * (α_D (k + 2) * f_D (k + 1)) := by ring
      _ ≤ α_D (k + 3) * f_D (k + 2) :=
          mul_le_mul_of_nonneg_left hlb (by simp [α_D]; positivity)

noncomputable def cfData_D : CFData where
  α := α_D
  β := β_D
  f := f_D
  g := g_D
  hf_rec := f_D_rec
  hg_rec := g_D_rec
  hf_ne_zero := f_D_ne_zero
  C := 1 / 2
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 2
  hn₀ := le_refl _
  h_mult := M_D_bound

end TheoremD_Instance

/-! ## Theorems A, C, G: Negative β cases

Recurrence proofs are definitional. Non-vanishing requires
the closed form or an explicit bound that α dominates |β|.
For now, define the sequences and recurrences.
-/

section TheoremA_Instance

def α_A (n : ℕ) : ℚ := 3 * (n : ℚ) ^ 2 + 9 * n + 5
def β_A (n : ℕ) : ℚ := -4 * ((n : ℚ) + 1) ^ 2

noncomputable def f_A : ℕ → ℚ
  | 0 => 1
  | 1 => 5
  | (n + 2) => α_A (n + 2) * f_A (n + 1) + β_A (n + 2) * f_A n

noncomputable def g_A : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_A (n + 2) * g_A (n + 1) + β_A (n + 2) * g_A n

theorem f_A_rec (n : ℕ) (hn : n ≥ 2) :
    f_A n = α_A n * f_A (n - 1) + β_A n * f_A (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [f_A]

theorem g_A_rec (n : ℕ) (hn : n ≥ 2) :
    g_A n = α_A n * g_A (n - 1) + β_A n * g_A (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [g_A]

-- Non-vanishing via α-dominance (modular complement argument):
-- The SL(2) positive eigenspace dominates because f(n+1)/f(n) ≥ 2,
-- and α(n) - |β(n)|/2 = n²+9n+17 ≥ 2 for all n.
theorem f_A_pos : ∀ n, 0 < f_A n := by
  suffices h : ∀ n, 0 < f_A n ∧ 2 * f_A n ≤ f_A (n + 1) from fun n => (h n).1
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact ⟨by norm_num [f_A], by change 2 * f_A 0 ≤ f_A 1; norm_num [f_A, α_A, β_A]⟩
    | 1 => refine ⟨by norm_num [f_A], ?_⟩
           change 2 * f_A 1 ≤ α_A 2 * f_A 1 + β_A 2 * f_A 0; norm_num [f_A, α_A, β_A]
    | n + 2 =>
      have ⟨hpn, hrn⟩ := ih n (by omega)
      have ⟨hpn1, hrn1⟩ := ih (n + 1) (by omega)
      constructor
      · -- 0 < f_A(n+2) = α·f(n+1) + β·f(n) ≥ (n²+9n+17)·f(n+1) > 0
        change 0 < α_A (n + 2) * f_A (n + 1) + β_A (n + 2) * f_A n
        simp only [α_A, β_A]; push_cast
        nlinarith [sq_nonneg ((n : ℚ) + 3), Nat.cast_nonneg (α := ℚ) n,
                   mul_nonneg (sq_nonneg ((n : ℚ) + 3))
                     (show 0 ≤ f_A (n + 1) - 2 * f_A n from by linarith)]
      · -- 2·f(n+2) ≤ f(n+3): (α(n+3)-2)·f(n+2) ≥ 4(n+4)²·f(n+1)
        change 2 * (α_A (n + 2) * f_A (n + 1) + β_A (n + 2) * f_A n) ≤
             α_A (n + 3) * (α_A (n + 2) * f_A (n + 1) + β_A (n + 2) * f_A n) +
             β_A (n + 3) * f_A (n + 1)
        -- Extract: f(n+2) ≥ 2·f(n+1) from IH (hrn1 unfolds definitionally)
        have hf2 : 2 * f_A (n + 1) ≤
            α_A (n + 2) * f_A (n + 1) + β_A (n + 2) * f_A n := hrn1
        simp only [α_A, β_A] at hf2 ⊢; push_cast at hf2 ⊢
        nlinarith [sq_nonneg ((n : ℚ) + 4), Nat.cast_nonneg (α := ℚ) n]

theorem f_A_ne_zero (n : ℕ) : f_A n ≠ 0 := ne_of_gt (f_A_pos n)

-- Stronger ratio bound: (n+2)² * f_A(n) ≤ f_A(n+1) for all n.
-- This implies f_A(n) ≥ (n+1)²·n²·f_A(n-2), used in the multiplier bound.
theorem f_A_ratio (n : ℕ) : ((n : ℚ) + 2) ^ 2 * f_A n ≤ f_A (n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 =>
      change ((0 : ℚ) + 2) ^ 2 * f_A 0 ≤ f_A 1
      norm_num [f_A]
    | 1 =>
      change ((1 : ℚ) + 2) ^ 2 * f_A 1 ≤ f_A 2
      norm_num [f_A, α_A, β_A]
    | n + 2 =>
      have hrn1 := ih (n + 1) (by omega)
      -- hrn1 : ((n+1)+2)² * f_A(n+1) ≤ f_A(n+1+1) = f_A(n+2)
      have hrn1' : ((n : ℚ) + 3) ^ 2 * f_A (n + 1) ≤ f_A (n + 2) := by
        have h := hrn1
        simp only [show n + 1 + 1 = n + 2 from by omega] at h
        convert h using 2; push_cast; ring
      -- Goal: (↑(n+2)+2)² * f_A(n+2) ≤ f_A(n+3) = α_A(n+3)*f_A(n+2) + β_A(n+3)*f_A(n+1)
      change ((↑(n + 2) : ℚ) + 2) ^ 2 * f_A (n + 2) ≤
        α_A (n + 3) * f_A (n + 2) + β_A (n + 3) * f_A (n + 1)
      simp only [α_A, β_A]; push_cast
      -- (α_A(n+3) - (n+4)²) = 2n²+19n+43, use as coefficient in key
      have key : 0 ≤ (2 * (n : ℚ) ^ 2 + 19 * n + 43) *
          (f_A (n + 2) - ((n : ℚ) + 3) ^ 2 * f_A (n + 1)) :=
        mul_nonneg (by positivity) (by linarith [hrn1'])
      -- Explicit gap: (2n²+19n+43)(n+3)² - 4(n+4)² = 2n⁴+31n³+171n²+397n+323 > 0
      have gap : 0 ≤ (2 * (n : ℚ) ^ 4 + 31 * n ^ 3 + 171 * n ^ 2 + 397 * n + 323) *
          f_A (n + 1) :=
        mul_nonneg (by positivity) (f_A_pos (n + 1)).le
      nlinarith [key, gap, f_A_pos (n + 1), Nat.cast_nonneg (α := ℚ) n]

-- Multiplier bound: |β_A(n) * (f_A(n-2) / f_A(n))| ≤ 1/2 for n ≥ 2.
-- Key chain: f_A(n) ≥ (n+1)²·n²·f_A(n-2), so
-- |β_A(n)| · f_A(n-2) / f_A(n) = 4(n+1)² · f_A(n-2) / f_A(n) ≤ 4/n² ≤ 1/2 for n ≥ 3.
-- n=2 case: 4·9·1/139 = 36/139 < 1/2.
theorem M_A_bound (n : ℕ) (hn : n ≥ 2) :
    |β_A n * (f_A (n - 2) / f_A n)| ≤ 1 / 2 := by
  have hfn := f_A_pos n
  rw [abs_mul, abs_div, abs_of_pos (f_A_pos _), abs_of_pos hfn,
      ← mul_div_assoc, div_le_iff₀ hfn]
  -- Goal: |β_A n| * f_A(n-2) ≤ 1/2 * f_A n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 2 = k from by omega]
  match k with
  | 0 =>
    -- n = 2: direct computation f_A 2 = 139
    have habs : |β_A 2| = 36 := by simp [β_A]; norm_num
    rw [habs]; norm_num [f_A, α_A, β_A]
  | k + 1 =>
    -- n = k+3 ≥ 3: use ratio chain
    -- f_A(k+3) ≥ (k+4)²*(k+3)² * f_A(k+1)
    have hr1 := f_A_ratio (k + 1)
    -- hr1: ((k+1)+2)²*f_A(k+1) ≤ f_A(k+2)
    simp only [show k + 1 + 1 = k + 2 from by omega] at hr1
    have hr1' : ((k : ℚ) + 3) ^ 2 * f_A (k + 1) ≤ f_A (k + 2) := by
      convert hr1 using 2; push_cast; ring
    have hr2 := f_A_ratio (k + 2)
    -- hr2: ((k+2)+2)²*f_A(k+2) ≤ f_A(k+3)
    simp only [show k + 2 + 1 = k + 3 from by omega] at hr2
    have hr2' : ((k : ℚ) + 4) ^ 2 * f_A (k + 2) ≤ f_A (k + 3) := by
      convert hr2 using 2; push_cast; ring
    -- Chain: f_A(k+3) ≥ (k+4)²*(k+3)²*f_A(k+1)
    have hchain : ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 3) ^ 2 * f_A (k + 1) ≤ f_A (k + 3) :=
      calc ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 3) ^ 2 * f_A (k + 1)
          = ((k : ℚ) + 4) ^ 2 * (((k : ℚ) + 3) ^ 2 * f_A (k + 1)) := by ring
        _ ≤ ((k : ℚ) + 4) ^ 2 * f_A (k + 2) :=
            mul_le_mul_of_nonneg_left hr1' (by positivity)
        _ ≤ f_A (k + 3) := hr2'
    -- |β_A(k+3)| = 4*(k+4)²
    have habs : |β_A (k + 3)| = 4 * ((k : ℚ) + 4) ^ 2 := by
      simp only [β_A]; push_cast
      rw [show -4 * ((k : ℚ) + 3 + 1) ^ 2 = -(4 * ((k : ℚ) + 4) ^ 2) from by ring]
      rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [habs]
    -- Goal: 4*(k+4)²*f_A(k+1) ≤ 1/2 * f_A(k+3)
    -- (k+3)² ≥ 9 for k ≥ 0, so 4 ≤ (k+3)²/2, chain gives the result
    have hk3 : (8 : ℚ) ≤ ((k : ℚ) + 3) ^ 2 := by
      have := Nat.cast_nonneg (α := ℚ) k; nlinarith
    nlinarith [hchain, f_A_pos (k + 1)]

noncomputable def cfData_A : CFData where
  α := α_A
  β := β_A
  f := f_A
  g := g_A
  hf_rec := f_A_rec
  hg_rec := g_A_rec
  hf_ne_zero := f_A_ne_zero
  C := 1 / 2
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 2
  hn₀ := le_refl _
  h_mult := M_A_bound

end TheoremA_Instance

section TheoremC_Instance

def α_C (n : ℕ) : ℚ := 3 * (n : ℚ) ^ 2 + 3 * n + 1
def β_C (n : ℕ) : ℚ := -(n : ℚ) ^ 3 * (2 * n - 3)

noncomputable def f_C : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | (n + 2) => α_C (n + 2) * f_C (n + 1) + β_C (n + 2) * f_C n

noncomputable def g_C : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_C (n + 2) * g_C (n + 1) + β_C (n + 2) * g_C n

theorem f_C_rec (n : ℕ) (hn : n ≥ 2) :
    f_C n = α_C n * f_C (n - 1) + β_C n * f_C (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [f_C]

theorem g_C_rec (n : ℕ) (hn : n ≥ 2) :
    g_C n = α_C n * g_C (n - 1) + β_C n * g_C (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [g_C]

-- Non-vanishing via α-dominance with ratio (n+2)²:
-- α_C(n+2) - (n+3)² = 2n²+9n+10, |β_C(n+2)|/(n+2)² = (n+2)(2n+1),
-- gap = (2n²+9n+10) - (n+2)(2n+1) = 4n+8 > 0.
theorem f_C_pos : ∀ n, 0 < f_C n := by
  suffices h : ∀ n, n ≥ 1 → 0 < f_C n ∧ ((n : ℚ) + 2) ^ 2 * f_C n ≤ f_C (n + 1) from by
    intro n
    match n with
    | 0 => norm_num [f_C]
    | n + 1 => exact (h (n + 1) (by omega)).1
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => omega
    | 1 =>
      refine ⟨by norm_num [f_C], ?_⟩
      change ((1 : ℚ) + 2) ^ 2 * f_C 1 ≤ f_C 2
      norm_num [f_C, α_C, β_C]
    | n + 2 =>
      have ⟨hpn1, hrn1⟩ := ih (n + 1) (by omega) (by omega)
      have hrn1' : ((n : ℚ) + 3) ^ 2 * f_C (n + 1) ≤ f_C (n + 2) := by
        have h := hrn1
        simp only [show n + 1 + 1 = n + 2 from by omega] at h
        convert h using 2; push_cast; ring
      constructor
      · linarith [mul_pos (show 0 < ((n : ℚ) + 3) ^ 2 from by positivity) hpn1]
      · change ((↑(n + 2) : ℚ) + 2) ^ 2 * f_C (n + 2) ≤
          α_C (n + 3) * f_C (n + 2) + β_C (n + 3) * f_C (n + 1)
        simp only [α_C, β_C]; push_cast
        -- α_C(n+3) - (n+4)² = 2n²+13n+21, |β_C(n+3)|/(n+3)² = (n+3)(2n+3)
        -- gap = (2n²+13n+21) - (n+3)(2n+3) = 4n+12 > 0
        have key : 0 ≤ (2 * (n : ℚ) ^ 2 + 13 * n + 21) *
            (f_C (n + 2) - ((n : ℚ) + 3) ^ 2 * f_C (n + 1)) :=
          mul_nonneg (by positivity) (by linarith [hrn1'])
        -- Also need: gap ≥ 0 as a product with f_C(n+1) to help nlinarith
        have gap : 0 ≤ 4 * ((n : ℚ) + 3) ^ 3 * f_C (n + 1) := by positivity
        nlinarith [key, gap, hpn1, Nat.cast_nonneg (α := ℚ) n]

theorem f_C_ne_zero (n : ℕ) : f_C n ≠ 0 := ne_of_gt (f_C_pos n)

-- Tighter cuff: 3(n+2)²·f_C(n) ≤ 2·f_C(n+1) for n ≥ 2.
-- Self-sustaining gap: k²+20k+61 > 0 (always).
theorem f_C_strong_ratio (n : ℕ) (hn : n ≥ 2) :
    3 * ((n : ℚ) + 2) ^ 2 * f_C n ≤ 2 * f_C (n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    match k with
    | 0 =>
      change 3 * ((2 : ℚ) + 2) ^ 2 * f_C 2 ≤ 2 * f_C 3
      norm_num [f_C, α_C, β_C]
    | k + 1 =>
      -- n = k+3, IH at k+2 gives: 3*(↑(k+2)+2)²*f_C(k+2) ≤ 2*f_C(k+3)
      have ih_raw := ih (k + 2) (by omega) (by omega)
      simp only [show k + 2 + 1 = k + 3 from by omega] at ih_raw
      -- ih_raw : 3*(↑(k+2)+2)²*f_C(k+2) ≤ 2*f_C(k+3)
      -- (↑(k+2)+2)² = (↑k+4)² by arithmetic
      have heq : ((↑(k + 2) : ℚ) + 2) ^ 2 = ((k : ℚ) + 4) ^ 2 := by push_cast; ring
      have ih' : 3 * ((k : ℚ) + 4) ^ 2 * f_C (k + 2) ≤ 2 * f_C (k + 3) := by
        rw [← heq]; exact ih_raw
      -- f_C(k+4) = α_C(k+4)·f_C(k+3) + β_C(k+4)·f_C(k+2)
      -- Goal: 3*(↑(k+3)+2)²*f_C(k+3) ≤ 2*f_C(k+4)
      change 3 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_C (k + 3) ≤
        2 * (α_C (k + 4) * f_C (k + 3) + β_C (k + 4) * f_C (k + 2))
      simp only [α_C, β_C]; push_cast
      -- (↑(k+3)+2)² = (↑k+5)², α_C(k+4) = 3*(↑k+4)²+3*(↑k+4)+1
      -- β_C(k+4) = -(↑k+4)³*(2*(↑k+4)-3)
      -- Goal after simp: 3*(↑k+5)²*f_C(k+3) ≤ 2*((3*(↑k+4)²+3*(↑k+4)+1)*f_C(k+3) - (↑k+4)³*(2*(↑k+4)-3)*f_C(k+2))
      -- Gap coefficient: 2*(3*(↑k+4)²+3*(↑k+4)+1) - 3*(↑k+5)² = k²+20k+61 > 0
      have key : 0 ≤ ((k : ℚ) ^ 2 + 20 * k + 61) *
          (2 * f_C (k + 3) - 3 * ((k : ℚ) + 4) ^ 2 * f_C (k + 2)) :=
        mul_nonneg (by positivity) (by linarith)
      -- `key` says (k²+20k+61)*(2*f_C(k+3)-3*(k+4)²*f_C(k+2)) ≥ 0
      -- negation of goal (after hksq): (3k²+24k+47)*f_C(k+3) < 2*(k+4)³*(2k+5)*f_C(k+2)
      -- Combine: need (3k²+24k+47)*(3*(k+4)²/2)*f_C(k+2) < 2*(k+4)³*(2k+5)*f_C(k+2)
      --          i.e. 3*(3k²+24k+47) < 4*(k+4)*(2k+5), i.e. k²+20k+61 > 0. Done via key.
      have hksq : (↑k + 3 + 2 : ℚ) ^ 2 = (↑k + 5) ^ 2 := by ring
      have hfk2pos := (f_C_pos (k + 2)).le
      have hknn : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      -- Provide explicit product to help nlinarith bridge degree gap
      have hprod : 0 ≤ ((k : ℚ)^2 + 20*k + 61) * ((k + 4)^2 * f_C (k + 2)) :=
        mul_nonneg (by nlinarith) (mul_nonneg (by nlinarith) hfk2pos)
      nlinarith [key, hprod, sq_nonneg ((k : ℚ) + 4), sq_nonneg ((k : ℚ) + 5)]

-- Multiplier bound: |M_C(n)| ≤ 8/9 for n ≥ 2.
-- Chain: 9(n-2+4)²(n-2+5)²·f_C(n-2) ≤ 4·f_C(n) for n ≥ 4.
-- Polynomial: -(β_C(k+4)) ≤ 2*(k+4)²*(k+5)² iff 5k+42 ≥ 0 (always true).
theorem M_C_bound (n : ℕ) (hn : n ≥ 2) :
    |β_C n * (f_C (n - 2) / f_C n)| ≤ 8 / 9 := by
  have hfn := f_C_pos n
  rw [abs_mul, abs_div, abs_of_pos (f_C_pos _), abs_of_pos hfn,
      ← mul_div_assoc, div_le_iff₀ hfn]
  -- Goal: |β_C n| * f_C(n-2) ≤ 8/9 * f_C n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 2 = k from by omega]
  match k with
  | 0 => -- n = 2: |β_C 2| = 4, f_C 0 = 1, f_C 2 = 7. 4*1 ≤ 8/9*7
    norm_num [f_C, α_C, β_C]
  | 1 => -- n = 3: |β_C 3| = 27, f_C 1 = 1, f_C 3 = 65. 27 ≤ 8/9*65
    norm_num [f_C, α_C, β_C]
  | k + 2 => -- n = k+4 ≥ 4; goal: |β_C (k+2+2)| * f_C (k+2) ≤ 8/9 * f_C (k+2+2)
    -- Simplify index k+2+2 = k+4
    simp only [show k + 2 + 2 = k + 4 from by omega]
    -- Get two steps of strong ratio (convert pushes cast arithmetic)
    have hr1 : 3 * ((k : ℚ) + 4) ^ 2 * f_C (k + 2) ≤ 2 * f_C (k + 3) := by
      have h := f_C_strong_ratio (k + 2) (by omega)
      simp only [show k + 2 + 1 = k + 3 from by omega] at h
      have heq : ((↑(k + 2) : ℚ) + 2) = ((k : ℚ) + 4) := by push_cast; ring
      linarith [show 3 * ((↑(k + 2) : ℚ) + 2) ^ 2 * f_C (k + 2) =
        3 * ((k : ℚ) + 4) ^ 2 * f_C (k + 2) from by rw [heq]]
    have hr2 : 3 * ((k : ℚ) + 5) ^ 2 * f_C (k + 3) ≤ 2 * f_C (k + 4) := by
      have h := f_C_strong_ratio (k + 3) (by omega)
      simp only [show k + 3 + 1 = k + 4 from by omega] at h
      have heq : ((↑(k + 3) : ℚ) + 2) = ((k : ℚ) + 5) := by push_cast; ring
      linarith [show 3 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_C (k + 3) =
        3 * ((k : ℚ) + 5) ^ 2 * f_C (k + 3) from by rw [heq]]
    -- Chain: 9*(k+4)²*(k+5)²*f_C(k+2) ≤ 4*f_C(k+4)
    have hchain : 9 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_C (k + 2) ≤
        4 * f_C (k + 4) :=
      calc 9 * ((k:ℚ)+4)^2 * ((k:ℚ)+5)^2 * f_C (k+2)
          = 3 * ((k:ℚ)+5)^2 * (3 * ((k:ℚ)+4)^2 * f_C (k+2)) := by ring
        _ ≤ 3 * ((k:ℚ)+5)^2 * (2 * f_C (k+3)) :=
            mul_le_mul_of_nonneg_left hr1 (by positivity)
        _ = 2 * (3 * ((k:ℚ)+5)^2 * f_C (k+3)) := by ring
        _ ≤ 2 * (2 * f_C (k+4)) :=
            mul_le_mul_of_nonneg_left hr2 (by norm_num)
        _ = 4 * f_C (k+4) := by ring
    -- β_C(k+4) < 0: β_C(k+4) = -(k+4)^3*(2*(k+4)-3), and (k+4)^3>0, 2*(k+4)-3 = 2k+5 > 0
    have hbeta_neg : β_C (k + 4) < 0 := by
      simp only [β_C]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have h4 : (0 : ℚ) < k + 4 := by linarith
      nlinarith [sq_nonneg ((k : ℚ) + 4), mul_pos h4 h4, mul_pos (mul_pos h4 h4) h4]
    -- |β_C(k+4)| = -β_C(k+4)
    rw [abs_of_neg hbeta_neg]
    -- Polynomial bound: -(β_C(k+4)) ≤ 2*(k+4)²*(k+5)²
    -- i.e. (k+4)^3*(2k+5) ≤ 2*(k+4)^2*(k+5)^2, i.e. 7k+30 ≥ 0
    have hpoly : -β_C (k + 4) ≤ 2 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 := by
      simp only [β_C]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      nlinarith [sq_nonneg ((k : ℚ) + 4)]
    -- Combine: (-β_C(k+4)) * f_C(k+2) ≤ 2*(k+4)²*(k+5)²*f_C(k+2) ≤ (8/9)*f_C(k+4)
    have hfk2 := (f_C_pos (k + 2)).le
    calc -β_C (k + 4) * f_C (k + 2)
        ≤ 2 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_C (k + 2) :=
          mul_le_mul_of_nonneg_right hpoly hfk2
      _ ≤ (8/9) * f_C (k + 4) := by nlinarith [hchain, f_C_pos (k + 2)]

noncomputable def cfData_C : CFData where
  α := α_C
  β := β_C
  f := f_C
  g := g_C
  hf_rec := f_C_rec
  hg_rec := g_C_rec
  hf_ne_zero := f_C_ne_zero
  C := 8 / 9
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 2
  hn₀ := le_refl _
  h_mult := M_C_bound

end TheoremC_Instance

section TheoremG_Instance

def α_G (n : ℕ) : ℚ := 3 * (n : ℚ) ^ 2 + n - 1
def β_G (n : ℕ) : ℚ := -(n : ℚ) ^ 2 * ((n : ℚ) + 2) * (2 * n - 5)

noncomputable def f_G : ℕ → ℚ
  | 0 => 1
  | 1 => 3
  | (n + 2) => α_G (n + 2) * f_G (n + 1) + β_G (n + 2) * f_G n

noncomputable def g_G : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_G (n + 2) * g_G (n + 1) + β_G (n + 2) * g_G n

theorem f_G_rec (n : ℕ) (hn : n ≥ 2) :
    f_G n = α_G n * f_G (n - 1) + β_G n * f_G (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [f_G]

theorem g_G_rec (n : ℕ) (hn : n ≥ 2) :
    g_G n = α_G n * g_G (n - 1) + β_G n * g_G (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [g_G]

-- Non-vanishing via α-dominance with growing ratio (n+2)²:
-- Key: α_G(n+2) - (n+3)² = 2n²+7n+4, and |β_G(n+2)|/(n+2)² = (n+4)(2n-1),
-- so 2n²+7n+4 - (n+4)(2n-1) = 8 > 0 for all n.
theorem f_G_pos : ∀ n, 0 < f_G n := by
  -- Prove: for n ≥ 1, 0 < f_G n ∧ (n+2)² * f_G n ≤ f_G (n+1)
  suffices h : ∀ n, n ≥ 1 → 0 < f_G n ∧ ((n : ℚ) + 2) ^ 2 * f_G n ≤ f_G (n + 1) from by
    intro n
    match n with
    | 0 => norm_num [f_G]
    | n + 1 => exact (h (n + 1) (by omega)).1
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => omega
    | 1 =>
      refine ⟨by norm_num [f_G], ?_⟩
      change ((1 : ℚ) + 2) ^ 2 * f_G 1 ≤ f_G 2
      norm_num [f_G, α_G, β_G]
    | n + 2 =>
      have ⟨hpn1, hrn1⟩ := ih (n + 1) (by omega) (by omega)
      -- Normalize hrn1: (↑(n+1)+2)² → (↑n+3)², f_G(n+1+1) → f_G(n+2)
      have hrn1' : ((n : ℚ) + 3) ^ 2 * f_G (n + 1) ≤ f_G (n + 2) := by
        have h := hrn1
        simp only [show n + 1 + 1 = n + 2 from by omega] at h
        convert h using 2; push_cast; ring
      constructor
      · -- 0 < f_G(n+2) from ratio bound
        linarith [mul_pos (show 0 < ((n : ℚ) + 3) ^ 2 from by positivity) hpn1]
      · -- ((n+4))² · f_G(n+2) ≤ f_G(n+3)
        change ((↑(n + 2) : ℚ) + 2) ^ 2 * f_G (n + 2) ≤
          α_G (n + 3) * f_G (n + 2) + β_G (n + 3) * f_G (n + 1)
        simp only [α_G, β_G]; push_cast
        -- Key: (2n²+11n+13) ≥ (n+5)(2n+1) = 2n²+11n+5, gap = 8
        have key : 0 ≤ (2 * (n : ℚ) ^ 2 + 11 * n + 13) *
            (f_G (n + 2) - ((n : ℚ) + 3) ^ 2 * f_G (n + 1)) :=
          mul_nonneg (by positivity) (by linarith [hrn1'])
        nlinarith [key, hpn1, Nat.cast_nonneg (α := ℚ) n]

theorem f_G_ne_zero (n : ℕ) : f_G n ≠ 0 := ne_of_gt (f_G_pos n)

-- Tighter cuff: 3*(n+2)²*f_G(n) ≤ 2*f_G(n+1) for n ≥ 2.
-- Gap polynomial: k²+9 > 0 (always).
theorem f_G_strong_ratio (n : ℕ) (hn : n ≥ 2) :
    3 * ((n : ℚ) + 2) ^ 2 * f_G n ≤ 2 * f_G (n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    match k with
    | 0 =>
      change 3 * ((2 : ℚ) + 2) ^ 2 * f_G 2 ≤ 2 * f_G 3
      norm_num [f_G, α_G, β_G]
    | k + 1 =>
      -- n = k+3, IH at k+2
      have ih_raw := ih (k + 2) (by omega) (by omega)
      simp only [show k + 2 + 1 = k + 3 from by omega] at ih_raw
      have heq : ((↑(k + 2) : ℚ) + 2) = ((k : ℚ) + 4) := by push_cast; ring
      have ih' : 3 * ((k : ℚ) + 4) ^ 2 * f_G (k + 2) ≤ 2 * f_G (k + 3) := by
        have : ((↑(k + 2) : ℚ) + 2) ^ 2 = ((k : ℚ) + 4) ^ 2 := by rw [heq]
        linarith [show 3 * ((↑(k + 2) : ℚ) + 2) ^ 2 * f_G (k + 2) =
          3 * ((k : ℚ) + 4) ^ 2 * f_G (k + 2) from by rw [this]]
      -- Goal: 3*(↑(k+3)+2)²*f_G(k+3) ≤ 2*f_G(k+4)
      change 3 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_G (k + 3) ≤
        2 * (α_G (k + 4) * f_G (k + 3) + β_G (k + 4) * f_G (k + 2))
      simp only [α_G, β_G]; push_cast
      -- Gap: 2*(3*(k+4)^2+(k+4)-1) - 3*(k+5)^2 = 3k^2+20k+27
      -- key uses gap: (k^2+9)*(2*f_G(k+3)-3*(k+4)^2*f_G(k+2)) ≥ 0
      have hknn : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have hfk2pos := (f_G_pos (k + 2)).le
      have key : 0 ≤ (3 * (k : ℚ) ^ 2 + 20 * k + 27) *
          (2 * f_G (k + 3) - 3 * ((k : ℚ) + 4) ^ 2 * f_G (k + 2)) :=
        mul_nonneg (by nlinarith) (by linarith)
      have hksq : (↑k + 3 + 2 : ℚ) ^ 2 = (↑k + 5) ^ 2 := by ring
      have hprod : 0 ≤ ((k : ℚ) ^ 2 + 9) * (((k : ℚ) + 4) ^ 2 * f_G (k + 2)) :=
        mul_nonneg (by nlinarith) (mul_nonneg (by nlinarith) hfk2pos)
      nlinarith [key, hprod, sq_nonneg ((k : ℚ) + 4), sq_nonneg ((k : ℚ) + 5)]

-- Multiplier bound: |M_G(n)| ≤ 8/9 for n ≥ 3.
-- β_G(n) = -n²*(n+2)*(2n-5), negative for n ≥ 3.
-- Chain: 9*(k+5)²*(k+6)²*f_G(k+3) ≤ 4*f_G(k+5) for k ≥ 0.
-- Polynomial: (k+5)²*(k+7)*(2k+5) ≤ 2*(k+5)²*(k+6)² iff 5k+37 ≥ 0.
theorem M_G_bound (n : ℕ) (hn : n ≥ 3) :
    |β_G n * (f_G (n - 2) / f_G n)| ≤ 8 / 9 := by
  have hfn := f_G_pos n
  rw [abs_mul, abs_div, abs_of_pos (f_G_pos _), abs_of_pos hfn,
      ← mul_div_assoc, div_le_iff₀ hfn]
  -- Goal: |β_G n| * f_G(n-2) ≤ 8/9 * f_G n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 2 = k + 1 from by omega]
  match k with
  | 0 => -- n = 3: |β_G 3|*f_G 1 ≤ 8/9*f_G 3
    norm_num [f_G, α_G, β_G]
  | 1 => -- n = 4: |β_G 4|*f_G 2 ≤ 8/9*f_G 4
    norm_num [f_G, α_G, β_G]
  | k + 2 => -- n = k+5 ≥ 5
    -- Simplify index k+2+3 = k+5
    simp only [show k + 2 + 3 = k + 5 from by omega,
               show k + 2 + 1 = k + 3 from by omega]
    -- Get two steps of strong ratio
    have hr1 : 3 * ((k : ℚ) + 5) ^ 2 * f_G (k + 3) ≤ 2 * f_G (k + 4) := by
      have h := f_G_strong_ratio (k + 3) (by omega)
      simp only [show k + 3 + 1 = k + 4 from by omega] at h
      have heq : ((↑(k + 3) : ℚ) + 2) = ((k : ℚ) + 5) := by push_cast; ring
      linarith [show 3 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_G (k + 3) =
        3 * ((k : ℚ) + 5) ^ 2 * f_G (k + 3) from by rw [show ((↑(k + 3) : ℚ) + 2)^2 =
          ((k : ℚ) + 5)^2 from by rw [heq]]]
    have hr2 : 3 * ((k : ℚ) + 6) ^ 2 * f_G (k + 4) ≤ 2 * f_G (k + 5) := by
      have h := f_G_strong_ratio (k + 4) (by omega)
      simp only [show k + 4 + 1 = k + 5 from by omega] at h
      have heq : ((↑(k + 4) : ℚ) + 2) = ((k : ℚ) + 6) := by push_cast; ring
      linarith [show 3 * ((↑(k + 4) : ℚ) + 2) ^ 2 * f_G (k + 4) =
        3 * ((k : ℚ) + 6) ^ 2 * f_G (k + 4) from by rw [show ((↑(k + 4) : ℚ) + 2)^2 =
          ((k : ℚ) + 6)^2 from by rw [heq]]]
    -- Chain: 9*(k+5)²*(k+6)²*f_G(k+3) ≤ 4*f_G(k+5)
    have hchain : 9 * ((k : ℚ) + 5) ^ 2 * ((k : ℚ) + 6) ^ 2 * f_G (k + 3) ≤
        4 * f_G (k + 5) :=
      calc 9 * ((k:ℚ)+5)^2 * ((k:ℚ)+6)^2 * f_G (k+3)
          = 3 * ((k:ℚ)+6)^2 * (3 * ((k:ℚ)+5)^2 * f_G (k+3)) := by ring
        _ ≤ 3 * ((k:ℚ)+6)^2 * (2 * f_G (k+4)) :=
            mul_le_mul_of_nonneg_left hr1 (by positivity)
        _ = 2 * (3 * ((k:ℚ)+6)^2 * f_G (k+4)) := by ring
        _ ≤ 2 * (2 * f_G (k+5)) :=
            mul_le_mul_of_nonneg_left hr2 (by norm_num)
        _ = 4 * f_G (k+5) := by ring
    -- β_G(k+5) < 0 (since 2*(k+5)-5 = 2k+5 > 0)
    have hbeta_neg : β_G (k + 5) < 0 := by
      simp only [β_G]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have h5 : (0 : ℚ) < k + 5 := by linarith
      nlinarith [sq_nonneg ((k : ℚ) + 5), mul_pos h5 h5, mul_pos (mul_pos h5 h5) h5]
    -- |β_G(k+5)| = -β_G(k+5) = (k+5)²*(k+7)*(2k+5)
    rw [abs_of_neg hbeta_neg]
    -- Polynomial bound: -(β_G(k+5)) ≤ 2*(k+5)²*(k+6)²
    -- i.e. (k+5)²*(k+7)*(2k+5) ≤ 2*(k+5)²*(k+6)²
    -- Dividing by (k+5)²: (k+7)*(2k+5) ≤ 2*(k+6)², i.e. 5k+37 ≥ 0
    have hpoly : -β_G (k + 5) ≤ 2 * ((k : ℚ) + 5) ^ 2 * ((k : ℚ) + 6) ^ 2 := by
      simp only [β_G]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      nlinarith [sq_nonneg ((k : ℚ) + 5)]
    have hfk3 := (f_G_pos (k + 3)).le
    calc -β_G (k + 5) * f_G (k + 3)
        ≤ 2 * ((k : ℚ) + 5) ^ 2 * ((k : ℚ) + 6) ^ 2 * f_G (k + 3) :=
          mul_le_mul_of_nonneg_right hpoly hfk3
      _ ≤ (8/9) * f_G (k + 5) := by nlinarith [hchain, f_G_pos (k + 3)]

/-- **CFData for Theorem G (32/π²).** -/
noncomputable def cfData_G : CFData where
  α := α_G
  β := β_G
  f := f_G
  g := g_G
  hf_rec := f_G_rec
  hg_rec := g_G_rec
  hf_ne_zero := f_G_ne_zero
  C := 8 / 9
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 3
  hn₀ := by norm_num
  h_mult := M_G_bound

end TheoremG_Instance

section TheoremH_Instance

def α_H (n : ℕ) : ℚ := 3 * (n : ℚ) ^ 2 + 7 * n + 3
def β_H (n : ℕ) : ℚ := -(n : ℚ) ^ 2 * ((n : ℚ) + 2) * (2 * n - 3)

noncomputable def f_H : ℕ → ℚ
  | 0 => 3
  | 1 => 42
  | (n + 2) => α_H (n + 2) * f_H (n + 1) + β_H (n + 2) * f_H n

noncomputable def g_H : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_H (n + 2) * g_H (n + 1) + β_H (n + 2) * g_H n

theorem f_H_rec (n : ℕ) (hn : n ≥ 2) :
    f_H n = α_H n * f_H (n - 1) + β_H n * f_H (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [f_H]

theorem g_H_rec (n : ℕ) (hn : n ≥ 2) :
    g_H n = α_H n * g_H (n - 1) + β_H n * g_H (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [g_H]

-- Non-vanishing via α-dominance with growing ratio (n+2)²:
-- Key: α_H(n+2) - (n+3)² = 2n²+11n+12, and |β_H(n+2)|/(n+2)² = (n+4)(2n+1),
-- so 2n²+11n+12 - (n+4)(2n+1) = 2n+8 > 0.
theorem f_H_pos : ∀ n, 0 < f_H n := by
  suffices h : ∀ n, n ≥ 1 → 0 < f_H n ∧ ((n : ℚ) + 2) ^ 2 * f_H n ≤ f_H (n + 1) from by
    intro n
    match n with
    | 0 => norm_num [f_H]
    | n + 1 => exact (h (n + 1) (by omega)).1
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => omega
    | 1 =>
      refine ⟨by norm_num [f_H], ?_⟩
      change ((1 : ℚ) + 2) ^ 2 * f_H 1 ≤ f_H 2
      norm_num [f_H, α_H, β_H]
    | n + 2 =>
      have ⟨hpn1, hrn1⟩ := ih (n + 1) (by omega) (by omega)
      have hrn1' : ((n : ℚ) + 3) ^ 2 * f_H (n + 1) ≤ f_H (n + 2) := by
        have h := hrn1
        simp only [show n + 1 + 1 = n + 2 from by omega] at h
        convert h using 2; push_cast; ring
      constructor
      · linarith [mul_pos (show 0 < ((n : ℚ) + 3) ^ 2 from by positivity) hpn1]
      · change ((↑(n + 2) : ℚ) + 2) ^ 2 * f_H (n + 2) ≤
          α_H (n + 3) * f_H (n + 2) + β_H (n + 3) * f_H (n + 1)
        simp only [α_H, β_H]; push_cast
        -- Key: (2n²+15n+27) ≥ (n+5)(2n+3) = 2n²+13n+15, gap = 2n+12
        have key : 0 ≤ (2 * (n : ℚ) ^ 2 + 15 * n + 27) *
            (f_H (n + 2) - ((n : ℚ) + 3) ^ 2 * f_H (n + 1)) :=
          mul_nonneg (by positivity) (by linarith [hrn1'])
        have gap : 0 ≤ (2 * (n : ℚ) + 12) * ((n : ℚ) + 3) ^ 2 * f_H (n + 1) :=
          by positivity
        nlinarith [key, gap, hpn1, Nat.cast_nonneg (α := ℚ) n]

theorem f_H_ne_zero (n : ℕ) : f_H n ≠ 0 := ne_of_gt (f_H_pos n)

-- Tighter cuff: 2*(n+2)²*f_H(n) ≤ f_H(n+1) for n ≥ 2.
-- Self-sustaining gap: (5k+23)/2 > 0 (always).
theorem f_H_strong_ratio (n : ℕ) (hn : n ≥ 2) :
    2 * ((n : ℚ) + 2) ^ 2 * f_H n ≤ f_H (n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    match k with
    | 0 =>
      change 2 * ((2 : ℚ) + 2) ^ 2 * f_H 2 ≤ f_H 3
      norm_num [f_H, α_H, β_H]
    | k + 1 =>
      -- n = k+3, IH at k+2
      have ih_raw := ih (k + 2) (by omega) (by omega)
      simp only [show k + 2 + 1 = k + 3 from by omega] at ih_raw
      have heq : ((↑(k + 2) : ℚ) + 2) = ((k : ℚ) + 4) := by push_cast; ring
      have ih' : 2 * ((k : ℚ) + 4) ^ 2 * f_H (k + 2) ≤ f_H (k + 3) := by
        have : ((↑(k + 2) : ℚ) + 2) ^ 2 = ((k : ℚ) + 4) ^ 2 := by rw [heq]
        linarith [show 2 * ((↑(k + 2) : ℚ) + 2) ^ 2 * f_H (k + 2) =
          2 * ((k : ℚ) + 4) ^ 2 * f_H (k + 2) from by rw [this]]
      -- Goal: 2*(↑(k+3)+2)²*f_H(k+3) ≤ f_H(k+4)
      change 2 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_H (k + 3) ≤
        α_H (k + 4) * f_H (k + 3) + β_H (k + 4) * f_H (k + 2)
      simp only [α_H, β_H]; push_cast
      -- Gap: α_H(k+4) - (k+5)(2k+5)/(2(k+4)²)·(k+4)² - 2(k+5)²
      --    = 3(k+4)²+7(k+4)+3 - (k+5)(2k+5)/2 - 2(k+5)²
      --    = (5k+23)/2 > 0
      have hknn : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have hfk2pos := (f_H_pos (k + 2)).le
      have key : 0 ≤ (5 * (k : ℚ) + 23) *
          (f_H (k + 3) - 2 * ((k : ℚ) + 4) ^ 2 * f_H (k + 2)) :=
        mul_nonneg (by linarith) (by linarith)
      have hksq : (↑k + 3 + 2 : ℚ) ^ 2 = (↑k + 5) ^ 2 := by ring
      have hprod : 0 ≤ (5 * (k : ℚ) + 23) * (((k : ℚ) + 4) ^ 2 * f_H (k + 2)) :=
        mul_nonneg (by linarith) (mul_nonneg (by nlinarith) hfk2pos)
      nlinarith [key, hprod, sq_nonneg ((k : ℚ) + 4), sq_nonneg ((k : ℚ) + 5)]

-- Multiplier bound: |M_H(n)| ≤ 1/2 for n ≥ 2.
-- Chain: f_H(n) ≥ 4*n²*(n+1)²*f_H(n-2) for n ≥ 4 (two strong ratio steps).
-- Polynomial: |β_H(n)|/(4n²(n+1)²) = (n+2)(2n-3)/(4(n+1)²) ≤ 1/2 iff 3n+8 ≥ 0 (always).
-- n=2,3: direct computation.
theorem M_H_bound (n : ℕ) (hn : n ≥ 2) :
    |β_H n * (f_H (n - 2) / f_H n)| ≤ 1 / 2 := by
  have hfn := f_H_pos n
  rw [abs_mul, abs_div, abs_of_pos (f_H_pos _), abs_of_pos hfn,
      ← mul_div_assoc, div_le_iff₀ hfn]
  -- Goal: |β_H n| * f_H(n-2) ≤ 1/2 * f_H n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 2 = k from by omega]
  match k with
  | 0 => -- n = 2: |β_H 2| * f_H 0 ≤ 1/2 * f_H 2
    norm_num [f_H, α_H, β_H]
  | 1 => -- n = 3: |β_H 3| * f_H 1 ≤ 1/2 * f_H 3
    norm_num [f_H, α_H, β_H]
  | k + 2 => -- n = k+4 ≥ 4
    simp only [show k + 2 + 2 = k + 4 from by omega]
    -- Get two steps of strong ratio
    have hr1 : 2 * ((k : ℚ) + 4) ^ 2 * f_H (k + 2) ≤ f_H (k + 3) := by
      have h := f_H_strong_ratio (k + 2) (by omega)
      simp only [show k + 2 + 1 = k + 3 from by omega] at h
      have heq : ((↑(k + 2) : ℚ) + 2) = ((k : ℚ) + 4) := by push_cast; ring
      linarith [show 2 * ((↑(k + 2) : ℚ) + 2) ^ 2 * f_H (k + 2) =
        2 * ((k : ℚ) + 4) ^ 2 * f_H (k + 2) from by rw [show ((↑(k + 2) : ℚ) + 2)^2 =
          ((k : ℚ) + 4)^2 from by rw [heq]]]
    have hr2 : 2 * ((k : ℚ) + 5) ^ 2 * f_H (k + 3) ≤ f_H (k + 4) := by
      have h := f_H_strong_ratio (k + 3) (by omega)
      simp only [show k + 3 + 1 = k + 4 from by omega] at h
      have heq : ((↑(k + 3) : ℚ) + 2) = ((k : ℚ) + 5) := by push_cast; ring
      linarith [show 2 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_H (k + 3) =
        2 * ((k : ℚ) + 5) ^ 2 * f_H (k + 3) from by rw [show ((↑(k + 3) : ℚ) + 2)^2 =
          ((k : ℚ) + 5)^2 from by rw [heq]]]
    -- Chain: 4*(k+4)²*(k+5)²*f_H(k+2) ≤ f_H(k+4)
    have hchain : 4 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_H (k + 2) ≤
        f_H (k + 4) :=
      calc 4 * ((k:ℚ)+4)^2 * ((k:ℚ)+5)^2 * f_H (k+2)
          = 2 * ((k:ℚ)+5)^2 * (2 * ((k:ℚ)+4)^2 * f_H (k+2)) := by ring
        _ ≤ 2 * ((k:ℚ)+5)^2 * f_H (k+3) :=
            mul_le_mul_of_nonneg_left hr1 (by positivity)
        _ ≤ f_H (k+4) := hr2
    -- β_H(k+4) < 0 (since 2*(k+4)-3 = 2k+5 > 0)
    have hbeta_neg : β_H (k + 4) < 0 := by
      simp only [β_H]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have h4 : (0 : ℚ) < k + 4 := by linarith
      nlinarith [sq_nonneg ((k : ℚ) + 4), mul_pos h4 h4, mul_pos (mul_pos h4 h4) h4]
    -- |β_H(k+4)| = -β_H(k+4) = (k+4)²*(k+6)*(2k+5)
    rw [abs_of_neg hbeta_neg]
    -- Polynomial bound: -(β_H(k+4)) ≤ 2*(k+4)²*(k+5)²
    -- i.e. (k+4)²*(k+6)*(2k+5) ≤ 2*(k+4)²*(k+5)²
    -- Dividing by (k+4)²: (k+6)*(2k+5) ≤ 2*(k+5)², i.e. 3k+20 ≥ 0
    have hpoly : -β_H (k + 4) ≤ 2 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 := by
      simp only [β_H]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      nlinarith [sq_nonneg ((k : ℚ) + 4)]
    have hfk2 := (f_H_pos (k + 2)).le
    calc -β_H (k + 4) * f_H (k + 2)
        ≤ 2 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_H (k + 2) :=
          mul_le_mul_of_nonneg_right hpoly hfk2
      _ ≤ (1/2) * f_H (k + 4) := by nlinarith [hchain, f_H_pos (k + 2)]

noncomputable def cfData_H : CFData where
  α := α_H
  β := β_H
  f := f_H
  g := g_H
  hf_rec := f_H_rec
  hg_rec := g_H_rec
  hf_ne_zero := f_H_ne_zero
  C := 1 / 2
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 2
  hn₀ := le_refl _
  h_mult := M_H_bound

end TheoremH_Instance

section TheoremI_Instance

/-! ## Theorem I: 16/(π²-8) variant 1

a_n = 3n²+11n+9, b_n = -n(n+2)²(2n-1).
Characteristic roots: (2, 1).
-/

def α_I (n : ℕ) : ℚ := 3 * (n : ℚ) ^ 2 + 11 * n + 9
def β_I (n : ℕ) : ℚ := -(n : ℚ) * ((n : ℚ) + 2) ^ 2 * (2 * n - 1)

noncomputable def f_I : ℕ → ℚ
  | 0 => 9
  | 1 => 198
  | (n + 2) => α_I (n + 2) * f_I (n + 1) + β_I (n + 2) * f_I n

noncomputable def g_I : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_I (n + 2) * g_I (n + 1) + β_I (n + 2) * g_I n

theorem f_I_rec (n : ℕ) (hn : n ≥ 2) :
    f_I n = α_I n * f_I (n - 1) + β_I n * f_I (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [f_I]

theorem g_I_rec (n : ℕ) (hn : n ≥ 2) :
    g_I n = α_I n * g_I (n - 1) + β_I n * g_I (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [g_I]

-- Non-vanishing via α-dominance with growing ratio (n+2)²:
-- α_I(n+3) = 3(n+3)²+11(n+3)+9 = 3n²+29n+69, (n+4)² = n²+8n+16
-- Gap = 2n²+21n+53. For the β absorption:
-- gap·(n+3) - (n+5)²(2n+5) = 2n³+26n²+108n+146 > 0.
theorem f_I_pos : ∀ n, 0 < f_I n := by
  suffices h : ∀ n, n ≥ 1 → 0 < f_I n ∧ ((n : ℚ) + 2) ^ 2 * f_I n ≤ f_I (n + 1) from by
    intro n
    match n with
    | 0 => norm_num [f_I]
    | n + 1 => exact (h (n + 1) (by omega)).1
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => omega
    | 1 =>
      refine ⟨by norm_num [f_I], ?_⟩
      change ((1 : ℚ) + 2) ^ 2 * f_I 1 ≤ f_I 2
      norm_num [f_I, α_I, β_I]
    | n + 2 =>
      have ⟨hpn1, hrn1⟩ := ih (n + 1) (by omega) (by omega)
      have hrn1' : ((n : ℚ) + 3) ^ 2 * f_I (n + 1) ≤ f_I (n + 2) := by
        have h := hrn1
        simp only [show n + 1 + 1 = n + 2 from by omega] at h
        convert h using 2; push_cast; ring
      constructor
      · linarith [mul_pos (show 0 < ((n : ℚ) + 3) ^ 2 from by positivity) hpn1]
      · change ((↑(n + 2) : ℚ) + 2) ^ 2 * f_I (n + 2) ≤
          α_I (n + 3) * f_I (n + 2) + β_I (n + 3) * f_I (n + 1)
        simp only [α_I, β_I]; push_cast
        have key : 0 ≤ (2 * (n : ℚ) ^ 2 + 21 * n + 53) *
            (f_I (n + 2) - ((n : ℚ) + 3) ^ 2 * f_I (n + 1)) :=
          mul_nonneg (by positivity) (by linarith [hrn1'])
        have gap : 0 ≤ (2 * (n : ℚ) ^ 3 + 26 * n ^ 2 + 108 * n + 146) *
            f_I (n + 1) :=
          mul_nonneg (by positivity) hpn1.le
        nlinarith [key, gap, hpn1, Nat.cast_nonneg (α := ℚ) n]

theorem f_I_ne_zero (n : ℕ) : f_I n ≠ 0 := ne_of_gt (f_I_pos n)

-- Tighter cuff: 2*(n+2)²*f_I(n) ≤ f_I(n+1) for n ≥ 2.
-- Self-sustaining gap: 7k²+66k+156 > 0 (always).
theorem f_I_strong_ratio (n : ℕ) (hn : n ≥ 2) :
    2 * ((n : ℚ) + 2) ^ 2 * f_I n ≤ f_I (n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    match k with
    | 0 =>
      change 2 * ((2 : ℚ) + 2) ^ 2 * f_I 2 ≤ f_I 3
      norm_num [f_I, α_I, β_I]
    | k + 1 =>
      -- n = k+3, IH at k+2 gives: 2*(↑(k+2)+2)²*f_I(k+2) ≤ f_I(k+3)
      have ih_raw := ih (k + 2) (by omega) (by omega)
      simp only [show k + 2 + 1 = k + 3 from by omega] at ih_raw
      have heq : ((↑(k + 2) : ℚ) + 2) ^ 2 = ((k : ℚ) + 4) ^ 2 := by push_cast; ring
      have ih' : 2 * ((k : ℚ) + 4) ^ 2 * f_I (k + 2) ≤ f_I (k + 3) := by
        linarith [show 2 * ((↑(k + 2) : ℚ) + 2) ^ 2 * f_I (k + 2) =
          2 * ((k : ℚ) + 4) ^ 2 * f_I (k + 2) from by rw [heq]]
      -- Goal: 2*(↑(k+3)+2)²*f_I(k+3) ≤ f_I(k+4) = α_I(k+4)*f_I(k+3) + β_I(k+4)*f_I(k+2)
      change 2 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_I (k + 3) ≤
        α_I (k + 4) * f_I (k + 3) + β_I (k + 4) * f_I (k + 2)
      simp only [α_I, β_I]; push_cast
      -- Gap: 2(k+4)·α_I(k+4) - (k+6)²(2k+7) - 4(k+4)(k+5)²
      -- = 7k²+66k+156 > 0
      have key : 0 ≤ (7 * (k : ℚ) ^ 2 + 66 * k + 156) *
          (f_I (k + 3) - 2 * ((k : ℚ) + 4) ^ 2 * f_I (k + 2)) :=
        mul_nonneg (by positivity) (by linarith)
      have hfk2pos := (f_I_pos (k + 2)).le
      have hknn : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have hprod : 0 ≤ (7 * (k : ℚ) ^ 2 + 66 * k + 156) * ((k + 4) ^ 2 * f_I (k + 2)) :=
        mul_nonneg (by nlinarith) (mul_nonneg (by nlinarith) hfk2pos)
      nlinarith [key, hprod, sq_nonneg ((k : ℚ) + 4), sq_nonneg ((k : ℚ) + 5)]

-- Multiplier bound: |M_I(n)| ≤ 8/9 for n ≥ 2.
-- Chain: two strong ratio steps give 4*(k+4)²*(k+5)²*f_I(k+2) ≤ f_I(k+4).
-- Polynomial: 9(k+4)(k+6)²(2k+7) ≤ 32(k+4)²(k+5)², i.e. 14k³+169k²+676k+932 ≥ 0.
theorem M_I_bound (n : ℕ) (hn : n ≥ 2) :
    |β_I n * (f_I (n - 2) / f_I n)| ≤ 8 / 9 := by
  have hfn := f_I_pos n
  rw [abs_mul, abs_div, abs_of_pos (f_I_pos _), abs_of_pos hfn,
      ← mul_div_assoc, div_le_iff₀ hfn]
  -- Goal: |β_I n| * f_I(n-2) ≤ 8/9 * f_I n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 2 = k from by omega]
  match k with
  | 0 => -- n = 2: |β_I 2|*f_I 0 ≤ 8/9*f_I 2
    norm_num [f_I, α_I, β_I]
  | 1 => -- n = 3: |β_I 3|*f_I 1 ≤ 8/9*f_I 3
    norm_num [f_I, α_I, β_I]
  | k + 2 => -- n = k+4 ≥ 4
    simp only [show k + 2 + 2 = k + 4 from by omega]
    -- Get two steps of strong ratio
    have hr1 : 2 * ((k : ℚ) + 4) ^ 2 * f_I (k + 2) ≤ f_I (k + 3) := by
      have h := f_I_strong_ratio (k + 2) (by omega)
      simp only [show k + 2 + 1 = k + 3 from by omega] at h
      have heq : ((↑(k + 2) : ℚ) + 2) = ((k : ℚ) + 4) := by push_cast; ring
      linarith [show 2 * ((↑(k + 2) : ℚ) + 2) ^ 2 * f_I (k + 2) =
        2 * ((k : ℚ) + 4) ^ 2 * f_I (k + 2) from by rw [show ((↑(k + 2) : ℚ) + 2)^2 =
          ((k : ℚ) + 4)^2 from by rw [heq]]]
    have hr2 : 2 * ((k : ℚ) + 5) ^ 2 * f_I (k + 3) ≤ f_I (k + 4) := by
      have h := f_I_strong_ratio (k + 3) (by omega)
      simp only [show k + 3 + 1 = k + 4 from by omega] at h
      have heq : ((↑(k + 3) : ℚ) + 2) = ((k : ℚ) + 5) := by push_cast; ring
      linarith [show 2 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_I (k + 3) =
        2 * ((k : ℚ) + 5) ^ 2 * f_I (k + 3) from by rw [show ((↑(k + 3) : ℚ) + 2)^2 =
          ((k : ℚ) + 5)^2 from by rw [heq]]]
    -- Chain: 4*(k+4)²*(k+5)²*f_I(k+2) ≤ f_I(k+4)
    have hchain : 4 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_I (k + 2) ≤
        f_I (k + 4) :=
      calc 4 * ((k:ℚ)+4)^2 * ((k:ℚ)+5)^2 * f_I (k+2)
          = 2 * ((k:ℚ)+5)^2 * (2 * ((k:ℚ)+4)^2 * f_I (k+2)) := by ring
        _ ≤ 2 * ((k:ℚ)+5)^2 * f_I (k+3) :=
            mul_le_mul_of_nonneg_left hr1 (by positivity)
        _ ≤ f_I (k+4) := hr2
    -- β_I(k+4) < 0 (since (k+4) > 0, (k+6)² > 0, 2(k+4)-1 = 2k+7 > 0)
    have hbeta_neg : β_I (k + 4) < 0 := by
      simp only [β_I]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have h4 : (0 : ℚ) < k + 4 := by linarith
      nlinarith [sq_nonneg ((k : ℚ) + 6), mul_pos h4 h4]
    rw [abs_of_neg hbeta_neg]
    -- Need: -(β_I(k+4)) * f_I(k+2) ≤ 8/9 * f_I(k+4)
    -- Using chain: f_I(k+4) ≥ 4(k+4)²(k+5)²*f_I(k+2), so suffices:
    -- -(β_I(k+4)) ≤ (8/9)*4*(k+4)²*(k+5)² = (32/9)*(k+4)²*(k+5)²
    -- -(β_I(k+4)) = (k+4)(k+6)²(2k+7)
    -- Need: 9(k+4)(k+6)²(2k+7) ≤ 32(k+4)²(k+5)²
    -- i.e. 9(k+6)²(2k+7) ≤ 32(k+4)(k+5)²
    -- Gap: 14k³+169k²+676k+932 ≥ 0 (always true)
    have hpoly : -β_I (k + 4) ≤ (32 / 9) * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 := by
      simp only [β_I]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      nlinarith [sq_nonneg ((k : ℚ) + 4), sq_nonneg ((k : ℚ) + 5),
                 sq_nonneg ((k : ℚ) + 6), sq_nonneg (k : ℚ)]
    have hfk2 := (f_I_pos (k + 2)).le
    calc -β_I (k + 4) * f_I (k + 2)
        ≤ (32 / 9) * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_I (k + 2) :=
          mul_le_mul_of_nonneg_right hpoly hfk2
      _ = (8 / 9) * (4 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_I (k + 2)) := by ring
      _ ≤ (8 / 9) * f_I (k + 4) :=
          mul_le_mul_of_nonneg_left hchain (by norm_num)

/-- **CFData for Theorem I (16/(π²-8) variant 1).** -/
noncomputable def cfData_I : CFData where
  α := α_I
  β := β_I
  f := f_I
  g := g_I
  hf_rec := f_I_rec
  hg_rec := g_I_rec
  hf_ne_zero := f_I_ne_zero
  C := 8 / 9
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 2
  hn₀ := le_refl _
  h_mult := M_I_bound

end TheoremI_Instance

section TheoremK_Instance

/-! ## Theorem K: 12/(32-3π²)

α_K(n) = 3n² + 9n + 5, β_K(n) = -n²(n+3)(2n-3).
Spectral family (3,-2), braiding c=3.
Note: β_K(1) = -1·4·(-1) = 4 > 0; β_K(n) < 0 for n ≥ 2.
-/

def α_K (n : ℕ) : ℚ := 3 * (n : ℚ) ^ 2 + 9 * n + 5
def β_K (n : ℕ) : ℚ := -(n : ℚ) ^ 2 * ((n : ℚ) + 3) * (2 * (n : ℚ) - 3)

noncomputable def f_K : ℕ → ℚ
  | 0 => 5
  | 1 => 89
  | (n + 2) => α_K (n + 2) * f_K (n + 1) + β_K (n + 2) * f_K n

noncomputable def g_K : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_K (n + 2) * g_K (n + 1) + β_K (n + 2) * g_K n

theorem f_K_rec (n : ℕ) (hn : n ≥ 2) :
    f_K n = α_K n * f_K (n - 1) + β_K n * f_K (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [f_K]

theorem g_K_rec (n : ℕ) (hn : n ≥ 2) :
    g_K n = α_K n * g_K (n - 1) + β_K n * g_K (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [g_K]

-- Non-vanishing via α-dominance with growing ratio (n+2)²:
-- α_K(n+3) = 3(n+3)²+9(n+3)+5 = 3n²+27n+59, (n+4)² = n²+8n+16
-- Gap in α: 2n²+19n+43. For the β absorption:
-- (2n²+19n+43) - (n+6)(2n+3) = 4n+25 > 0.
theorem f_K_pos : ∀ n, 0 < f_K n := by
  suffices h : ∀ n, n ≥ 1 → 0 < f_K n ∧ ((n : ℚ) + 2) ^ 2 * f_K n ≤ f_K (n + 1) from by
    intro n
    match n with
    | 0 => norm_num [f_K]
    | n + 1 => exact (h (n + 1) (by omega)).1
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => omega
    | 1 =>
      refine ⟨by norm_num [f_K], ?_⟩
      change ((1 : ℚ) + 2) ^ 2 * f_K 1 ≤ f_K 2
      norm_num [f_K, α_K, β_K]
    | n + 2 =>
      have ⟨hpn1, hrn1⟩ := ih (n + 1) (by omega) (by omega)
      have hrn1' : ((n : ℚ) + 3) ^ 2 * f_K (n + 1) ≤ f_K (n + 2) := by
        have h := hrn1
        simp only [show n + 1 + 1 = n + 2 from by omega] at h
        convert h using 2; push_cast; ring
      constructor
      · linarith [mul_pos (show 0 < ((n : ℚ) + 3) ^ 2 from by positivity) hpn1]
      · change ((↑(n + 2) : ℚ) + 2) ^ 2 * f_K (n + 2) ≤
          α_K (n + 3) * f_K (n + 2) + β_K (n + 3) * f_K (n + 1)
        simp only [α_K, β_K]; push_cast
        -- Key: (2n²+19n+43) ≥ (n+6)(2n+3) = 2n²+15n+18, gap = 4n+25
        have key : 0 ≤ (2 * (n : ℚ) ^ 2 + 19 * n + 43) *
            (f_K (n + 2) - ((n : ℚ) + 3) ^ 2 * f_K (n + 1)) :=
          mul_nonneg (by positivity) (by linarith [hrn1'])
        have gap : 0 ≤ (4 * (n : ℚ) + 25) * ((n : ℚ) + 3) ^ 2 * f_K (n + 1) :=
          by positivity
        nlinarith [key, gap, hpn1, Nat.cast_nonneg (α := ℚ) n]

theorem f_K_ne_zero (n : ℕ) : f_K n ≠ 0 := ne_of_gt (f_K_pos n)

-- Tighter cuff: 2*(n+2)²*f_K(n) ≤ f_K(n+1) for n ≥ 2.
-- α_K(k+4) = 3k²+33k+89, 2(k+5)² = 2k²+20k+50.
-- α_K(k+4) - 2(k+5)² = k²+13k+39.
-- Self-sustaining gap: (k+4)²[2(k²+13k+39) - (k+7)(2k+5)]
--   = (k+4)²[2k²+26k+78 - 2k²-19k-35] = (k+4)²*(7k+43) > 0.
theorem f_K_strong_ratio (n : ℕ) (hn : n ≥ 2) :
    2 * ((n : ℚ) + 2) ^ 2 * f_K n ≤ f_K (n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    match k with
    | 0 =>
      change 2 * ((2 : ℚ) + 2) ^ 2 * f_K 2 ≤ f_K 3
      norm_num [f_K, α_K, β_K]
    | k + 1 =>
      -- n = k+3, IH at k+2
      have ih_raw := ih (k + 2) (by omega) (by omega)
      simp only [show k + 2 + 1 = k + 3 from by omega] at ih_raw
      have heq : ((↑(k + 2) : ℚ) + 2) = ((k : ℚ) + 4) := by push_cast; ring
      have ih' : 2 * ((k : ℚ) + 4) ^ 2 * f_K (k + 2) ≤ f_K (k + 3) := by
        have : ((↑(k + 2) : ℚ) + 2) ^ 2 = ((k : ℚ) + 4) ^ 2 := by rw [heq]
        linarith [show 2 * ((↑(k + 2) : ℚ) + 2) ^ 2 * f_K (k + 2) =
          2 * ((k : ℚ) + 4) ^ 2 * f_K (k + 2) from by rw [this]]
      -- Goal: 2*(↑(k+3)+2)²*f_K(k+3) ≤ f_K(k+4)
      change 2 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_K (k + 3) ≤
        α_K (k + 4) * f_K (k + 3) + β_K (k + 4) * f_K (k + 2)
      simp only [α_K, β_K]; push_cast
      -- Gap: α_K(k+4) - 2(k+5)² = k²+13k+39
      -- (k+4)²[2(k²+13k+39) - (k+7)(2k+5)] = (k+4)²(7k+43) > 0
      have hknn : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have hfk2pos := (f_K_pos (k + 2)).le
      have key : 0 ≤ (7 * (k : ℚ) + 43) *
          (f_K (k + 3) - 2 * ((k : ℚ) + 4) ^ 2 * f_K (k + 2)) :=
        mul_nonneg (by linarith) (by linarith)
      have hksq : (↑k + 3 + 2 : ℚ) ^ 2 = (↑k + 5) ^ 2 := by ring
      have hprod : 0 ≤ (7 * (k : ℚ) + 43) * (((k : ℚ) + 4) ^ 2 * f_K (k + 2)) :=
        mul_nonneg (by linarith) (mul_nonneg (by nlinarith) hfk2pos)
      nlinarith [key, hprod, sq_nonneg ((k : ℚ) + 4), sq_nonneg ((k : ℚ) + 5)]

-- Multiplier bound: |M_K(n)| ≤ 8/9 for n ≥ 2.
-- Chain: two strong ratio steps give 4*(k+4)²*(k+5)²*f_K(k+2) ≤ f_K(k+4).
-- Polynomial: 9(k+7)(2k+5) ≤ 32(k+5)², i.e. 14k²+149k+485 ≥ 0 (always).
theorem M_K_bound (n : ℕ) (hn : n ≥ 2) :
    |β_K n * (f_K (n - 2) / f_K n)| ≤ 8 / 9 := by
  have hfn := f_K_pos n
  rw [abs_mul, abs_div, abs_of_pos (f_K_pos _), abs_of_pos hfn,
      ← mul_div_assoc, div_le_iff₀ hfn]
  -- Goal: |β_K n| * f_K(n-2) ≤ 8/9 * f_K n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 2 = k from by omega]
  match k with
  | 0 => -- n = 2: |β_K 2| * f_K 0 ≤ 8/9 * f_K 2
    norm_num [f_K, α_K, β_K]
  | 1 => -- n = 3: |β_K 3| * f_K 1 ≤ 8/9 * f_K 3
    norm_num [f_K, α_K, β_K]
  | k + 2 => -- n = k+4 ≥ 4
    simp only [show k + 2 + 2 = k + 4 from by omega]
    -- Get two steps of strong ratio
    have hr1 : 2 * ((k : ℚ) + 4) ^ 2 * f_K (k + 2) ≤ f_K (k + 3) := by
      have h := f_K_strong_ratio (k + 2) (by omega)
      simp only [show k + 2 + 1 = k + 3 from by omega] at h
      have heq : ((↑(k + 2) : ℚ) + 2) = ((k : ℚ) + 4) := by push_cast; ring
      linarith [show 2 * ((↑(k + 2) : ℚ) + 2) ^ 2 * f_K (k + 2) =
        2 * ((k : ℚ) + 4) ^ 2 * f_K (k + 2) from by rw [show ((↑(k + 2) : ℚ) + 2)^2 =
          ((k : ℚ) + 4)^2 from by rw [heq]]]
    have hr2 : 2 * ((k : ℚ) + 5) ^ 2 * f_K (k + 3) ≤ f_K (k + 4) := by
      have h := f_K_strong_ratio (k + 3) (by omega)
      simp only [show k + 3 + 1 = k + 4 from by omega] at h
      have heq : ((↑(k + 3) : ℚ) + 2) = ((k : ℚ) + 5) := by push_cast; ring
      linarith [show 2 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_K (k + 3) =
        2 * ((k : ℚ) + 5) ^ 2 * f_K (k + 3) from by rw [show ((↑(k + 3) : ℚ) + 2)^2 =
          ((k : ℚ) + 5)^2 from by rw [heq]]]
    -- Chain: 4*(k+4)²*(k+5)²*f_K(k+2) ≤ f_K(k+4)
    have hchain : 4 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_K (k + 2) ≤
        f_K (k + 4) :=
      calc 4 * ((k:ℚ)+4)^2 * ((k:ℚ)+5)^2 * f_K (k+2)
          = 2 * ((k:ℚ)+5)^2 * (2 * ((k:ℚ)+4)^2 * f_K (k+2)) := by ring
        _ ≤ 2 * ((k:ℚ)+5)^2 * f_K (k+3) :=
            mul_le_mul_of_nonneg_left hr1 (by positivity)
        _ ≤ f_K (k+4) := hr2
    -- β_K(k+4) < 0 (since 2*(k+4)-3 = 2k+5 > 0)
    have hbeta_neg : β_K (k + 4) < 0 := by
      simp only [β_K]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have h4 : (0 : ℚ) < k + 4 := by linarith
      nlinarith [sq_nonneg ((k : ℚ) + 4), mul_pos h4 h4, mul_pos (mul_pos h4 h4) h4]
    -- |β_K(k+4)| = -β_K(k+4) = (k+4)²*(k+7)*(2k+5)
    rw [abs_of_neg hbeta_neg]
    -- Polynomial bound: -(β_K(k+4)) ≤ (32/9)*(k+4)²*(k+5)²
    -- i.e. 9*(k+4)²*(k+7)*(2k+5) ≤ 32*(k+4)²*(k+5)²
    -- Dividing by (k+4)²: 9*(k+7)*(2k+5) ≤ 32*(k+5)², i.e. 14k²+149k+485 ≥ 0
    have hpoly : -β_K (k + 4) ≤ (32 / 9) * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 := by
      simp only [β_K]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      nlinarith [sq_nonneg ((k : ℚ) + 4), sq_nonneg ((k : ℚ) + 5), sq_nonneg (k : ℚ)]
    have hfk2 := (f_K_pos (k + 2)).le
    calc -β_K (k + 4) * f_K (k + 2)
        ≤ (32 / 9) * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_K (k + 2) :=
          mul_le_mul_of_nonneg_right hpoly hfk2
      _ = (8 / 9) * (4 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_K (k + 2)) := by ring
      _ ≤ (8 / 9) * f_K (k + 4) :=
          mul_le_mul_of_nonneg_left hchain (by norm_num)

/-- **CFData for Theorem K (12/(32-3π²)).** -/
noncomputable def cfData_K : CFData where
  α := α_K
  β := β_K
  f := f_K
  g := g_K
  hf_rec := f_K_rec
  hg_rec := g_K_rec
  hf_ne_zero := f_K_ne_zero
  C := 8 / 9
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 2
  hn₀ := le_refl _
  h_mult := M_K_bound

end TheoremK_Instance

section TheoremJ_Instance

/-! ## Theorem J: 16/(π²-8) variant 2

a_n = 3n²+5n+1, b_n = -(n-1)²·n·(n+2).
Spectral family (3,-1). |M|_∞ ≈ 0.146.
-/

def α_J (n : ℕ) : ℚ := 3 * (n : ℚ) ^ 2 + 5 * n + 1
def β_J (n : ℕ) : ℚ := -((n : ℚ) - 1) ^ 2 * (n : ℚ) * ((n : ℚ) + 2)

noncomputable def f_J : ℕ → ℚ
  | 0 => 1
  | 1 => 9
  | (n + 2) => α_J (n + 2) * f_J (n + 1) + β_J (n + 2) * f_J n

noncomputable def g_J : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_J (n + 2) * g_J (n + 1) + β_J (n + 2) * g_J n

theorem f_J_rec (n : ℕ) (hn : n ≥ 2) :
    f_J n = α_J n * f_J (n - 1) + β_J n * f_J (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [f_J]

theorem g_J_rec (n : ℕ) (hn : n ≥ 2) :
    g_J n = α_J n * g_J (n - 1) + β_J n * g_J (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [g_J]

-- Non-vanishing via α-dominance with growing ratio (n+2)²:
-- α_J(n+3) = 3(n+3)²+5(n+3)+1 = 3n²+23n+43, (n+4)² = n²+8n+16
-- Gap in α: 2n²+15n+27. For the β absorption:
-- (2n²+15n+27)·(n+3)² - (n+2)²·(n+3)·(n+5) = (n+3)(n³+12n²+48n+61) > 0.
theorem f_J_pos : ∀ n, 0 < f_J n := by
  suffices h : ∀ n, n ≥ 1 → 0 < f_J n ∧ ((n : ℚ) + 2) ^ 2 * f_J n ≤ f_J (n + 1) from by
    intro n
    match n with
    | 0 => norm_num [f_J]
    | n + 1 => exact (h (n + 1) (by omega)).1
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => omega
    | 1 =>
      refine ⟨by norm_num [f_J], ?_⟩
      change ((1 : ℚ) + 2) ^ 2 * f_J 1 ≤ f_J 2
      norm_num [f_J, α_J, β_J]
    | n + 2 =>
      have ⟨hpn1, hrn1⟩ := ih (n + 1) (by omega) (by omega)
      have hrn1' : ((n : ℚ) + 3) ^ 2 * f_J (n + 1) ≤ f_J (n + 2) := by
        have h := hrn1
        simp only [show n + 1 + 1 = n + 2 from by omega] at h
        convert h using 2; push_cast; ring
      constructor
      · linarith [mul_pos (show 0 < ((n : ℚ) + 3) ^ 2 from by positivity) hpn1]
      · change ((↑(n + 2) : ℚ) + 2) ^ 2 * f_J (n + 2) ≤
          α_J (n + 3) * f_J (n + 2) + β_J (n + 3) * f_J (n + 1)
        simp only [α_J, β_J]; push_cast
        -- Gap: (2n²+15n+27)(n+3)² - (n+2)²(n+3)(n+5) = (n+3)(n³+12n²+48n+61)
        have key : 0 ≤ (2 * (n : ℚ) ^ 2 + 15 * n + 27) *
            (f_J (n + 2) - ((n : ℚ) + 3) ^ 2 * f_J (n + 1)) :=
          mul_nonneg (by positivity) (by linarith [hrn1'])
        have gap : 0 ≤ ((n : ℚ) ^ 3 + 12 * n ^ 2 + 48 * n + 61) *
            ((n : ℚ) + 3) * f_J (n + 1) :=
          by positivity
        nlinarith [key, gap, hpn1, Nat.cast_nonneg (α := ℚ) n]

theorem f_J_ne_zero (n : ℕ) : f_J n ≠ 0 := ne_of_gt (f_J_pos n)

-- Tighter cuff: 2*(n+2)²*f_J(n) ≤ f_J(n+1) for n ≥ 2.
-- α_J(k+4) - 2(k+5)² = (3(k+4)²+5(k+4)+1) - 2(k+5)² = k²+9k+19.
-- Self-sustaining gap: (k+4)[2(k²+9k+19)(k+4) - (k+3)²(k+6)]
--   = (k+4)(k³+14k²+65k+98) > 0 (always).
theorem f_J_strong_ratio (n : ℕ) (hn : n ≥ 2) :
    2 * ((n : ℚ) + 2) ^ 2 * f_J n ≤ f_J (n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    match k with
    | 0 =>
      change 2 * ((2 : ℚ) + 2) ^ 2 * f_J 2 ≤ f_J 3
      norm_num [f_J, α_J, β_J]
    | k + 1 =>
      -- n = k+3, IH at k+2
      have ih_raw := ih (k + 2) (by omega) (by omega)
      simp only [show k + 2 + 1 = k + 3 from by omega] at ih_raw
      have heq : ((↑(k + 2) : ℚ) + 2) = ((k : ℚ) + 4) := by push_cast; ring
      have ih' : 2 * ((k : ℚ) + 4) ^ 2 * f_J (k + 2) ≤ f_J (k + 3) := by
        have : ((↑(k + 2) : ℚ) + 2) ^ 2 = ((k : ℚ) + 4) ^ 2 := by rw [heq]
        linarith [show 2 * ((↑(k + 2) : ℚ) + 2) ^ 2 * f_J (k + 2) =
          2 * ((k : ℚ) + 4) ^ 2 * f_J (k + 2) from by rw [this]]
      -- Goal: 2*(↑(k+3)+2)²*f_J(k+3) ≤ f_J(k+4)
      change 2 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_J (k + 3) ≤
        α_J (k + 4) * f_J (k + 3) + β_J (k + 4) * f_J (k + 2)
      simp only [α_J, β_J]; push_cast
      -- Gap: 2(k²+9k+19)(k+4)² - (k+3)²(k+4)(k+6) = (k+4)(k³+14k²+65k+98) > 0
      have hknn : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have hfk2pos := (f_J_pos (k + 2)).le
      have key : 0 ≤ ((k : ℚ) ^ 2 + 9 * k + 19) *
          (f_J (k + 3) - 2 * ((k : ℚ) + 4) ^ 2 * f_J (k + 2)) :=
        mul_nonneg (by nlinarith) (by linarith)
      have hksq : (↑k + 3 + 2 : ℚ) ^ 2 = (↑k + 5) ^ 2 := by ring
      have hprod : 0 ≤ ((k : ℚ) ^ 2 + 9 * k + 19) * (((k : ℚ) + 4) ^ 2 * f_J (k + 2)) :=
        mul_nonneg (by nlinarith) (mul_nonneg (by nlinarith) hfk2pos)
      nlinarith [key, hprod, sq_nonneg ((k : ℚ) + 4), sq_nonneg ((k : ℚ) + 5)]

-- Multiplier bound: |M_J(n)| ≤ 1/2 for n ≥ 2.
-- Chain: f_J(n) ≥ 4*n²*(n+1)²*f_J(n-2) for n ≥ 4 (two strong ratio steps).
-- Polynomial: (n-1)²·n·(n+2) ≤ 2·n²·(n+1)²,
--   i.e. (n-1)²·(n+2) ≤ 2n(n+1)², gap = n³+4n²+5n-2 > 0 for n ≥ 1.
-- With k-indexing (n=k+4): (k+3)²(k+6) ≤ 2(k+4)(k+5)², gap = k³+16k²+85k+146 > 0.
-- n=2,3: direct computation.
theorem M_J_bound (n : ℕ) (hn : n ≥ 2) :
    |β_J n * (f_J (n - 2) / f_J n)| ≤ 1 / 2 := by
  have hfn := f_J_pos n
  rw [abs_mul, abs_div, abs_of_pos (f_J_pos _), abs_of_pos hfn,
      ← mul_div_assoc, div_le_iff₀ hfn]
  -- Goal: |β_J n| * f_J(n-2) ≤ 1/2 * f_J n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 2 = k from by omega]
  match k with
  | 0 => -- n = 2: |β_J 2| * f_J 0 ≤ 1/2 * f_J 2
    norm_num [f_J, α_J, β_J]
  | 1 => -- n = 3: |β_J 3| * f_J 1 ≤ 1/2 * f_J 3
    norm_num [f_J, α_J, β_J]
  | k + 2 => -- n = k+4 ≥ 4
    simp only [show k + 2 + 2 = k + 4 from by omega]
    -- Get two steps of strong ratio
    have hr1 : 2 * ((k : ℚ) + 4) ^ 2 * f_J (k + 2) ≤ f_J (k + 3) := by
      have h := f_J_strong_ratio (k + 2) (by omega)
      simp only [show k + 2 + 1 = k + 3 from by omega] at h
      have heq : ((↑(k + 2) : ℚ) + 2) = ((k : ℚ) + 4) := by push_cast; ring
      linarith [show 2 * ((↑(k + 2) : ℚ) + 2) ^ 2 * f_J (k + 2) =
        2 * ((k : ℚ) + 4) ^ 2 * f_J (k + 2) from by rw [show ((↑(k + 2) : ℚ) + 2)^2 =
          ((k : ℚ) + 4)^2 from by rw [heq]]]
    have hr2 : 2 * ((k : ℚ) + 5) ^ 2 * f_J (k + 3) ≤ f_J (k + 4) := by
      have h := f_J_strong_ratio (k + 3) (by omega)
      simp only [show k + 3 + 1 = k + 4 from by omega] at h
      have heq : ((↑(k + 3) : ℚ) + 2) = ((k : ℚ) + 5) := by push_cast; ring
      linarith [show 2 * ((↑(k + 3) : ℚ) + 2) ^ 2 * f_J (k + 3) =
        2 * ((k : ℚ) + 5) ^ 2 * f_J (k + 3) from by rw [show ((↑(k + 3) : ℚ) + 2)^2 =
          ((k : ℚ) + 5)^2 from by rw [heq]]]
    -- Chain: 4*(k+4)²*(k+5)²*f_J(k+2) ≤ f_J(k+4)
    have hchain : 4 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_J (k + 2) ≤
        f_J (k + 4) :=
      calc 4 * ((k:ℚ)+4)^2 * ((k:ℚ)+5)^2 * f_J (k+2)
          = 2 * ((k:ℚ)+5)^2 * (2 * ((k:ℚ)+4)^2 * f_J (k+2)) := by ring
        _ ≤ 2 * ((k:ℚ)+5)^2 * f_J (k+3) :=
            mul_le_mul_of_nonneg_left hr1 (by positivity)
        _ ≤ f_J (k+4) := hr2
    -- β_J(k+4) < 0 (since (k+3)² > 0, (k+4) > 0, (k+6) > 0)
    have hbeta_neg : β_J (k + 4) < 0 := by
      simp only [β_J]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have h4 : (0 : ℚ) < k + 4 := by linarith
      nlinarith [sq_nonneg ((k : ℚ) + 3), mul_pos h4 h4]
    -- |β_J(k+4)| = (k+3)²(k+4)(k+6)
    rw [abs_of_neg hbeta_neg]
    -- Polynomial bound: -(β_J(k+4)) ≤ 2*(k+4)²*(k+5)²
    -- i.e. (k+3)²(k+6) ≤ 2(k+4)(k+5)², gap = k³+16k²+85k+146 ≥ 0
    have hpoly : -β_J (k + 4) ≤ 2 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 := by
      simp only [β_J]; push_cast
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      nlinarith [sq_nonneg ((k : ℚ) + 3), sq_nonneg ((k : ℚ) + 4),
                 sq_nonneg ((k : ℚ) + 5)]
    have hfk2 := (f_J_pos (k + 2)).le
    calc -β_J (k + 4) * f_J (k + 2)
        ≤ 2 * ((k : ℚ) + 4) ^ 2 * ((k : ℚ) + 5) ^ 2 * f_J (k + 2) :=
          mul_le_mul_of_nonneg_right hpoly hfk2
      _ ≤ (1/2) * f_J (k + 4) := by nlinarith [hchain, f_J_pos (k + 2)]

/-- **CFData for Theorem J (16/(π²-8) variant 2).** -/
noncomputable def cfData_J : CFData where
  α := α_J
  β := β_J
  f := f_J
  g := g_J
  hf_rec := f_J_rec
  hg_rec := g_J_rec
  hf_ne_zero := f_J_ne_zero
  C := 1 / 2
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 2
  hn₀ := le_refl _
  h_mult := M_J_bound

end TheoremJ_Instance

section TheoremL_Instance

/-! ## Theorem L: 16/(π²-4)

α_L(n) = 5n²+7n+2 = (5n+2)(n+1), β_L(n) = -4n²(n+1)².
Spectral family (5,-4), roots (4,1), |M|_∞ = 1/4.

KEY DESIGN CHOICE: The convergent numerators p_L(n) = (n+1)!(n+2)! grow only
polynomially in the reduced recurrence (they lie on the root-1 branch), giving
|M_n| = 4n/(n+2) → 4 > 1. The compositor requires |M_n| < 1, so we use a
FAST-GROWING auxiliary solution f_L with initial conditions (2, 13) = p_L + q_L.
This solution has a nonzero component on the root-4 branch, giving
|M_n| → 1/4. The growth bound 3(n+2)²·f_L(n) ≤ f_L(n+1) holds for n ≥ 6,
yielding C = 4/9 with n₀ = 8 (two chain steps each need n-2 ≥ 6).

Self-sustaining gap: α_L(n+1) - (13/3)(n+2)² = (2n²-n-10)/3 = (2n-5)(n+2)/3 ≥ 0
for n ≥ 3, so the cuff propagates once established.
-/

def α_L (n : ℕ) : ℚ := 5 * (n : ℚ) ^ 2 + 7 * n + 2
def β_L (n : ℕ) : ℚ := -4 * (n : ℚ) ^ 2 * ((n : ℚ) + 1) ^ 2

-- Fast-growing auxiliary solution (convergent numerators + denominators)
noncomputable def f_L : ℕ → ℚ
  | 0 => 2
  | 1 => 13
  | (n + 2) => α_L (n + 2) * f_L (n + 1) + β_L (n + 2) * f_L n

noncomputable def g_L : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => α_L (n + 2) * g_L (n + 1) + β_L (n + 2) * g_L n

theorem f_L_rec (n : ℕ) (hn : n ≥ 2) :
    f_L n = α_L n * f_L (n - 1) + β_L n * f_L (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [f_L]

theorem g_L_rec (n : ℕ) (hn : n ≥ 2) :
    g_L n = α_L n * g_L (n - 1) + β_L n * g_L (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; simp [g_L]

-- Non-vanishing via strong ratio bound.
-- Strategy: prove 0 < f_L n ∧ 3(n+2)²·f_L(n) ≤ f_L(n+1) for n ≥ 6.
-- Base cases n=0..6 by computation; inductive step via self-sustaining gap.
-- The gap polynomial: α_L(n+1) - (13/3)(n+2)² = (2n-5)(n+2)/3,
-- positive for n ≥ 3, so the cuff propagates from n=6 onward.
theorem f_L_pos : ∀ n, 0 < f_L n := by
  -- Prove: for n ≥ 6, 0 < f_L n ∧ 3*(n+2)²*f_L n ≤ f_L (n+1)
  suffices h : ∀ n, n ≥ 6 → 0 < f_L n ∧ 3 * ((n : ℚ) + 2) ^ 2 * f_L n ≤ f_L (n + 1) from by
    intro n
    match n with
    | 0 => norm_num [f_L]
    | 1 => norm_num [f_L]
    | 2 => norm_num [f_L, α_L, β_L]
    | 3 => norm_num [f_L, α_L, β_L]
    | 4 => norm_num [f_L, α_L, β_L]
    | 5 => norm_num [f_L, α_L, β_L]
    | 6 => exact (h 6 (by omega)).1
    | n + 7 => exact (h (n + 7) (by omega)).1
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 =>
      constructor
      · norm_num [f_L, α_L, β_L]
      · change 3 * ((6 : ℚ) + 2) ^ 2 * f_L 6 ≤ f_L 7
        norm_num [f_L, α_L, β_L]
    | n + 7 =>
      have ⟨hpn1, hrn1⟩ := ih (n + 6) (by omega) (by omega)
      have hrn1' : 3 * ((n : ℚ) + 8) ^ 2 * f_L (n + 6) ≤ f_L (n + 7) := by
        have h := hrn1
        simp only [show n + 6 + 1 = n + 7 from by omega] at h
        convert h using 2; push_cast; ring
      constructor
      · -- 0 < f_L(n+7): from ratio bound and positivity
        linarith [mul_pos (show 0 < 3 * ((n : ℚ) + 8) ^ 2 from by positivity) hpn1]
      · -- 3*(n+9)²*f_L(n+7) ≤ f_L(n+8)
        change 3 * ((↑(n + 7) : ℚ) + 2) ^ 2 * f_L (n + 7) ≤
          α_L (n + 8) * f_L (n + 7) + β_L (n + 8) * f_L (n + 6)
        simp only [α_L, β_L]; push_cast
        -- Self-sustaining gap: α_L(n+8) - 3(n+9)² = 2n²+33n+135 = (2n+15)(n+9)
        -- Combined gap: 3(2n²+33n+135) - 4(n+9)² = 2n²+27n+81 = (2n+9)(n+9) ≥ 0
        have key : 0 ≤ (2 * (n : ℚ) ^ 2 + 33 * n + 135) *
            (f_L (n + 7) - 3 * ((n : ℚ) + 8) ^ 2 * f_L (n + 6)) :=
          mul_nonneg (by positivity) (by linarith [hrn1'])
        have hfn6pos := hpn1.le
        have hknn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
        -- gap · (n+8)² · f_L(n+6) ≥ 0 helps nlinarith bridge the degree
        have hprod : 0 ≤ (2 * (n : ℚ) ^ 2 + 33 * n + 135) *
            (((n : ℚ) + 8) ^ 2 * f_L (n + 6)) :=
          mul_nonneg (by positivity) (mul_nonneg (by positivity) hfn6pos)
        nlinarith [key, hprod, sq_nonneg ((n : ℚ) + 8), sq_nonneg ((n : ℚ) + 9)]

theorem f_L_ne_zero (n : ℕ) : f_L n ≠ 0 := ne_of_gt (f_L_pos n)

-- Strong ratio bound: 3*(n+2)²*f_L(n) ≤ f_L(n+1) for n ≥ 6.
-- Extracted from the positivity proof for reuse in the multiplier bound.
theorem f_L_strong_ratio (n : ℕ) (hn : n ≥ 6) :
    3 * ((n : ℚ) + 2) ^ 2 * f_L n ≤ f_L (n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    match k with
    | 0 =>
      change 3 * ((6 : ℚ) + 2) ^ 2 * f_L 6 ≤ f_L 7
      norm_num [f_L, α_L, β_L]
    | k + 1 =>
      -- n = k+7, IH at k+6
      have ih_raw := ih (k + 6) (by omega) (by omega)
      simp only [show k + 6 + 1 = k + 7 from by omega] at ih_raw
      have heq : ((↑(k + 6) : ℚ) + 2) = ((k : ℚ) + 8) := by push_cast; ring
      have ih' : 3 * ((k : ℚ) + 8) ^ 2 * f_L (k + 6) ≤ f_L (k + 7) := by
        have : ((↑(k + 6) : ℚ) + 2) ^ 2 = ((k : ℚ) + 8) ^ 2 := by rw [heq]
        linarith [show 3 * ((↑(k + 6) : ℚ) + 2) ^ 2 * f_L (k + 6) =
          3 * ((k : ℚ) + 8) ^ 2 * f_L (k + 6) from by rw [this]]
      -- Goal: 3*(↑(k+7)+2)²*f_L(k+7) ≤ f_L(k+8)
      change 3 * ((↑(k + 7) : ℚ) + 2) ^ 2 * f_L (k + 7) ≤
        α_L (k + 8) * f_L (k + 7) + β_L (k + 8) * f_L (k + 6)
      simp only [α_L, β_L]; push_cast
      -- Self-sustaining gap: α_L(k+8) - 3(k+9)² = 2k²+33k+135 = (2k+15)(k+9)
      -- Combined gap: 3(2k²+33k+135) - 4(k+9)² = 2k²+27k+81 = (2k+9)(k+9) ≥ 0
      have hknn : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have hfk6pos := (f_L_pos (k + 6)).le
      have key : 0 ≤ (2 * (k : ℚ) ^ 2 + 33 * k + 135) *
          (f_L (k + 7) - 3 * ((k : ℚ) + 8) ^ 2 * f_L (k + 6)) :=
        mul_nonneg (by positivity) (by linarith)
      have hksq : (↑k + 7 + 2 : ℚ) ^ 2 = (↑k + 9) ^ 2 := by ring
      have hprod : 0 ≤ (2 * (k : ℚ) ^ 2 + 33 * k + 135) *
          (((k : ℚ) + 8) ^ 2 * f_L (k + 6)) :=
        mul_nonneg (by positivity) (mul_nonneg (by positivity) hfk6pos)
      nlinarith [key, hprod, sq_nonneg ((k : ℚ) + 8), sq_nonneg ((k : ℚ) + 9)]

-- Multiplier bound: |M_L(n)| ≤ 4/9 for n ≥ 8.
-- With n = k+8: chain f_L(k+8) ≥ 9(k+8)²(k+9)²·f_L(k+6) (two strong ratio steps).
-- |β_L(k+8)| = 4(k+8)²(k+9)² = (4/9)·9(k+8)²(k+9)², giving exact ratio 4/9.
theorem M_L_bound (n : ℕ) (hn : n ≥ 8) :
    |β_L n * (f_L (n - 2) / f_L n)| ≤ 4 / 9 := by
  have hfn := f_L_pos n
  rw [abs_mul, abs_div, abs_of_pos (f_L_pos _), abs_of_pos hfn,
      ← mul_div_assoc, div_le_iff₀ hfn]
  -- Goal: |β_L n| * f_L(n-2) ≤ 4/9 * f_L n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  simp only [show k + 8 - 2 = k + 6 from by omega]
  -- Get two steps of strong ratio
  have hr1 : 3 * ((k : ℚ) + 8) ^ 2 * f_L (k + 6) ≤ f_L (k + 7) := by
    have h := f_L_strong_ratio (k + 6) (by omega)
    simp only [show k + 6 + 1 = k + 7 from by omega] at h
    have heq : ((↑(k + 6) : ℚ) + 2) = ((k : ℚ) + 8) := by push_cast; ring
    linarith [show 3 * ((↑(k + 6) : ℚ) + 2) ^ 2 * f_L (k + 6) =
      3 * ((k : ℚ) + 8) ^ 2 * f_L (k + 6) from by rw [show ((↑(k + 6) : ℚ) + 2)^2 =
        ((k : ℚ) + 8)^2 from by rw [heq]]]
  have hr2 : 3 * ((k : ℚ) + 9) ^ 2 * f_L (k + 7) ≤ f_L (k + 8) := by
    have h := f_L_strong_ratio (k + 7) (by omega)
    simp only [show k + 7 + 1 = k + 8 from by omega] at h
    have heq : ((↑(k + 7) : ℚ) + 2) = ((k : ℚ) + 9) := by push_cast; ring
    linarith [show 3 * ((↑(k + 7) : ℚ) + 2) ^ 2 * f_L (k + 7) =
      3 * ((k : ℚ) + 9) ^ 2 * f_L (k + 7) from by rw [show ((↑(k + 7) : ℚ) + 2)^2 =
        ((k : ℚ) + 9)^2 from by rw [heq]]]
  -- Chain: 9*(k+8)²*(k+9)²*f_L(k+6) ≤ f_L(k+8)
  have hchain : 9 * ((k : ℚ) + 8) ^ 2 * ((k : ℚ) + 9) ^ 2 * f_L (k + 6) ≤
      f_L (k + 8) :=
    calc 9 * ((k:ℚ)+8)^2 * ((k:ℚ)+9)^2 * f_L (k+6)
        = 3 * ((k:ℚ)+9)^2 * (3 * ((k:ℚ)+8)^2 * f_L (k+6)) := by ring
      _ ≤ 3 * ((k:ℚ)+9)^2 * f_L (k+7) :=
          mul_le_mul_of_nonneg_left hr1 (by positivity)
      _ ≤ f_L (k+8) := hr2
  -- β_L(k+8) < 0
  have hbeta_neg : β_L (k + 8) < 0 := by
    simp only [β_L]; push_cast
    have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have h8 : (0 : ℚ) < k + 8 := by linarith
    nlinarith [sq_nonneg ((k : ℚ) + 8), mul_pos h8 h8,
               mul_pos (mul_pos h8 h8) h8]
  -- |β_L(k+8)| = 4*(k+8)²*(k+9)²
  rw [abs_of_neg hbeta_neg]
  -- Key: -(β_L(k+8)) = 4(k+8)²(k+9)² = (4/9) * 9*(k+8)²*(k+9)²
  have hfk6 := (f_L_pos (k + 6)).le
  calc -β_L (k + 8) * f_L (k + 6)
      = (4 / 9) * (9 * ((k : ℚ) + 8) ^ 2 * ((k : ℚ) + 9) ^ 2 * f_L (k + 6)) := by
        simp only [β_L]; push_cast; ring
    _ ≤ (4 / 9) * f_L (k + 8) :=
        mul_le_mul_of_nonneg_left hchain (by norm_num)

/-- **CFData for Theorem L (16/(π²-4)).** -/
noncomputable def cfData_L : CFData where
  α := α_L
  β := β_L
  f := f_L
  g := g_L
  hf_rec := f_L_rec
  hg_rec := g_L_rec
  hf_ne_zero := f_L_ne_zero
  C := 4 / 9
  hC_pos := by norm_num
  hC_lt1 := by norm_num
  n₀ := 8
  hn₀ := by norm_num
  h_mult := M_L_bound

/-- **Convergence of 16/(π²-4) CF.** -/
theorem cf_L_converges (N : ℕ) (hN : N ≥ 8) (M : ℕ) :
    |cfData_L.z (N + M) - cfData_L.z N| ≤
      |cfData_L.Delta N| * (4 / 9 / (1 - 4 / 9)) :=
  cfData_L.cauchy_bound N hN M

/-- Simplified: tail bound is (4/5)|Δ_N| (since C/(1-C) = (4/9)/(5/9) = 4/5). -/
theorem cf_L_tail (N : ℕ) (hN : N ≥ 8) (M : ℕ) :
    |cfData_L.z (N + M) - cfData_L.z N| ≤ (4 / 5) * |cfData_L.Delta N| := by
  have h := cf_L_converges N hN M
  have : (4 : ℚ) / 9 / (1 - 4 / 9) = 4 / 5 := by norm_num
  linarith

/-- SL(2) chain contraction for Theorem L. -/
theorem cf_L_contractive :
    ∀ n, n ≥ 8 → |cfData_L.Delta (n + 1)| ≤ 4 / 9 * |cfData_L.Delta n| :=
  cfData_L.chain_is_contractive

end TheoremL_Instance

/-! ## Summary of what's proved

FULLY INSTANTIATED (0 sorry):
- Theorem F (8/π²): cfData_F with cauchy_bound, tail bound ≤ |Δ_N|,
  SL(2) chain contraction at rate 1/2.
- Theorem B (30/π²): cfData_B (positive β, α-dominance multiplier)
- Theorem D (18/π²): cfData_D (positive β, α-dominance multiplier)
- Theorem E (24/π²): cfData_E (positive β, α-dominance multiplier; n₀=3)
- Theorem A (18/(π²-8)): cfData_A (negative β; f_A_ratio + chain multiplier; n₀=2)
- Theorem C (16/(4+π²)): cfData_C (negative β; f_C_strong_ratio chain; C=8/9; n₀=2)
- Theorem G (32/π²): cfData_G (negative β; f_G_strong_ratio chain; C=8/9; n₀=3)
- Theorem H (22/π²): cfData_H (negative β; f_H_strong_ratio chain; C=1/2; n₀=2)
- Theorem I (16/(π²-8) v1): cfData_I (negative β; f_I_strong_ratio chain; C=8/9; n₀=2)
- Theorem K (12/(32-3π²)): cfData_K (negative β; f_K_strong_ratio chain; C=8/9; n₀=2)
- Theorem J (16/(π²-8) v2): cfData_J (negative β; f_J_strong_ratio chain; C=1/2; n₀=2)
- Theorem L (16/(π²-4)): cfData_L (spectral family (5,-4); fast-branch auxiliary
  solution; f_L_strong_ratio chain; C=4/9; n₀=8)

All 12 CFs have full CFData instantiations. 0 sorry in the file.
-/
