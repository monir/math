/-
  EllipseProofs/CFCompositor.lean

  The Compositor Functor: takes a CF data package and produces
  convergence theorems. This is the crown jewel connecting
  CFReduction (framework) and CFArithmetic (per-theorem data).

  STRUCTURE:
  - CFData: bundles recurrence, solutions, contraction bound
  - Derived: z_n, Δ_n, M_n
  - Theorems: reduction, geometric decay, telescoping, tail bound, Cauchy bound
  - Instantiations: one per CF theorem

  Paper reference: cfproof_strip13.tex, Proposition 2 + all seven §Phase III
-/

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.Basic
import EllipseProofs.CFReduction
import EllipseProofs.CFArithmetic

open Finset

/-! ## Section 0: The CFData Structure -/

/-- A CF data package: everything needed to run convergent reduction.
    The "object" in our compositor functor. -/
structure CFData where
  /-- Reduced recurrence coefficients -/
  α : ℕ → ℚ
  β : ℕ → ℚ
  /-- Two solutions to y_n = α_n · y_{n-1} + β_n · y_{n-2} -/
  f : ℕ → ℚ
  g : ℕ → ℚ
  /-- f satisfies the recurrence for n ≥ 2 -/
  hf_rec : ∀ n, n ≥ 2 → f n = α n * f (n - 1) + β n * f (n - 2)
  /-- g satisfies the recurrence for n ≥ 2 -/
  hg_rec : ∀ n, n ≥ 2 → g n = α n * g (n - 1) + β n * g (n - 2)
  /-- f never vanishes -/
  hf_ne_zero : ∀ n, f n ≠ 0
  /-- Contraction constant in (0, 1) -/
  C : ℚ
  hC_pos : 0 < C
  hC_lt1 : C < 1
  /-- Start index for multiplier bound -/
  n₀ : ℕ
  hn₀ : n₀ ≥ 2
  /-- |M_n| ≤ C for n ≥ n₀ -/
  h_mult : ∀ n, n ≥ n₀ → |β n * (f (n - 2) / f n)| ≤ C

namespace CFData

/-- The quotient z_n = g_n / f_n -/
def z (d : CFData) (n : ℕ) : ℚ := d.g n / d.f n

/-- The difference Δ_n = z_n - z_{n-1} for n ≥ 1, and 0 for n = 0 -/
noncomputable def Delta (d : CFData) : ℕ → ℚ
  | 0 => 0
  | n + 1 => d.z (n + 1) - d.z n

/-- The multiplier M_n = -β_n · f_{n-2} / f_n -/
def M (d : CFData) (n : ℕ) : ℚ := -d.β n * (d.f (n - 2) / d.f n)

/-! ## Section 1: Reduction Identity

Wraps `quotient_reduction_step` from CFReduction.lean in CFData language.
-/

/-- |M_n| ≤ C for n ≥ n₀. Bridge from the raw multiplier_bound. -/
theorem abs_M_le_C (d : CFData) (n : ℕ) (hn : n ≥ d.n₀) :
    |d.M n| ≤ d.C := by
  unfold M
  rw [neg_mul, abs_neg]
  exact d.h_mult n hn

/-- Core reduction: Δ_{n+1} = M_{n+1} · Δ_n for n + 1 ≥ 2 (i.e., n ≥ 1).
    This wraps quotient_reduction_step. -/
theorem delta_eq_M_mul (d : CFData) (n : ℕ) (hn : n ≥ 1) :
    d.Delta (n + 1) = d.M (n + 1) * d.Delta n := by
  -- Unfold Delta at the successor
  change d.z (n + 1) - d.z n = d.M (n + 1) * d.Delta n
  -- For n ≥ 1, Delta n = z n - z (n - 1)
  have hn1 : n + 1 ≥ 2 := by omega
  have : d.Delta n = d.z n - d.z (n - 1) := by
    cases n with
    | zero => omega
    | succ m => simp [Delta, z]
  rw [this]
  -- Now apply quotient_reduction_step
  have hfn1 := d.hf_ne_zero (n + 1)
  have hfn := d.hf_ne_zero n
  have hfn_1 := d.hf_ne_zero (n - 1)
  have hf := d.hf_rec (n + 1) hn1
  have hg := d.hg_rec (n + 1) hn1
  -- quotient_reduction_step gives:
  -- g(n+1)/f(n+1) - g(n)/f(n) = -β(n+1) * (f(n-1)/f(n+1)) * (g(n)/f(n) - g(n-1)/f(n-1))
  -- Note: for the recurrence at index n+1, the terms are f(n+1), f(n), f(n+1-2)=f(n-1)
  have hsub : n + 1 - 1 = n := by omega
  have hsub2 : n + 1 - 2 = n - 1 := by omega
  rw [hsub, hsub2] at hf hg
  have key := quotient_reduction_step (d.α (n + 1)) (d.β (n + 1))
    (d.f (n + 1)) (d.f n) (d.f (n - 1))
    (d.g (n + 1)) (d.g n) (d.g (n - 1))
    hfn1 hfn hfn_1 hf hg
  -- key : g(n+1)/f(n+1) - g(n)/f(n) = -β(n+1)*(f(n-1)/f(n+1))*(g(n)/f(n) - g(n-1)/f(n-1))
  simp only [z, M]
  rw [hsub2]
  exact key

/-! ## Section 2: Geometric Decay

By induction: |Δ_{n₀ + k}| ≤ |Δ_{n₀}| · C^k.
-/

/-- Geometric decay of the differences. -/
theorem delta_geometric (d : CFData) (k : ℕ) :
    |d.Delta (d.n₀ + k)| ≤ |d.Delta d.n₀| * d.C ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- |Δ(n₀ + k + 1)| = |M(n₀+k+1) · Δ(n₀+k)| = |M| · |Δ(n₀+k)|
    have hn₀k : d.n₀ + k ≥ 1 := by have := d.hn₀; omega
    have hge : d.n₀ + k + 1 ≥ d.n₀ := by omega
    have hred := d.delta_eq_M_mul (d.n₀ + k) hn₀k
    -- hred : Delta(n₀ + k + 1) = M(n₀+k+1) * Delta(n₀+k)
    rw [show d.n₀ + (k + 1) = d.n₀ + k + 1 from by omega]
    rw [hred, abs_mul, pow_succ]
    -- Goal: |M(n₀+k+1)| * |Δ(n₀+k)| ≤ |Δ(n₀)| * (C^k * C)
    have hM := d.abs_M_le_C (d.n₀ + k + 1) hge
    calc |d.M (d.n₀ + k + 1)| * |d.Delta (d.n₀ + k)|
        ≤ d.C * |d.Delta (d.n₀ + k)| := by
          apply mul_le_mul_of_nonneg_right hM (abs_nonneg _)
      _ ≤ d.C * (|d.Delta d.n₀| * d.C ^ k) := by
          apply mul_le_mul_of_nonneg_left ih d.hC_pos.le
      _ = |d.Delta d.n₀| * (d.C ^ k * d.C) := by ring

/-! ## Section 3: Telescoping Identity

z_N = z_0 + Σ_{k=0}^{N-1} Δ_{k+1}.
-/

/-- The telescoping sum: z_N = z_0 + Σ_{k=0}^{N-1} Δ(k+1). -/
theorem telescoping (d : CFData) (N : ℕ) :
    d.z N = d.z 0 + (Finset.range N).sum (fun k => d.Delta (k + 1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    simp [Delta]

/-! ## Section 4: Partial Sum Bound

Σ_{k=0}^{N-1} |Δ(n₀ + k + 1)| ≤ |Δ(n₀)| · C/(1-C).
-/

/-- Each tail term is bounded by the geometric series. -/
theorem partial_tail_bound (d : CFData) (N : ℕ) :
    (Finset.range N).sum (fun k => |d.Delta (d.n₀ + k + 1)|)
      ≤ |d.Delta d.n₀| * (d.C / (1 - d.C)) := by
  -- Bound each term: |Δ(n₀+k+1)| ≤ |Δ(n₀)| · C^{k+1}
  have hterms : ∀ k ∈ Finset.range N,
      |d.Delta (d.n₀ + k + 1)| ≤ |d.Delta d.n₀| * d.C ^ (k + 1) := by
    intro k _
    have := d.delta_geometric (k + 1)
    rwa [show d.n₀ + (k + 1) = d.n₀ + k + 1 from by omega] at this
  calc (Finset.range N).sum (fun k => |d.Delta (d.n₀ + k + 1)|)
      ≤ (Finset.range N).sum (fun k => |d.Delta d.n₀| * d.C ^ (k + 1)) :=
        Finset.sum_le_sum hterms
    _ = |d.Delta d.n₀| * (Finset.range N).sum (fun k => d.C ^ (k + 1)) := by
        rw [← Finset.mul_sum]
    _ ≤ |d.Delta d.n₀| * (d.C / (1 - d.C)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact geometric_tail_partial d.C d.hC_pos d.hC_lt1 N

/-! ## Section 5: Cauchy Bound

|z_{N+M} - z_N| ≤ |Δ_N| · C/(1-C) for N ≥ n₀.
This is the algebraic crown jewel: the sequence is Cauchy with explicit rate.
-/

/-- Generalized geometric decay: for any base N ≥ n₀,
    |Δ(N + k)| ≤ |Δ(N)| · C^k. -/
theorem delta_geometric_from (d : CFData) (N : ℕ) (hN : N ≥ d.n₀) (k : ℕ) :
    |d.Delta (N + k)| ≤ |d.Delta N| * d.C ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hn₀k : N + k ≥ 1 := by have := d.hn₀; omega
    have hge : N + k + 1 ≥ d.n₀ := by omega
    have hred := d.delta_eq_M_mul (N + k) hn₀k
    rw [show N + (k + 1) = N + k + 1 from by omega]
    rw [hred, abs_mul, pow_succ]
    have hM := d.abs_M_le_C (N + k + 1) hge
    calc |d.M (N + k + 1)| * |d.Delta (N + k)|
        ≤ d.C * |d.Delta (N + k)| :=
          mul_le_mul_of_nonneg_right hM (abs_nonneg _)
      _ ≤ d.C * (|d.Delta N| * d.C ^ k) :=
          mul_le_mul_of_nonneg_left ih d.hC_pos.le
      _ = |d.Delta N| * (d.C ^ k * d.C) := by ring

/-- Shifted telescoping: z(N+M) - z(N) = Σ_{k=0}^{M-1} Δ(N+k+1). -/
theorem telescoping_shifted (d : CFData) (N M : ℕ) :
    d.z (N + M) - d.z N =
      (Finset.range M).sum (fun k => d.Delta (N + k + 1)) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    have heq : N + (m + 1) = N + m + 1 := by omega
    rw [heq]; simp only [Delta]; ring

/-- The Cauchy bound: the tail of the quotient sequence is controlled.
    This is the algebraic crown jewel of convergent reduction. -/
theorem cauchy_bound (d : CFData) (N : ℕ) (hN : N ≥ d.n₀) (M : ℕ) :
    |d.z (N + M) - d.z N| ≤ |d.Delta N| * (d.C / (1 - d.C)) := by
  rw [d.telescoping_shifted N M]
  calc |(Finset.range M).sum (fun k => d.Delta (N + k + 1))|
      ≤ (Finset.range M).sum (fun k => |d.Delta (N + k + 1)|) :=
        abs_sum_le_sum_abs _ _
    _ ≤ |d.Delta N| * (d.C / (1 - d.C)) := by
        have hterms : ∀ k ∈ Finset.range M,
            |d.Delta (N + k + 1)| ≤ |d.Delta N| * d.C ^ (k + 1) := by
          intro k _
          have := d.delta_geometric_from N hN (k + 1)
          rwa [show N + (k + 1) = N + k + 1 from by omega] at this
        calc (Finset.range M).sum (fun k => |d.Delta (N + k + 1)|)
            ≤ (Finset.range M).sum (fun k => |d.Delta N| * d.C ^ (k + 1)) :=
              Finset.sum_le_sum hterms
          _ = |d.Delta N| * (Finset.range M).sum (fun k => d.C ^ (k + 1)) := by
              rw [← Finset.mul_sum]
          _ ≤ |d.Delta N| * (d.C / (1 - d.C)) := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              exact geometric_tail_partial d.C d.hC_pos d.hC_lt1 M

end CFData

/-! ## Section 6: Instantiation for Theorem A

Pilot instantiation: 18/(π² - 8).
CF: a_n = 3n²+9n+5, b_n = -4(n+1)².
Reduced: α_n = a_{n-1}/(n(n-1)), β_n = b_{n-1}/(n²(n-1)²).
Multiplier: M_n = n²/(2(n+1)(2n+5)), bounded by 1/2 for n ≥ 1.
-/

-- The reduced coefficients for Theorem A
def alpha_A (n : ℕ) : ℚ := (3 * (n - 1 : ℤ) ^ 2 + 9 * (n - 1) + 5) / (n * (n - 1))

def beta_A (n : ℕ) : ℚ := (-4 * (n : ℤ) ^ 2) / ((n : ℤ) ^ 2 * ((n : ℤ) - 1) ^ 2)

-- The closed-form numerator sequence for Theorem A:
-- f_n = 6(n+1)(n!)²/(2n+3)! (the "reduced p̂_n")
-- For instantiation we use the first several values and the recurrence.
-- f_0 = 1, f_1 = 5, f_2 = 81/4, ...
-- Actually the integer numerator sequence: p_0=1, p_1=5, p_2=81
-- After (n!)² normalization: p̂_n = p_n/(n!)²

-- For the pilot, we verify the compositor structure compiles
-- with a minimal example using explicit rational sequences.

-- Pilot: a 3-term CF data package for Theorem A using explicit values.
-- This demonstrates the compositor pattern works. Full instantiation
-- requires the closed-form sequence definition.
-- def cf_data_A_pilot : CFData where ...
-- (deferred: requires closed-form f, g as ℕ → ℚ with proved recurrence)

/-! ## Section 7: Bridge Lemma Template

For each CF, we need: from "n² < 2(n+1)(2n+5)" over ℕ,
derive "|n²/(2(n+1)(2n+5))| ≤ 1/2" over ℚ.
-/

/-- Bridge: Theorem A multiplier bound in ℚ form.
    n²/(2(n+1)(2n+5)) ≤ 1/2 for n ≥ 1. -/
theorem multiplier_bound_18_rat (n : ℕ) (hn : n ≥ 1) :
    (n : ℚ) ^ 2 / (2 * ((n : ℚ) + 1) * (2 * n + 5)) ≤ 1 / 2 := by
  have hd : (0 : ℚ) < 2 * ((n : ℚ) + 1) * (2 * n + 5) := by positivity
  -- Equivalent to 2n² ≤ 2(n+1)(2n+5), which is 0 ≤ 2n²+14n+10
  have key : 2 * (n : ℚ) ^ 2 ≤ 2 * ((n : ℚ) + 1) * (2 * n + 5) := by
    nlinarith [sq_nonneg (n : ℚ)]
  -- a/b ≤ 1/2 ← 2a ≤ b ← key
  rw [div_le_div_iff₀ hd (by norm_num : (0 : ℚ) < 2)]; linarith

/-- Bridge: Theorem F multiplier bound in ℚ form. -/
theorem multiplier_bound_8_rat (n : ℕ) (hn : n ≥ 1) :
    (n : ℚ) ^ 2 / (((n : ℚ) + 1) * (2 * n + 1)) ≤ 1 / 2 := by
  have hd : (0 : ℚ) < ((n : ℚ) + 1) * (2 * n + 1) := by positivity
  have key : 2 * (n : ℚ) ^ 2 ≤ ((n : ℚ) + 1) * (2 * n + 1) := by
    nlinarith [sq_nonneg (n : ℚ)]
  rw [div_le_div_iff₀ hd (by norm_num : (0 : ℚ) < 2)]; linarith

/-- Bridge: Theorem D multiplier bound in ℚ form. -/
theorem multiplier_bound_18pi2_rat (n : ℕ) (hn : n ≥ 1) :
    (n : ℚ) / (2 * (2 * (n : ℚ) + 1)) ≤ 1 / 2 := by
  have hd : (0 : ℚ) < 2 * (2 * (n : ℚ) + 1) := by positivity
  have key : 2 * (n : ℚ) ≤ 2 * (2 * (n : ℚ) + 1) := by nlinarith
  rw [div_le_div_iff₀ hd (by norm_num : (0 : ℚ) < 2)]; linarith

/-! ## Section 8: SL(2) Chain Interface

The transfer matrices T_n = [[α_n, β_n], [1, 0]] live in GL(2,ℚ) with
det(T_n) = -β_n. The product T_1 · T_2 · ... · T_n encodes the full
CF convergent. The compositor functor works because:

1. **Local cuffing**: |M_n| ≤ C < 1 is a spectral-radius condition on
   the "Schur complement" of T_n acting on the quotient z_n = g_n/f_n.
   Each step contracts the error by factor ≤ C.

2. **ω-weak coverage**: The condition need only hold eventually (∀ n ≥ n₀).
   Finitely many "bad" initial terms contribute a bounded prefix.

3. **Chain composition**: The product ∏_{k=n₀}^n |M_k| ≤ C^{n-n₀} gives
   geometric decay. This is the SL(2) → contraction bridge.

The key theorem: an ω-weak chain of contractions composes into
global geometric convergence. This is `delta_geometric_from`.
-/

/-- **SL(2) chain contraction (omega-weak).**
    If each local transfer step contracts by ≤ C, then
    the composed product contracts geometrically.
    This is the abstract interface: given ANY sequence
    with local contraction, the full chain converges.

    Concretely: if |a_{n+1}| ≤ C · |a_n| for all n ≥ n₀,
    then |a_{n₀+k}| ≤ |a_{n₀}| · C^k. -/
theorem sl2_chain_contraction
    (a : ℕ → ℚ) (C : ℚ) (hC_pos : 0 < C)
    (n₀ : ℕ)
    (h_contract : ∀ n, n ≥ n₀ → |a (n + 1)| ≤ C * |a n|)
    (k : ℕ) :
    |a (n₀ + k)| ≤ |a n₀| * C ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hge : n₀ + k ≥ n₀ := by omega
    have := h_contract (n₀ + k) hge
    rw [show n₀ + (k + 1) = n₀ + k + 1 from by omega]
    calc |a (n₀ + k + 1)|
        ≤ C * |a (n₀ + k)| := this
      _ ≤ C * (|a n₀| * C ^ k) :=
          mul_le_mul_of_nonneg_left ih hC_pos.le
      _ = |a n₀| * C ^ (k + 1) := by ring

/-- **Tail from chain contraction.**
    The geometric tail bound follows from chain contraction
    + the rational geometric series bound. -/
theorem sl2_chain_tail
    (a : ℕ → ℚ) (C : ℚ) (hC_pos : 0 < C) (hC_lt1 : C < 1)
    (n₀ : ℕ)
    (h_contract : ∀ n, n ≥ n₀ → |a (n + 1)| ≤ C * |a n|)
    (N : ℕ) :
    (Finset.range N).sum (fun k => |a (n₀ + k + 1)|)
      ≤ |a n₀| * (C / (1 - C)) := by
  have hterms : ∀ k ∈ Finset.range N,
      |a (n₀ + k + 1)| ≤ |a n₀| * C ^ (k + 1) := by
    intro k _
    have := sl2_chain_contraction a C hC_pos n₀ h_contract (k + 1)
    rwa [show n₀ + (k + 1) = n₀ + k + 1 from by omega] at this
  calc (Finset.range N).sum (fun k => |a (n₀ + k + 1)|)
      ≤ (Finset.range N).sum (fun k => |a n₀| * C ^ (k + 1)) :=
        Finset.sum_le_sum hterms
    _ = |a n₀| * (Finset.range N).sum (fun k => C ^ (k + 1)) := by
        rw [← Finset.mul_sum]
    _ ≤ |a n₀| * (C / (1 - C)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact geometric_tail_partial C hC_pos hC_lt1 N

/-- **CFData uses the SL(2) chain.**
    The compositor's geometric decay is an instance of `sl2_chain_contraction`
    applied to the sequence `Delta`. -/
theorem CFData.chain_is_contractive (d : CFData) :
    ∀ n, n ≥ d.n₀ → |d.Delta (n + 1)| ≤ d.C * |d.Delta n| := by
  intro n hn
  have hn1 : n ≥ 1 := by have := d.hn₀; omega
  have hred := d.delta_eq_M_mul n hn1
  rw [hred, abs_mul]
  have hM := d.abs_M_le_C (n + 1) (by omega)
  exact mul_le_mul_of_nonneg_right hM (abs_nonneg _)
