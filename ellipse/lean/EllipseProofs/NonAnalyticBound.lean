/-
  EllipseProofs/NonAnalyticBound.lean

  Formal skeleton for the non-analytic lower bound on approximation error.

  PROOF ESSENCE (3 sentences):
  An analytic function D(x) matching R(x) at orders 0 and 1 differs from R(x)
  by (d₂ - c₂)x² - (7π/704)x²ln(x) + o(x²). The x²|ln x| term dominates x²
  as x → 0⁺ because |ln x| → ∞. Therefore the non-analytic term sets an
  irreducible floor: |D(x) - R(x)| ≥ (7π/704)x²|ln x| - Cx².

  Paper reference: Theorem 5.4 (Non-analytic barrier)
-/

import Mathlib.Tactic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import AnalysisBridges.TaylorBounds

open Asymptotics Real Filter Topology

/-!
## Key Lemma: x² log x is not analytic at 0

An analytic function at 0 has bounded third derivative in a neighborhood.
But (d³/dx³)(x² log x) = 2/x - 2/x + ... has a 2/x singularity, so
x² log x cannot be analytic at 0. Equivalently, it has no convergent
Taylor series at 0.
-/

/-- x² * log x tends to 0 as x → 0⁺ (l'Hôpital). -/
lemma x_sq_log_tendsto_zero :
    Filter.Tendsto (fun x : ℝ => x ^ 2 * log x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 2) (by positivity : (0 : ℝ) < 2)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x _
  simp only [rpow_ofNat, mul_comm]

/-- The third derivative of x² log x is 2/x + 2, unbounded near 0. -/
lemma third_deriv_x_sq_log_unbounded :
    ¬ Filter.BoundedAtFilter (nhdsWithin 0 (Set.Ioi 0))
      (fun x : ℝ => 2 / x + 2) := by
  -- BoundedAtFilter means f =O[l] 1, i.e. IsBoundedUnder (· ≤ ·) l (‖f ·‖)
  -- But 2/x + 2 → +∞ as x → 0⁺, so ‖2/x + 2‖ → +∞, contradicting boundedness
  intro h_bdd
  -- Show 2/x + 2 → +∞
  have h_tend : Filter.Tendsto (fun x : ℝ => 2 / x + 2)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    (tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num : (0:ℝ) < 2)).atTop_add
      tendsto_const_nhds
  -- So ‖2/x + 2‖ → +∞
  have h_norm_tend : Filter.Tendsto (fun x : ℝ => ‖2 / x + 2‖)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_norm_atTop_atTop.comp h_tend
  -- A function with ‖·‖ → +∞ is not IsBoundedUnder
  exact Filter.not_isBoundedUnder_of_tendsto_atTop h_norm_tend
    ((Asymptotics.isBigO_one_iff ℝ).mp h_bdd)

/-- x² log x is not analytic at 0.
    Proof: If analytic, the isolated zeros theorem gives f(z) = z^n · g(z) with g(0) ≠ 0.
    For n ≤ 1: g(z) → 0 as z → 0⁺ (from x_sq_log_tendsto_zero), so g(0) = 0. Contradiction.
    For n ≥ 2: g(z) = z^{2-n} · log z → -∞ as z → 0⁺. Contradicts g continuous. -/
theorem x_sq_log_not_analytic : ¬ AnalyticAt ℝ (fun x : ℝ => x ^ 2 * log x) 0 := by
  intro h_an
  -- Step 1: f is not identically zero near 0
  have h_not_zero : ¬ (∀ᶠ z in 𝓝 (0 : ℝ), z ^ 2 * log z = 0) := by
    rw [Metric.eventually_nhds_iff]
    push_neg
    intro ε hε
    refine ⟨min (ε / 2) (1 / 2), ?_, ?_⟩
    · simp only [dist_zero_right, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < min (ε / 2) (1 / 2))]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · have hz_pos : (0 : ℝ) < min (ε / 2) (1 / 2) := by positivity
      have hz_lt_one : min (ε / 2) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      linarith [mul_neg_of_pos_of_neg (by positivity : min (ε / 2) (1 / 2) ^ 2 > 0)
        (Real.log_neg hz_pos hz_lt_one)]
  -- Step 2: Factor f(z) = (z-0)^n · g(z) with g analytic, g(0) ≠ 0
  obtain ⟨n, g, hg_an, hg_ne, hg_eq⟩ := h_an.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h_not_zero
  have hg_cont : ContinuousAt g 0 := hg_an.continuousAt
  have hg_tendsto : Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) :=
    hg_cont.tendsto.mono_left nhdsWithin_le_nhds
  -- Simplify factorization: (z - 0)^n • g z  →  z^n * g z
  replace hg_eq : ∀ᶠ z in 𝓝 (0 : ℝ), z ^ 2 * log z = z ^ n * g z := by
    filter_upwards [hg_eq] with z hz
    simp only [sub_zero, smul_eq_mul] at hz; exact hz
  by_cases hn0 : n = 0
  · -- n = 0: g(z) = z^2 * log z near 0, g(0) = 0, contradicts g(0) ≠ 0
    apply hg_ne
    have : ∀ᶠ z in 𝓝 (0 : ℝ), g z = z ^ 2 * log z := by
      filter_upwards [hg_eq] with z hz; simp [hn0] at hz; linarith
    exact this.self_of_nhds.trans (by simp [Real.log_zero])
  · by_cases hn1 : n = 1
    · -- n = 1: g(z) = z * log z for z ≠ 0 near 0, g(z) → 0, g(0) = 0
      apply hg_ne
      have h_g_eq : ∀ᶠ z in nhdsWithin (0 : ℝ) (Set.Ioi 0), g z = z * log z := by
        filter_upwards [hg_eq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
          with z hz hz_pos
        simp only [hn1, pow_one] at hz
        -- hz : z ^ 2 * log z = z * g z. For z > 0, cancel z.
        have h_rw : z ^ 2 * log z = z * (z * log z) := by ring
        exact mul_left_cancel₀ (ne_of_gt hz_pos) (by linarith : z * g z = z * (z * log z))
      -- z * log z → 0 as z → 0⁺
      have h_xlx : Tendsto (fun z : ℝ => z * log z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) (by norm_num : (0 : ℝ) < 1)
        refine h.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x _
        simp only [rpow_one, mul_comm]
      exact tendsto_nhds_unique hg_tendsto ((Filter.tendsto_congr' h_g_eq).mpr h_xlx)
    · -- n ≥ 2: log z = z^{n-2} * g(z), but log → -∞ while product has finite limit
      have hn2 : n ≥ 2 := by omega
      have h_log_eq : ∀ᶠ z in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          log z = z ^ (n - 2) * g z := by
        filter_upwards [hg_eq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
          with z hz hz_pos
        have hz2_ne : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz_pos)
        have h_split : z ^ n = z ^ 2 * z ^ (n - 2) := by
          rw [← pow_add]; congr 1; omega
        exact mul_left_cancel₀ hz2_ne
          (by rw [← mul_assoc, ← h_split]; exact hz : z ^ 2 * log z = z ^ 2 * (z ^ (n - 2) * g z))
      -- z^{n-2} * g(z) has a finite limit as z → 0⁺
      have h_finite : Tendsto (fun z => z ^ (n - 2) * g z)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 ^ (n - 2) * g 0)) :=
        ((continuous_pow (n - 2)).continuousAt.tendsto.mul hg_cont.tendsto).mono_left
          nhdsWithin_le_nhds
      -- But log z → -∞ as z → 0⁺, so z^{n-2} * g(z) → -∞ too
      have h_bot : Tendsto (fun z => z ^ (n - 2) * g z)
          (nhdsWithin 0 (Set.Ioi 0)) atBot :=
        (Filter.tendsto_congr' h_log_eq).mp tendsto_log_nhdsGT_zero
      exact absurd h_finite (not_tendsto_nhds_of_tendsto_atBot h_bot _)

/-!
## Main Theorem: Non-analytic lower bound

If D(x) is any analytic function matching R(x) at orders 0 and 1,
then the x² log x term in R(x) creates an irreducible approximation floor.
-/

/-- The logarithmic coefficient from the flat-limit expansion: 7π/704. -/
noncomputable def logCoeff : ℝ := 7 * π / 704

/-- logCoeff > 0 since π > 0. -/
lemma logCoeff_pos : logCoeff > 0 := by
  unfold logCoeff
  positivity

/-- **Non-analytic lower bound (Theorem 5.4)**.

    Let D be analytic at 0 with D(0) = 7π/22 and D'(0) = α₁.
    Let R(x) = 7π/22 + α₁·x + (7π/704)·x²·ln(x) + c₂·x² + o(x²).
    Then for x near 0⁺:  |D(x) - R(x)| ≥ (7π/704)·x²·|ln x| - C·x².

    Proof skeleton:
    1. D analytic ⟹ D(x) = 7π/22 + α₁·x + d₂·x² + O(x³) near 0
    2. D(x) - R(x) = (d₂ - c₂)·x² - (7π/704)·x²·ln(x) + o(x²)
    3. Triangle inequality: |D - R| ≥ (7π/704)·x²·|ln x| - |d₂ - c₂|·x² - |o(x²)|
    4. For x small enough, the log term dominates. -/
theorem non_analytic_lower_bound
    (D : ℝ → ℝ) (α₁ c₂ : ℝ)
    (h_an : AnalyticAt ℝ D 0)
    (h_D0 : D 0 = 7 * π / 22)
    (h_D'0 : HasDerivAt D α₁ 0)
    -- R is the true expansion with log singularity
    (R : ℝ → ℝ)
    (_h_R : ∀ x > 0, R x = 7 * π / 22 + α₁ * x
                       + logCoeff * x ^ 2 * log x + c₂ * x ^ 2
                       + (R x - (7 * π / 22 + α₁ * x
                           + logCoeff * x ^ 2 * log x + c₂ * x ^ 2)))
    -- The remainder is o(x²)
    (h_rem : (fun x => R x - (7 * π / 22 + α₁ * x
                + logCoeff * x ^ 2 * log x + c₂ * x ^ 2))
             =o[nhdsWithin 0 (Set.Ioi 0)] (fun x => x ^ 2)) :
    -- Conclusion: ∃ C, for x near 0⁺, |D(x) - R(x)| ≥ logCoeff * x²|ln x| - C*x²
    ∃ C : ℝ, ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
      |D x - R x| ≥ logCoeff * x ^ 2 * |log x| - C * x ^ 2 := by
  -- Step 1: extract a quadratic Taylor model for `D` on the right neighborhood.
  obtain ⟨d₂, h_D_expand⟩ : ∃ d₂ : ℝ,
      (fun x => D x - (7 * π / 22 + α₁ * x + d₂ * x ^ 2))
        =o[nhdsWithin 0 (Set.Ioi 0)] (fun x => x ^ 2) := by
    obtain ⟨r, hr, hTaylor⟩ := AnalysisBridges.analytic_taylor2_local (f := D) (x₀ := 0) h_an
    let s : Set ℝ := Set.Icc (-r) r
    let d₂ : ℝ := ((2 : ℝ)⁻¹) * iteratedDerivWithin 2 D s 0
    have hs_mem : s ∈ 𝓝 (0 : ℝ) := by
      dsimp [s]
      exact Icc_mem_nhds (by linarith [hr]) (by linarith [hr])
    have hs_ud : UniqueDiffWithinAt ℝ s 0 := by
      dsimp [s]
      exact (uniqueDiffOn_Icc (show (-r) < r by linarith [hr]) 0
        (by constructor <;> linarith [hr]))
    have hDerivWithin : derivWithin D s 0 = α₁ := by
      exact (h_D'0.hasDerivWithinAt).derivWithin hs_ud
    have hTaylor2 :
        (fun x : ℝ => D x - (D 0 + derivWithin D s 0 * x + d₂ * x ^ 2))
          =o[𝓝[s] 0] (fun x : ℝ => x ^ 2) := by
      simpa [AnalysisBridges.taylorWithinEval_two, d₂, s, one_add_one_eq_two, sub_eq_add_neg,
        add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hTaylor
    have hTaylorIoi :
        (fun x : ℝ => D x - (D 0 + derivWithin D s 0 * x + d₂ * x ^ 2))
          =o[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ 2) := by
      have hInter :
          (fun x : ℝ => D x - (D 0 + derivWithin D s 0 * x + d₂ * x ^ 2))
            =o[𝓝[Set.Ioi 0 ∩ s] 0] (fun x : ℝ => x ^ 2) := by
        exact hTaylor2.mono (nhdsWithin_mono _ Set.inter_subset_right)
      have hRestr : 𝓝[Set.Ioi 0] (0 : ℝ) = 𝓝[Set.Ioi 0 ∩ s] (0 : ℝ) :=
        nhdsWithin_restrict' (Set.Ioi 0) hs_mem
      simpa [hRestr] using hInter
    refine ⟨d₂, ?_⟩
    convert hTaylorIoi using 1
    funext x
    simp [h_D0, hDerivWithin]
  -- Step 2: combine the two little-o remainders and isolate the log term.
  let dErr : ℝ → ℝ := fun x => D x - (7 * π / 22 + α₁ * x + d₂ * x ^ 2)
  let rErr : ℝ → ℝ := fun x => R x - (7 * π / 22 + α₁ * x + logCoeff * x ^ 2 * log x + c₂ * x ^ 2)
  have hdErr : dErr =o[nhdsWithin 0 (Set.Ioi 0)] (fun x => x ^ 2) := by
    simpa [dErr] using h_D_expand
  have hrErr : rErr =o[nhdsWithin 0 (Set.Ioi 0)] (fun x => x ^ 2) := by
    simpa [rErr] using h_rem
  have hErr : (fun x => dErr x - rErr x) =o[nhdsWithin 0 (Set.Ioi 0)] (fun x => x ^ 2) :=
    hdErr.sub hrErr
  have hErrBound : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), |dErr x - rErr x| ≤ x ^ 2 := by
    have hB := hErr.bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hB] with x hx
    have hx2 : 0 ≤ x ^ 2 := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hx2] using hx
  have h_pos : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), 0 < x := by
    exact (eventually_mem_nhdsWithin :
      ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), x ∈ Set.Ioi (0 : ℝ)).mono
      (fun x hx => hx)
  have h_lt1 : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), x < (1 : ℝ) := by
    have h_lt1_nhds : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x < (1 : ℝ) :=
      Iio_mem_nhds (by norm_num : (0 : ℝ) < (1 : ℝ))
    exact h_lt1_nhds.filter_mono (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  refine ⟨|d₂ - c₂| + 1, ?_⟩
  filter_upwards [hErrBound, h_pos, h_lt1] with x hErrx hxpos hxlt1
  let a : ℝ := logCoeff * x ^ 2 * |log x|
  let b : ℝ := (d₂ - c₂) * x ^ 2 + (dErr x - rErr x)
  have hlogabs : |log x| = -log x := abs_of_neg (Real.log_neg hxpos hxlt1)
  have hdecomp :
      D x - R x =
        (-logCoeff * x ^ 2 * log x) + ((d₂ - c₂) * x ^ 2 + (dErr x - rErr x)) := by
    simp [dErr, rErr]
    ring
  have hrewrite : D x - R x = a + b := by
    unfold a b
    rw [hdecomp, hlogabs]
    ring
  have ha_nonneg : 0 ≤ a := by
    unfold a
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have hlogc : 0 ≤ logCoeff := le_of_lt logCoeff_pos
    have hmul : 0 ≤ logCoeff * x ^ 2 := mul_nonneg hlogc hx2
    exact mul_nonneg hmul (abs_nonneg (log x))
  have htri : a - |b| ≤ |a + b| := by
    have haux : |a| ≤ |a + b| + |b| := by
      simpa [abs_neg, add_assoc, add_left_comm, add_comm] using abs_add_le (a + b) (-b)
    have habs : |a| = a := abs_of_nonneg ha_nonneg
    linarith
  have hb : |b| ≤ (|d₂ - c₂| + 1) * x ^ 2 := by
    unfold b
    have hx2 : 0 ≤ x ^ 2 := by positivity
    calc
      |(d₂ - c₂) * x ^ 2 + (dErr x - rErr x)|
          ≤ |(d₂ - c₂) * x ^ 2| + |dErr x - rErr x| := abs_add_le _ _
      _ = |d₂ - c₂| * x ^ 2 + |dErr x - rErr x| := by
        simp [abs_mul, abs_of_nonneg hx2]
      _ ≤ |d₂ - c₂| * x ^ 2 + x ^ 2 := by gcongr
      _ = (|d₂ - c₂| + 1) * x ^ 2 := by ring
  have hmain : |D x - R x| ≥ a - (|d₂ - c₂| + 1) * x ^ 2 := by
    have : a - (|d₂ - c₂| + 1) * x ^ 2 ≤ |D x - R x| := by
      calc
        a - (|d₂ - c₂| + 1) * x ^ 2 ≤ a - |b| := by linarith [hb]
        _ ≤ |a + b| := htri
        _ = |D x - R x| := by rw [← hrewrite]
    exact this
  simpa [a] using hmain

/-- **Corollary**: No analytic correction can achieve o(x² log x) accuracy.
    The non-analytic barrier is structural, not a matter of parameter tuning. -/
theorem analytic_barrier_corollary
    (D : ℝ → ℝ) (h_an : AnalyticAt ℝ D 0) :
    ¬ AnalyticAt ℝ (fun x => D x - (7 * π / 22 + logCoeff * x ^ 2 * log x)) 0 := by
  intro h_diff
  have hDconst : AnalyticAt ℝ (fun x => D x - (7 * π / 22)) 0 := h_an.sub analyticAt_const
  have hScaled :
      AnalyticAt ℝ (fun x => (-logCoeff) * (x ^ 2 * log x)) 0 := by
    have hTmp :
        AnalyticAt ℝ
          (fun x => (D x - (7 * π / 22 + logCoeff * x ^ 2 * log x)) - (D x - (7 * π / 22))) 0 :=
      h_diff.sub hDconst
    convert hTmp using 1
    funext x
    ring
  have hCoeff_ne : (-logCoeff) ≠ 0 := neg_ne_zero.mpr (ne_of_gt logCoeff_pos)
  have h_base : AnalyticAt ℝ (fun x => x ^ 2 * log x) 0 := by
    have hMulInv :
        AnalyticAt ℝ (fun x => (-logCoeff)⁻¹ * ((-logCoeff) * (x ^ 2 * log x))) 0 :=
      analyticAt_const.mul hScaled
    convert hMulInv using 1
    funext x
    have hlogCoeff_ne : logCoeff ≠ 0 := ne_of_gt logCoeff_pos
    have hmul : (-logCoeff)⁻¹ * (-logCoeff * (x ^ 2 * log x)) = x ^ 2 * log x := by
      calc
        (-logCoeff)⁻¹ * (-logCoeff * (x ^ 2 * log x))
            = ((-logCoeff)⁻¹ * (-logCoeff)) * (x ^ 2 * log x) := by ring
        _ = 1 * (x ^ 2 * log x) := by simp [hlogCoeff_ne]
        _ = x ^ 2 * log x := by ring
    exact hmul.symm
  exact x_sq_log_not_analytic h_base
