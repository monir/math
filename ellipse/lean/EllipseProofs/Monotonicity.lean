/-
  EllipseProofs/Monotonicity.lean

  Formal skeleton of Theorem 6.1 (Strict monotonicity at fixed product):
  Fix N > 0. Define P_N(a) = P(a, N/a) for a >= sqrt(N). Then P_N is strictly increasing.

  ESSENCE IN THREE SENTENCES:
  The integrand F(u,θ) = √(e^{2u}cos²θ + e^{-2u}sin²θ) satisfies F'' = F + 4AB/F³ > 0,
  so I(u) = ∫F dθ is strictly convex. The symmetry I(-u) = I(u) forces I'(0) = 0.
  Strict convexity with vanishing derivative at the origin implies I'(u) > 0 for all u > 0.

  Paper reference: proof_v14.tex, Section 6.1, Theorem 6.1 (thm:mono)
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Real MeasureTheory Set
open scoped Interval

noncomputable section

/-! ## Definitions -/

/-- The integrand F(u,θ) = √(e^{2u}cos²θ + e^{-2u}sin²θ).
    This is the speed of the parametric ellipse (√N·eᵘ, √N·e⁻ᵘ)
    at angle θ, divided by √N. -/
def F (u θ : ℝ) : ℝ :=
  Real.sqrt (exp (2 * u) * cos θ ^ 2 + exp (-2 * u) * sin θ ^ 2)

/-- The perimeter integral I(u) = ∫₀^{π/2} F(u,θ) dθ.
    The actual perimeter is P_N(u) = 4√N · I(u). -/
def I (u : ℝ) : ℝ :=
  ∫ θ in (0)..(π / 2), F u θ

/-- First u-derivative integrand formula for `F`. -/
def F1 (u θ : ℝ) : ℝ :=
  (2 * exp (2 * u) * cos θ ^ 2 - 2 * exp (-2 * u) * sin θ ^ 2) / (2 * F u θ)

/-- Second u-derivative integrand formula for `F`. -/
def F2 (u θ : ℝ) : ℝ :=
  F u θ + 4 * cos θ ^ 2 * sin θ ^ 2 / F u θ ^ 3

/-! ## Step 1: Strict positivity of the integrand -/

/-- The argument inside the square root is strictly positive for all u, θ. -/
lemma F_sq_pos (u θ : ℝ) : exp (2 * u) * cos θ ^ 2 + exp (-2 * u) * sin θ ^ 2 > 0 := by
  have hc := sq_nonneg (cos θ)
  have hs := sq_nonneg (sin θ)
  have he1 : exp (2 * u) > 0 := exp_pos _
  have he2 : exp (-2 * u) > 0 := exp_pos _
  -- cos²θ + sin²θ = 1, so at least one is positive; both exponentials are positive
  have hcs : cos θ ^ 2 + sin θ ^ 2 = 1 := cos_sq_add_sin_sq θ
  have h1 : exp (2 * u) * cos θ ^ 2 ≥ 0 := mul_nonneg he1.le hc
  have h2 : exp (-2 * u) * sin θ ^ 2 ≥ 0 := mul_nonneg he2.le hs
  -- The sum equals exp(2u)*cos² + exp(-2u)*sin² ≥ min(exp(2u),exp(-2u)) * 1 > 0
  -- We show this by noting exp(-2u)*cos² ≤ exp(2u)*cos² or vice versa
  by_cases hc0 : cos θ ^ 2 = 0
  · -- If cos² = 0, then sin² = 1, so the sum = exp(-2u) > 0
    have : sin θ ^ 2 = 1 := by linarith
    nlinarith
  · -- If cos² > 0, then exp(2u) * cos² > 0
    have hc_pos : cos θ ^ 2 > 0 := lt_of_le_of_ne hc (Ne.symm hc0)
    nlinarith [mul_pos he1 hc_pos]

/-- F(u,θ) > 0 for all u, θ. -/
lemma F_pos (u θ : ℝ) : F u θ > 0 := by
  unfold F
  exact Real.sqrt_pos_of_pos (F_sq_pos u θ)

/-! ## Technical local bounds for dominated differentiation -/

/-- If `x ∈ [u-1, u+1]`, then `|x| ≤ |u| + 1`. -/
private lemma abs_le_abs_add_one {u x : ℝ} (hx : x ∈ Icc (u - 1) (u + 1)) :
    |x| ≤ |u| + 1 := by
  have hx_abs : |x - u| ≤ 1 := by
    refine abs_le.2 ?_
    constructor
    · linarith [hx.1]
    · linarith [hx.2]
  have htri : |(x - u) + u| ≤ |x - u| + |u| := by
    simpa [Real.norm_eq_abs] using (norm_add_le (x - u) u)
  calc
    |x| = |(x - u) + u| := by ring_nf
    _ ≤ |x - u| + |u| := htri
    _ ≤ 1 + |u| := by gcongr
    _ = |u| + 1 := by ring

/-- Local upper bound on the expression under the square root in `F`. -/
private lemma F_sq_upper_local (u x θ : ℝ) (hx : x ∈ Icc (u - 1) (u + 1)) :
    exp (2 * x) * cos θ ^ 2 + exp (-2 * x) * sin θ ^ 2 ≤ exp (2 * (|u| + 1)) := by
  have habs : |x| ≤ |u| + 1 := abs_le_abs_add_one hx
  have h_exp1 : exp (2 * x) ≤ exp (2 * (|u| + 1)) := by
    refine exp_le_exp.mpr ?_
    nlinarith [le_abs_self x, habs]
  have h_exp2 : exp (-2 * x) ≤ exp (2 * (|u| + 1)) := by
    refine exp_le_exp.mpr ?_
    nlinarith [neg_le_abs x, habs]
  have h1 : exp (2 * x) * cos θ ^ 2 ≤ exp (2 * (|u| + 1)) * cos θ ^ 2 := by
    gcongr
  have h2 : exp (-2 * x) * sin θ ^ 2 ≤ exp (2 * (|u| + 1)) * sin θ ^ 2 := by
    gcongr
  calc
    exp (2 * x) * cos θ ^ 2 + exp (-2 * x) * sin θ ^ 2
        ≤ exp (2 * (|u| + 1)) * cos θ ^ 2 + exp (2 * (|u| + 1)) * sin θ ^ 2 :=
          add_le_add h1 h2
    _ = exp (2 * (|u| + 1)) * (cos θ ^ 2 + sin θ ^ 2) := by ring
    _ = exp (2 * (|u| + 1)) := by simp [cos_sq_add_sin_sq]

/-- Local lower bound on the expression under the square root in `F`. -/
private lemma F_sq_lower_local (u x θ : ℝ) (hx : x ∈ Icc (u - 1) (u + 1)) :
    exp (-2 * (|u| + 1)) ≤ exp (2 * x) * cos θ ^ 2 + exp (-2 * x) * sin θ ^ 2 := by
  have habs : |x| ≤ |u| + 1 := abs_le_abs_add_one hx
  have h_exp1 : exp (-2 * (|u| + 1)) ≤ exp (2 * x) := by
    refine exp_le_exp.mpr ?_
    nlinarith [neg_abs_le x, habs]
  have h_exp2 : exp (-2 * (|u| + 1)) ≤ exp (-2 * x) := by
    refine exp_le_exp.mpr ?_
    nlinarith [le_abs_self x, habs]
  have h1 : exp (-2 * (|u| + 1)) * cos θ ^ 2 ≤ exp (2 * x) * cos θ ^ 2 := by
    gcongr
  have h2 : exp (-2 * (|u| + 1)) * sin θ ^ 2 ≤ exp (-2 * x) * sin θ ^ 2 := by
    gcongr
  calc
    exp (-2 * (|u| + 1))
        = exp (-2 * (|u| + 1)) * 1 := by ring
    _ = exp (-2 * (|u| + 1)) * (cos θ ^ 2 + sin θ ^ 2) := by
          simp [cos_sq_add_sin_sq]
    _ = exp (-2 * (|u| + 1)) * cos θ ^ 2 + exp (-2 * (|u| + 1)) * sin θ ^ 2 := by ring
    _ ≤ exp (2 * x) * cos θ ^ 2 + exp (-2 * x) * sin θ ^ 2 := add_le_add h1 h2

/-- Uniform local upper bound on `F` over `x ∈ [u-1, u+1]`. -/
private lemma F_bound_local (u x θ : ℝ) (hx : x ∈ Icc (u - 1) (u + 1)) :
    F x θ ≤ exp (2 * (|u| + 1)) + 1 := by
  have hsq : F x θ ^ 2 = exp (2 * x) * cos θ ^ 2 + exp (-2 * x) * sin θ ^ 2 := by
    unfold F
    exact sq_sqrt (le_of_lt (F_sq_pos x θ))
  have hsq_le : F x θ ^ 2 ≤ exp (2 * (|u| + 1)) := by
    simpa [hsq] using F_sq_upper_local u x θ hx
  have hF_le_sq1 : F x θ ≤ F x θ ^ 2 + 1 := by
    nlinarith [sq_nonneg (F x θ)]
  linarith

/-- Uniform local bound on the first `u`-derivative integrand `F1`. -/
private lemma F1_norm_bound_local (u x θ : ℝ) (hx : x ∈ Icc (u - 1) (u + 1)) :
    ‖F1 x θ‖ ≤ exp (2 * (|u| + 1)) + 1 := by
  rw [norm_eq_abs]
  have hFpos : 0 < F x θ := F_pos x θ
  have hden_pos : 0 < 2 * F x θ := by positivity
  let A : ℝ := 2 * exp (2 * x) * cos θ ^ 2
  let B : ℝ := 2 * exp (-2 * x) * sin θ ^ 2
  have hnum :
      |A - B| ≤ A + B := by
    have hA : 0 ≤ A := by
      unfold A
      positivity
    have hB : 0 ≤ B := by
      unfold B
      positivity
    have hnum' : |A - B| ≤ |A| + |B| := by
      simpa [sub_eq_add_neg] using (abs_sub_le A 0 B)
    simpa [abs_of_nonneg hA, abs_of_nonneg hB] using hnum'
  have hdiv :
      |F1 x θ| ≤
        (A + B) / (2 * F x θ) := by
    unfold F1
    rw [abs_div]
    have hden_nonneg : 0 ≤ 2 * F x θ := le_of_lt hden_pos
    have hden_abs : |2 * F x θ| = 2 * F x θ := abs_of_nonneg hden_nonneg
    simpa [A, B, hden_abs] using (div_le_div_of_nonneg_right hnum hden_nonneg)
  have hsq : F x θ ^ 2 = exp (2 * x) * cos θ ^ 2 + exp (-2 * x) * sin θ ^ 2 := by
    unfold F
    exact sq_sqrt (le_of_lt (F_sq_pos x θ))
  have hratio :
      (A + B) / (2 * F x θ) = F x θ := by
    have hFnz : F x θ ≠ 0 := ne_of_gt hFpos
    have hAB : A + B = 2 * (exp (2 * x) * cos θ ^ 2 + exp (-2 * x) * sin θ ^ 2) := by
      unfold A B
      ring
    calc
      (A + B) / (2 * F x θ)
          = (2 * (exp (2 * x) * cos θ ^ 2 + exp (-2 * x) * sin θ ^ 2)) / (2 * F x θ) := by
              rw [hAB]
      _ = (exp (2 * x) * cos θ ^ 2 + exp (-2 * x) * sin θ ^ 2) / F x θ := by
              field_simp [hFnz]
      _ = F x θ ^ 2 / F x θ := by simp [hsq]
      _ = F x θ := by field_simp [hFnz]
  have hF1_le_F : |F1 x θ| ≤ F x θ := by
    exact hdiv.trans (le_of_eq hratio)
  exact hF1_le_F.trans (F_bound_local u x θ hx)

/-- Uniform local bound on the second `u`-derivative integrand `F2`. -/
private lemma F2_norm_bound_local (u x θ : ℝ) (hx : x ∈ Icc (u - 1) (u + 1)) :
    ‖F2 x θ‖ ≤
      (exp (2 * (|u| + 1)) + 1) + 4 / (Real.sqrt (exp (-2 * (|u| + 1)))) ^ 3 := by
  have hFbound : F x θ ≤ exp (2 * (|u| + 1)) + 1 := F_bound_local u x θ hx
  have hm_pos : 0 < exp (-2 * (|u| + 1)) := by positivity
  have hF_lower :
      Real.sqrt (exp (-2 * (|u| + 1))) ≤ F x θ := by
    unfold F
    exact Real.sqrt_le_sqrt (F_sq_lower_local u x θ hx)
  have hpow :
      (Real.sqrt (exp (-2 * (|u| + 1)))) ^ 3 ≤ F x θ ^ 3 := by
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hF_lower 3
  have hterm_le1 :
      4 * cos θ ^ 2 * sin θ ^ 2 / F x θ ^ 3 ≤
        4 * cos θ ^ 2 * sin θ ^ 2 / (Real.sqrt (exp (-2 * (|u| + 1)))) ^ 3 := by
    have hnum_nonneg : 0 ≤ 4 * cos θ ^ 2 * sin θ ^ 2 := by positivity
    exact div_le_div_of_nonneg_left hnum_nonneg (by positivity) hpow
  have hcos_le1 : cos θ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (sin θ), cos_sq_add_sin_sq θ]
  have hsin_le1 : sin θ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (cos θ), cos_sq_add_sin_sq θ]
  have hprod_le1 : cos θ ^ 2 * sin θ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (cos θ), sq_nonneg (sin θ), hcos_le1, hsin_le1]
  have hterm_le2 :
      4 * cos θ ^ 2 * sin θ ^ 2 / (Real.sqrt (exp (-2 * (|u| + 1)))) ^ 3 ≤
        4 / (Real.sqrt (exp (-2 * (|u| + 1)))) ^ 3 := by
    have hden_pos : 0 < (Real.sqrt (exp (-2 * (|u| + 1)))) ^ 3 := by positivity
    exact div_le_div_of_nonneg_right (by nlinarith) (le_of_lt hden_pos)
  have hterm :
      4 * cos θ ^ 2 * sin θ ^ 2 / F x θ ^ 3 ≤
        4 / (Real.sqrt (exp (-2 * (|u| + 1)))) ^ 3 := hterm_le1.trans hterm_le2
  have hF2_nonneg : 0 ≤ F2 x θ := by
    unfold F2
    have hF : 0 ≤ F x θ := (F_pos x θ).le
    have hterm_nonneg : 0 ≤ 4 * cos θ ^ 2 * sin θ ^ 2 / F x θ ^ 3 := by positivity
    linarith
  rw [norm_eq_abs, abs_of_nonneg hF2_nonneg]
  unfold F2
  linarith

private lemma F_continuous_theta (u : ℝ) : Continuous (fun θ => F u θ) := by
  unfold F
  fun_prop

private lemma F1_continuous_theta (u : ℝ) : Continuous (fun θ => F1 u θ) := by
  have hnum : Continuous (fun θ => 2 * exp (2 * u) * cos θ ^ 2 - 2 * exp (-2 * u) * sin θ ^ 2) := by
    fun_prop
  have hden : Continuous (fun θ => 2 * F u θ) := by
    simpa using (continuous_const.mul (F_continuous_theta u))
  have hden_ne : ∀ θ, (2 * F u θ) ≠ 0 := by
    intro θ
    exact mul_ne_zero two_ne_zero (ne_of_gt (F_pos u θ))
  unfold F1
  exact hnum.div hden hden_ne

private lemma F2_continuous_theta (u : ℝ) : Continuous (fun θ => F2 u θ) := by
  have hF : Continuous (fun θ => F u θ) := F_continuous_theta u
  have hnum : Continuous (fun θ => 4 * cos θ ^ 2 * sin θ ^ 2) := by
    fun_prop
  have hden : Continuous (fun θ => F u θ ^ 3) := hF.pow 3
  have hden_ne : ∀ θ, F u θ ^ 3 ≠ 0 := by
    intro θ
    exact pow_ne_zero 3 (ne_of_gt (F_pos u θ))
  unfold F2
  exact hF.add (hnum.div hden hden_ne)

/-! ## Step 2: The second derivative identity F'' = F + 4AB/F³

Let A = cos²θ, B = sin²θ. Then:
  ∂²F/∂u² = F + 4AB/F³

This is a direct computation. We state it and sorry the calculus. -/

/-- HasDerivAt for exp(c·v), clean of `id`. -/
private lemma hasDerivAt_exp_scaled (c v : ℝ) :
    HasDerivAt (fun w => exp (c * w)) (c * exp (c * v)) v := by
  have h := ((hasDerivAt_id v).const_mul c).exp
  simp only [id, mul_one] at h
  exact h.congr_deriv (by ring)

/-- First derivative of `u ↦ F u θ`. -/
lemma F_hasDerivAt (u θ : ℝ) :
    HasDerivAt (fun w => F w θ) (F1 u θ) u := by
  set A := cos θ ^ 2
  set B := sin θ ^ 2
  have hG : HasDerivAt (fun w => exp (2 * w) * A + exp (-2 * w) * B)
      (2 * exp (2 * u) * A - 2 * exp (-2 * u) * B) u := by
    have h1 := (hasDerivAt_exp_scaled 2 u).mul_const A
    have h2 := (hasDerivAt_exp_scaled (-2) u).mul_const B
    convert h1.add h2 using 1
    ring
  unfold F1 F
  convert HasDerivAt.sqrt hG (ne_of_gt (F_sq_pos u θ)) using 1

/-- Pointwise derivative identity for `u ↦ F u θ`. -/
lemma deriv_F_eq_F1 (θ : ℝ) :
    deriv (fun w => F w θ) = fun u => F1 u θ := by
  funext u
  exact (F_hasDerivAt u θ).deriv

/-- F''(u,θ) = F(u,θ) + 4cos²θ·sin²θ / F(u,θ)³.
    Proof: Write G = F². Then G = Ae^{2u} + Be^{-2u},
    G' = 2Ae^{2u} - 2Be^{-2u}, G'' = 4G.
    F' = G'/(2F), F'' = (G''·2F - G'·2F')/(4F²) = (4G·F - (G')²/F)/(2F²)
    = (4G·F² - (G')²)/(2F³) = 4(G² - (G'/2)²)/F³ ... = F + 4AB/F³.
    The key identity: 4G² - (G')² = 16AB, giving F'' = (4G + 16AB/G)/2/F = ... -/
lemma F_second_deriv (u θ : ℝ) :
    deriv (deriv (fun v => F v θ)) u =
      F u θ + 4 * cos θ ^ 2 * sin θ ^ 2 / F u θ ^ 3 := by
  set A := cos θ ^ 2
  set B := sin θ ^ 2
  have hG_pos : ∀ v, exp (2 * v) * A + exp (-2 * v) * B > 0 := fun v => F_sq_pos v θ
  -- HasDerivAt of G(v) = e^{2v}A + e^{-2v}B at any v
  have hG : ∀ v, HasDerivAt (fun w => exp (2 * w) * A + exp (-2 * w) * B)
      (2 * exp (2 * v) * A - 2 * exp (-2 * v) * B) v := by
    intro v
    have h1 := (hasDerivAt_exp_scaled 2 v).mul_const A
    have h2 := (hasDerivAt_exp_scaled (-2) v).mul_const B
    (convert h1.add h2 using 1; ring)
  -- First derivative: F'(v) = G'(v) / (2F(v)) via sqrt chain rule
  have hF : ∀ v, HasDerivAt (fun w => F w θ)
      ((2 * exp (2 * v) * A - 2 * exp (-2 * v) * B) / (2 * F v θ)) v := by
    intro v; unfold F; exact HasDerivAt.sqrt (hG v) (ne_of_gt (hG_pos v))
  -- Extract deriv F pointwise
  have hd : deriv (fun w => F w θ) =
      fun v => (2 * exp (2 * v) * A - 2 * exp (-2 * v) * B) / (2 * F v θ) :=
    funext fun v => (hF v).deriv
  -- HasDerivAt of G'(v) = 2e^{2v}A - 2e^{-2v}B (gives G'' = 4G)
  have hN : HasDerivAt (fun v => 2 * exp (2 * v) * A - 2 * exp (-2 * v) * B)
      (4 * exp (2 * u) * A + 4 * exp (-2 * u) * B) u := by
    have h1 := ((hasDerivAt_exp_scaled 2 u).const_mul 2).mul_const A
    have h2 := ((hasDerivAt_exp_scaled (-2) u).const_mul 2).mul_const B
    (convert h1.sub h2 using 1; ring)
  -- HasDerivAt of 2F (denominator)
  have hD := (hF u).const_mul 2
  -- Quotient rule: HasDerivAt (G'/(2F)) ... u
  have hFu_pos : 0 < F u θ := F_pos u θ
  have h2Fu_ne : (2 * F u θ) ≠ 0 := by linarith
  have hQ := hN.div hD h2Fu_ne
  -- Bridge the syntactic mismatch: hQ.deriv is for Pi.div, goal has pointwise div
  have hQderiv :
      deriv (fun v => (2 * exp (2 * v) * A - 2 * exp (-2 * v) * B) / (2 * F v θ)) u =
        (((4 * exp (2 * u) * A + 4 * exp (-2 * u) * B) * (2 * F u θ) -
            (2 * exp (2 * u) * A - 2 * exp (-2 * u) * B) *
              (2 * ((2 * exp (2 * u) * A - 2 * exp (-2 * u) * B) / (2 * F u θ)))) /
          (2 * F u θ) ^ 2) := by
    have : (fun v => (2 * exp (2 * v) * A - 2 * exp (-2 * v) * B) / (2 * F v θ)) =
        ((fun v => 2 * exp (2 * v) * A - 2 * exp (-2 * v) * B) /
         (fun v => 2 * F v θ)) := by ext; rfl
    rw [this]; exact hQ.deriv
  rw [hd, hQderiv]
  -- Algebraic identity: quotient rule result = F + 4AB/F³
  have hFp : F u θ > 0 := F_pos u θ
  have hFn : F u θ ≠ 0 := ne_of_gt hFp
  have hFsq : F u θ ^ 2 = exp (2 * u) * A + exp (-2 * u) * B := by
    unfold F; exact sq_sqrt (le_of_lt (hG_pos u))
  have hef : exp (2 * u) * exp (-2 * u) = 1 := by rw [← exp_add]; simp
  -- Bridge exp(-2*u) ↔ exp(-(2*u)) for field_simp normalization
  have h_neg : exp (-2 * u) = exp (-(2 * u)) := by congr 1; ring
  rw [h_neg] at hFsq  -- hFsq now uses -(2*u) form
  have hef2 : exp (2 * u) * exp (-(2 * u)) = 1 := by rw [← h_neg]; exact hef
  -- Key identity: 4G² - G'² = 16AB (the algebraic core)
  have hkey_raw : (exp (2 * u) * A + exp (-(2 * u)) * B) ^ 2 * 4 -
      (2 * exp (2 * u) * A - 2 * exp (-(2 * u)) * B) ^ 2 =
      16 * (exp (2 * u) * exp (-(2 * u))) * A * B := by ring
  have hkey : (exp (2 * u) * A + exp (-(2 * u)) * B) ^ 2 * 4 -
      (2 * exp (2 * u) * A - 2 * exp (-(2 * u)) * B) ^ 2 = 16 * A * B := by
    rw [hkey_raw, hef2]; ring
  -- Clear denominators and verify polynomial identity
  field_simp
  nlinarith [hFsq, hkey, hef2, sq_nonneg (F u θ), sq_nonneg A, sq_nonneg B,
    sq_nonneg (exp (2 * u) * A - exp (-(2 * u)) * B)]

/-- F''(u,θ) > 0 for all u, θ.
    Immediate from F > 0 and 4AB/F³ >= 0. -/
lemma F_second_deriv_pos (u θ : ℝ) : F u θ + 4 * cos θ ^ 2 * sin θ ^ 2 / F u θ ^ 3 > 0 := by
  have hF := F_pos u θ
  have hF3 : F u θ ^ 3 > 0 := by positivity
  have hAB : 4 * cos θ ^ 2 * sin θ ^ 2 / F u θ ^ 3 ≥ 0 := by positivity
  linarith

private lemma I_hasDerivAt (u : ℝ) :
    HasDerivAt I (∫ θ in (0)..(π / 2), F1 u θ) u := by
  unfold I
  let s : Set ℝ := Icc (u - 1) (u + 1)
  let bound : ℝ → ℝ := fun _ => exp (2 * (|u| + 1)) + 1
  have hleft : u - 1 < u := by nlinarith
  have hright : u < u + 1 := by nlinarith
  have hs : s ∈ nhds u := by
    dsimp [s]
    exact Icc_mem_nhds hleft hright
  have hF_meas :
      ∀ᶠ x in nhds u, AEStronglyMeasurable (F x) (volume.restrict (Ι (0 : ℝ) (π / 2))) := by
    exact Filter.Eventually.of_forall (fun x =>
      (F_continuous_theta x).stronglyMeasurable.aestronglyMeasurable)
  have hF_int : IntervalIntegrable (F u) volume (0 : ℝ) (π / 2) :=
    (F_continuous_theta u).intervalIntegrable _ _
  have hF'_meas : AEStronglyMeasurable (F1 u) (volume.restrict (Ι (0 : ℝ) (π / 2))) :=
    (F1_continuous_theta u).stronglyMeasurable.aestronglyMeasurable
  have h_bound :
      ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (π / 2) → ∀ x ∈ s, ‖F1 x t‖ ≤ bound t := by
    exact Filter.Eventually.of_forall (fun t _ x hx => by
      simpa [bound] using F1_norm_bound_local u x t hx)
  have bound_integrable : IntervalIntegrable bound volume (0 : ℝ) (π / 2) := by
    simp [bound]
  have h_diff :
      ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (π / 2) → ∀ x ∈ s,
        HasDerivAt (fun y => F y t) (F1 x t) x := by
    exact Filter.Eventually.of_forall (fun t _ x _ => by
      simpa using F_hasDerivAt x t)
  exact
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (F' := F1) (x₀ := u) (a := 0) (b := π / 2) (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2

private lemma I1_hasDerivAt (u : ℝ) :
    HasDerivAt (fun x => ∫ θ in (0)..(π / 2), F1 x θ)
      (∫ θ in (0)..(π / 2), F2 u θ) u := by
  let s : Set ℝ := Icc (u - 1) (u + 1)
  let bound : ℝ → ℝ :=
    fun _ => (exp (2 * (|u| + 1)) + 1) + 4 / (Real.sqrt (exp (-2 * (|u| + 1)))) ^ 3
  have hleft : u - 1 < u := by nlinarith
  have hright : u < u + 1 := by nlinarith
  have hs : s ∈ nhds u := by
    dsimp [s]
    exact Icc_mem_nhds hleft hright
  have hF_meas :
      ∀ᶠ x in nhds u, AEStronglyMeasurable (F1 x) (volume.restrict (Ι (0 : ℝ) (π / 2))) := by
    exact Filter.Eventually.of_forall (fun x =>
      (F1_continuous_theta x).stronglyMeasurable.aestronglyMeasurable)
  have hF_int : IntervalIntegrable (F1 u) volume (0 : ℝ) (π / 2) :=
    (F1_continuous_theta u).intervalIntegrable _ _
  have hF'_meas : AEStronglyMeasurable (F2 u) (volume.restrict (Ι (0 : ℝ) (π / 2))) :=
    (F2_continuous_theta u).stronglyMeasurable.aestronglyMeasurable
  have h_bound :
      ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (π / 2) → ∀ x ∈ s, ‖F2 x t‖ ≤ bound t := by
    exact Filter.Eventually.of_forall (fun t _ x hx => by
      simpa [bound] using F2_norm_bound_local u x t hx)
  have bound_integrable : IntervalIntegrable bound volume (0 : ℝ) (π / 2) := by
    simp [bound]
  have h_diff :
      ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (π / 2) → ∀ x ∈ s,
        HasDerivAt (fun y => F1 y t) (F2 x t) x := by
    refine Filter.Eventually.of_forall ?_
    intro t _ x _
    have hderiv_ne : deriv (fun z => deriv (fun v => F v t) z) x ≠ 0 := by
      rw [F_second_deriv x t]
      exact (F_second_deriv_pos x t).ne'
    have hdiff : DifferentiableAt ℝ (fun z => deriv (fun v => F v t) z) x :=
      differentiableAt_of_deriv_ne_zero hderiv_ne
    have hhas0 :
        HasDerivAt (fun z => deriv (fun v => F v t) z)
          (deriv (fun z => deriv (fun v => F v t) z) x) x := hdiff.hasDerivAt
    have hhas :
        HasDerivAt (fun z => deriv (fun v => F v t) z) (F2 x t) x := by
      simpa [F_second_deriv x t] using hhas0
    simpa [deriv_F_eq_F1 t] using hhas
  exact
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F1) (F' := F2) (x₀ := u) (a := 0) (b := π / 2) (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2

/-! ## Step 3: Strict convexity of I(u)

I''(u) = ∫₀^{π/2} F''(u,θ) dθ > 0

because the integrand F'' is continuous and strictly positive on [0, π/2].
Differentiation under the integral sign is justified by dominated convergence
(the integrand and its derivatives are bounded on compact sets). -/

/-- I is twice differentiable and I''(u) > 0 for all u.
    This uses: (a) differentiation under the integral sign (Leibniz),
    (b) the integral of a positive continuous function on [0,π/2] is positive. -/
theorem I_strictly_convex (u : ℝ) : deriv (deriv I) u > 0 := by
  have hDerivI : deriv I = fun x => ∫ θ in (0)..(π / 2), F1 x θ := by
    funext x
    exact (I_hasDerivAt x).deriv
  have h2 : deriv (deriv I) u = ∫ θ in (0)..(π / 2), F2 u θ := by
    rw [hDerivI]
    exact (I1_hasDerivAt u).deriv
  rw [h2]
  apply intervalIntegral.intervalIntegral_pos_of_pos
  · exact (F2_continuous_theta u).intervalIntegrable 0 (π / 2)
  · intro θ
    exact F_second_deriv_pos u θ
  · positivity

/-! ## Step 4: Symmetry I(-u) = I(u), hence I'(0) = 0

The substitution θ ↦ π/2 - θ swaps cos²θ ↔ sin²θ, which is the same
as negating u in the integrand. So I(-u) = I(u). Differentiating: I'(0) = 0. -/

/-- F(-u, π/2 - θ) = F(u, θ).
    Proof: cos(π/2-θ) = sinθ, sin(π/2-θ) = cosθ, so the roles of A,B swap,
    which is the same as negating u (since e^{2(-u)} swaps with e^{-2(-u)}). -/
lemma F_symmetry (u θ : ℝ) : F (-u) (π / 2 - θ) = F u θ := by
  unfold F
  congr 1
  rw [cos_pi_div_two_sub, sin_pi_div_two_sub]
  ring_nf

/-- I(-u) = I(u). The substitution θ ↦ π/2 - θ is measure-preserving on [0, π/2]. -/
theorem I_even (u : ℝ) : I (-u) = I u := by
  unfold I
  -- Step 1: Replace F u θ by F (-u) (π/2 - θ) using F_symmetry
  conv_rhs => arg 1; ext θ; rw [← F_symmetry u θ]
  -- Step 2: Apply the substitution θ ↦ π/2 - θ
  rw [intervalIntegral.integral_comp_sub_left]
  -- Step 3: Simplify π/2 - π/2 = 0 and π/2 - 0 = π/2
  simp

/-- I'(0) = 0, from the symmetry I(-u) = I(u).
    If f(-x) = f(x) and f is differentiable at 0, then f'(0) = 0. -/
theorem I_deriv_zero : deriv I 0 = 0 := by
  -- From I_even: ∀ u, I(-u) = I(u), so (fun u => I(-u)) = I pointwise.
  -- By deriv_comp_neg: deriv (fun u => I(-u)) 0 = -deriv I (-0) = -deriv I 0
  -- Since (fun u => I(-u)) and I agree everywhere, their derivatives agree:
  --   deriv I 0 = -deriv I 0, hence deriv I 0 = 0.
  have h1 : deriv (fun u => I (-u)) 0 = deriv I 0 := by
    congr 1; ext u; exact I_even u
  have h2 : deriv (fun u => I (-u)) 0 = -deriv I 0 := by
    rw [deriv_comp_neg]; simp
  linarith

/-! ## Step 5: The Main Theorem

Strict convexity (I'' > 0) + I'(0) = 0 => I'(u) > 0 for u > 0.

This is the mean value theorem: I'(u) - I'(0) = I''(c) · u for some c ∈ (0,u).
Since I''(c) > 0 and u > 0, we get I'(u) > 0. -/

/-- **Theorem 6.1 (Strict monotonicity at fixed product).**
    For u > 0, I'(u) > 0, hence P_N(u) = 4√N · I(u) is strictly increasing.

    Proof: By the mean value theorem, I'(u) = I'(0) + I''(c)·u for some c ∈ (0,u).
    Since I'(0) = 0 (symmetry) and I''(c) > 0 (strict convexity) and u > 0,
    we conclude I'(u) > 0. -/
theorem I_deriv_pos {u : ℝ} (hu : u > 0) : deriv I u > 0 := by
  -- deriv (deriv I) is positive everywhere (I_strictly_convex),
  -- so deriv I is strictly monotone.
  have hI'_strictMono : StrictMono (deriv I) :=
    strictMono_of_deriv_pos (fun x => I_strictly_convex x)
  -- Since deriv I is strictly monotone and u > 0, deriv I u > deriv I 0.
  have h := hI'_strictMono hu
  -- And deriv I 0 = 0 by I_deriv_zero.
  rw [I_deriv_zero] at h
  exact h

/-- The uncurried integrand is continuous (F is jointly continuous in u and θ). -/
lemma F_uncurry_continuous : Continuous (Function.uncurry F) := by
  unfold F Function.uncurry
  simp only
  fun_prop

/-- I is continuous (continuous parametric integral of continuous integrand). -/
lemma I_continuous : Continuous I := by
  unfold I
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    F_uncurry_continuous 0 (π / 2)

/-- **Corollary: I is strictly monotone on [0, ∞).**
    Since I'(u) > 0 for u > 0, I is strictly increasing on the nonneg reals. -/
theorem I_strictMono_nonneg : StrictMonoOn I (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact I_continuous.continuousOn
  · intro x hx
    rw [interior_Ici] at hx
    exact I_deriv_pos hx

/-- **Corollary: The perimeter function P_N is strictly monotone on [0, ∞).**
    Since P_N(u) = 4√N · I(u) and I is strictly increasing on [0, ∞),
    P_N is strictly increasing on [0, ∞). -/
theorem perimeter_strictly_increasing {N : ℝ} (hN : N > 0) :
    StrictMonoOn (fun u => 4 * Real.sqrt N * I u) (Set.Ici 0) := by
  have hc : 4 * Real.sqrt N > 0 := by positivity
  intro x hx y hy hxy
  exact mul_lt_mul_of_pos_left (I_strictMono_nonneg hx hy hxy) hc

end
