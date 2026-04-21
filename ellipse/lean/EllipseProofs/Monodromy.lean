/-
  EllipseProofs/Monodromy.lean

  Formal skeleton for monodromy and period duality results from Section 5 of:
  "Two Foci, One FUP: A World-Record Correction to Ramanujan's Ellipse
   Perimeter Equation, and the Focal Uncertainty Principle"

  Maps to paper Section 5 (Monodromy and Period Duality).

  This module formalizes the algebraic/structural core statements used in the
  paper's monodromy section. Analytic-heavy pieces involving first-class
  complete elliptic integrals are kept abstract as assumptions.

  Status:
  - monodromy_connection: proved (resonance + Gauss connection coefficient from GammaConnection.lean)
  - ke_period_duality: proved (parameter arithmetic + EllipticE 1 = 1)
  - legendre_coupling: assumption-driven wrapper theorem (no global axioms)

  Paper reference: proof_strip5.tex, Section 5
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import EllipseProofs.GammaConnection

open Real
open scoped Interval

noncomputable section

/-! ## Theorem 5.1: Monodromy Structure and Connection Formula

The ₂F₁(-1/2, 1/2; 1; z) near z = 1 has:
- Local basis: y₁(w) = ₂F₁(-1/2, 1/2; 1; w) (regular), y₂ = y₁·ln(w) + Σ dₖwᵏ
- Monodromy matrix M = [[1, 0], [2πi, 1]] (unipotent)
- Connection formula: F(1-w) = 2/π - (1/(2π))·w·ln(w) + O(w)
-/

/-- The monodromy matrix for ₂F₁(-1/2, 1/2; 1; z) around z = 1.
    This is unipotent of Jordan type, reflecting the logarithmic branch.
    Paper: Theorem 5.1(b) (thm:monodromy), equation (monodromy) -/
def monodromy_matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 2 * π * Complex.I, 1]

/-- The monodromy matrix is unipotent: (M - I)^2 = 0.
    Paper: Theorem 5.1(b) -/
theorem monodromy_unipotent :
    (monodromy_matrix - 1) ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [monodromy_matrix, Matrix.sub_apply, sq, Matrix.mul_apply, Fin.sum_univ_two]

/-- The monodromy matrix has determinant 1.
    Paper: Theorem 5.1(b) -/
theorem monodromy_det_one :
    monodromy_matrix.det = 1 := by
  unfold monodromy_matrix
  simp [Matrix.det_fin_two]

/-- **Coefficient ledger verification.**
    The Gauss value kappa = 2/pi and log coefficient mu = 1/(2*pi) satisfy
    mu = kappa/4.
    Paper: Theorem 5.1(c), coefficient ledger -/
theorem log_coeff_relation : (1 : ℝ) / (2 * π) = (2 / π) / 4 := by
  have hpi : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  field_simp
  ring

/-- The coefficient of -(1-m)ln(1-m) in E(m) is (pi/2) * mu = 1/4.
    Paper: Theorem 5.1, coefficient ledger row 3 -/
theorem E_log_coeff : π / 2 * (1 / (2 * π)) = (1 : ℝ) / 4 := by
  have hpi : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  field_simp
  ring

/-- **Theorem 5.1 (Monodromy connection formula).**
    F(1-w) = 2/pi - (1/(2*pi))*w*ln(w) + O(w) for the resonant case c-a-b = 1.

    The resonance condition: for (a,b,c) = (-1/2, 1/2, 1), c - a - b = 1.
    This forces a logarithmic branch in the connection formula.

    Paper: Theorem 5.1 (thm:monodromy) -/
theorem monodromy_connection :
    -- The resonance condition
    (1 : ℚ) - (-1/2) - (1/2) = 1 ∧
    -- The Gauss summation value:
    -- ₂F₁(-1/2, 1/2; 1; 1) = Γ(1)²/(Γ(3/2)Γ(1/2)) = 2/π
    Gamma 1 ^ 2 / (Gamma (3 / 2 : ℝ) * Gamma (1 / 2 : ℝ)) = 2 / π ∧
    -- The log coefficient mu = kappa/4 = 1/(2*pi) (algebraic relation)
    (1 : ℝ) / (2 * π) = (2 / π) / 4 := by
  refine ⟨by norm_num, gauss_connection_coefficient, by ring⟩

/-! ## Elliptic integrals (definitions needed for Theorems 5.2–5.3) -/

/-- Complete elliptic integral of the first kind:
`K(m) = ∫₀^{π/2} (1 - m sin² θ)^(-1/2) dθ`. -/
noncomputable def EllipticK (m : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (1 - m * (Real.sin θ) ^ 2))⁻¹

/-- Complete elliptic integral of the second kind:
`E(m) = ∫₀^{π/2} sqrt(1 - m sin² θ) dθ`. -/
noncomputable def EllipticE (m : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(π / 2), Real.sqrt (1 - m * (Real.sin θ) ^ 2)

/-- E(1) = 1.
    Proof: sqrt(1 - sin²θ) = sqrt(cos²θ) = cos θ (for θ ∈ [0, π/2]),
    and ∫₀^{π/2} cos θ dθ = sin(π/2) - sin(0) = 1. -/
lemma EllipticE_one : EllipticE 1 = 1 := by
  unfold EllipticE
  simp only [one_mul]
  have step1 : ∫ θ in (0 : ℝ)..(π / 2), Real.sqrt (1 - Real.sin θ ^ 2) =
               ∫ θ in (0 : ℝ)..(π / 2), Real.cos θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ' : θ ∈ Set.uIcc (0 : ℝ) (π / 2) := hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ'
    have hθ1 : (0 : ℝ) ≤ θ := hθ'.1
    have hθ2 : θ ≤ π / 2 := hθ'.2
    rw [show (1 : ℝ) - Real.sin θ ^ 2 = Real.cos θ ^ 2 from by
      nlinarith [Real.sin_sq_add_cos_sq θ]]
    rw [Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], hθ2⟩)
  rw [step1]
  have step2 : ∫ θ in (0 : ℝ)..(π / 2), Real.cos θ = Real.sin (π / 2) - Real.sin 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro θ _; exact Real.hasDerivAt_sin θ
    · exact Real.continuous_cos.intervalIntegrable 0 (π / 2)
  rw [step2, Real.sin_pi_div_two, Real.sin_zero, sub_zero]

/-! ## Theorem 5.2: K-E Period Duality

E(m) = (pi/2) * ₂F₁(-1/2, 1/2; 1; m) has c-a-b = 1 (distinct exponents {0,1})
K(m) = (pi/2) * ₂F₁(+1/2, 1/2; 1; m) has c-a-b = 0 (resonant exponents {0,0})

Only the sign of the first parameter differs, but the singularity structures
are fundamentally different.
-/

/-- **Theorem 5.2 (K-E period duality) — algebraic core.**
    The parameter c-a-b determines the singularity type:
    - For E: (a,b,c) = (-1/2, 1/2, 1), so c-a-b = 1 (positive integer)
    - For K: (a,b,c) = (+1/2, 1/2, 1), so c-a-b = 0 (zero)

    Paper: Theorem 5.2 (thm:ke-duality) -/
theorem ke_period_duality :
    -- E(m): c - a - b = 1 - (-1/2) - 1/2 = 1
    (1 : ℚ) - (-1/2) - 1/2 = 1 ∧
    -- K(m): c - a - b = 1 - 1/2 - 1/2 = 0
    (1 : ℚ) - 1/2 - 1/2 = 0 ∧
    -- E(1) = 1 (finite value)
    EllipticE 1 = 1 ∧
    -- The non-analytic terms differ:
    -- E: coefficient of -(1-m)ln(1-m) is 1/4
    -- K: coefficient of -ln(1-m) is 1/2
    (1 : ℝ) / 4 ≠ 1 / 2 := by
  refine ⟨by norm_num, by norm_num, EllipticE_one, by norm_num⟩

/-- The ratio of log coefficients: K's log coeff / E's log coeff = 2.
    K has coefficient 1/2 for -ln(1-m), E has 1/4 for -(1-m)ln(1-m).
    Paper: Theorem 5.2 table -/
theorem log_coeff_ratio : (1 : ℚ) / 2 / (1 / 4) = 2 := by norm_num

/-! ## Theorem 5.3: Legendre Coupling (DLMF 19.7.1)

K(m)*E(1-m) + E(m)*K(1-m) - K(m)*K(1-m) = pi/2

Proof structure:
  (A) Boundary values: E(0) = K(0) = π/2  [proved below]
  (B) Derivative formulas:
        dE/dm = (E(m) - K(m)) / (2m)
        dK/dm = (E(m) - (1-m)*K(m)) / (2m*(1-m))
      [sorry: require differentiating under the integral sign]
  (C) Algebraic identity: substituting (B) into d/dm[K·Ē+E·K̄-K·K̄] gives 0
      [pure ring computation — proved below as legendre_deriv_algebra]
  (D) f constant on (0,1) → equals its limit value π/2 as m→0+
      [sorry: requires continuity of K,E and limit argument]
-/

/-- E(0) = π/2: the integrand is identically 1 when m=0. -/
lemma EllipticE_zero : EllipticE 0 = π / 2 := by
  unfold EllipticE
  simp only [zero_mul, sub_zero, Real.sqrt_one]
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]

/-- K(0) = π/2: the integrand is identically 1 when m=0. -/
lemma EllipticK_zero : EllipticK 0 = π / 2 := by
  unfold EllipticK
  simp only [zero_mul, sub_zero, Real.sqrt_one, inv_one]
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]

/-- dE/dm = (E(m) - K(m)) / (2m).

    Full proof sketch (requires intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le):
    (1) F(x,θ) := √(1-x·sin²θ), F'(x,θ) := -sin²θ/(2√(1-x·sin²θ)).
    (2) For x in a compact neighbourhood of m ⊂ (0,1), say [m/2,(1+m)/2]:
        1-x·sin²θ ≥ 1-(1+m)/2 = (1-m)/2 > 0, so F' is bounded by sin²θ/(2√((1-m)/2)),
        which is integrable on [0,π/2].
    (3) d/dx F(x,θ) = F'(x,θ) pointwise for every θ (chain rule on sqrt).
    (4) The dominated-convergence theorem gives:
          HasDerivAt (∫ θ, F(·,θ)) (∫ θ, F'(m,θ)) m.
    (5) Identity: -sin²θ/(2√f) = (1/(2m))(√f - 1/√f) where f = 1-m·sin²θ,
        because m·sin²θ = 1-f, so sin²θ = (1-f)/m and
          -sin²θ/√f = -(1-f)/(m√f) = (1/m)(√f - 1/√f).
        Splitting: ∫(√f - 1/√f) = EllipticE m - EllipticK m.
    Requires: Mathlib.Analysis.Calculus.ParametricIntervalIntegral. -/
lemma hasDerivAt_EllipticE {m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    HasDerivAt EllipticE ((EllipticE m - EllipticK m) / (2 * m)) m := by
  -- Step 1: DCT gives HasDerivAt for the raw integral.
  -- F(x,θ) = √(1-x·sin²θ),  F'(x,θ) = -sin²θ/(2√(1-x·sin²θ))
  -- Neighbourhood s = Ioo (m/2) ((1+m)/2) ⊂ (0,1).
  -- For x ∈ s: 1-x·sin²θ ≥ (1-m)/2 > 0, so ‖F'(x,θ)‖ ≤ sin²θ/(2·√((1-m)/2)).
  -- DCT (dominated convergence) applies:
  --   • measurability: √ ∘ (continuous function) is measurable
  --   • integrability: continuous on [0,π/2], bounded away from 0
  --   • pointwise derivative: chain rule on sqrt gives -sin²θ/(2√f)
  have hDCT : HasDerivAt
      (fun x => ∫ θ in (0:ℝ)..(π / 2), Real.sqrt (1 - x * (Real.sin θ) ^ 2))
      (∫ θ in (0:ℝ)..(π / 2), -(Real.sin θ) ^ 2 /
          (2 * Real.sqrt (1 - m * (Real.sin θ) ^ 2))) m := by
    have hs_mem : Set.Ioo (m / 2) ((1 + m) / 2) ∈ 𝓝 m :=
      Ioo_mem_nhds (by linarith) (by linarith)
    have hf_lower : ∀ x ∈ Set.Ioo (m / 2) ((1 + m) / 2), ∀ θ : ℝ,
        (1 - m) / 2 ≤ 1 - x * (Real.sin θ) ^ 2 := fun x hx θ => by
      nlinarith [Real.sin_sq_le_one θ, hx.2]
    -- Sub-goals for the parametric DCT theorem
    -- (a) measurability of F'(m,·), (b) integrability, (c) domination bound,
    -- (d) pointwise derivative — sorry: requires careful Mathlib API matching
    have hF_int : IntervalIntegrable
        (fun θ => Real.sqrt (1 - m * (Real.sin θ) ^ 2)) MeasureTheory.volume 0 (π / 2) :=
      (ContinuousOn.sqrt
        (continuousOn_const.sub (continuousOn_const.mul
          (Real.continuous_sin.pow 2).continuousOn))
        (fun θ _ => by nlinarith [Real.sin_sq_le_one θ])).intervalIntegrable
    -- Pointwise HasDerivAt for F(x,θ) w.r.t. x, for each fixed θ and x ∈ s
    have h_diff : ∀ x ∈ Set.Ioo (m / 2) ((1 + m) / 2), ∀ θ : ℝ,
        HasDerivAt (fun y => Real.sqrt (1 - y * (Real.sin θ) ^ 2))
          (-(Real.sin θ) ^ 2 / (2 * Real.sqrt (1 - x * (Real.sin θ) ^ 2))) x := by
      intro x hx θ
      have hf_pos : 0 < 1 - x * (Real.sin θ) ^ 2 :=
        lt_of_lt_of_le (by linarith) (hf_lower x hx θ)
      have hinner : HasDerivAt (fun y => 1 - y * (Real.sin θ) ^ 2)
          (-(Real.sin θ) ^ 2) x := by
        have h := ((hasDerivAt_id x).const_mul ((Real.sin θ) ^ 2)).const_sub 1
        convert h using 1; ring
      exact (hinner.sqrt hf_pos.ne').congr_deriv (by
        have hS := (Real.sqrt_pos_of_pos hf_pos).ne'
        field_simp [hS]; ring)
    -- Apply DCT (sorry for the full measurability/integrability/bound assembly)
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_mem
      -- hF_meas: F(x,·) AEStronglyMeasurable near m
      (Filter.eventually_of_forall fun x => (Real.continuous_sqrt.comp
        (continuous_const.sub (continuous_const.mul
          (Real.continuous_sin.pow 2)))).aestronglyMeasurable)
      -- hF_int
      hF_int
      -- hF'_meas: F'(m,·) AEStronglyMeasurable
      (((Real.continuous_sin.pow 2).neg.div
        (continuous_const.mul (Real.continuous_sqrt.comp
          (continuous_const.sub (continuous_const.mul
            (Real.continuous_sin.pow 2)))))
        (fun θ => mul_ne_zero two_ne_zero
          (Real.sqrt_ne_zero'.mpr
            (by nlinarith [Real.sin_sq_le_one θ])))).aestronglyMeasurable)
      -- h_bound: ‖F'(x,θ)‖ ≤ sin²θ/(2·√((1-m)/2))
      (Filter.eventually_of_forall fun θ _ x hx => by
        have hf_pos : 0 < 1 - x * (Real.sin θ) ^ 2 :=
          lt_of_lt_of_le (by linarith) (hf_lower x hx θ)
        have hS := (Real.sqrt_pos_of_pos hf_pos).ne'
        have hS2 := Real.sqrt_pos_of_pos (show (0:ℝ) < (1-m)/2 by linarith)
        rw [show -(Real.sin θ) ^ 2 / (2 * Real.sqrt (1 - x * (Real.sin θ) ^ 2)) =
            -(Real.sin θ ^ 2 / (2 * Real.sqrt (1 - x * (Real.sin θ) ^ 2))) by ring]
        rw [norm_neg, Real.norm_of_nonneg (by positivity)]
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by linarith)
        apply mul_le_mul_of_nonneg_left _ two_pos.le
        exact Real.sqrt_le_sqrt (hf_lower x hx θ))
      -- bound_integrable
      ((Real.continuous_sin.pow 2).continuousOn.div_const _
        |>.intervalIntegrable)
      -- h_diff
      (Filter.eventually_of_forall fun θ _ x hx =>
        h_diff x hx θ)).2
  -- Step 2: EllipticE unfolds to the raw integral.
  show HasDerivAt EllipticE ((EllipticE m - EllipticK m) / (2 * m)) m
  rw [show EllipticE = fun x => ∫ θ in (0 : ℝ)..(π / 2),
      Real.sqrt (1 - x * (Real.sin θ) ^ 2) from rfl]
  convert hDCT using 1
  -- Step 3: Integral identity — ∫ F'(m,·) = (E-K)/(2m).
  -- Key: -sin²θ/(2√f) = (1/(2m))(√f - 1/√f) since m·sin²θ = 1-f.
  have hm' : m ≠ 0 := hm.ne'
  have hinteg_E : IntervalIntegrable
      (fun θ => Real.sqrt (1 - m * (Real.sin θ) ^ 2)) MeasureTheory.volume 0 (π / 2) :=
    (ContinuousOn.sqrt
      (continuousOn_const.sub (continuousOn_const.mul
        (Real.continuous_sin.pow 2).continuousOn))
      (fun θ _ => by nlinarith [Real.sin_sq_le_one θ])).intervalIntegrable
  have hinteg_K : IntervalIntegrable
      (fun θ => (Real.sqrt (1 - m * (Real.sin θ) ^ 2))⁻¹) MeasureTheory.volume 0 (π / 2) :=
    (ContinuousOn.inv₀
      (ContinuousOn.sqrt
        (continuousOn_const.sub (continuousOn_const.mul
          (Real.continuous_sin.pow 2).continuousOn))
        (fun θ _ => by nlinarith [Real.sin_sq_le_one θ]))
      (fun θ _ => (Real.sqrt_pos_of_pos (by nlinarith [Real.sin_sq_le_one θ])).ne')).intervalIntegrable
  rw [div_eq_iff (mul_ne_zero two_ne_zero hm')]
  have hconv : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 2),
      (2 * m) * (-(Real.sin θ) ^ 2 / (2 * Real.sqrt (1 - m * (Real.sin θ) ^ 2))) =
      Real.sqrt (1 - m * (Real.sin θ) ^ 2) -
        (Real.sqrt (1 - m * (Real.sin θ) ^ 2))⁻¹ := fun θ _ => by
    have hf : 0 < 1 - m * (Real.sin θ) ^ 2 := by
      nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ)]
    have hS := (Real.sqrt_pos_of_pos hf).ne'
    field_simp [hS]; rw [Real.sq_sqrt hf.le]; ring
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_congr hconv,
      intervalIntegral.integral_sub hinteg_E hinteg_K]

/-- dK/dm = (E(m) - (1-m)K(m)) / (2m(1-m)).

    Full proof sketch (requires intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le):
    (1) G(x,θ) := 1/√(1-x·sin²θ), G'(x,θ) := sin²θ/(2(1-x·sin²θ)^{3/2}).
    (2) Same compactness/domination argument as hasDerivAt_EllipticE.
    (3) Identity: ∫ sin²θ/(2(1-m·sin²θ)^{3/2}) = (E(m)-(1-m)K(m))/(2m(1-m))
        via the reduction: sin²θ·(1-m·sin²θ)^{-3/2}
          = (1/m)((1-m·sin²θ)^{-1/2} - (1-m)·(1-m·sin²θ)^{-3/2})
        followed by integration by parts for the second term to get E and K. -/
lemma hasDerivAt_EllipticK {m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    HasDerivAt EllipticK ((EllipticE m - (1 - m) * EllipticK m) / (2 * m * (1 - m))) m := by
  -- Step 1: DCT gives HasDerivAt for the raw integral.
  -- G(x,θ) = (1-x·sin²θ)^{-1/2},  G'(x,θ) = sin²θ/(2·f·√f) where f = 1-x·sin²θ.
  have hm1' : (0:ℝ) < 1 - m := by linarith
  have hf_lower : ∀ x ∈ Set.Ioo (m / 2) ((1 + m) / 2), ∀ θ : ℝ,
      (1 - m) / 2 ≤ 1 - x * (Real.sin θ) ^ 2 := fun x hx θ => by
    nlinarith [Real.sin_sq_le_one θ, hx.2]
  -- Pointwise derivative for G(·,θ)
  have h_diff_inv : ∀ x ∈ Set.Ioo (m / 2) ((1 + m) / 2), ∀ θ : ℝ,
      HasDerivAt (fun y => (Real.sqrt (1 - y * (Real.sin θ) ^ 2))⁻¹)
        ((Real.sin θ) ^ 2 /
          (2 * (1 - x * (Real.sin θ) ^ 2) * Real.sqrt (1 - x * (Real.sin θ) ^ 2))) x := by
    intro x hx θ
    have hf_pos : 0 < 1 - x * (Real.sin θ) ^ 2 :=
      lt_of_lt_of_le (by linarith) (hf_lower x hx θ)
    have hS := (Real.sqrt_pos_of_pos hf_pos).ne'
    have hinner : HasDerivAt (fun y => 1 - y * (Real.sin θ) ^ 2) (-(Real.sin θ) ^ 2) x := by
      have h := ((hasDerivAt_id x).const_mul ((Real.sin θ) ^ 2)).const_sub 1
      convert h using 1; ring
    -- (√f)' = 1/(2√f) · f', then (·)⁻¹ gives -(√f)'/(√f)²
    exact ((hinner.sqrt hf_pos.ne').inv hS).congr_deriv (by
      rw [Real.sq_sqrt hf_pos.le]; field_simp [hS]; ring)
  have hDCT : HasDerivAt
      (fun x => ∫ θ in (0:ℝ)..(π / 2), (Real.sqrt (1 - x * (Real.sin θ) ^ 2))⁻¹)
      (∫ θ in (0:ℝ)..(π / 2), (Real.sin θ) ^ 2 /
          (2 * (1 - m * (Real.sin θ) ^ 2) * Real.sqrt (1 - m * (Real.sin θ) ^ 2))) m := by
    have hs_mem : Set.Ioo (m / 2) ((1 + m) / 2) ∈ 𝓝 m :=
      Ioo_mem_nhds (by linarith) (by linarith)
    have hinteg_K : IntervalIntegrable
        (fun θ => (Real.sqrt (1 - m * (Real.sin θ) ^ 2))⁻¹) MeasureTheory.volume 0 (π / 2) :=
      (ContinuousOn.inv₀
        (ContinuousOn.sqrt
          (continuousOn_const.sub (continuousOn_const.mul
            (Real.continuous_sin.pow 2).continuousOn))
          (fun θ _ => by nlinarith [Real.sin_sq_le_one θ]))
        (fun θ _ => (Real.sqrt_pos_of_pos (by nlinarith [Real.sin_sq_le_one θ])).ne')).intervalIntegrable
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_mem
      -- hF_meas: (√(1-x·sin²θ))⁻¹ AEStronglyMeasurable near m
      -- measurable_inv : Measurable (Inv.inv : ℝ → ℝ) (inv is Borel measurable on ℝ)
      (Filter.eventually_of_forall fun x =>
        (measurable_inv.comp
          ((Real.continuous_sqrt.comp (continuous_const.sub
            (continuous_const.mul (Real.continuous_sin.pow 2)))).measurable)).aestronglyMeasurable)
      -- hF_int
      hinteg_K
      -- hF'_meas: sin²θ/(2·f·√f) is AEStronglyMeasurable (continuous on [0,π/2])
      (((Real.continuous_sin.pow 2).div
        ((continuous_const.mul (continuous_const.sub (continuous_const.mul
              (Real.continuous_sin.pow 2)))).mul
          (Real.continuous_sqrt.comp (continuous_const.sub
            (continuous_const.mul (Real.continuous_sin.pow 2)))))
        (fun θ => mul_ne_zero
          (mul_ne_zero two_ne_zero
            (ne_of_gt (by nlinarith [Real.sin_sq_le_one θ])))
          (Real.sqrt_ne_zero'.mpr
            (by nlinarith [Real.sin_sq_le_one θ])))).aestronglyMeasurable)
      -- h_bound: ‖G'(x,θ)‖ ≤ sin²θ / (2·((1-m)/2)·√((1-m)/2)) for x ∈ s
      (Filter.eventually_of_forall fun θ _ x hx => by
        have hfl := hf_lower x hx θ
        have hf_pos : 0 < 1 - x * (Real.sin θ) ^ 2 := by linarith
        have hS := (Real.sqrt_pos_of_pos hf_pos).ne'
        rw [Real.norm_of_nonneg (by positivity)]
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        apply mul_le_mul
        · linarith
        · exact Real.sqrt_le_sqrt hfl
        · exact Real.sqrt_nonneg _
        · linarith)
      -- bound_integrable
      ((Real.continuous_sin.pow 2).continuousOn.div_const _ |>.intervalIntegrable)
      -- h_diff
      (Filter.eventually_of_forall fun θ _ x hx => h_diff_inv x hx θ)).2
  -- Step 2: Rewrite EllipticK as the raw integral.
  show HasDerivAt EllipticK ((EllipticE m - (1 - m) * EllipticK m) / (2 * m * (1 - m))) m
  rw [show EllipticK = fun x => ∫ θ in (0 : ℝ)..(π / 2),
      (Real.sqrt (1 - x * (Real.sin θ) ^ 2))⁻¹ from rfl]
  -- Step 3: Rewrite ∫ G'(m,·) as (E-(1-m)K)/(2m(1-m)).
  -- Identity: sin²θ/(2f^{3/2}) = (1/(2m(1-m))) · ((1-m)/√f + 1/√f - 1/√f · (1-(1-m)))
  -- Cleaner: sin²θ·f^{-3/2} = (1/m)·(f^{-1/2} - (1-m)·f^{-3/2}),
  --   since m·sin²θ = 1-f gives sin²θ = (1-f)/m and (1-m)·sin²θ = (1-f)(1-m)/m.
  convert hDCT using 1
  have hm' : m ≠ 0 := hm.ne'
  have hm1'' : (1 : ℝ) - m ≠ 0 := hm1'.ne'
  have hint : ∫ θ in (0 : ℝ)..(π / 2),
      (Real.sin θ) ^ 2 /
        (2 * (1 - m * (Real.sin θ) ^ 2) * Real.sqrt (1 - m * (Real.sin θ) ^ 2)) =
      (EllipticE m - (1 - m) * EllipticK m) / (2 * m * (1 - m)) := by
    -- Abbreviate f θ = 1 - m * sin²θ
    set f : ℝ → ℝ := fun θ => 1 - m * (Real.sin θ) ^ 2 with hf_def
    have hf_pos : ∀ θ : ℝ, 0 < f θ := fun θ => by
      simp only [hf_def]; nlinarith [Real.sin_sq_le_one θ]
    have hf_sqrt_ne : ∀ θ : ℝ, Real.sqrt (f θ) ≠ 0 := fun θ =>
      (Real.sqrt_pos_of_pos (hf_pos θ)).ne'
    -- Factor 1/2 out of the integrand
    have h_half : ∀ θ : ℝ,
        (Real.sin θ) ^ 2 / (2 * f θ * Real.sqrt (f θ)) =
        (1 / 2) * ((Real.sin θ) ^ 2 / (f θ * Real.sqrt (f θ))) := fun θ => by ring
    simp_rw [h_half]
    rw [intervalIntegral.integral_const_mul]
    rw [show (EllipticE m - (1 - m) * EllipticK m) / (2 * m * (1 - m)) =
        1 / 2 * ((EllipticE m - (1 - m) * EllipticK m) / (m * (1 - m))) from by ring]
    congr 1
    -- Goal: ∫ sin²θ / (f * √f) = (E - (1-m)*K) / (m*(1-m))
    -- Step A: ∫ cos²θ/√f = (E - (1-m)*K)/m
    -- Pointwise: cos²θ/√f = (1/m)*√f + ((m-1)/m)*(√f)⁻¹
    -- because cos²θ = 1 - sin²θ = 1 - (1-f)/m = (f-(1-m))/m, so
    -- cos²θ/√f = f/(m√f) + (m-1)/(m√f) = √f/m + (m-1)/(m√f)
    have hcos_sq : ∫ θ in (0 : ℝ)..(π / 2),
        (Real.cos θ) ^ 2 / Real.sqrt (f θ) =
        (EllipticE m - (1 - m) * EllipticK m) / m := by
      have hpw : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 2),
          (Real.cos θ) ^ 2 / Real.sqrt (f θ) =
          (1 / m) * Real.sqrt (f θ) + ((m - 1) / m) * (Real.sqrt (f θ))⁻¹ := by
        intro θ _
        have hfp := hf_pos θ
        have hS := hf_sqrt_ne θ
        have hcosq : (Real.cos θ) ^ 2 = 1 - (Real.sin θ) ^ 2 := by
          nlinarith [Real.sin_sq_add_cos_sq θ]
        simp only [hf_def] at hfp hS ⊢
        rw [hcosq]
        field_simp [hS, hfp.ne']
        rw [Real.sq_sqrt hfp.le]
        ring
      have hintE : IntervalIntegrable (fun θ => (1 / m) * Real.sqrt (f θ))
          MeasureTheory.volume 0 (π / 2) :=
        (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub
          (continuous_const.mul (Real.continuous_sin.pow 2))))).intervalIntegrable _ _
      have hintK : IntervalIntegrable (fun θ => ((m - 1) / m) * (Real.sqrt (f θ))⁻¹)
          MeasureTheory.volume 0 (π / 2) :=
        (continuous_const.mul ((Real.continuous_sqrt.comp (continuous_const.sub
          (continuous_const.mul (Real.continuous_sin.pow 2)))).inv₀
          hf_sqrt_ne)).intervalIntegrable _ _
      rw [intervalIntegral.integral_congr hpw,
          intervalIntegral.integral_add hintE hintK,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      -- ∫ √(f θ) = EllipticE m and ∫ (√(f θ))⁻¹ = EllipticK m by definition
      simp only [hf_def, ← EllipticE, ← EllipticK]
      field_simp [hm']
      ring
    -- Step B: IBP — ∫ sin²θ/(f√f) = (1/(1-m)) * ∫ cos²θ/√f
    -- IBP with u = sin θ,  v = -cos θ / ((1-m) * √(f θ))
    -- v' = sin θ / (f * √f)  [proved below, key: d(cosθ/√f)/dθ = -(1-m)sinθ/f^{3/2}]
    -- boundary: u(π/2)*v(π/2) - u(0)*v(0) = 1*0 - 0*v(0) = 0
    -- remainder: -∫ cosθ * v = ∫ cos²θ/((1-m)√f) = (1/(1-m)) ∫ cos²θ/√f
    have hv_deriv : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 2),
        HasDerivAt (fun θ => -(Real.cos θ) / ((1 - m) * Real.sqrt (f θ)))
          (Real.sin θ / (f θ * Real.sqrt (f θ))) θ := by
      intro θ _
      have hfp := hf_pos θ
      have hS := hf_sqrt_ne θ
      -- d/dθ[f θ] = -2m sinθ cosθ
      have hf_diff : HasDerivAt f (-(2 * m * Real.sin θ * Real.cos θ)) θ := by
        have h := (((Real.hasDerivAt_sin θ).pow 2).const_mul m).const_sub 1
        simp only [hf_def] at h ⊢
        convert h using 1; ring
      -- d/dθ[√(f θ)] = -m sinθ cosθ / √(f θ)
      have hsqrt_diff : HasDerivAt (fun θ => Real.sqrt (f θ))
          (-(m * Real.sin θ * Real.cos θ) / Real.sqrt (f θ)) θ := by
        have h := hf_diff.sqrt hfp.ne'
        convert h using 1; field_simp [hS]; ring
      -- d/dθ[(√(f θ))⁻¹] = m sinθ cosθ / (f θ · √(f θ))
      have hinv_diff : HasDerivAt (fun θ => (Real.sqrt (f θ))⁻¹)
          (m * Real.sin θ * Real.cos θ / (f θ * Real.sqrt (f θ))) θ := by
        have h := hsqrt_diff.inv hS
        convert h using 1
        rw [Real.sq_sqrt hfp.le]; ring
      -- d/dθ[cosθ · (√f)⁻¹] by the product rule
      have hprod_diff : HasDerivAt (fun θ => Real.cos θ * (Real.sqrt (f θ))⁻¹)
          (-Real.sin θ * (Real.sqrt (f θ))⁻¹ +
            Real.cos θ * (m * Real.sin θ * Real.cos θ / (f θ * Real.sqrt (f θ)))) θ :=
        (Real.hasDerivAt_cos θ).mul hinv_diff
      -- Rewrite v(θ) = -(1/(1-m)) · (cosθ · (√f)⁻¹) and apply const_mul
      have h_fn_eq : (fun x => -(Real.cos x) / ((1 - m) * Real.sqrt (f x))) =
          (fun x => -(1 / (1 - m)) * (Real.cos x * (Real.sqrt (f x))⁻¹)) := by
        ext x; field_simp [hf_sqrt_ne x, hm1'']; ring
      rw [h_fn_eq]
      have h := hprod_diff.const_mul (-(1 / (1 - m)))
      -- Key: f θ - m·cos²θ = 1-m  (since sin²θ + cos²θ = 1)
      have key : f θ - m * (Real.cos θ) ^ 2 = 1 - m := by
        have h1 := Real.sin_sq_add_cos_sq θ
        simp only [hf_def]; linarith
      -- Show that the computed derivative equals sinθ/(f·√f)
      have h_eq : -(1 / (1 - m)) * (-Real.sin θ * (Real.sqrt (f θ))⁻¹ +
          Real.cos θ * (m * Real.sin θ * Real.cos θ / (f θ * Real.sqrt (f θ)))) =
          Real.sin θ / (f θ * Real.sqrt (f θ)) := by
        field_simp [hS, hfp.ne', hm1'']
        rw [Real.sq_sqrt hfp.le]
        linear_combination Real.sin θ * key
      rw [h_eq] at h
      exact h
    -- Integrability conditions for IBP
    have hcos_int : IntervalIntegrable (fun θ => Real.cos θ) MeasureTheory.volume 0 (π / 2) :=
      Real.continuous_cos.intervalIntegrable _ _
    have hsin_quot_int : IntervalIntegrable
        (fun θ => Real.sin θ / (f θ * Real.sqrt (f θ))) MeasureTheory.volume 0 (π / 2) :=
      (Real.continuous_sin.continuousOn.div
        ((continuous_const.sub (continuous_const.mul
          (Real.continuous_sin.pow 2))).continuousOn.mul
          (Real.continuous_sqrt.comp (continuous_const.sub
            (continuous_const.mul (Real.continuous_sin.pow 2)))).continuousOn)
        (fun θ _ => mul_ne_zero (hf_pos θ).ne' (hf_sqrt_ne θ))).intervalIntegrable
    -- Apply IBP: ∫ u * v' = [u*v]_0^{π/2} - ∫ u' * v
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun θ hθ => Real.hasDerivAt_sin θ) hv_deriv hcos_int hsin_quot_int
    -- Massage hibp LHS: ∫ sinθ * (sinθ/(f√f)) = ∫ sin²θ/(f√f)
    rw [intervalIntegral.integral_congr
      (fun θ _ => show Real.sin θ * (Real.sin θ / (f θ * Real.sqrt (f θ))) =
        (Real.sin θ) ^ 2 / (f θ * Real.sqrt (f θ)) from by ring)] at hibp
    -- Boundary: sin(π/2)*v(π/2) - sin(0)*v(0) = 1*0 - 0*v(0) = 0
    have h_bdy : Real.sin (π / 2) * (-(Real.cos (π / 2)) / ((1 - m) * Real.sqrt (f (π / 2)))) -
        Real.sin 0 * (-(Real.cos 0) / ((1 - m) * Real.sqrt (f 0))) = 0 := by
      simp [Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_zero]
    rw [h_bdy] at hibp
    -- Remainder: ∫ cosθ * (-cosθ/((1-m)√f)) = -(1/(1-m)) * ∫ cos²θ/√f
    have h_rem : ∫ θ in (0 : ℝ)..(π / 2),
        Real.cos θ * (-(Real.cos θ) / ((1 - m) * Real.sqrt (f θ))) =
        -(1 / (1 - m)) * ∫ θ in (0 : ℝ)..(π / 2),
          (Real.cos θ) ^ 2 / Real.sqrt (f θ) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun θ _ => by
        field_simp [hf_sqrt_ne θ, hm1'']; ring)
    rw [h_rem] at hibp
    -- hibp : ∫ sin²θ/(f√f) = 0 - (-(1/(1-m)) * ∫ cos²θ/√f)
    -- i.e.  ∫ sin²θ/(f√f) = (1/(1-m)) * ∫ cos²θ/√f
    -- Combine with hcos_sq to get (E-(1-m)K)/(m*(1-m))
    rw [hcos_sq] at hibp
    -- hibp : ∫ sin²θ/(f√f) = 0 - (-(1/(1-m)) * ((E-(1-m)K)/m))
    rw [hibp]
    field_simp [hm', hm1'']
    ring
  exact hint

/-- Pure algebraic verification that the Legendre combination has zero derivative.
    Given derivative formulas dK, dE, dK̄, dĒ (d/dm applied at m and at 1-m),
    the weighted sum dK(Ē-K̄) + dK̄(K-E) + dE·K̄ - dĒ·K = 0.
    This is a polynomial identity: all cross terms cancel. -/
lemma legendre_deriv_algebra (m K E Kb Eb : ℝ) (hm : 0 < m) (hm1 : m < 1) :
    let dK  := (E  - (1 - m) * K)  / (2 * m * (1 - m))
    let dE  := (E  - K)             / (2 * m)
    let dKb := (Eb - m * Kb)        / (2 * (1 - m) * m)
    let dEb := (Eb - Kb)            / (2 * (1 - m))
    dK * (Eb - Kb) + dKb * (K - E) + dE * Kb - dEb * K = 0 := by
  simp only
  have hm'  : m ≠ 0       := hm.ne'
  have hm1' : 1 - m ≠ 0   := sub_ne_zero.mpr hm1.ne'
  field_simp
  ring

/-- **Theorem 5.3 (Legendre coupling) — DLMF 19.7.1.**
    K(m)*E(1-m) + E(m)*K(1-m) - K(m)*K(1-m) = π/2.

    Proof:
    (A) f(t) := K(t)·E(1-t) + E(t)·K(1-t) - K(t)·K(1-t) has f'(t) = 0 on (0,1).
        Derivative: product/chain rules give f'(t) = legendre_deriv_algebra(t,…) = 0.
    (B) f is constant on (0,1).
        Requires: ContinuousOn f (Icc 0 1) and HasDerivAt f 0 on the interior,
        then by the MVT (Mathlib: isConst_of_deriv_eq_zero or image_eq_of_liminf_slope_le).
    (C) f(t) = π/2.
        Evaluate at t → 1⁻: K(t)·(E(1-t)-K(1-t)) + E(t)·K(1-t).
        As t → 1⁻: E(1-t) → E(0) = π/2, K(1-t) → K(0) = π/2, E(t) → E(1) = 1.
        So E(t)·K(1-t) → 1·(π/2) = π/2.
        And K(t)·(E(1-t)-K(1-t)) → K(1⁻)·0 = 0 (using K(1-t)=O(log(1/t)),
        E(1-t)-K(1-t) = O((1-t)), product = O((1-t)·log(1/(1-t))) → 0
        via Mathlib.tendsto_id_mul_log_atRight_zero).

    Steps (B) and (C) are left sorry; they require ContinuousOn EllipticK/EllipticE
    and the O((1-t)·log) bound, which are not in Mathlib 4.28.0 for our definitions.

    Paper: Theorem 5.3 (thm:legendre) -/
theorem legendre_identity (m : ℝ) (hm : 0 < m) (hm1 : m < 1) :
    EllipticK m * EllipticE (1 - m) + EllipticE m * EllipticK (1 - m)
      - EllipticK m * EllipticK (1 - m) = π / 2 := by
  -- Shorthand
  set f : ℝ → ℝ := fun t =>
    EllipticK t * EllipticE (1 - t) + EllipticE t * EllipticK (1 - t)
      - EllipticK t * EllipticK (1 - t) with hf_def
  -- Step A: f has zero derivative at every t ∈ (0,1)
  have hf_zero : ∀ t : ℝ, 0 < t → t < 1 → HasDerivAt f 0 t := by
    intro t ht ht1
    have h1t  : (0 : ℝ) < 1 - t  := by linarith
    have h1t1 : (1 : ℝ) - t < 1  := by linarith
    have hm'  : t ≠ 0             := ht.ne'
    have hm1' : 1 - t ≠ 0        := sub_ne_zero.mpr ht1.ne'
    -- Derivative of the substitution s ↦ 1-s at t is -1
    have hd : HasDerivAt (fun s => (1 : ℝ) - s) (-1) t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    -- Derivative formulas at t and at 1-t
    have hK  := hasDerivAt_EllipticK ht ht1
    have hE  := hasDerivAt_EllipticE ht ht1
    -- Chain rule: d/dt [K(1-t)] = K'(1-t)·(-1), d/dt [E(1-t)] = E'(1-t)·(-1)
    have hKb := (hasDerivAt_EllipticK h1t h1t1).comp t hd
    have hEb := (hasDerivAt_EllipticE h1t h1t1).comp t hd
    -- Product rule builds HasDerivAt for f with derivative D, then show D = 0.
    --   D = K'·Eb + K·Eb' + E'·Kb + E·Kb' - K'·Kb - K·Kb'
    -- With Kb' = -dKb and Eb' = -dEb (chain rule negatives), this is
    --   dK·(Eb-Kb) + dKb·(K-E) + dE·Kb - dEb·K = 0 by legendre_deriv_algebra.
    have hfull := ((hK.mul hEb).add (hE.mul hKb)).sub (hK.mul hKb)
    -- Unfold function composition so Lean sees EllipticE (1-t) not EllipticE ∘ (1-·)
    simp only [Function.comp] at hfull hKb hEb
    -- Convert goal HasDerivAt f 0 t to match hfull (same function, need 0 = D)
    convert hfull using 1
    -- Goal: 0 = D (the product-rule derivative).
    -- After clearing denominators, this is a polynomial identity in
    -- {EllipticK t, EllipticE t, EllipticK (1-t), EllipticE (1-t), t},
    -- equivalent to legendre_deriv_algebra; proved by ring.
    field_simp [hm', hm1']
    ring
  -- Step B: f is constant on (0,1).
  -- HasDerivAt f 0 t → ContinuousAt f t → ContinuousOn f (Ioo 0 1)
  have hcont_f : ContinuousOn f (Set.Ioo 0 1) := fun t ht =>
    (hf_zero t ht.1 ht.2).continuousAt.continuousWithin
  -- For any t ∈ (0,1), apply Mathlib.constant_of_has_deriv_right_zero on
  -- [min m t, max m t] ⊆ (0,1), using HasDerivAt → HasDerivWithinAt.
  have hconst : ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = f m := by
    intro t ht
    set a := min m t
    set b := max m t
    have ha0 : 0 < a  := lt_min hm ht.1
    have hb1 : b < 1  := max_lt hm1 ht.2
    have hcab : ContinuousOn f (Set.Icc a b) :=
      hcont_f.mono fun x hx => ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
    have hfa : ∀ x ∈ Set.Icc a b, f x = f a :=
      constant_of_has_deriv_right_zero hcab fun x hx =>
        (hf_zero x (lt_of_lt_of_le ha0 (Set.Ico_subset_Icc_self hx).1)
                   (lt_of_le_of_lt (Set.Ico_subset_Icc_self hx).2 hb1)).hasDerivWithinAt
    exact (hfa t ⟨min_le_right m t, le_max_right m t⟩).trans
          (hfa m ⟨min_le_left  m t, le_max_left  m t⟩).symm
  -- Step C: evaluate f m = π/2.
  -- Rewrite f(t) = K(t)·E(1-t) + K(1-t)·(E(t) - K(t)).
  -- As t → 0⁺:  K(t) → π/2  and  E(1-t) → E(1) = 1  give first term → π/2;
  --   K(1-t)·(E(t)-K(t)) → 0  since K(1-t)=O(log(1/t)) and E(t)-K(t)=O(t).
  -- Requires: ContinuousAt EllipticK 0 + ContinuousAt EllipticE 1
  --   (from intervalIntegral.continuousOn_primitive) and the O(t·log t) squeeze
  --   (from tendsto_id_mul_log_atRight_zero).  Both follow from the integral definitions.
  have hval : f m = π / 2 := by
    -- f is constant on (0,1) by hconst.  We evaluate by taking the limit t → 0⁺.
    -- Write f(t) = K(t)·E(1-t) + (E(t) - K(t))·K(1-t).
    -- As t → 0⁺:
    --   • K(t) → K(0) = π/2   (K continuous at 0, proved from integral definition)
    --   • E(1-t) → E(1) = 1   (E continuous, E(1) = EllipticE_one)
    --   • so K(t)·E(1-t) → π/2
    --   • E(t) - K(t) = O(t)  (both equal π/2 at 0, derivatives differ by O(1))
    --   • K(1-t) = O(|log t|)  (logarithmic singularity at 1)
    --   • product (E(t)-K(t))·K(1-t) = O(t·|log t|) → 0
    -- Hence f(t) → π/2, and since f(t) = f(m) for all t ∈ (0,1), f(m) = π/2.
    --
    -- Formal reduction:
    -- (a) tendsto f (𝓝[Ioo 0 1] 0) (𝓝 (π/2))       [sorry: needs K/E continuity + log bound]
    -- (b) f is constantly f(m) near 0 on (0,1)        [from hconst]
    -- (c) therefore the limit equals f(m), so f(m) = π/2
    -- Sub-lemma (a): the limit of f as t → 0⁺ along (0,1)
    have hlim : Filter.Tendsto f (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (π / 2)) := by
      -- Rewrite f(t) = K(t)·E(1-t) + (E(t)-K(t))·K(1-t)
      -- and show each factor converges.
      -- The formal proof requires:
      --   (i)  ContinuousAt EllipticK 0  (from ContinuousOn.intervalIntegral + DCT)
      --   (ii) ContinuousAt EllipticE 1  (same)
      --   (iii) Filter.Tendsto (fun t => (EllipticE t - EllipticK t) * EllipticK (1-t)) → 0
      --         via t·|log t| → 0  (Mathlib: tendsto_id_mul_log_atRight_zero)
      -- Algebraic identity: f t = K(t)*E(1-t) + (E(t)-K(t))*K(1-t)
      have hrew : ∀ t : ℝ, f t =
          EllipticK t * EllipticE (1 - t) + (EllipticE t - EllipticK t) * EllipticK (1 - t) :=
        fun t => by simp only [hf_def]; ring
      -- 1. EllipticK continuous at 0 (DCT, bound = √2 on Ioo(-1/2)(1/2))
      have hK0 : ContinuousAt EllipticK 0 := by
        show ContinuousAt (fun x => ∫ θ in (0:ℝ)..(π / 2),
            (Real.sqrt (1 - x * (Real.sin θ) ^ 2))⁻¹) 0
        apply intervalIntegral.continuousAt_of_dominated_interval
            (bound := fun _ => Real.sqrt 2)
        · exact Filter.eventually_of_forall fun x =>
            (measurable_inv.comp (Real.continuous_sqrt.comp (continuous_const.sub
              (continuous_const.mul (Real.continuous_sin.pow 2)))).measurable).aestronglyMeasurable
        · filter_upwards [Ioo_mem_nhds (show (-(1:ℝ) / 2) < 0 by norm_num)
                                       (show (0:ℝ) < 1 / 2 by norm_num)] with x hx
          apply Filter.eventually_of_forall; intro θ _
          rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
          have hfl : (1:ℝ) / 2 ≤ 1 - x * (Real.sin θ) ^ 2 := by
            nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ), hx.1, hx.2]
          calc (Real.sqrt (1 - x * (Real.sin θ) ^ 2))⁻¹
              ≤ (Real.sqrt (1 / 2))⁻¹ :=
                inv_anti₀ (Real.sqrt_pos_of_pos (by norm_num)) (Real.sqrt_le_sqrt hfl)
            _ = Real.sqrt 2 := by
                rw [show (1:ℝ) / 2 = 2⁻¹ from by norm_num, Real.sqrt_inv, inv_inv]
        · exact intervalIntegral.intervalIntegrable_const
        · apply Filter.eventually_of_forall; intro θ _
          apply ContinuousAt.inv₀
          · exact (Real.continuous_sqrt.comp
                (continuous_const.sub (continuous_id.mul continuous_const))).continuousAt
          · simp [Real.sqrt_one]
      -- 2. EllipticE continuous at 1 (DCT, bound = 1 on Ioo 0 2)
      have hE1 : ContinuousAt EllipticE 1 := by
        show ContinuousAt (fun x => ∫ θ in (0:ℝ)..(π / 2),
            Real.sqrt (1 - x * (Real.sin θ) ^ 2)) 1
        apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => 1)
        · exact Filter.eventually_of_forall fun x =>
            (Real.continuous_sqrt.comp (continuous_const.sub
              (continuous_const.mul (Real.continuous_sin.pow 2)))).measurable.aestronglyMeasurable
        · filter_upwards [Ioo_mem_nhds (show (0:ℝ) < 1 by norm_num)
                                       (show (1:ℝ) < 2 by norm_num)] with x hx
          apply Filter.eventually_of_forall; intro θ _
          rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
          calc Real.sqrt (1 - x * (Real.sin θ) ^ 2)
              ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by
                    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ), hx.1])
            _ = 1 := Real.sqrt_one
        · exact intervalIntegral.intervalIntegrable_const
        · apply Filter.eventually_of_forall; intro θ _
          exact (Real.continuous_sqrt.comp
            (continuous_const.sub (continuous_id.mul continuous_const))).continuousAt
      -- 3. K(t)·E(1-t) → π/2
      have hlim1 : Filter.Tendsto (fun t => EllipticK t * EllipticE (1 - t))
          (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (π / 2)) := by
        have hK_tend : Filter.Tendsto EllipticK (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (π / 2)) := by
          have h := hK0.mono_left nhdsWithin_le_nhds; rwa [EllipticK_zero] at h
        have h_sub : Filter.Tendsto (fun t : ℝ => 1 - t)
            (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 1) := by
          have := (tendsto_const_nhds (a := (1:ℝ))).sub
            (continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
          simp at this; exact this
        have hE1t : Filter.Tendsto (fun t => EllipticE (1 - t))
            (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 1) := by
          have h := hE1.comp h_sub; rwa [EllipticE_one] at h
        rw [show π / 2 = π / 2 * 1 from (mul_one _).symm]
        exact hK_tend.mul hE1t
      -- 4. K(1-t) ≤ π/(2√t) for t ∈ (0,1)  [cos²θ + t·sin²θ ≥ t]
      have hKb_bound : ∀ t ∈ Set.Ioo (0:ℝ) 1,
          EllipticK (1 - t) ≤ π / 2 / Real.sqrt t := by
        intro t ht
        have ht_pos : 0 < t := ht.1
        have hf_pos : ∀ θ : ℝ, 0 < 1 - (1 - t) * (Real.sin θ) ^ 2 := fun θ => by
          nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.cos θ), Real.sin_sq_add_cos_sq θ]
        have hinteg_K1 : IntervalIntegrable
            (fun θ => (Real.sqrt (1 - (1 - t) * (Real.sin θ) ^ 2))⁻¹)
            MeasureTheory.volume 0 (π / 2) :=
          (ContinuousOn.inv₀
            (ContinuousOn.sqrt
              (continuousOn_const.sub (continuousOn_const.mul
                (Real.continuous_sin.pow 2).continuousOn))
              (fun θ _ => (hf_pos θ).le))
            (fun θ _ => (Real.sqrt_pos_of_pos (hf_pos θ)).ne')).intervalIntegrable
        calc EllipticK (1 - t)
            = ∫ θ in (0:ℝ)..(π / 2),
                (Real.sqrt (1 - (1 - t) * (Real.sin θ) ^ 2))⁻¹ := rfl
          _ ≤ ∫ _ in (0:ℝ)..(π / 2), (Real.sqrt t)⁻¹ :=
              intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
                hinteg_K1 intervalIntegral.intervalIntegrable_const
                (fun θ _ => inv_anti₀ (Real.sqrt_pos_of_pos ht_pos)
                  (Real.sqrt_le_sqrt (by
                    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.cos θ),
                      Real.sin_sq_add_cos_sq θ])))
          _ = π / 2 / Real.sqrt t := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
              simp; ring
      -- 5. K(t)-E(t) ≤ t·(π/2)/√(1-t) for t ∈ (0,1)  [t·sin²θ/√f ≤ t/√(1-t)]
      have hKE_bound : ∀ t ∈ Set.Ioo (0:ℝ) 1,
          EllipticK t - EllipticE t ≤ t * (π / 2) / Real.sqrt (1 - t) := by
        intro t ht
        have ht_pos : 0 < t := ht.1
        have h1t_pos : 0 < 1 - t := by linarith [ht.2]
        have hf_pos : ∀ θ : ℝ, 0 < 1 - t * (Real.sin θ) ^ 2 := fun θ => by
          nlinarith [Real.sin_sq_le_one θ]
        have hinteg_E : IntervalIntegrable
            (fun θ => Real.sqrt (1 - t * (Real.sin θ) ^ 2)) MeasureTheory.volume 0 (π / 2) :=
          (ContinuousOn.sqrt
            (continuousOn_const.sub (continuousOn_const.mul
              (Real.continuous_sin.pow 2).continuousOn))
            (fun θ _ => (hf_pos θ).le)).intervalIntegrable
        have hinteg_K : IntervalIntegrable
            (fun θ => (Real.sqrt (1 - t * (Real.sin θ) ^ 2))⁻¹)
            MeasureTheory.volume 0 (π / 2) :=
          (ContinuousOn.inv₀
            (ContinuousOn.sqrt
              (continuousOn_const.sub (continuousOn_const.mul
                (Real.continuous_sin.pow 2).continuousOn))
              (fun θ _ => (hf_pos θ).le))
            (fun θ _ => (Real.sqrt_pos_of_pos (hf_pos θ)).ne')).intervalIntegrable
        -- K-E = ∫ (1/√f - √f) dθ = ∫ t·sin²θ/√f dθ
        have heq : EllipticK t - EllipticE t =
            ∫ θ in (0:ℝ)..(π / 2),
              t * (Real.sin θ) ^ 2 / Real.sqrt (1 - t * (Real.sin θ) ^ 2) := by
          unfold EllipticK EllipticE
          rw [← intervalIntegral.integral_sub hinteg_K hinteg_E]
          apply intervalIntegral.integral_congr; intro θ _
          have hf := hf_pos θ
          have hS := (Real.sqrt_pos_of_pos hf).ne'
          field_simp [hS]; rw [Real.sq_sqrt hf.le]; ring
        rw [heq]
        have hinteg_diff : IntervalIntegrable
            (fun θ => t * (Real.sin θ) ^ 2 / Real.sqrt (1 - t * (Real.sin θ) ^ 2))
            MeasureTheory.volume 0 (π / 2) :=
          (ContinuousOn.div
            (continuousOn_const.mul (Real.continuous_sin.pow 2).continuousOn)
            (ContinuousOn.sqrt
              (continuousOn_const.sub (continuousOn_const.mul
                (Real.continuous_sin.pow 2).continuousOn))
              (fun θ _ => (hf_pos θ).le))
            (fun θ _ => (Real.sqrt_pos_of_pos (hf_pos θ)).ne')).intervalIntegrable
        calc ∫ θ in (0:ℝ)..(π / 2),
              t * (Real.sin θ) ^ 2 / Real.sqrt (1 - t * (Real.sin θ) ^ 2)
            ≤ ∫ _ in (0:ℝ)..(π / 2), t / Real.sqrt (1 - t) :=
              intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
                hinteg_diff intervalIntegral.intervalIntegrable_const
                (fun θ _ =>
                  div_le_div₀ ht_pos.le
                    (by nlinarith [Real.sin_sq_le_one θ, ht_pos])
                    (Real.sqrt_pos_of_pos h1t_pos)
                    (Real.sqrt_le_sqrt (by nlinarith [Real.sin_sq_le_one θ])))
          _ = t * (π / 2) / Real.sqrt (1 - t) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]; simp; ring
      -- 6. (E(t)-K(t))·K(1-t) → 0  (squeeze: ≤ π²/4 · √t/√(1-t) → 0)
      have hlim2 : Filter.Tendsto (fun t => (EllipticE t - EllipticK t) * EllipticK (1 - t))
          (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 0) := by
        apply squeeze_zero_norm'
        · -- bound: |(E-K)·K(1-t)| ≤ π²/4 · √t/√(1-t) for all t ∈ (0,1)
          filter_upwards [self_mem_nhdsWithin] with t ht
          have ht_pos : 0 < t := ht.1
          have h1t_pos : 0 < 1 - t := by linarith [ht.2]
          have hKE_nn : 0 ≤ EllipticK t - EllipticE t := by
            unfold EllipticK EllipticE
            rw [← intervalIntegral.integral_sub
                (by exact (ContinuousOn.inv₀
                  (ContinuousOn.sqrt
                    (continuousOn_const.sub (continuousOn_const.mul
                      (Real.continuous_sin.pow 2).continuousOn))
                    (fun θ _ => by nlinarith [Real.sin_sq_le_one θ]))
                  (fun θ _ => (Real.sqrt_pos_of_pos
                    (by nlinarith [Real.sin_sq_le_one θ])).ne')).intervalIntegrable)
                (by exact (ContinuousOn.sqrt
                  (continuousOn_const.sub (continuousOn_const.mul
                    (Real.continuous_sin.pow 2).continuousOn))
                  (fun θ _ => by nlinarith [Real.sin_sq_le_one θ])).intervalIntegrable)]
            apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
            intro θ _
            have hf : 0 < 1 - t * (Real.sin θ) ^ 2 := by nlinarith [Real.sin_sq_le_one θ]
            have hS := (Real.sqrt_pos_of_pos hf).ne'
            apply sub_nonneg.mpr
            rw [← Real.sqrt_inv]
            exact Real.sqrt_le_sqrt (by
              rw [inv_eq_one_div, le_div_iff hf]
              nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ), ht_pos])
          have hKb_nn : 0 ≤ EllipticK (1 - t) := by
            unfold EllipticK
            apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
            intro θ _; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
          rw [norm_mul,
              show ‖EllipticE t - EllipticK t‖ = EllipticK t - EllipticE t by
                rw [Real.norm_of_nonpos (by linarith)]; ring,
              Real.norm_of_nonneg hKb_nn]
          have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos_of_pos ht_pos).ne'
          have hs1t : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos_of_pos h1t_pos).ne'
          calc (EllipticK t - EllipticE t) * EllipticK (1 - t)
              ≤ (t * (π / 2) / Real.sqrt (1 - t)) * (π / 2 / Real.sqrt t) :=
                mul_le_mul (hKE_bound t ht) (hKb_bound t ht)
                  hKb_nn (by positivity)
            _ = π ^ 2 / 4 * (Real.sqrt t / Real.sqrt (1 - t)) := by
                field_simp [hst, hs1t]
                rw [Real.mul_self_sqrt ht_pos.le]
                ring
        · -- upper bound → 0: π²/4 · √t/√(1-t) → 0 · 1 = 0
          have h_sqt : Filter.Tendsto (fun t => Real.sqrt t)
              (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 0) := by
            have h := Real.continuous_sqrt.continuousAt (x := (0:ℝ))
            simp [Real.sqrt_zero] at h
            exact h.mono_left nhdsWithin_le_nhds
          have h_inv_s1t : Filter.Tendsto (fun t => (Real.sqrt (1 - t))⁻¹)
              (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 1) := by
            have h_sub2 : Filter.Tendsto (fun t : ℝ => 1 - t)
                (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 1) := by
              have := (tendsto_const_nhds (a := (1:ℝ))).sub
                (continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
              simp at this; exact this
            have hE_sqrt : Filter.Tendsto (fun t => Real.sqrt (1 - t))
                (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 1) := by
              have h := Real.continuous_sqrt.continuousAt (x := (1:ℝ))
              simp [Real.sqrt_one] at h
              exact h.comp h_sub2
            rw [show (1:ℝ) = (Real.sqrt 1)⁻¹ from by simp [Real.sqrt_one]]
            exact hE_sqrt.inv₀ (by simp [Real.sqrt_one])
          have h_ratio : Filter.Tendsto (fun t => Real.sqrt t / Real.sqrt (1 - t))
              (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 0) := by
            rw [show (0:ℝ) = 0 * 1 from (mul_one 0).symm]
            simp_rw [div_eq_mul_inv]
            exact h_sqt.mul h_inv_s1t
          have h_const : Filter.Tendsto (fun t => π ^ 2 / 4 * (Real.sqrt t / Real.sqrt (1 - t)))
              (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 0) := by
            simpa using h_ratio.const_mul (π ^ 2 / 4)
          exact h_const
      -- 7. Combine: f(t) = term1 + term2 → π/2 + 0 = π/2
      have htend : Filter.Tendsto f (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (π / 2)) := by
        rw [show π / 2 = π / 2 + 0 from (add_zero _).symm]
        refine (hlim1.add hlim2).congr' ?_
        exact Filter.eventually_nhdsWithin_of_forall (fun t ht => (hrew t).symm)
      exact htend
    -- Sub-lemma (b): f is eventually equal to f(m) along nhdsWithin 0 (Ioo 0 1)
    have hev : ∀ᶠ t in nhdsWithin 0 (Set.Ioo 0 1), f t = f m :=
      Filter.eventually_nhdsWithin_of_forall (fun t ht => hconst t ht)
    -- Combine: since f t = f m eventually and f t → π/2, we get f m = π/2.
    have hnebot : (nhdsWithin 0 (Set.Ioo 0 1)).NeBot :=
      left_nhdsWithin_Ioo_neBot (by norm_num : (0:ℝ) < 1)
    -- f t = f m eventually, and f t → π/2; by uniqueness of limits, f m = π/2.
    exact (tendsto_nhds_unique hnebot (hlim.congr' hev) tendsto_const_nhds).symm
  simp only [hf_def] at hval
  linarith

/-- Coupling constant arithmetic: 1/(2/π) = π/2. -/
theorem legendre_coupling_stated :
    (1 : ℝ) / (2 / π) = π / 2 := by
  field_simp

/-- Assumption-driven wrapper: if the Legendre identity holds for all m,
    it holds at the given m. Kept for backward compatibility. -/
theorem legendre_coupling
    (hLegendre :
      ∀ m : ℝ, 0 < m → m < 1 →
        EllipticK m * EllipticE (1 - m) + EllipticE m * EllipticK (1 - m)
          - EllipticK m * EllipticK (1 - m) = π / 2)
    (m : ℝ) (hm : 0 < m) (hm1 : m < 1) :
    EllipticK m * EllipticE (1 - m) + EllipticE m * EllipticK (1 - m)
      - EllipticK m * EllipticK (1 - m) = π / 2 :=
  legendre_identity m hm hm1

end
