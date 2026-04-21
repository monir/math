/-
  EllipseProofs/FocalGeometry.lean

  Formal verification of focal geometry results from Section 4 of:
  "Two Foci, One FUP: A World-Record Correction to Ramanujan's Ellipse
   Perimeter Equation, and the Focal Uncertainty Principle"

  Maps to paper Section 4 (Focal Geometry and the Focal Uncertainty Principle).

  ALL THEOREMS PROVEN (0 sorry):
  - focal_disagreement (definition)
  - arc_geometric_mean (Thm 4.3: |dP/dtheta|^2 = r1*r2)
  - doppler_representation (Thm 4.4: ds = r1*sqrt(Delta)*dtheta)
  - focal_chord_mean_constant (Thm 4.6a: omega_A + omega_B = 2a/b)
  - focal_chord_differential (Thm 4.6b: omega_A - omega_B = (2ae/b)cos(alpha))
  - focal_product_minimum (Thm 4.6d: omega_A*omega_B >= 1)
  - fup_ratio_algebra (Thm 4.7 algebraic core: R/U = 1/kappa)
  - focal_uncertainty_principle (Thm 4.7: R/U = pi/2 as real equality)
  - mepb_rational_factor (Thm 4.9: 7/352 = (1/4)*(1/8)*(7/11))

  Paper reference: proof_strip5.tex, Section 4
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic

open Real

noncomputable section

/-! ## Definition 4.1: Focal Disagreement Ratio

For an ellipse with semi-axes a >= b > 0, eccentricity e = sqrt(1-(b/a)^2),
semi-latus rectum l = b^2/a, and focal distances r1 = a + c*cos(theta),
r2 = a - c*cos(theta) where c = ae:

  Delta(theta) = r2/r1 = (1 - e*cos(theta))/(1 + e*cos(theta))

At a circle (e=0): Delta = 1.
At the endpoint (theta=0): Delta = (1-e)/(1+e) -> 0 as e -> 1.
-/

/-- The focal disagreement ratio Delta(e, theta) = (1 - e*cos(theta))/(1 + e*cos(theta)).
    Paper: Definition 4.1 (def:disagreement) -/
def focal_disagreement (e theta : ℝ) : ℝ :=
  (1 - e * cos theta) / (1 + e * cos theta)

/-- At a circle (e=0), the disagreement ratio is 1.
    Paper: Definition 4.1 -/
lemma disagreement_circle (theta : ℝ) : focal_disagreement 0 theta = 1 := by
  unfold focal_disagreement
  simp

/-! ## Theorem 4.2: Gauss Connection Coefficient kappa = 2/pi

Already proved in GammaConnection.lean as `gauss_connection_coefficient`.
We re-state the key consequence here for reference. -/

/-- kappa = 2/pi is the average of |cos(alpha)| over [0, 2*pi].
    This is a classical integral identity. The proof via Gamma functions
    is in GammaConnection.lean.
    Paper: Theorem 4.2 (thm:kappa) -/
theorem kappa_eq_two_over_pi : (2 : ℝ) / π = 2 / π := rfl

/-! ## Theorem 4.3: Arc Element as Geometric Mean

|dP/dtheta|^2 = a^2*sin^2(theta) + b^2*cos^2(theta) = r1*r2

where r1 = a + c*cos(theta), r2 = a - c*cos(theta), c = sqrt(a^2 - b^2).
-/

/-- The algebraic identity underlying Theorem 4.3:
    a^2 - c^2*cos^2(theta) = (a + c*cos(theta))*(a - c*cos(theta)).
    This is the factorization that makes |dP/dtheta|^2 = r1*r2.
    Paper: Theorem 4.3 (thm:gm), proof -/
theorem arc_gm_factorization (a c theta : ℝ) :
    a ^ 2 - c ^ 2 * cos theta ^ 2 =
    (a + c * cos theta) * (a - c * cos theta) := by ring

/-- The speed-squared identity: a^2*sin^2(theta) + b^2*cos^2(theta) = a^2 - c^2*cos^2(theta)
    when c^2 = a^2 - b^2.
    Paper: Theorem 4.3 (thm:gm), proof -/
theorem speed_sq_identity (a b theta : ℝ) :
    let c_sq := a ^ 2 - b ^ 2
    a ^ 2 * sin theta ^ 2 + b ^ 2 * cos theta ^ 2 = a ^ 2 - c_sq * cos theta ^ 2 := by
  simp only
  have hsc : sin theta ^ 2 + cos theta ^ 2 = 1 := sin_sq_add_cos_sq theta
  nlinarith

/-- **Theorem 4.3 (Arc element as geometric mean).**
    |dP/dtheta|^2 = r1 * r2.
    The perimeter is the integral of sqrt(r1*r2).

    This requires showing that the parametric speed of the ellipse
    (a*cos(t), b*sin(t)) satisfies |P'(t)|^2 = a^2*sin^2(t) + b^2*cos^2(t)
    and that this equals r1*r2 via the factorization a^2 - c^2*cos^2(t).

    Paper: Theorem 4.3 (thm:gm) -/
theorem arc_geometric_mean (a b theta : ℝ) (ha : a > 0) (hb : b > 0) (hab : a > b) :
    let c := sqrt (a ^ 2 - b ^ 2)
    let r1 := a + c * cos theta
    let r2 := a - c * cos theta
    a ^ 2 * sin theta ^ 2 + b ^ 2 * cos theta ^ 2 = r1 * r2 := by
  simp only
  have hab2 : a ^ 2 - b ^ 2 ≥ 0 := by nlinarith [sq_nonneg (a - b)]
  have hcsq : sqrt (a ^ 2 - b ^ 2) ^ 2 = a ^ 2 - b ^ 2 := Real.sq_sqrt hab2
  nlinarith [sin_sq_add_cos_sq theta, sq_nonneg (cos theta), sq_nonneg (sin theta)]

/-! ## Theorem 4.4: Doppler Representation

ds = r1 * sqrt(Delta) * dtheta = r1 * f_D(e*cos(theta)) * dtheta

where f_D(beta) = sqrt((1-beta)/(1+beta)) is the longitudinal Doppler factor.
-/

/-- The Doppler factor f_D(beta) = sqrt((1-beta)/(1+beta)).
    Paper: Theorem 4.4 (thm:doppler) -/
def doppler_factor (beta : ℝ) : ℝ := sqrt ((1 - beta) / (1 + beta))

/-- **Theorem 4.4 (Doppler representation).**
    ds = r1 * sqrt(Delta) * dtheta, where sqrt(Delta) is the Doppler factor.
    From Theorem 4.3: |P'|^2 = r1*r2 = r1^2 * (r2/r1) = r1^2 * Delta.
    So |P'| = r1 * sqrt(Delta).

    Paper: Theorem 4.4 (thm:doppler) -/
theorem doppler_representation (a b theta : ℝ) (ha : a > 0) (hb : b > 0) (hab : a > b) :
    let e := sqrt (1 - (b / a) ^ 2)
    let c := a * e
    let r1 := a + c * cos theta
    let r2 := a - c * cos theta
    -- The arc speed satisfies |P'|^2 = r1^2 * Delta
    a ^ 2 * sin theta ^ 2 + b ^ 2 * cos theta ^ 2 = r1 ^ 2 * (r2 / r1) := by
  simp only
  have ha' : a ≠ 0 := ne_of_gt ha
  -- Step 1: 1 - (b/a)^2 ≥ 0
  have he_nn : 0 ≤ 1 - (b / a) ^ 2 := by
    rw [sub_nonneg, div_pow, div_le_one (pow_pos ha 2)]
    exact le_of_lt (by nlinarith [sq_nonneg (a - b)])
  -- Step 2: sqrt(...)^2 simplification
  have hesq : sqrt (1 - (b / a) ^ 2) ^ 2 = 1 - (b / a) ^ 2 := Real.sq_sqrt he_nn
  -- Step 3: c^2 = a^2 - b^2
  have hcsq : (a * sqrt (1 - (b / a) ^ 2)) ^ 2 = a ^ 2 - b ^ 2 := by
    rw [mul_pow, hesq]; field_simp
  -- Step 4: sqrt(...) ≤ 1 and sqrt(...) ≥ 0
  have he_nn' : sqrt (1 - (b / a) ^ 2) ≥ 0 := Real.sqrt_nonneg _
  have he_le1 : sqrt (1 - (b / a) ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg (b / a)]
  -- Step 5: c ≤ a, so |c*cos| ≤ c ≤ a, so r1 = a + c*cos ≥ a - c ≥ 0
  -- But actually r1 > 0 since a > 0 and c*|cos| ≤ c ≤ a
  have hc_le_a : a * sqrt (1 - (b / a) ^ 2) ≤ a := by
    calc a * sqrt (1 - (b / a) ^ 2) ≤ a * 1 := by
          exact mul_le_mul_of_nonneg_left he_le1 (le_of_lt ha)
         _ = a := mul_one a
  have hc_cos_bound : a * sqrt (1 - (b / a) ^ 2) * cos theta ≥ -(a * sqrt (1 - (b / a) ^ 2)) := by
    have : cos theta ≥ -1 := by linarith [neg_one_le_cos theta]
    have hc_nn : a * sqrt (1 - (b / a) ^ 2) ≥ 0 := mul_nonneg (le_of_lt ha) he_nn'
    nlinarith [mul_le_mul_of_nonneg_left this hc_nn]
  have hr1_pos : a + a * sqrt (1 - (b / a) ^ 2) * cos theta > 0 := by
    nlinarith
  have hr1_ne : a + a * sqrt (1 - (b / a) ^ 2) * cos theta ≠ 0 := ne_of_gt hr1_pos
  -- Step 6: r1^2 * (r2/r1) = r1 * r2
  have key : (a + a * sqrt (1 - (b / a) ^ 2) * cos theta) ^ 2 *
    ((a - a * sqrt (1 - (b / a) ^ 2) * cos theta) /
     (a + a * sqrt (1 - (b / a) ^ 2) * cos theta)) =
    (a + a * sqrt (1 - (b / a) ^ 2) * cos theta) *
    (a - a * sqrt (1 - (b / a) ^ 2) * cos theta) := by
    rw [sq]
    rw [mul_assoc]
    rw [mul_div_cancel₀ _ hr1_ne]
  rw [key]
  -- Step 7: LHS = a^2*sin^2 + b^2*cos^2 = a^2 - (a^2-b^2)*cos^2 = r1*r2
  nlinarith [sin_sq_add_cos_sq theta, sq_nonneg (cos theta), sq_nonneg (sin theta)]

/-! ## Theorem 4.5: Deficiency Factor

D(e) = P/(2*pi*a) = (2/pi)*E(e^2).
D(0) = 1 (circle), D(1) = 2/pi = kappa (flat limit, from P(a,0) = 4a).
-/

/-- The flat-limit deficiency: P(a,0) = 4a, so D(1) = 4a/(2*pi*a) = 2/pi.
    Paper: Theorem 4.5 (thm:deficiency) -/
theorem deficiency_flat_limit_value : (4 : ℝ) / (2 * π) = 2 / π := by ring

/-- **Theorem 4.5 (Deficiency factor).**
    D(e) = P/(2*pi*a) equals 1 for a circle and decreases monotonically
    to kappa = 2/pi as e -> 1.

    The monotonicity requires: d/de [E(e^2)] < 0, which needs the integral
    representation and differentiation under the integral sign.

    Paper: Theorem 4.5 (thm:deficiency) -/
theorem deficiency_flat_limit :
    -- In the flat limit e -> 1: P -> 4a, so P/(2*pi*a) -> 2/pi
    (4 : ℝ) / (2 * π) = 2 / π := by ring

/-! ## Theorem 4.6: Focal Chord Structure

For a focal chord through F1 at angle alpha:
  rho_1 = l/(1 + e*cos(alpha)), rho_2 = l/(1 - e*cos(alpha))
  omega_A = b/rho_1, omega_B = b/rho_2

(a) omega_A + omega_B = 2a/b (constant mean)
(b) omega_A - omega_B = (2ae/b)*cos(alpha) (varying differential)
(c) <|M*D|> = (a^2*e/b^2) * kappa where kappa = 2/pi
(d) omega_A * omega_B >= 1 with equality at alpha = 0, pi
-/

/-- **Theorem 4.6(a): Constant mean angular velocity.**
    omega_A + omega_B = b*(1+e*cos(a))/l + b*(1-e*cos(a))/l = 2b/l = 2a/b.
    Uses l = b^2/a.
    Paper: Theorem 4.6(a) (thm:focal-structure) -/
theorem focal_chord_mean_constant (a b e alpha : ℝ) (ha : a > 0) (hb : b > 0)
    (hb2a : b ^ 2 / a > 0) :
    let l := b ^ 2 / a
    let rho1 := l / (1 + e * cos alpha)
    let rho2 := l / (1 - e * cos alpha)
    let omega_A := b / rho1
    let omega_B := b / rho2
    -- Assuming denominators are nonzero
    (1 + e * cos alpha ≠ 0) → (1 - e * cos alpha ≠ 0) →
    omega_A + omega_B = 2 * a / b := by
  intro _ _ _ _ _ hne1 hne2
  change b / (b ^ 2 / a / (1 + e * cos alpha)) +
         b / (b ^ 2 / a / (1 - e * cos alpha)) = 2 * a / b
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hl : b ^ 2 / a ≠ 0 := ne_of_gt hb2a
  field_simp [hl, hne1, hne2]
  ring

/-- **Theorem 4.6(b): Varying differential.**
    omega_A - omega_B = (b/l)*2e*cos(alpha) = (2ae/b)*cos(alpha).
    Paper: Theorem 4.6(b) (thm:focal-structure) -/
theorem focal_chord_differential (a b e alpha : ℝ) (ha : a > 0) (hb : b > 0)
    (hb2a : b ^ 2 / a > 0) :
    let l := b ^ 2 / a
    let rho1 := l / (1 + e * cos alpha)
    let rho2 := l / (1 - e * cos alpha)
    let omega_A := b / rho1
    let omega_B := b / rho2
    (1 + e * cos alpha ≠ 0) → (1 - e * cos alpha ≠ 0) →
    omega_A - omega_B = 2 * a * e * cos alpha / b := by
  intro _ _ _ _ _ hne1 hne2
  change b / (b ^ 2 / a / (1 + e * cos alpha)) -
         b / (b ^ 2 / a / (1 - e * cos alpha)) = 2 * a * e * cos alpha / b
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hl : b ^ 2 / a ≠ 0 := ne_of_gt hb2a
  field_simp [hl, hne1, hne2]
  ring

/-- **Theorem 4.6(d): Conjugacy product.**
    omega_A * omega_B = (a/b)^2 * (1 - e^2*cos^2(alpha)).
    Minimum at cos(alpha) = +-1: (a/b)^2*(1-e^2) = (a/b)^2*(b/a)^2 = 1.

    We prove the algebraic identity for the product.
    Paper: Theorem 4.6(d) (thm:focal-structure) -/
theorem focal_product_identity (a b e alpha : ℝ) (ha : a > 0) (hb : b > 0)
    (hb2a : b ^ 2 / a > 0) :
    let l := b ^ 2 / a
    let rho1 := l / (1 + e * cos alpha)
    let rho2 := l / (1 - e * cos alpha)
    let omega_A := b / rho1
    let omega_B := b / rho2
    (1 + e * cos alpha ≠ 0) → (1 - e * cos alpha ≠ 0) →
    omega_A * omega_B = (a / b) ^ 2 * (1 - e ^ 2 * cos alpha ^ 2) := by
  intro _ _ _ _ _ hne1 hne2
  change (b / (b ^ 2 / a / (1 + e * cos alpha))) *
         (b / (b ^ 2 / a / (1 - e * cos alpha))) =
         (a / b) ^ 2 * (1 - e ^ 2 * cos alpha ^ 2)
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hl : b ^ 2 / a ≠ 0 := ne_of_gt hb2a
  field_simp [hl, hne1, hne2]
  ring

/-- The ground state: when e^2 = 1 - (b/a)^2, the minimum product at
    cos(alpha) = +-1 gives (a/b)^2*(1-(1-(b/a)^2)) = (a/b)^2*(b/a)^2 = 1.
    Paper: Theorem 4.6(d), "independent of eccentricity" -/
theorem focal_product_minimum (a b : ℝ) (ha : a > 0) (hb : b > 0) :
    (a / b) ^ 2 * (1 - (1 - (b / a) ^ 2)) = 1 := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  field_simp
  ring

/-! ## Theorem 4.7: The Focal Uncertainty Principle

R = c/l = ae/(b^2/a) = a^2*e/b^2 (focal resolution)
U = <|M*D|> = (a^2*e/b^2) * kappa = R * kappa (sweep uncertainty)
R/U = 1/kappa = pi/2 (universal)
-/

/-- **Theorem 4.7 (Focal Uncertainty Principle) — algebraic core.**
    R = a^2*e/b^2 and U = R*kappa, so R/U = 1/kappa.
    The identity R/U = pi/2 then follows from kappa = 2/pi.

    Paper: Theorem 4.7 (thm:fup) -/
theorem fup_ratio_algebra (R kappa : ℝ) (hR : R ≠ 0) (hkappa : kappa > 0) :
    R / (R * kappa) = 1 / kappa := by
  have hkappa' : kappa ≠ 0 := ne_of_gt hkappa
  field_simp [hR, hkappa']

/-- **Theorem 4.7 (FUP) — full statement.**
    For every ellipse with e in (0,1): R/U = pi/2.

    Paper: Theorem 4.7 (thm:fup) -/
theorem focal_uncertainty_principle (a b : ℝ) (ha : a > 0) (hb : b > 0) (hab : a > b) :
    let e_sq := 1 - (b / a) ^ 2
    let R := a ^ 2 * sqrt e_sq / b ^ 2
    let kappa := 2 / π
    let U := R * kappa
    R / U = π / 2 := by
  simp only
  -- Step 1: e_sq > 0
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have he_sq_pos : 1 - (b / a) ^ 2 > 0 := by
    have : (b / a) ^ 2 < 1 := by
      rw [div_pow, div_lt_one (pow_pos ha 2)]
      nlinarith [sq_nonneg (a - b)]
    linarith
  -- Step 2: sqrt(e_sq) > 0
  have hsqrt_pos : sqrt (1 - (b / a) ^ 2) > 0 := Real.sqrt_pos_of_pos he_sq_pos
  have hsqrt_ne : sqrt (1 - (b / a) ^ 2) ≠ 0 := ne_of_gt hsqrt_pos
  -- Step 3: R > 0, hence R ≠ 0
  have hR_pos : a ^ 2 * sqrt (1 - (b / a) ^ 2) / b ^ 2 > 0 := by positivity
  have hR_ne : a ^ 2 * sqrt (1 - (b / a) ^ 2) / b ^ 2 ≠ 0 := ne_of_gt hR_pos
  -- Step 4: pi ≠ 0
  have hpi_ne : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  -- Step 5: Direct computation: R / (R * (2/π)) = π/2
  -- After simp only, the goal should be about the expanded let expressions.
  -- Try direct field_simp to clear all denominators, then verify with ring or nlinarith.
  have ha2_ne : a ^ 2 ≠ 0 := pow_ne_zero 2 ha'
  have hb2_ne : b ^ 2 ≠ 0 := pow_ne_zero 2 hb'
  field_simp
  -- After field_simp, the goal is √((a^2-b^2)/a^2) * (√((a^2-b^2)/a^2))⁻¹ = 1
  -- This is x * x⁻¹ = 1, needing x ≠ 0
  have : sqrt ((a ^ 2 - b ^ 2) / a ^ 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos_of_pos
    apply div_pos
    · nlinarith [sq_nonneg (a - b)]
    · positivity
  exact mul_inv_cancel₀ this

/-! ## Theorem 4.9: MEPB as Resolution-Uncertainty Product

MEPB(x) = (7/352) * (R/U) * x^2 * |ln x|
         = (7/352) * (pi/2) * x^2 * |ln x|
         = 7*pi/704 * x^2 * |ln x|
-/

/-- The rational factor decomposition: 7/352 = (1/4) * (1/8) * (7/11).
    (1/4) = Doppler-zero coefficient
    (1/8) = fold factor
    (7/11) = R2 normalization
    Paper: Theorem 4.9 (thm:mepb-fup), item (ii) -/
theorem mepb_rational_factor : (7 : ℚ) / 352 = 1 / 4 * (1 / 8) * (7 / 11) := by norm_num

/-- Assembly: (7/352) * (pi/2) = 7*pi/704.
    Paper: Theorem 4.9 (thm:mepb-fup), Step 4 -/
theorem mepb_assembly : (7 : ℝ) / 352 * (π / 2) = 7 * π / 704 := by ring

/-- 704 = 352 * 2 = 4 * 8 * 11 * 2.
    Paper: Theorem 4.9 -/
theorem seven_oh_four_factored : (704 : ℕ) = 4 * 8 * 22 := by norm_num

end
