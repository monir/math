/-
  AnalysisBridges/TaylorBounds.lean

  Thin wrappers around Mathlib's Taylor expansion and asymptotics API,
  providing ready-to-instantiate templates for analytic-boundary proofs.

  Vendored from AnalysisBridges v0.1.0 (2026-02-26) to eliminate
  external path dependency.  Only Mathlib ≥ v4.28.0 is required.
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Taylor

open Filter Set
open scoped Topology

namespace AnalysisBridges

/-- Analytic power series control Taylor remainder in `IsBigO` form. -/
theorem analytic_taylor_isBigO {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ} {x : ℝ}
    (hf : HasFPowerSeriesAt f p x) (n : ℕ) :
    (fun y : ℝ => f (x + y) - p.partialSum n y) =O[𝓝 0] fun y : ℝ => ‖y‖ ^ n := by
  simpa using hf.isBigO_sub_partialSum_pow n

/-- Lagrange-form remainder theorem (ready to instantiate in concrete problems). -/
theorem taylor_lagrange_remainder {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ x' ∈ Ioo x₀ x, f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x₀) ^ (n + 1) /
        Nat.factorial (n + 1) :=
  taylor_mean_remainder_lagrange hx hf hf'

/-- Explicit quadratic form of `taylorWithinEval` (order `2`) on `ℝ → ℝ`. -/
theorem taylorWithinEval_two (f : ℝ → ℝ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f 2 s x₀ x =
      f x₀ + derivWithin f s x₀ * (x - x₀) +
        (((2 : ℝ)⁻¹) * iteratedDerivWithin 2 f s x₀) * (x - x₀) ^ 2 := by
  rw [taylor_within_apply]
  simp [Finset.sum_range_succ, iteratedDerivWithin_one, add_assoc, add_comm, mul_left_comm,
    mul_comm]

/-- Promote an `O(‖x‖^3)` remainder near zero to `o(‖x‖^2)`. -/
theorem isBigO_norm_pow_three_to_isLittleO_norm_pow_two {r : ℝ → ℝ}
    (hO : r =O[𝓝 0] fun x : ℝ => ‖x‖ ^ 3) :
    r =o[𝓝 0] fun x : ℝ => ‖x‖ ^ 2 :=
  hO.trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_norm_pow (m := 2) (n := 3) (by decide))

/-- Local quadratic Taylor template extracted from analyticity at a point. -/
theorem analytic_taylor2_local
    {f : ℝ → ℝ} {x₀ : ℝ} (hf : AnalyticAt ℝ f x₀) :
    ∃ r > 0,
      (fun x : ℝ => f x - taylorWithinEval f 2 (Icc (x₀ - r) (x₀ + r)) x₀ x)
        =o[𝓝[Icc (x₀ - r) (x₀ + r)] x₀] fun x : ℝ => (x - x₀) ^ 2 := by
  rcases hf.exists_ball_analyticOnNhd with ⟨R, hRpos, hRanalytic⟩
  refine ⟨R / 2, by linarith, ?_⟩
  let s : Set ℝ := Icc (x₀ - R / 2) (x₀ + R / 2)
  have hs_convex : Convex ℝ s := by
    simpa [s] using convex_Icc (x₀ - R / 2) (x₀ + R / 2)
  have hx₀s : x₀ ∈ s := by
    constructor <;> linarith
  have hs_subset_ball : s ⊆ Metric.ball x₀ R := by
    intro x hx
    simp only [Metric.mem_ball, Real.dist_eq]
    have habs : |x - x₀| ≤ R / 2 := by
      refine abs_le.2 ?_
      constructor <;> linarith [hx.1, hx.2]
    exact lt_of_le_of_lt habs (by linarith [hRpos])
  have hcont_ball : ContDiffOn ℝ 2 f (Metric.ball x₀ R) :=
    hRanalytic.contDiffOn_of_completeSpace (n := 2)
  have hcont_s : ContDiffOn ℝ 2 f s := hcont_ball.mono hs_subset_ball
  have hTaylor :
      (fun x : ℝ => f x - taylorWithinEval f 2 s x₀ x)
        =o[𝓝[s] x₀] fun x : ℝ => (x - x₀) ^ 2 := by
    exact taylor_isLittleO hs_convex hx₀s hcont_s
  simpa [s] using hTaylor

end AnalysisBridges
