/-
  SnowCrystalProofs
  ===================
  Top-level entry point for the snow-crystal Lean library.

  This library holds Lean formalizations for the v4 proof-level audit
  (research_scripts/snow_crystal_v4_proof_v3.py) that backs the
  8.94 ± 0.46 cm⁻¹ prediction for Ice Ih's basal/prism face
  splitting, plus (as of 2026-04-14) a theta-mean module for the
  "Crystal Math and Theta Means" paper sequence.

  ─────────────────────────────────────────────────────────────────
  PROOF STATUS (revised 2026-04-14 after peer review)
  ─────────────────────────────────────────────────────────────────

  Of the 15 theorems in the v3 audit, 14 have corresponding modules
  in this library with varying proof completeness:

    T1  — C₆ᵥ Great Orthogonality            (C6vOrthogonality.lean)
    T2  — (2+2) cluster = E₁ ⊕ E₂            (ClusterDecomposition.lean)
    T3  — Hexagonal factor (16-4√3)/13        (HexagonalFactor.lean)
    T4  — Poincaré-Hopf on T²                 (PoincareHopf.lean)
    T5  — Acoustic sum rule                   (AcousticSumRule.lean)
    T6/T13 — Lyddane-Sachs-Teller            (LyddaneSachsTeller.lean)
    T7  — Eigenvector orthogonality          (EigenvectorOrthogonality.lean)
    T8  — cos(π/6) = √3/2                    (CosPiOverSix.lean)
    T9  — Tensor E₁⊗E₂ decomposition         (TensorE1E2.lean)
    T10 — 7/10 best rational                  (BestRational.lean)
    T11 — Morse inequalities                  (MorseInequalities.lean)
    T12 — Gauge invariance                    (GaugeInvariance.lean)
    T14 — Variational bound                   (VariationalBound.lean)
    T15 — QHA quartic bound                   (QhaQuarticBound.lean)

  The exact mix of sorry-free proofs, axiom-backed proofs, and
  partial proofs varies by module.  Individual modules carry their
  own honest-status headers.  Do not read this list as "all 14 are
  kernel-verified" without checking each module.

  ─────────────────────────────────────────────────────────────────
  ADD-ON (2026-04-14): theta-mean framework
  ─────────────────────────────────────────────────────────────────

    ThetaMean.lean — definitions + P1 idempotency (proved);
                     P2, P3 stated in paper, NOT Lean-proved;
                     P4 axiomatized with explicit gaussian-integral
                     axiom.  See its header for honest details.

  Companion documents:
    - research_scripts/snow_crystal_v4_proof_v3.py — v4 full audit
    - research_findings/HEXAGONAL_RENORMALIZATION_PROGRAM_2026-04-12.md
    - research_findings/SNOWFLAKE_GRAND_THEORY.md
    - research_findings/SNOWCRYSTAL_PEER_REVIEW_2026-04-14.md
      (peer-review findings addressed in this revision)

  Registered: 2026-04-13.  Revised: 2026-04-14 (peer-review pass).
-/
import SnowCrystalProofs.HexagonalFactor
import SnowCrystalProofs.PoincareHopf
import SnowCrystalProofs.BestRational
import SnowCrystalProofs.C6vOrthogonality
import SnowCrystalProofs.ClusterDecomposition
import SnowCrystalProofs.LyddaneSachsTeller
import SnowCrystalProofs.AcousticSumRule
import SnowCrystalProofs.TensorE1E2
import SnowCrystalProofs.CosPiOverSix
import SnowCrystalProofs.EigenvectorOrthogonality
import SnowCrystalProofs.MorseInequalities
import SnowCrystalProofs.GaugeInvariance
import SnowCrystalProofs.VariationalBound
import SnowCrystalProofs.QhaQuarticBound
import SnowCrystalProofs.ThetaMean
import SnowCrystalProofs.CrystalMathDerivations
import SnowCrystalProofs.LipowskyPuckering
