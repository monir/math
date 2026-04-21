# Snow Crystal & ZBU Research

Mathematical theory of snow crystal formation, habit diagrams, and the
(Z, B, U) self-adjoint triple framework.

## Papers

| File | Description |
|------|-------------|
| `crystal_math_theta_means_part1_v2` | Crystal Math & Theta Means — Part I (rigorous framework) |
| `crystal_math_theta_means_part2_v4` | Part II — Zipularity, DNA strands, Galois structure |
| `crystal_math_theta_means_part3_v2` | Part III — Phase field, logatomic bridge |
| `crystal_math_theta_means_underwood_addendum_v1` | Underwood basis addendum |
| `snow_crystal_splitting_v2` | Snow crystal splitting: 8.94 cm⁻¹, 15 theorems (Paper IV) |
| `snow_crystal_theory_unified_v2` | Unified grand theory: 9/9 habit, vortex-prime twinning |
| `how_to_make_a_snowflake_v3` | Accessible derivation of snow crystal habit |
| `how_to_make_a_snowflake_siam_v1` | SIAM-formatted version |
| `how_to_make_ice_v1` | Ice Ih structure from first principles |

Each paper ships with its LaTeX source (`.tex`) and compiled PDF.

## ZBU Framework

The **(Z, B, U) self-adjoint triple** (Apr 2026):
- **Z** — bizipular operator carrying Z[ω]+δ = c/8 + 8 water species
- **B** — C₆ᵥ irrep dual (basal/prism face selector)
- **U** — UNDERWOOD log-ladder connector

Key results: H5 closes Tᶜ_basal to −5.16°C (0.56°C residual); d_QLL = 4·ξ;
26/26 physics tests pass. See `notes/SNOW_CRYSTAL_ZBU_TRIPLE_COMPLETE.md`.

## Directory Layout

```
papers/      — latest PDF + TeX for each paper series
notes/       — research findings, ZBU status, peer reviews
lean/        — Lean 4 machine-verified proofs (SnowCrystalProofs)
scripts/     — Python solvers (ZBU multiphase, Nakaya simulator, zipularity scan)
```

## Publishing Flow

Research workspace → `ellipse/active/paper/` (TeX drafts)
→ `ellipse/release/paper/paper_mamoun_*_DATE.pdf` (dated release)
→ `monir/math/snowcrystal/papers/` (this directory, clean filenames, latest only)

To update: copy the new dated PDF/TeX from `ellipse/release/paper/` here,
strip the date suffix, and push.
