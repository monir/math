# Snow Crystal Peer Review Notes — 2026-04-14

Scope reviewed:
- `265ae7f2b23bd0421baf2cd9ea7e2b5c68332409` (`2026-04-14 07:37:50 -0400`): `snow_crystal_theory_unified_v1.tex`
- Current uncommitted follow-up in `ellipse/active/lean/SnowCrystalProofs.lean`
- Current uncommitted `ellipse/active/lean/SnowCrystalProofs/ThetaMean.lean`

## Findings

### [P0] The latest Lean follow-up breaks the advertised build outright

Files:
- `ellipse/active/lean/SnowCrystalProofs.lean:50`
- `ellipse/active/lean/SnowCrystalProofs/ThetaMean.lean:45`

`SnowCrystalProofs.lean` now imports `SnowCrystalProofs.ThetaMean`, but `ThetaMean.lean` imports `Mathlib.Algebra.BigOperators.Basic`, which does not exist in the configured toolchain. Running `lake build SnowCrystalProofs` from `ellipse/active/lean/` fails with:

```text
error: no such file or directory
file: .../Mathlib/Algebra/BigOperators/Basic.lean
error: SnowCrystalProofs/ThetaMean.lean: bad import 'Mathlib.Algebra.BigOperators.Basic'
error: SnowCrystalProofs.lean: bad import 'SnowCrystalProofs.ThetaMean'
```

This means the current "latest snow crystal work" is not reproducible even at the build level, and it directly invalidates the same-day monograph's claim that the library "builds in ~40 s".

### [P1] The monograph's `T_c` derivation is numerically wrong and confuses absolute temperature with undercooling

File:
- `ellipse/active/paper/snow_crystal_theory_unified_v1.tex:190-221`

The paper states:

- `E_HB = 22.6 meV`
- `T_c = E_HB / k_B = 263 K`
- and then equates that to "`-14.4 °C undercooling`"

Those numbers do not agree. Using the paper's own inputs:

- `182.7 cm^-1 -> 22.6519 meV`
- `22.6519 meV / 0.0861733 meV/K = 262.86 K`
- `262.86 K = -10.29 °C`
- the corresponding undercooling is `273.15 - 262.86 = 10.29 K`, not `14.4 K`

There is also a semantic error: Eq. (morphology) uses `r(ΔT)` with `ΔT` as undercooling, but `E_HB / k_B` gives an absolute temperature. If this derivation is supposed to feed the morphology equation, the paper needs `ΔT_c = T_m - E_HB/k_B`, not `T_c = E_HB/k_B`.

As written, the headline claim that the dendrite resonance temperature is "derived from the splitting microphysics" is not defensible.

### [P1] `ThetaMean` claims a monotonicity proof, but the theorem body proves only `True`

File:
- `ellipse/active/lean/SnowCrystalProofs/ThetaMean.lean:22-24`
- `ellipse/active/lean/SnowCrystalProofs/ThetaMean.lean:28-31`
- `ellipse/active/lean/SnowCrystalProofs/ThetaMean.lean:137-141`

The module header says:

- `P3 (Monotonicity)` is a formalized property
- "`P3 is proved for the partial-sum approximation`"

But the actual theorem is:

```lean
theorem thetaMean_monotone_reverse_partial ... : True := by
  trivial
```

That is not a monotonicity proof. It is a placeholder wrapped in theorem-shaped syntax. Shipping this under the `SnowCrystalProofs` namespace makes the proof status look materially stronger than it is.

### [P1] `ThetaMean` injects axioms into the proof tree, so it is not mechanically verified in the way the surrounding prose implies

File:
- `ellipse/active/lean/SnowCrystalProofs/ThetaMean.lean:30-31`
- `ellipse/active/lean/SnowCrystalProofs/ThetaMean.lean:166-181`

The new module introduces at least two axioms:

- `gaussian_integral_dim2`
- `thetaMean_N_asymptotic_equipartition`

That is a valid staging technique while formalization is incomplete, but then it must be described as assumed, not kernel-verified. Importing this module into the top-level `SnowCrystalProofs` library blurs the boundary between proved results and postulated ones.

If this module is meant to support any paper-level statement about "mechanically checked" snow crystal mathematics, the current wording is overstated.

### [P2] The top-level Lean entrypoint now contradicts itself about what is formalized

File:
- `ellipse/active/lean/SnowCrystalProofs.lean:11-26`
- `ellipse/active/lean/SnowCrystalProofs.lean:36-50`

The file header still says only six theorems are formalized and the rest are "verified in the Python audit but not yet formalized in Lean". The same file then imports the later theorem modules, and now also imports `ThetaMean`.

That leaves a reviewer unable to tell which status is real:

- six formalized
- fourteen formalized
- or fourteen plus an unfinished fifteenth add-on that currently breaks the build

At minimum, the module-level status summary needs to be brought back into sync before any paper cites this library as evidence.

## Verification performed

Commands run:

```bash
git log --since='2026-04-14 00:00' --until='2026-04-14 23:59:59' --all --date=iso --pretty=format:'%H%x09%ad%x09%s' -- ellipse/active/paper ellipse/active/research_findings ellipse/active/research_scripts

lake build SnowCrystalProofs

python3 - <<'PY'
from math import *
cm_to_meV = 0.12398419843320026
omega = 182.7
E = omega * cm_to_meV
kB_meV = 0.08617333262145
print(E, E / kB_meV, E / kB_meV - 273.15, 273.15 - E / kB_meV)
PY
```

Bottom line: the newest snow crystal work today is not just rough around the edges; part of it is internally inconsistent, and the latest Lean follow-up currently does not build.

## Second pass: phase-field / 3D / twin-angle review

### [P0] The paper claims a 3D implementation, but the repo only contains a 2D solver plus a 3D outline

Files:
- `ellipse/active/paper/snow_crystal_theory_unified_v1.tex:65`
- `ellipse/active/paper/snow_crystal_theory_unified_v1.tex:80`
- `ellipse/active/paper/snow_crystal_theory_unified_v1.tex:545-549`
- `ellipse/active/research_scripts/snow_crystal_phase_field_v3.py:13-18`
- `ellipse/active/research_scripts/snow_crystal_3d_growth_demo_v1.py:3-6`
- `ellipse/active/research_scripts/snow_crystal_3d_growth_demo_v1.py:130-181`

The monograph repeatedly says it "demonstrates 3D phase-field growth". The reproducibility section says something else:

- `snow_crystal_phase_field_v3.py` is explicitly `2D Nakaya`
- `snow_crystal_3d_growth_demo_v1.py` is explicitly a `3D growth model outline`

That is not a nit. It is the difference between "we implemented a 3D PDE" and "we wrote down a sketch for one". The repo currently supports the latter, not the former.

### [P1] The advertised "full Kobayashi" anisotropic PDE is only partially implemented, and the browser demo skips the correction altogether

Files:
- `ellipse/active/paper/snow_crystal_theory_unified_v1.tex:355-359`
- `ellipse/active/research_scripts/snow_crystal_phase_field_v3.py:137-150`
- `ellipse/active/demo/snowflake_nakaya_2d.html:353-357`

The paper writes the anisotropic term as

```text
∇·(ε²∇φ) + ∂x[ε ε' ∂yφ] - ∂y[ε ε' ∂xφ]
```

But the Python solver immediately downgrades the first term:

```python
# The first part is approximately ε²·∇²φ
rhs = eps**2 * lap
```

That drops the `∇(ε²)·∇φ` contribution when `ε = ε(θ(∇φ))`, so it is not the full operator the paper claims.

The browser demo is looser still. It says:

```text
// Full Kobayashi anisotropy correction: approximated via ...
// Skip for speed — the dominant anisotropy comes from eps²
```

So the public "living PDE" demo omits the cross-gradient correction it advertises. The paper should stop calling this a full implementation.

### [P1] The "derived α(T)" claim is false in the 3D code path; the baseline growth rate is injected empirically

Files:
- `ellipse/active/paper/snow_crystal_theory_unified_v1.tex:585`
- `ellipse/active/research_scripts/snow_crystal_3d_growth_demo_v1.py:133-151`

The paper says:

```text
We provide derived α(T) from the v4 chain.
```

But the 3D demo does:

```python
alpha_baseline = 0.01 * sigma  # empirical baseline
alpha_prism/alpha_basal = 10**r(T)
```

That means only the ratio is coming from `r(T)`. The absolute scale is still a hand-set empirical constant, and intermediate faces are just returned as the same baseline. This is not "derived α(T)" in any serious sense.

### [P1] The twin-reduction prediction in the paper contradicts the dedicated twin script

Files:
- `ellipse/active/paper/snow_crystal_theory_unified_v1.tex:509-510`
- `ellipse/active/research_scripts/snow_crystal_v4_twin.py:96-145`
- `ellipse/active/research_scripts/outputs/snow_crystal_v4_twin.output:13-32`

The paper says:

```text
10% twin volume should reduce Δ_split by 0.88 cm⁻¹
```

The actual twin script says something radically different. Its saved output gives:

- `f = 0.10 -> observed_split = 8.8091 cm⁻¹`
- shift from bare `+0.0091 cm⁻¹`
- best-fit twin fraction for the 8.8 cm⁻¹ observation is `0.00%`

That is not a rounding difference. It flips the sign and changes the magnitude by roughly two orders of magnitude. The paper's stated prediction is not supported by the repo's own twin calculation.

### [P1] The 3D demo prints a catastrophic mismatch and then declares success anyway

Files:
- `ellipse/active/research_scripts/snow_crystal_3d_growth_demo_v1.py:123-125`
- `ellipse/active/research_scripts/outputs/snow_crystal_3d_growth_demo_v1.output:31-36`
- `ellipse/active/research_scripts/outputs/snow_crystal_3d_growth_demo_v1.json`

The script computes:

- `Tc_derived_K = 262.871`
- `Tc_paper_K = 14.4`
- `match_quality_pct = -1625.49`

and then prints:

```text
→ v4's ω values reproduce the paper's Tc to <2% error ✓
```

That is not a subtle scientific disagreement. That is a plain logic failure in the demo narrative.

### [P2] The repo already contains an internal peer review saying the twin-angle/Heisenberg story is speculative

File:
- `ellipse/active/research_scripts/snow_crystal_theta_morphology_v2_peer_review.py:153-174`

That internal review states:

- the twin-angle formula is "just trigonometry"
- the Atkin-Lehner connection has "NO actual map"
- the "Heisenberg correction" is "just a guess"
- real status: "AESTHETIC ANALOGY, not theorem"

So even inside this codebase there is written evidence that the paper's twin-angle rhetoric is oversold.

## 3D / MHD reality check

If this work wants to talk about `vortex precession`, `3D growth`, or any field-theoretic transport story, the missing governing equations are the real issue.

What is actually implemented:

- a scalar 2D phase field `φ(x,y,t)`
- a scalar diffusive field `u(x,y,t)`
- algebraic anisotropy through `ε(θ)` and a hand-chosen forcing term

What is **not** implemented anywhere in the paper/code path reviewed here:

- mass continuity:
  `∂_t ρ + ∇·(ρ v) = 0`
- momentum balance:
  `ρ(∂_t v + v·∇v) = -∇p + μ∇²v + f`
- vorticity transport:
  `∂_t ω = ∇×(v×ω) + ν∇²ω + ...`
- Stefan / interface energy balance in a sharp-interface sense
- any magnetic field equation whatsoever:
  `∂_t B = ∇×(v×B - η∇×B)`
- solenoidal constraint:
  `∇·B = 0`
- Lorentz-force coupling:
  `J×B`, with `J = μ₀^{-1}∇×B`

That means the work is not "getting the 3D MHD formulas wrong". It is not writing them down in the first place. The current implementation is a 2D scalar phase-field toy with fitted/hand-injected closures. Calling the twin-angle story "vortex precession" or the demo "3D growth" does not upgrade it into a 3D transport theory.

## Additional verification

Commands and artifacts checked in this second pass:

```bash
python3 ellipse/active/research_scripts/snow_crystal_v4_twin.py

nl -ba ellipse/active/research_scripts/outputs/snow_crystal_3d_growth_demo_v1.output | sed -n '23,36p'

rg -n "continuity|induction|Lorentz|magnetic|vorticity|velocity|Navier|Stokes|pressure"
   ellipse/active/research_scripts/snow_crystal_3d_growth_demo_v1.py
   ellipse/active/research_scripts/snow_crystal_phase_field_v3.py
   ellipse/active/paper/snow_crystal_theory_unified_v1.tex
```

The last search returned no hits in the reviewed files. That matches the core review point: the paper uses 3D/vortex language without supplying the corresponding field equations.
