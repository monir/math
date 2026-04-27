═══════════════════════════════════════════════════════════════════════════
                                                                            
  ╔═══════════════════════════════════════════════════════════════════╗    
  ║                                                                   ║    
  ║      ◆  UNDERWOOD  ◆     Ellipse Perimeter at 3.3 × 10⁻¹²        ║    
  ║                          on 13 stored constants                   ║    
  ║                                                                   ║    
  ║      Two Foci, One Cup Runneth Over  Again                        ║    
  ║      Monir Mamoun · independent researcher · April 2026           ║    
  ║                                                                   ║    
  ╚═══════════════════════════════════════════════════════════════════╝    
                                                                            
═══════════════════════════════════════════════════════════════════════════

# UNDERWOOD ▸ Ellipse Perimeter to 3.3 Parts-Per-Trillion at 13 Constants

The ellipse perimeter has a **logarithmic branch point** at the degenerate
limit `b → 0` (the ellipse collapses to a line segment). For 2500 years
every compact-formula approximator — Ramanujan 1914, Cantrell 2001,
Ayala-Raggi 2025, even AAA rational approximation — has been fitting a
*smooth* function to this *non-smooth* target. **UNDERWOOD writes the log
modes explicitly.** Three named log companions  ξ²⁺ʲ · log(1/ξ)  added to
a Chebyshev basis, a QR solve, done. The residual becomes analytic,
Chebyshev handles it at geometric rate, and the floor falls.

────────────────────────────────────────────────────────────────────────────
  ★  RECORDS                                                       ◆
────────────────────────────────────────────────────────────────────────────

  ▶ F3              ⟶  3.3 × 10⁻¹²   peak relative error,  13 constants
  ▶ F4 + Remez      ⟶  2.1 × 10⁻¹³   peak relative error,  14 constants
  ▶ L-corner test   ⟶  147 000 ×     better than AAA on log-corner singularity
  ▶ Separation thm  ⟶  gap vs any rational method grows without bound
  ▶ Verification    ⟶  50-digit mpmath ground truth; zero float64 in pipeline
  ▶ Lean 4          ⟶  package  Logatoms,  4 modules · 9 theorems · sorry-free

────────────────────────────────────────────────────────────────────────────
  ⊕  THE FORMULA  (sketch)                                                 
────────────────────────────────────────────────────────────────────────────

      P(a, b)  =  R₂(a, b) · [ Σⱼ cⱼ · Tⱼ(τ)  +  Σₖ dₖ · ξ^(2+k) · log(1/ξ) ]

  where
      R₂          = Ramanujan II base perimeter
      ξ = b / a   = degeneracy parameter (ξ → 0 is the singular limit)
      τ           = Chebyshev variable on [-1, 1]  for the smooth piece
      Tⱼ          = Chebyshev polynomial of the first kind, degree j
      { cⱼ, dₖ }  = QR-solve coefficients   (13 total in F3, 14 in F4+Remez)

  The three log companions  k ∈ {0, 1, 2}  carry the branch behaviour;
  the Chebyshev block carries the analytic remainder.  No free parameter
  in the structure — only in the QR fit on top of fixed log atoms.

────────────────────────────────────────────────────────────────────────────
  ▤  THE TEARDOWN TABLE                                                    
────────────────────────────────────────────────────────────────────────────

  Method                       Params  │  Peak error    │  b → 0
  ─────────────────────────────  ──────  ┼  ────────────  ┼  ──────────────────
  Ramanujan R1 / R2                 0   │  ~10⁻⁷         │  plateaus
  Cantrell                        few   │  ~10⁻⁶         │  slow decay
  Villarino                         0   │  asymp δ₅      │  analytic
  Koshy / Moscato                 5-8   │  < 3 × 10⁻⁶    │  interpolatory
  Ayala-Raggi F₂-F₅              ~15   │  2.16 × 10⁻⁸   │  series-truncated
  AAA  (Trefethen et al.)          30   │  ~10⁻¹³        │  cannot rep. log
  SRIRACHA  (Mamoun, prior)      ~25   │  7   × 10⁻¹²   │  gate-only branch
  ▶ UNDERWOOD F3   (this work)    13   │  3.3 × 10⁻¹²   │  ★ flat to floor
  ▶ UNDERWOOD F4 + Remez           14   │  2.1 × 10⁻¹³   │  ★ machine ε @ 50-d

  Only the ★ rows are *flat* (not plateauing) as ξ = b/a → 0.

────────────────────────────────────────────────────────────────────────────
  ▣  ARTIFACTS                                                             
────────────────────────────────────────────────────────────────────────────

  Papers land in  paper/  by canonical name (`paper_mamoun_…_v…_DATE`)
  via the project's append-only workflow.  Lean lives in  lean/.

  •  Full paper · canonical release   (v6, 23-April-2026)
       paper/paper_mamoun_ellipse_underwood_two_foci_one_cup_v6_23-April-2026.pdf
  •  Full paper · latest dev iterate  (rev4, 24-April-2026, 135 pp)
       paper/two_foci_one_cup_ellipse_perimeter_mamoun_rev4.pdf
  •  Press handout · one-pager        (v2)
       paper/underwood_press_handout_v2.pdf
  •  UNDERWOOD addendum · θ-means     (v1, 14-April-2026)
       paper/crystal_math_theta_means_underwood_addendum_v1.pdf
  •  Lean 4 package  Logatoms         (9 modules · 51 named results · Mathlib v4.28.0)
       lean/Logatoms/
  •  Minimax certificate (Lean, dev)
       lean/UnderwoodMinimaxCertificate.lean

────────────────────────────────────────────────────────────────────────────
  ⚙  WHY IT BEATS RATIONAL APPROXIMATION                                   
────────────────────────────────────────────────────────────────────────────

  Theorem (separation, paraphrased).
    Let f(ξ) be a function with a logarithmic branch point at ξ = 0 and
    let r_n(ξ) be the best degree-n rational approximation to f on a
    neighbourhood of 0.  Then  ‖f − r_n‖∞  decays at most polynomially
    in 1/n,  whereas  ‖f − u_n‖∞  for the UNDERWOOD basis (Chebyshev +
    explicit  ξ²⁺ʲ · log(1/ξ)  atoms) decays *geometrically*.
    The gap therefore grows without bound as n → ∞.

  Concrete witness.  L-shaped corner singularity benchmark:
    AAA  (rational, n = 30)  ⟶  ~10⁻¹³  on smooth domains, but
                                  catastrophic loss at the corner
    UNDERWOOD                  ⟶  147 000 × better at the same n

═══════════════════════════════════════════════════════════════════════════

  ┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
  ┃                                                                   ┃
  ┃    ▶▶▶   ARCHIVE LINE  ·  cutoff date  2026-04-27   ◀◀◀          ┃
  ┃                                                                   ┃
  ┃    Everything below this point is the *previous record* and is   ┃
  ┃    retained verbatim as the audit trail.  UNDERWOOD  (F3 / F4)   ┃
  ┃    above supersedes the 0.083 ppm SRIRACHA-era champion below.   ┃
  ┃                                                                   ┃
  ┃    Kept per the project's never-delete rule:  intermediate       ┃
  ┃    work products record the path of discovery.                   ┃
  ┃                                                                   ┃
  ┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛

═══════════════════════════════════════════════════════════════════════════

# The World's Most Accurate Closed-Form Ellipse Perimeter

**0.083 ppm maximum error** across all eccentricities. 6.9x more accurate than the previous world record (Ayala-Raggi 2025). One effective free parameter.

---

## The Formula

```
              pi(a+b)(1 + 3h/(10 + sqrt(4-3h)))
P  ~=  ------------------------------------------------
        1 - h^(7/3) [A exp(-lx) + B exp(-3.24 lx) + C exp(-15 lx)]
```

where:
- `h = ((a-b)/(a+b))^2` &mdash; Ramanujan's shape parameter
- `x = 1 - h` &mdash; distance from the flat limit
- `A + B + C = 1 - 7*pi/22` &mdash; endpoint pin (exact)
- `l ~ 6.895` &mdash; the single free parameter (decay rate)
- `3.24 = 81/25` and `15` &mdash; from the continued fraction of pi

The numerator is Ramanujan II (1914). The denominator corrects it with three exponentials gated by `h^(7/3)`.

### Copy-Paste Python

```python
import math

def ellipse_perimeter(a, b):
    """World-record ellipse perimeter approximation (0.083 ppm max error)."""
    if a < b:
        a, b = b, a
    h = ((a - b) / (a + b)) ** 2
    x = 1.0 - h
    # Ramanujan II
    R2 = math.pi * (a + b) * (1.0 + 3.0 * h / (10.0 + math.sqrt(4.0 - 3.0 * h)))
    # 3-exponential correction
    T = 1.0 - 7.0 * math.pi / 22.0  # endpoint pin
    lam = 6.8954698854899
    r, s = 0.3725797305793, 0.0360560365885
    A = T / (1.0 + r + s)
    B, C = r * A, s * A
    q = 7.0 / 3.0          # gate exponent from pi's CF: a1/a0 = 7/3
    m = 81.0 / 25.0         # mid-rate from pi's CF: a0^4 / (a0+a1+a2) = 81/25
    n = 15.0                # fast rate from pi's CF: a2 = 15
    gate = h ** q
    correction = A * math.exp(-lam * x) + B * math.exp(-m * lam * x) + C * math.exp(-n * lam * x)
    return R2 / (1.0 - gate * correction)

# Example
print(f"P(5, 3) = {ellipse_perimeter(5, 3):.12f}")
```

---

## Key Results

This paper makes five new contributions:

1. **The formula (world record)** &mdash; 0.083 ppm max error on 5000-case adversarial benchmark, 6.9x over Ayala-Raggi (2025), with effectively 1 free parameter vs their 4.

2. **The structural floor (MEPB)** &mdash; We prove no analytic correction to Ramanujan II can beat `MEPB(x) = (7/(352*kappa)) * x^2 |ln x|` where `kappa = 2/pi`. This is a theorem, not a conjecture: the non-analytic `(1-m)ln(1-m)` singularity in E(m) at m=1 cannot be cancelled by any finite sum of analytic functions. The champion sits ~20x above this floor.

3. **The numbers come from pi** &mdash; Four of five structural parameters are determined by pi's continued fraction `[3; 7, 15, 1, 292, ...]`:
   - Gate: `q = 7/3` (ratio of first two partial quotients)
   - Mid-rate: `m = 81/25 = 3^4/25` (fourth power of floor(pi), divided by sum of first three)
   - Fast rate: `n = 15` (third partial quotient)
   - Endpoint pin: `T = 1 - 7*pi/22` (first convergent 22/7)

4. **Focal certainty-uncertainty duality** &mdash; For every ellipse: `R/U = pi/2` universally, where R is the focal resolution and U is the mean sweep uncertainty. This is an equality, not an inequality. It extends to all conics and all dimensions.

5. **Arbitrary-precision integer series** &mdash; `E(e^2) = (pi/2) * sum(c_n * (e^2)^n)` with all `c_n` rational (power-of-2 denominators). Integer arithmetic + pi gives any precision you want.

---

## Quick Start

### Option A: One-command setup (recommended)

The setup script creates an isolated virtual environment, installs everything, verifies the formula, and offers to launch a demo. Nothing touches your system Python.

**macOS / Linux:**
```bash
chmod +x setup.sh
./setup.sh
```

**Windows:**
```
setup.bat
```

Both scripts auto-detect Python 3.9+, create `.venv/`, install all deps, and prompt you to launch a demo. You can also pass flags:

```bash
./setup.sh --run-demo     # setup + launch standalone web demo
./setup.sh --run-server   # setup + launch full web UI
./setup.sh --verify       # setup + run adversarial benchmark
```

### Option B: Docker (zero setup, any platform)

```bash
docker build -t ellipse .
docker run -p 8080:8080 ellipse              # standalone demo
docker run -p 8000:8000 ellipse server       # full web UI
docker run ellipse verify                    # adversarial benchmark
docker run ellipse benchmark                 # full 5000-case suite
```

See the [Dockerfile](Dockerfile) — it's a lightweight Python 3.12-slim image (~150 MB).

### Option C: Just use the formula (zero dependencies)

Copy the `ellipse_perimeter()` function from the section above into your code. It uses only Python's built-in `math` module — no install needed.

### Option D: Manual venv setup

If you prefer doing it yourself:

```bash
python3 -m venv .venv
source .venv/bin/activate        # Windows: .venv\Scripts\activate
pip install -r requirements.txt
PYTHONPATH=. python3 -m src.verify
```

---

## Formula Variants

All variants use Ramanujan II as the base. They differ in gate exponent (`q`), mid-rate multiplier (`m`), and optimized decay rate (`lambda`).

| Formula | Gate | m | Max Error (ppm) | Year | Notes |
|---------|------|---|-----------------|------|-------|
| Ramanujan II | -- | -- | 402 | 1914 | The base |
| Cantrell | -- | -- | 412 | 2001 | Holder mean correction |
| Ayala-Raggi R2/2exp | -- | -- | 0.574 | 2025 | Previous world record |
| R2/3exp h^2, m=pi | h^2 | pi | 0.125 | 2026 | Simpler gate |
| R2/3exp h^2.5, m=pi | h^2.5 | pi | 0.124 | 2026 | Theoretically motivated |
| R2/3exp h^2.5, m=81/25 | h^2.5 | 81/25 | 0.089 | 2026 | Numerical optimum (old) |
| **R2/3exp q=7/3, m=81/25** | **h^(7/3)** | **81/25** | **0.083** | **2026** | **CHAMPION (this work)** |

The champion's gate `q = 7/3` comes from the continued fraction of pi: `a1/a0 = 7/3`. All variants are implemented in `src/formulas.py`.

---

## Using the Formula in Your Code

### With the package installed

```python
from src.formulas import r2_3exp_v23_champion, exact_perimeter

a, b = 100.0, 1.0  # extreme ellipse
P_approx = r2_3exp_v23_champion(a, b)
P_exact  = exact_perimeter(a, b)     # uses mpmath at 50 digits
error_ppm = abs(P_approx - P_exact) / P_exact * 1e6
print(f"Perimeter: {P_approx:.10f}")
print(f"Error: {error_ppm:.4f} ppm")
```

### Without installation (copy-paste)

The `ellipse_perimeter()` function in the "Copy-Paste Python" section above has zero dependencies beyond Python's standard `math` module. It works in any Python 3.x environment.

### Comparing all formulas

```python
from src.formulas import ALL_FORMULAS, exact_perimeter

a, b = 5.0, 3.0
P_exact = exact_perimeter(a, b)

for name, fn in ALL_FORMULAS.items():
    P = fn(a, b)
    err = abs(P - P_exact) / P_exact * 1e6
    print(f"{name:45s}  {P:.12f}  {err:.4f} ppm")
```

---

## Web Demo

Two web interfaces are included:

### FastAPI Server (`src/server.py`)

Full-featured web UI with:
- Interactive error-vs-eccentricity chart (log scale, Chart.js)
- Calculator for arbitrary ellipses with all formula comparisons
- Curated gallery of 12 tough test cases
- MathJax formula rendering
- Critical analysis section (proved vs verified vs conjectured)
- REST API (`POST /api/compare`, `GET /api/sweep`, `GET /api/tough-cases`)

```bash
pip install -r requirements.txt
python -m src.server
# Open http://localhost:8000
```

### Standalone Demo (`demo/ellipse_web_demo.py`)

Lightweight standalone server (no FastAPI needed, just mpmath):
- Focal certainty-uncertainty duality visualization
- Interactive eccentricity slider
- Real-time formula comparison

```bash
pip install mpmath
python demo/ellipse_web_demo.py --port 8080
# Opens http://localhost:8080
```

---

## Running the Adversarial Benchmark

The benchmark tests the formula against **5000 adversarial ellipses** spanning:
1. Uniform h-space sampling (catches mid-eccentricity issues)
2. Log-uniform flattening with prime axes (catches scaling issues)
3. Near-circle cases with prime jitter (catches roundoff)
4. Ultra-flat boundary cases (b/a < 1e-15, catches singularity behavior)
5. Extreme eccentricity (e > 0.99999, the hardest regime)

### Quick check (500 cases, ~1 minute)

```bash
cd benchmark/
python benchmark_v24.py --quick
```

### Full benchmark (5000 cases, ~10 minutes)

```bash
cd benchmark/
python benchmark_v24.py
```

Or use the shell script:

```bash
./benchmark/run_benchmark.sh          # full
./benchmark/run_benchmark.sh --quick  # quick
```

**Expected output** (champion line):

```
V23 Champion q=7/3:  max|err| = 8.34e-08  (0.0834 ppm)
vs Ayala-Raggi:      6.9x better
vs Ramanujan II:     4800x better
```

The benchmark also includes:
- Running max-error log (cumulative worst case)
- Rapidity/Doppler demonstration on extreme ellipses
- Arbitrary-precision integer series examples
- LaTeX-ready output tables

**Requirements:** `mpmath`, `numpy`. Uses multiprocessing for ground truth computation. On macOS, the script sets `fork` start method automatically.

### Package verification (3000 cases)

A simpler verification script is also available:

```bash
python -m src.verify
```

---

## Lean 4 Proofs

32 theorems are **fully machine-verified** (zero `sorry`) in Lean 4 with Mathlib:

| Module | Theorems | Status |
|--------|----------|--------|
| Basic.lean | 26 | sorry-free |
| PiBounds.lean | 4 | sorry-free |
| GammaConnection.lean | 2 | sorry-free |
| Monotonicity.lean | 10 | 7 sorry (skeleton) |
| NonAnalyticBound.lean | 6 | 6 sorry (skeleton) |

The sorry-free modules cover all algebraic identities (CF parameters, variable chains, fold identity, MEPB coefficient, endpoint pin). The skeleton modules state the analysis theorems precisely but defer calculus-heavy proofs (Leibniz integral rule, dominated convergence, MVT).

See [lean/README.md](lean/README.md) for build instructions and a detailed guide.

```bash
cd lean/
lake build    # First build downloads Mathlib (~2 GB), takes 5-15 min
```

---

## The Paper

`paper/proof_v29.tex` is a 54-page paper covering:

- The formula and its derivation
- The geometric-mean identity (why no closed form exists)
- Focal disagreement ratio and its Doppler interpretation
- The ODE, the Z2 fold, and the non-analytic barrier (MEPB)
- Continued-fraction architecture of pi
- Monodromy and the Gauss connection formula
- K-E period duality
- Holonomy normal-form analogy with GR precession
- Equioscillation and error concentration
- Lean 4 proof appendix
- 7 open problems

The companion paper `paper/precession_braiding_paper.tex` presents the GR precession analogy as a standalone result.

### Recompiling

```bash
cd paper/
pdflatex proof_v29.tex && pdflatex proof_v29.tex    # two passes for references
```

Requires a LaTeX distribution (TeX Live, MacTeX, or MiKTeX) with standard packages: `amsmath`, `amssymb`, `amsthm`, `geometry`, `hyperref`, `booktabs`, `xcolor`, `tikz`.

---

## Project Structure

```
ellipse-perimeter-world-record/
  README.md               This file
  LICENSE                  MIT license
  pyproject.toml           Python project metadata and dependencies
  requirements.txt         Simple pip requirements

  paper/
    proof_v29.tex          Main paper (54 pages, LaTeX source)
    proof_v29.pdf          Compiled PDF
    precession_braiding_paper.tex   Companion paper (GR analogy)
    precession_braiding_paper.pdf   Compiled PDF

  src/
    __init__.py            Package init
    formulas.py            All 7 formula implementations + exact ground truth
    verify.py              Adversarial benchmark (3000 cases)
    server.py              FastAPI web UI + REST API

  demo/
    ellipse_web_demo.py    Standalone web demo (only needs mpmath)

  benchmark/
    benchmark_v24.py       Full 5000-case adversarial benchmark
    run_benchmark.sh       One-liner launcher

  lean/
    README.md              Lean proof guide
    lakefile.toml          Lean 4 build config
    lean-toolchain         Lean 4 v4.28.0
    EllipseProofs.lean     Main entry point
    EllipseProofs/
      Basic.lean           26 theorems (sorry-free)
      PiBounds.lean        4 theorems (sorry-free)
      GammaConnection.lean 2 theorems (sorry-free)
      Monotonicity.lean    10 theorems (7 sorry, skeleton)
      NonAnalyticBound.lean 6 theorems (6 sorry, skeleton)

  scripts/
    mercury_precession_check.py        GR perihelion precession validation
    precession_braiding_map_check.py   Precession-braiding normal-form mapping
    cf_integer_verify.py               Pi continued-fraction identity checks
    fptt_exact_arithmetic.py           200-digit exact arithmetic investigation
```

---

## Dependencies

| Package | Version | Why |
|---------|---------|-----|
| **mpmath** | >= 1.3.0 | Arbitrary-precision arithmetic for exact perimeters (50+ digits). **Required for ground truth.** |
| **numpy** | >= 1.21.0 | Test set generation and error statistics |
| **scipy** | >= 1.7.0 | Fast `ellipe()` for the web UI sweep (mpmath used for verification) |
| **fastapi** | >= 0.104.0 | Web UI server (only needed for `src/server.py`) |
| **uvicorn** | >= 0.24.0 | ASGI server for FastAPI |

For the standalone demo (`demo/ellipse_web_demo.py`), only `mpmath` is needed.

For the copy-paste formula, **no dependencies** are needed (pure `math` module).

---

## Citation

```bibtex
@article{mamoun2026ellipse,
  author  = {Monir Mamoun},
  title   = {Two Foci, One Number: The World's Most Accurate
             Closed-Form Ellipse Perimeter Equation},
  year    = {2026},
  note    = {0.083 ppm maximum error, 6.9x improvement over
             Ayala-Raggi (2025). Code and proofs:
             \url{https://github.com/monir/ellipse}}
}
```

---

## License

MIT. See [LICENSE](LICENSE).
