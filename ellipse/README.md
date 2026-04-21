# The World's Most Accurate Closed-Form Ellipse Perimeter

**0.007 ppb maximum error** (7 parts per *trillion*) across all eccentricities. Verified at 300 decimal digits. **Below the naive pointwise MEPB floor** — the gate `q = 11.82` suppresses correction where that pointwise bound peaks and reallocates capacity to the high-eccentricity tail.

---

## Two Formulas, Two Use Cases

### The Practical Formula (0.083 ppm -- better than any prior work)

A single equation you can copy-paste anywhere. Three exponentials, one free parameter, all structural constants derived from the continued fraction of pi.

```
              pi(a+b)(1 + 3h/(10 + sqrt(4-3h)))
P  ~=  ------------------------------------------------
        1 - h^(7/3) [A exp(-lx) + B exp(-3.24 lx) + C exp(-15 lx)]
```

where `h = ((a-b)/(a+b))^2`, `x = 1 - h`, `l ~ 6.895`, and `A + B + C = 1 - 7*pi/22`.

### The Grand Champion (0.007 ppb -- 7 parts per trillion)

A convergent tower through `R6`, matched to 25 Taylor coefficients of the exact series and corrected by 16 exponentials + 3 log-enriched terms with continuously optimized rates. Verified at 300 digits.

The formula is fully written out in the [paper](paper/paper_mamoun_ellipse_perimeter_v1_19-March-2026.pdf) (Equation 1, boxed).

---

## Copy-Paste Python

### Practical formula (0.083 ppm, zero dependencies)

```python
import math

def ellipse_perimeter(a, b):
    """World-record practical ellipse perimeter (0.083 ppm max error).
    Uses only Python's math module -- no install needed."""
    if a < b:
        a, b = b, a
    h = ((a - b) / (a + b)) ** 2
    x = 1.0 - h
    R2 = math.pi * (a + b) * (1.0 + 3.0 * h / (10.0 + math.sqrt(4.0 - 3.0 * h)))
    T = 1.0 - 7.0 * math.pi / 22.0
    lam = 6.8954698854899
    r, s = 0.3725797305793, 0.0360560365885
    A = T / (1.0 + r + s)
    B, C = r * A, s * A
    gate = h ** (7.0 / 3.0)
    corr = A * math.exp(-lam * x) + B * math.exp(-3.24 * lam * x) + C * math.exp(-15 * lam * x)
    return R2 / (1.0 - gate * corr)

print(f"P(5, 3) = {ellipse_perimeter(5, 3):.12f}")
```

### Grand champion — R6+16exp+3log SCOR (0.007 ppb, requires `scipy`)

```python
from src.formulas import r6_scor_champion, exact_perimeter

a, b = 100.0, 1.0  # extreme ellipse
P_approx = r6_scor_champion(a, b)
P_exact  = exact_perimeter(a, b)
error_ppb = abs(P_approx - P_exact) / P_exact * 1e9
print(f"Perimeter: {P_approx:.15f}")
print(f"Error: {error_ppb:.4f} ppb")
```

---

## Key Results

| Formula | Base | Exp+Log | Max Error | Year |
|---------|------|---------|-----------|------|
| Ramanujan II | R2 | 0 | 402 ppm | 1914 |
| Ayala-Rendon | R2 | 2 | 0.574 ppm | 2025 |
| Mamoun R2/3exp | R2 | 3 | 0.083 ppm | 2026 |
| Mamoun R3+2exp+1log | R3 | 2+1 | 34 ppb | 2026 |
| Mamoun R5+3exp+3log | R5 | 3+3 | 2.3 ppb | 2026 |
| Mamoun R3+4exp+3log | R3 | 4+3 | 0.67 ppb | 2026 |
| Mamoun R5+6exp+3log | R5 | 6+3 | 0.093 ppb | 2026 |
| **Mamoun R6+16exp+3log** | **R6** | **16+3** | **0.007 ppb** | **2026** |

The paper establishes five structural results:

1. **The convergent tower** -- Each level Rk adds 5 Taylor coefficients via constrained Pade approximants, pinned to successive convergents of pi (22/7, 355/113, 103993/33102, ...).

2. **The structural floor (MEPB)** -- The naive pointwise barrier is `MEPB(x) = (7/352)(R/U) x^2 |ln x|`. The R6+16exp+3log SCOR champion falls far below that curve because the logarithmic enrichment terms absorb the singularity directly, and the gate suppresses correction exactly where the pointwise barrier peaks.

3. **The numbers come from pi** -- All structural parameters derive from pi's continued fraction `[3; 7, 15, 1, 292, ...]`: gate `q = 7/3`, rates `m = 81/25`, `n = 15`, endpoint pin `T = 1 - 7pi/22`.

4. **Focal certainty-uncertainty duality** -- `R/U = pi/2` universally for every ellipse, where R is the focal resolution and U is the mean sweep uncertainty.

5. **VARPRO separation** -- For fixed rates, the optimal coefficients solve a linear Chebyshev problem, reducing (N+2)-dimensional optimization to a 2D search over (lambda, q).

---

## Quick Start

### Option A: One-command setup (macOS / Linux)

```bash
chmod +x setup.sh && ./setup.sh
```

Auto-detects Python 3.9+, creates `.venv/`, installs deps, and offers to launch a demo.

```bash
./setup.sh --run-demo     # setup + launch standalone web demo
./setup.sh --run-server   # setup + launch full web UI
./setup.sh --verify       # setup + run adversarial benchmark
```

### Option B: Just use the formula

Copy the `ellipse_perimeter()` function above. Zero dependencies.

### Option C: Manual venv

```bash
python3 -m venv .venv
source .venv/bin/activate        # Windows: .venv\Scripts\activate
pip install -r requirements.txt
PYTHONPATH=. python3 -m src.verify
```

---

## Web Demo

### Static Demo (`demo/index.html`)

Open `demo/index.html` directly in any browser -- no server needed. All computation runs client-side in JavaScript. The published copy is at [monir.github.io/ellipse](https://monir.github.io/ellipse/).

Features:
- Interactive eccentricity slider
- All 10 formulas compared in real time
- Error-vs-eccentricity landscape
- Signed error curves
- Focal certainty-uncertainty duality visualization

### FastAPI Server (`src/server.py`)

Full web UI with REST API:

```bash
pip install -r requirements.txt
python -m src.server
# Open http://localhost:8000
```

---

## Lean 4 Proofs

Formalization in Lean 4 with Mathlib. The release tree contains **28 modules**. The arithmetic/combinatorial core is largely sorry-free; several analysis and transfer modules still use explicitly marked axioms or pending plumbing.

| Module | Lines | Module | Lines |
|--------|-------|--------|-------|
| Basic | 288 | CFCompositor | 379 |
| PiBounds | 47 | CFIdentities | 192 |
| GammaConnection | 40 | CFMatrixChain | 759 |
| Monotonicity | 577 | CFSpectral | 139 |
| NonAnalyticBound | 312 | CFWorpitzky | 170 |
| FocalGeometry | 371 | CFArithmetic | 260 |
| Monodromy | 957 | CFInstances | 1942 |
| Optimality | 212 | CFQPairs | 349 |
| LittlewoodObstruction | 123 | CFReduction | 282 |
| LittlewoodCoupling | 266 | CubicCuff | 177 |
| DenjoyKoksma | 249 | FranelConnection | 321 |
| FourierDenjoyKoksma | 258 | GaussCFMinimal | 249 |
| ToricLittlewood | 501 | MatlibCFBridge | 147 |
| KinematicChain | 280 | MEPBDuality | 296 |

### Tower Hierarchy (world records at each level)

| Level | Pinned to | Budget T_k | Exp | Peak Error |
|-------|-----------|-----------|-----|-----------|
| R2 | 22/7 | 4.0×10⁻⁴ | 3 | 0.083 ppm |
| R3 | 355/113 | 8.5×10⁻⁸ | 15 | 1.43 ppb |
| R4 | 103993/33102 | 1.8×10⁻¹⁰ | 20 | 0.492 ppb |
| R5 | 104348/33215 | 1.1×10⁻¹⁰ | 16 | 0.045 ppb |
| R6 | 208341/66317 | 3.9×10⁻¹¹ | 16+3 | **0.007 ppb** ★ |

```bash
cd lean/ && lake build
```

---

## The Paper

[`paper/two_foci_one_cup_ellipse_perimeter_mamoun_v17.pdf`](paper/two_foci_one_cup_ellipse_perimeter_mamoun_v17.pdf) -- 40 pages covering:

- The convergent tower and its Pade construction
- The CF-to-Newman proof chain (why exponentials work)
- Division-form corrections and the MEPB
- Focal certainty-uncertainty duality
- VARPRO separation theorem
- Complete catalog of 55 formulas (Appendix A)
- 6 open problems

### Recompiling

```bash
cd paper/
latexmk -pdf proof_strip16.tex
```

---

## Project Structure

```
ellipse/
  README.md               This file
  LICENSE                  MIT license
  setup.sh                One-command setup (macOS / Linux)
  pyproject.toml           Project metadata
  requirements.txt         pip requirements

  src/
    formulas.py            All formula implementations (R2 through R6 + tower)
    verify.py              Adversarial benchmark (2000 cases)
    server.py              FastAPI web UI + REST API

  demo/
    index.html             Static demo (open in browser, no server needed)
    ellipse_web_demo.py    Standalone web demo server
    export_static_demo.py  Demo generator script

  paper/
    proof_strip16.tex      Main paper (LaTeX source)
    proof_strip16.pdf      Compiled PDF (40 pages)
    paper_mamoun_*.pdf     Versioned paper archive (never deleted)

  lean/
    EllipseProofs/         Lean 4 formalization (28 modules, Mathlib)

  scripts/
    Various verification and investigation scripts
```

---

## Citation

```bibtex
@article{mamoun2026ellipse,
  author  = {Monir Mamoun},
  title   = {Two Foci, One Number: The World's Most Accurate
             Closed-Form Ellipse Perimeter Equation},
  year    = {2026},
  note    = {0.007 ppb maximum error (7 parts per trillion),
             verified at 300 decimal digits. Code and proofs:
             \url{https://github.com/monir/ellipse}}
}
```

---

## License

MIT. See [LICENSE](LICENSE).
