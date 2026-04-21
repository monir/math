#!/usr/bin/env python3
"""
Enhanced FastAPI server with comprehensive web UI for ellipse perimeter comparison.
Features:
  - Interactive error-vs-eccentricity chart (log scale, Chart.js)
  - Calculator for arbitrary ellipses
  - Curated gallery of tough test cases
  - MathJax-rendered formula explanation
  - Critical analysis section
  - REST API for programmatic access
"""
import math
import numpy as np
from scipy.special import ellipe as scipy_ellipe
from fastapi import FastAPI
from fastapi.responses import HTMLResponse, JSONResponse
from pydantic import BaseModel, Field
from src.formulas import ALL_FORMULAS, exact_perimeter, h_param, ramanujan_ii, ayala_raggi_r2_2exp, r2_3exp_gated, r2_3exp_gated_h2, r2_3exp_v23_champion

app = FastAPI(
    title="Ellipse Perimeter World Record",
    description="Practical ellipse formula explorer for the 2026 release: R2/3exp at 0.083426 ppm, with the broader release champion at 0.018 ppb",
    version="3.0.0",
)


# ─── Models ───────────────────────────────────────────────

class EllipseRequest(BaseModel):
    a: float = Field(..., gt=0, description="Semi-major axis")
    b: float = Field(..., gt=0, description="Semi-minor axis")


class FormulaResult(BaseModel):
    name: str
    perimeter: float
    relative_error: float
    error_ppm: float


class EllipseResponse(BaseModel):
    a: float
    b: float
    h: float
    eccentricity: float
    exact_perimeter: float
    results: list[FormulaResult]


# ─── Helpers ──────────────────────────────────────────────

def exact_fast(a, b):
    """Fast exact perimeter using scipy (double precision, ~15 significant digits)."""
    a, b = max(a, b), min(a, b)
    if a <= 0:
        return 0.0
    e_sq = 1.0 - (b / a) ** 2
    return 4.0 * a * float(scipy_ellipe(e_sq))


# ─── API Endpoints ────────────────────────────────────────

@app.post("/api/compare", response_model=EllipseResponse)
def compare_formulas(req: EllipseRequest):
    """Compare all formulas for the given ellipse."""
    a, b = max(req.a, req.b), min(req.a, req.b)
    h = h_param(a, b)
    e = math.sqrt(1.0 - (b / a) ** 2) if a > 0 else 0.0
    pe = exact_perimeter(a, b)

    results = []
    for name, fn in ALL_FORMULAS.items():
        pf = fn(a, b)
        rel_err = abs((pf - pe) / pe) if pe > 0 else float("inf")
        results.append(FormulaResult(
            name=name, perimeter=pf,
            relative_error=rel_err, error_ppm=rel_err * 1e6,
        ))
    results.sort(key=lambda r: r.relative_error)
    return EllipseResponse(a=a, b=b, h=h, eccentricity=e, exact_perimeter=pe, results=results)


@app.get("/api/sweep")
def sweep_eccentricity(n: int = 500):
    """Sweep h from 0 to ~1 and return error profiles for all formulas. Uses scipy for speed."""
    hs = np.linspace(0.0, 0.9999, n)
    data = {name: [] for name in ALL_FORMULAS}

    for h_val in hs:
        t = math.sqrt(h_val)
        k = (1.0 - t) / (1.0 + t) if t < 1.0 else 1e-300
        a, b = 1.0, max(k, 1e-300)
        pe = exact_fast(a, b)
        for name, fn in ALL_FORMULAS.items():
            pf = fn(a, b)
            err = abs((pf - pe) / pe) if pe > 0 and math.isfinite(pf) else 0.0
            data[name].append(err * 1e6)

    return {"h_values": hs.tolist(), "errors_ppm": data}


@app.get("/api/tough-cases")
def tough_cases():
    """Curated gallery of adversarial and interesting test cases."""
    cases = [
        {"name": "Perfect Circle", "a": 1.0, "b": 1.0,
         "why": "Baseline: all methods exact (h=0)"},
        {"name": "Golden Ratio", "a": 1.618033988749895, "b": 1.0,
         "why": "Irrational aspect ratio (phi:1)"},
        {"name": "R2 Error Peak", "a": 1.0, "b": 0.35,
         "why": "Near the peak of Ramanujan II error"},
        {"name": "Moderate Eccentric", "a": 1.0, "b": 0.1,
         "why": "h=0.669, significant eccentricity"},
        {"name": "High Eccentricity", "a": 1.0, "b": 0.01,
         "why": "h=0.960, extreme eccentricity"},
        {"name": "Twin Primes", "a": 1000003.0, "b": 999983.0,
         "why": "Nearly-equal large primes (tiny h)"},
        {"name": "Unbalanced Primes", "a": 104729.0, "b": 7.0,
         "why": "Huge ratio, extreme eccentricity"},
        {"name": "Mersenne Pair", "a": 127.0, "b": 31.0,
         "why": "Mersenne primes (2^7-1, 2^5-1)"},
        {"name": "Near-Degenerate", "a": 1.0, "b": 1e-8,
         "why": "Almost a line segment (h~1)"},
        {"name": "Earth Orbit (km)", "a": 152100.0, "b": 147090.0,
         "why": "Real-world: Earth's orbital ellipse"},
        {"name": "Pi Ellipse", "a": 3.14159265358979, "b": 1.0,
         "why": "a = pi, transcendental axis"},
        {"name": "Worst Case Zone", "a": 1.0, "b": 0.06,
         "why": "Near the peak zone for the R2/3exp v23 champion"},
    ]

    results = []
    for case in cases:
        a, b = max(case["a"], case["b"]), min(case["a"], case["b"])
        h = h_param(a, b)
        pe = exact_perimeter(a, b)  # mpmath for accuracy

        formulas = {}
        for name, fn in ALL_FORMULAS.items():
            pf = fn(a, b)
            err = abs((pf - pe) / pe) * 1e6 if pe > 0 and math.isfinite(pf) else 0.0
            formulas[name] = {"perimeter": pf, "error_ppm": err}

        results.append({
            "name": case["name"],
            "a": a, "b": b, "h": h,
            "why": case["why"],
            "exact_perimeter": pe,
            "formulas": formulas,
        })

    return results


# ─── Web UI ───────────────────────────────────────────────

@app.get("/", response_class=HTMLResponse)
def index():
    return HTML_PAGE


HTML_PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Ellipse Perimeter World Record</title>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4"></script>
<script src="https://cdn.jsdelivr.net/npm/chartjs-plugin-annotation@3"></script>
<script>
window.MathJax = {
  tex: { inlineMath: [['$','$']], displayMath: [['$$','$$']] },
  startup: { typeset: true }
};
</script>
<script src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js" async></script>
<style>
*{box-sizing:border-box;margin:0;padding:0}
:root{--bg:#0a0a0a;--card:#111;--border:#222;--text:#d8d8d8;--muted:#888;
--green:#00ff88;--gold:#ffd700;--red:#ff6b6b;--blue:#4a9eff;--orange:#ff9b3d}
html{scroll-behavior:smooth}
body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif;
background:var(--bg);color:var(--text);line-height:1.6}
.container{max-width:1100px;margin:0 auto;padding:0 1.5rem}

/* Navigation */
nav{position:sticky;top:0;z-index:100;background:rgba(10,10,10,0.95);
border-bottom:1px solid var(--border);backdrop-filter:blur(10px)}
nav .container{display:flex;align-items:center;gap:1.5rem;padding:.8rem 1.5rem;overflow-x:auto}
nav a{color:var(--muted);text-decoration:none;font-size:.85rem;white-space:nowrap;
transition:color .2s}
nav a:hover{color:var(--green)}
nav .brand{color:#fff;font-weight:700;font-size:1rem;margin-right:auto}

/* Hero */
.hero{text-align:center;padding:4rem 1rem 3rem}
.hero h1{font-size:2.5rem;font-weight:800;color:#fff;margin-bottom:.3rem}
.hero .subtitle{color:var(--muted);font-size:1.1rem;margin-bottom:2rem}
.stats{display:flex;gap:1rem;justify-content:center;flex-wrap:wrap;margin-bottom:1rem}
.stat{background:var(--card);border:1px solid var(--border);border-radius:12px;
padding:1.2rem 1.8rem;min-width:180px}
.stat .value{font-size:2rem;font-weight:800;font-family:'SF Mono',monospace;color:var(--green)}
.stat .label{font-size:.75rem;color:var(--muted);text-transform:uppercase;letter-spacing:.1em;margin-top:.2rem}
.stat.gold .value{color:var(--gold)}
.stat.blue .value{color:var(--blue)}

/* Sections */
section{padding:3rem 0;border-top:1px solid var(--border)}
section h2{font-size:1.6rem;font-weight:700;color:#fff;margin-bottom:1rem}
section .desc{color:var(--muted);margin-bottom:1.5rem;max-width:700px}

/* Chart */
.chart-wrap{background:var(--card);border:1px solid var(--border);border-radius:12px;
padding:1.5rem;margin-bottom:1rem}
.chart-wrap canvas{width:100%!important;height:400px!important}
.chart-controls{display:flex;gap:.5rem;margin-bottom:1rem}
.chart-controls button{background:#1a1a1a;border:1px solid var(--border);color:var(--text);
padding:.4rem 1rem;border-radius:6px;cursor:pointer;font-size:.8rem}
.chart-controls button.active{background:var(--green);color:#000;border-color:var(--green)}

/* Calculator */
.calc-row{display:flex;gap:1rem;margin-bottom:1.5rem;align-items:end;flex-wrap:wrap}
.calc-row label{display:block;font-size:.8rem;color:var(--muted);margin-bottom:.3rem}
.calc-row input{background:#1a1a1a;border:1px solid var(--border);color:#fff;
padding:.6rem .8rem;border-radius:6px;font-size:1rem;width:160px;font-family:monospace}
.calc-row input:focus{outline:none;border-color:var(--green)}
.calc-row button{background:var(--green);color:#000;font-weight:600;border:none;
padding:.65rem 1.5rem;border-radius:6px;font-size:.95rem;cursor:pointer}
.calc-row button:hover{opacity:.9}
.quick-btns{display:flex;gap:.4rem;flex-wrap:wrap;margin-bottom:1rem}
.quick-btns button{background:#1a1a1a;border:1px solid var(--border);color:var(--muted);
padding:.3rem .7rem;border-radius:4px;cursor:pointer;font-size:.75rem}
.quick-btns button:hover{color:var(--green);border-color:var(--green)}
.meta-row{display:flex;gap:1rem;margin-bottom:1rem;flex-wrap:wrap}
.meta-box{background:var(--card);border:1px solid var(--border);border-radius:8px;
padding:.8rem 1rem;flex:1;min-width:150px}
.meta-box .lbl{font-size:.7rem;color:var(--muted);text-transform:uppercase;letter-spacing:.05em}
.meta-box .val{font-size:1.1rem;font-weight:600;color:#fff;font-family:monospace;margin-top:.1rem}

/* Results table */
table{width:100%;border-collapse:collapse}
th{text-align:left;padding:.5rem .7rem;border-bottom:2px solid #333;
font-size:.75rem;text-transform:uppercase;color:var(--muted);letter-spacing:.05em}
td{padding:.5rem .7rem;border-bottom:1px solid #1a1a1a;font-family:monospace;font-size:.85rem}
.err-col{text-align:right}
tr.winner{background:#061a06}
tr.winner td{color:var(--green);font-weight:600}
.tag{display:inline-block;background:#1a3d1a;color:var(--green);padding:.1rem .4rem;
border-radius:3px;font-size:.65rem;font-weight:700;margin-left:.4rem}

/* Tough cases */
.tc-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(320px,1fr));gap:1rem}
.tc-card{background:var(--card);border:1px solid var(--border);border-radius:10px;
padding:1.2rem;transition:border-color .2s}
.tc-card:hover{border-color:#444}
.tc-card h3{font-size:1rem;color:#fff;margin-bottom:.2rem}
.tc-card .tc-why{font-size:.8rem;color:var(--muted);margin-bottom:.8rem}
.tc-card .tc-params{font-size:.75rem;color:var(--muted);margin-bottom:.5rem;font-family:monospace}
.tc-card table{font-size:.8rem}
.tc-card td{padding:.25rem .4rem;border-bottom:1px solid #1a1a1a}
.tc-card .tc-best{color:var(--green);font-weight:600}
.tc-card .tc-worst{color:var(--red)}

/* Formula section */
.formula-box{background:var(--card);border:1px solid var(--border);border-radius:12px;
padding:2rem;margin:1.5rem 0;text-align:center;font-size:1.1rem;overflow-x:auto}
.formula-box .mjx-chtml{font-size:1.2em!important}
.components{display:grid;grid-template-columns:repeat(auto-fill,minmax(250px,1fr));gap:1rem;margin-top:1.5rem}
.comp{background:#0a0f0a;border:1px solid #1a3d1a;border-radius:8px;padding:1rem}
.comp h4{color:var(--green);font-size:.85rem;margin-bottom:.3rem}
.comp p{font-size:.8rem;color:var(--muted)}

/* Critical analysis */
.analysis-grid{display:grid;grid-template-columns:1fr 1fr;gap:1.5rem;margin-top:1rem}
@media(max-width:700px){.analysis-grid{grid-template-columns:1fr}}
.proven{background:#061a06;border:1px solid #1a4d1a;border-radius:10px;padding:1.2rem}
.proven h3{color:var(--green);font-size:.95rem;margin-bottom:.5rem}
.unproven{background:#1a0a06;border:1px solid #4d1a1a;border-radius:10px;padding:1.2rem}
.unproven h3{color:var(--red);font-size:.95rem;margin-bottom:.5rem}
.analysis-grid ul{padding-left:1.2rem;font-size:.85rem;line-height:1.7}
.analysis-grid li{margin-bottom:.2rem}

/* Footer */
footer{text-align:center;padding:2rem;color:var(--muted);font-size:.8rem;border-top:1px solid var(--border)}
footer a{color:var(--blue);text-decoration:none}

/* Loading */
.loading{text-align:center;padding:2rem;color:var(--muted)}
.spinner{display:inline-block;width:20px;height:20px;border:2px solid var(--border);
border-top-color:var(--green);border-radius:50%;animation:spin .8s linear infinite}
@keyframes spin{to{transform:rotate(360deg)}}
</style>
</head>
<body>

<!-- Navigation -->
<nav>
<div class="container">
<span class="brand">Ellipse WR</span>
<a href="#landscape">Error Landscape</a>
<a href="#calculator">Calculator</a>
<a href="#tough-cases">Tough Cases</a>
<a href="#formula">The Formula</a>
<a href="#insight">Key Insight</a>
<a href="#critical">Critical Analysis</a>
</div>
</nav>

<!-- Hero -->
<div class="hero container">
<h1>Ellipse Perimeter World Record</h1>
<p class="subtitle">R2/3exp v23 is the practical release formula; the full release champion is R6+16exp at 0.018 ppb</p>
<div class="stats">
<div class="stat"><div class="value">0.0834</div><div class="label">Max Error (ppm)</div></div>
<div class="stat gold"><div class="value">6.9&times;</div><div class="label">Better than Ayala-Rendón (2025)</div></div>
<div class="stat blue"><div class="value">4800&times;</div><div class="label">Better than Ramanujan II</div></div>
</div>
</div>

<!-- Error Landscape -->
<section id="landscape">
<div class="container">
<h2>Error Landscape</h2>
<p class="desc">Relative error (ppm) vs eccentricity parameter $h = \left(\frac{a-b}{a+b}\right)^2$ for all formulas. Log scale reveals orders-of-magnitude improvement.</p>
<div class="chart-controls">
<button class="active" onclick="setYScale('log',this)">Log Scale</button>
<button onclick="setYScale('linear',this)">Linear Scale</button>
<button onclick="toggleZoom()">Zoom to Best</button>
</div>
<div class="chart-wrap">
<canvas id="error-chart"></canvas>
</div>
<p style="font-size:.8rem;color:var(--muted)">Dashed lines: published max error bounds. Green = q=7/3 practical formula (0.0834 ppm). Gold = Ayala-Rendón 2025 (0.5736 ppm).</p>
</div>
</section>

<!-- Calculator -->
<section id="calculator">
<div class="container">
<h2>Interactive Calculator</h2>
<p class="desc">Enter any ellipse semi-axes and compare all methods against the exact perimeter (computed via mpmath at 50 digits).</p>
<div class="quick-btns">
<button onclick="setCalc(1,1)">Circle</button>
<button onclick="setCalc(1.618034,1)">Golden</button>
<button onclick="setCalc(1,0.35)">R2 Peak</button>
<button onclick="setCalc(1,0.01)">Extreme</button>
<button onclick="setCalc(127,31)">Mersenne</button>
<button onclick="setCalc(104729,7)">Unbalanced</button>
<button onclick="setCalc(1,1e-8)">Degenerate</button>
<button onclick="setCalc(3.14159265,1)">Pi Ellipse</button>
</div>
<div class="calc-row">
<div><label>Semi-major axis a</label><input type="number" id="inp-a" value="1.0" step="any" min="0.0001"></div>
<div><label>Semi-minor axis b</label><input type="number" id="inp-b" value="0.3" step="any" min="0.0001"></div>
<button onclick="compare()">Compare</button>
</div>
<div class="meta-row" id="meta" style="display:none">
<div class="meta-box"><div class="lbl">Exact Perimeter</div><div class="val" id="m-exact">-</div></div>
<div class="meta-box"><div class="lbl">h parameter</div><div class="val" id="m-h">-</div></div>
<div class="meta-box"><div class="lbl">Eccentricity</div><div class="val" id="m-ecc">-</div></div>
</div>
<table id="results" style="display:none">
<thead><tr><th>Formula</th><th>Perimeter</th><th class="err-col">Relative Error</th><th class="err-col">Error (ppm)</th></tr></thead>
<tbody id="tbody"></tbody>
</table>
</div>
</section>

<!-- Tough Cases -->
<section id="tough-cases">
<div class="container">
<h2>Tough Cases Gallery</h2>
<p class="desc">Curated adversarial and real-world test cases. Each computed against the exact elliptic integral at 50-digit precision.</p>
<div class="tc-grid" id="tc-grid">
<div class="loading"><span class="spinner"></span> Computing exact perimeters...</div>
</div>
</div>
</section>

<!-- The Formula -->
<section id="formula">
<div class="container">
<h2>The Formula</h2>
<p class="desc">A continued-fraction-locked three-exponential correction to Ramanujan II (1914), with q=7/3 gating and rates fixed at 1, 81/25, and 15.</p>

<div class="formula-box">
$$P = \frac{P_{R2}(a,b)}{1 \;-\; h^{7/3} \left[\, A\, e^{-\lambda(1-h)} \;+\; B\, e^{-(81/25)\lambda(1-h)} \;+\; C\, e^{-15\lambda(1-h)}\, \right]}$$
<div style="margin-top:1rem;font-size:.85rem;color:var(--muted)">
where $h = \left(\frac{a-b}{a+b}\right)^2$, &ensp; $P_{R2} = \pi(a+b)\!\left(1 + \frac{3h}{10+\sqrt{4-3h}}\right)$
</div>
</div>

<div class="components">
<div class="comp">
<h4>$P_{R2}$: Ramanujan II Base</h4>
<p>The legendary 1914 formula. Max error ~402 ppm. We build on it, not replace it.</p>
</div>
<div class="comp">
<h4>$h^{7/3}$: Gate Function</h4>
<p>Suppresses correction near circles ($h \approx 0$) where R2 is already excellent. The gate exponent $7/3$ is locked from the continued fraction of $\pi$: $a_1/a_0 = 7/3$.</p>
</div>
<div class="comp">
<h4>$T = 1 - 7\pi/22$: Endpoint Pin</h4>
<p>Forces $P \to 4a$ exactly as $b \to 0$. Pure arithmetic: $\pi \cdot \frac{14}{11} \div \frac{7\pi}{22} = 4$.</p>
</div>
<div class="comp">
<h4>$\lambda \approx 6.8955$: The ONE Free Parameter</h4>
<p>Once the structure is fixed ($q=7/3$, $m=81/25$, $n=15$, endpoint pin), the amplitudes $A$, $B$, and $C$ are determined by the ratio parameters. Only $\lambda$ remains free.</p>
</div>
<div class="comp">
<h4>$m = 81/25$: Mid-Rate Multiplier</h4>
<p>The middle exponential rate is $(81/25)\lambda = 3.24\lambda$, the continued-fraction-locked value used by the v23 champion.</p>
</div>
<div class="comp">
<h4>$n = 15$: Fast Rate Multiplier</h4>
<p>The fastest exponential rate is $15\lambda$. Together with $81/25$, it gives the simplest world-record correction published in this repo.</p>
</div>
</div>
</div>
</section>

<!-- Key Insight -->
<section id="insight">
<div class="container">
<h2>Key Insight: 1 Effective Free Parameter</h2>
<p class="desc">Why this formula beats Ayala-Rendón (2025) despite having <em>fewer</em> free parameters.</p>

<div style="background:var(--card);border:1px solid var(--border);border-radius:12px;padding:1.5rem;margin:1rem 0">
<h3 style="color:var(--green);margin-bottom:.7rem">The Parameter Count</h3>
<table style="max-width:600px">
<thead><tr><th>Formula</th><th class="err-col">Free Parameters</th><th class="err-col">Max Error (ppm)</th></tr></thead>
<tbody>
<tr><td>Ramanujan II (1914)</td><td class="err-col">0</td><td class="err-col" style="color:var(--red)">402</td></tr>
<tr><td>Cantrell (2001)</td><td class="err-col">1</td><td class="err-col" style="color:var(--orange)">412</td></tr>
<tr><td>Ayala-Rendón R2/2exp (2025)</td><td class="err-col">4</td><td class="err-col" style="color:var(--gold)">0.574</td></tr>
<tr><td>R2/3exp h&sup2;, m = &pi;</td><td class="err-col">1 (effective)</td><td class="err-col" style="color:var(--blue)">0.1245</td></tr>
<tr><td>R2/3exp h<sup>5/2</sup>, m = &pi;</td><td class="err-col">1 (effective)</td><td class="err-col" style="color:var(--blue)">0.1242</td></tr>
<tr class="winner"><td>R2/3exp q = 7/3, m = 81/25 [V23]</td><td class="err-col">1 (effective)</td><td class="err-col">0.0834</td></tr>
</tbody>
</table>
</div>

<div style="background:var(--card);border:1px solid var(--border);border-radius:12px;padding:1.5rem;margin:1rem 0">
<h3 style="color:var(--blue);margin-bottom:.7rem">Why 1 Parameter?</h3>
<p style="font-size:.9rem;line-height:1.7">The formula has three numerical parameters: $\lambda$, $r$, and $s$. But:</p>
<ol style="padding-left:1.5rem;font-size:.9rem;line-height:1.8;margin-top:.5rem">
<li>The total amplitude $A + E + C = T = 1 - 7\pi/22$ is <strong>fixed</strong> by the flat-limit pin.</li>
<li>The ratios $r = E/A$ and $s = C/A$ distribute $T$ among three exponentials.</li>
<li>For any fixed $\lambda$, the linearized error is <strong>affine</strong> in $(r, s)$.</li>
<li>By the <strong>Chebyshev equioscillation theorem</strong>, the minimax solution for an affine 2-parameter family on $[0,1]$ is <strong>unique</strong>.</li>
<li>Therefore $r(\lambda)$ and $s(\lambda)$ are <strong>determined</strong> by $\lambda$: the family is 1-dimensional.</li>
</ol>
<p style="font-size:.85rem;color:var(--muted);margin-top:.8rem">The parameter study (see <code>parameter_study.py</code>) confirms: $r(\lambda)$ and $s(\lambda)$ trace smooth curves as $\lambda$ varies. For the $h^{5/2}$ gate, the global minimum occurs at $\lambda \approx 6.512$; for $h^2$, at $\lambda \approx 7.341$.</p>
</div>
</div>
</section>

<!-- Critical Analysis -->
<section id="critical">
<div class="container">
<h2>Critical Analysis</h2>
<p class="desc">An honest assessment of what is proven, what is conjectured, and what remains open. Rigorous mathematics demands transparency.</p>

<div class="analysis-grid">
<div class="proven">
<h3>Proven (Mathematically Certain)</h3>
<ul>
<li><strong>Circle limit exact</strong>: $P = 2\pi a$ when $a = b$ (gate = 0, correction vanishes)</li>
<li><strong>Flat limit exact</strong>: $P = 4a$ when $b = 0$ via $T = 1 - 7\pi/22$ (pure arithmetic, no float error)</li>
<li><strong>Gate suppression</strong>: Correction is $O(h^2)$ near $h = 0$; Ramanujan II dominates for near-circles</li>
<li><strong>Scale invariance</strong>: $P(\lambda a, \lambda b) = \lambda \cdot P(a,b)$ (inherited from $P_{R2}$ and $h$)</li>
<li><strong>Continuity</strong>: Formula is $C^\infty$ on $(0,1)$ in $h$</li>
<li><strong>Numerical stability</strong>: No division by zero, overflow, or underflow for valid inputs</li>
<li><strong>Chebyshev uniqueness</strong>: For fixed $\lambda$, the linearized minimax has a unique solution in $(r, s)$</li>
</ul>
</div>

<div class="proven" style="background:#060a1a;border-color:#1a1a4d">
<h3 style="color:var(--blue)">Verified (Numerically Certain, Not Analytically Proven)</h3>
<ul>
<li><strong>Max error = 0.083426 ppm</strong> on the canonical normalized sweep used by the published result files</li>
<li><strong>6.9x better</strong> than Ayala-Rendón R2/2exp (2025) in worst-case accuracy</li>
<li><strong>4800x better</strong> than Ramanujan II (1914) in worst-case accuracy</li>
<li><strong>q = 7/3, m = 81/25, n = 15</strong> reproduces the published v23 champion from the continued-fraction-locked family</li>
<li><strong>The one-free-parameter family is reproducible</strong>: the published $(\lambda, \rho_2, \rho_3)$ constants regenerate the claimed curve</li>
</ul>
</div>

<div class="unproven">
<h3>Unproven / Conjectured</h3>
<ul>
<li><strong>Analytic error bound</strong>: We have no proof that $\max_{h \in [0,1]} |\text{error}| \le 0.1$ ppm. The bound is empirical.</li>
<li><strong>$q = 7/3$ exact optimality</strong>: It is motivated by the continued fraction of $\pi$, but we do not prove it is globally optimal.</li>
<li><strong>$m = 81/25$ structural optimality</strong>: The value is elegant and reproducible, but not derived from first principles.</li>
<li><strong>$n = 15$ optimal</strong>: Why not 14 or 16? Integer search result, not derived from theory.</li>
<li><strong>Global optimality</strong>: We don't prove this is the BEST possible 3-exponential correction.</li>
</ul>
</div>

<div class="unproven" style="background:#1a1a06;border-color:#4d4d1a">
<h3 style="color:var(--gold)">What Would Complete the Proof</h3>
<ul>
<li>Analytic upper bound: $\max_{h \in [0,1]} |P_{\text{approx}} - P_{\text{exact}}|/P_{\text{exact}} \le K$ for explicit $K$</li>
<li>Derive the locked values $q = 7/3$ and $m = 81/25$ from the analytic structure of $E(e)$</li>
<li>Prove equiripple (Chebyshev alternation) of the actual error (not the linearization)</li>
<li>Show the formula class $R2/k\text{exp-gated}$ is dense in $C[0,1]$ corrections</li>
<li>Closed-form or tight bounds for the optimal $\lambda$</li>
</ul>
</div>
</div>

<div style="background:var(--card);border:1px solid var(--border);border-radius:12px;padding:1.5rem;margin-top:1.5rem">
<h3 style="color:#fff;margin-bottom:.5rem">The Bottom Line</h3>
<p style="font-size:.9rem;line-height:1.7">The R2/3exp v23 formula is the <strong>practical</strong> formula in the release: compact, reproducible, and substantially better than prior low-complexity approximations. The broader release also contains the R6+16exp champion at 0.018 ppb for users who want the absolute best verified minimax error.</p>
</div>
</div>
</section>

<!-- Footer -->
<footer>
<div class="container">
<p>Ellipse Perimeter Release (2026) | practical R2/3exp explorer | <a href="/docs">API Documentation</a> | MIT License</p>
<p style="margin-top:.3rem">Built with FastAPI, Chart.js, MathJax | <code>pip install -e .</code> to verify locally</p>
</div>
</footer>

<script>
// ─── Colors and config ───
const COLORS = {
  'Ramanujan II (1914)': '#ff6b6b',
  'Cantrell (2001)': '#ff9b3d',
  'Ayala-Rendón R2/2exp (2025)': '#ffd700',
  'R2/3exp h^2, m=pi [THIS WORK]': '#4a9eff',
  'R2/3exp h^2.5, m=pi [THIS WORK]': '#7ee787',
  'R2/3exp h^2.5, m=81/25 [THIS WORK]': '#56d364',
  'R2/3exp q=7/3, m=81/25 [V23]': '#00ff88'
};
const NAMES_SHORT = {
  'Ramanujan II (1914)': 'Ramanujan II',
  'Cantrell (2001)': 'Cantrell',
  'Ayala-Rendón R2/2exp (2025)': 'Ayala-Rendón',
  'R2/3exp h^2, m=pi [THIS WORK]': 'h\u00B2, m=\u03c0',
  'R2/3exp h^2.5, m=pi [THIS WORK]': 'h\u00B2\u02D9\u2075, m=\u03c0',
  'R2/3exp h^2.5, m=81/25 [THIS WORK]': 'h\u00B2\u02D9\u2075, m=3.24',
  'R2/3exp q=7/3, m=81/25 [V23]': 'q=7/3 champion'
};

let chart = null;
let zoomedIn = false;

// ─── Error Landscape Chart ───
async function initChart() {
  const resp = await fetch('/api/sweep?n=500');
  const data = await resp.json();

  const datasets = Object.entries(data.errors_ppm).map(([name, errs]) => ({
    label: name,
    data: data.h_values.map((h, i) => ({x: h, y: Math.max(errs[i], 1e-5)})),
    borderColor: COLORS[name] || '#888',
    borderWidth: name.includes('[V23]') ? 3 : (name.includes('THIS WORK') ? 2 : 1.5),
    pointRadius: 0,
    tension: 0.1,
    order: (name.includes('[V23]') || name.includes('THIS WORK')) ? 0 : 1,
  }));

  const ctx = document.getElementById('error-chart').getContext('2d');
  chart = new Chart(ctx, {
    type: 'line',
    data: { datasets },
    options: {
      parsing: false,
      animation: false,
      responsive: true,
      maintainAspectRatio: false,
      interaction: { mode: 'nearest', intersect: false },
      scales: {
        x: {
          type: 'linear', min: 0, max: 1,
          title: { display: true, text: 'h = ((a-b)/(a+b))^2', color: '#888' },
          ticks: { color: '#666' }, grid: { color: '#1a1a1a' }
        },
        y: {
          type: 'logarithmic', min: 0.001, max: 500,
          title: { display: true, text: 'Relative Error (ppm)', color: '#888' },
          ticks: { color: '#666', callback: v => v >= 1 ? v : v.toFixed(3) },
          grid: { color: '#1a1a1a' }
        }
      },
      plugins: {
        legend: { labels: { color: '#ccc', usePointStyle: true, pointStyle: 'line' } },
        tooltip: {
          callbacks: {
            title: pts => 'h = ' + pts[0].parsed.x.toFixed(4),
            label: ctx => ctx.dataset.label + ': ' + ctx.parsed.y.toFixed(4) + ' ppm'
          }
        },
        annotation: {
          annotations: {
            ourLine: {
              type: 'line', yMin: 0.083426, yMax: 0.083426,
              borderColor: 'rgba(0,255,136,0.4)', borderWidth: 1, borderDash: [6,3],
              label: { display: true, content: '0.0834 ppm (q=7/3 practical formula)', position: 'start',
                       backgroundColor: 'rgba(0,255,136,0.15)', color: '#00ff88', font: {size: 10} }
            },
            arLine: {
              type: 'line', yMin: 0.573575, yMax: 0.573575,
              borderColor: 'rgba(255,215,0,0.4)', borderWidth: 1, borderDash: [6,3],
              label: { display: true, content: '0.5736 ppm (Ayala-Rendón)', position: 'start',
                       backgroundColor: 'rgba(255,215,0,0.15)', color: '#ffd700', font: {size: 10} }
            }
          }
        }
      }
    }
  });
}

function setYScale(type, btn) {
  if (!chart) return;
  chart.options.scales.y.type = type === 'log' ? 'logarithmic' : 'linear';
  if (type === 'linear') {
    chart.options.scales.y.min = 0;
    chart.options.scales.y.max = zoomedIn ? 1 : 500;
  } else {
    chart.options.scales.y.min = zoomedIn ? 0.001 : 0.001;
    chart.options.scales.y.max = zoomedIn ? 2 : 500;
  }
  chart.update();
  document.querySelectorAll('.chart-controls button').forEach(b => b.classList.remove('active'));
  btn.classList.add('active');
}

function toggleZoom() {
  if (!chart) return;
  zoomedIn = !zoomedIn;
  if (zoomedIn) {
    chart.options.scales.y.min = 0.001;
    chart.options.scales.y.max = 2;
  } else {
    chart.options.scales.y.min = 0.001;
    chart.options.scales.y.max = 500;
  }
  chart.update();
}

// ─── Calculator ───
function setCalc(a, b) {
  document.getElementById('inp-a').value = a;
  document.getElementById('inp-b').value = b;
  compare();
}

async function compare() {
  const a = parseFloat(document.getElementById('inp-a').value);
  const b = parseFloat(document.getElementById('inp-b').value);
  if (isNaN(a) || isNaN(b) || a <= 0 || b <= 0) return;

  const resp = await fetch('/api/compare', {
    method: 'POST', headers: {'Content-Type': 'application/json'},
    body: JSON.stringify({a, b})
  });
  const data = await resp.json();

  document.getElementById('meta').style.display = 'flex';
  document.getElementById('m-exact').textContent = data.exact_perimeter.toPrecision(12);
  document.getElementById('m-h').textContent = data.h.toFixed(8);
  document.getElementById('m-ecc').textContent = data.eccentricity.toFixed(8);

  const tbody = document.getElementById('tbody');
  tbody.innerHTML = '';
  data.results.forEach((r, i) => {
    const tr = document.createElement('tr');
    if (i === 0) tr.className = 'winner';
    const short = NAMES_SHORT[r.name] || r.name;
    tr.innerHTML =
      '<td>' + r.name + (i === 0 ? '<span class="tag">BEST</span>' : '') + '</td>' +
      '<td>' + r.perimeter.toPrecision(12) + '</td>' +
      '<td class="err-col">' + r.relative_error.toExponential(3) + '</td>' +
      '<td class="err-col">' + r.error_ppm.toFixed(4) + '</td>';
    tbody.appendChild(tr);
  });
  document.getElementById('results').style.display = 'table';
}

// ─── Tough Cases ───
async function loadToughCases() {
  const grid = document.getElementById('tc-grid');
  try {
    const resp = await fetch('/api/tough-cases');
    const cases = await resp.json();
    grid.innerHTML = '';

    for (const c of cases) {
      const card = document.createElement('div');
      card.className = 'tc-card';

      let rows = '';
      const entries = Object.entries(c.formulas).sort((a, b) => a[1].error_ppm - b[1].error_ppm);
      entries.forEach(([name, f], i) => {
        const short = NAMES_SHORT[name] || name;
        const cls = i === 0 ? 'tc-best' : (i === entries.length - 1 ? 'tc-worst' : '');
        rows += '<tr><td class="' + cls + '">' + short +
          (i === 0 ? ' <span class="tag">BEST</span>' : '') +
          '</td><td class="err-col ' + cls + '">' + f.error_ppm.toFixed(4) + ' ppm</td></tr>';
      });

      card.innerHTML =
        '<h3>' + c.name + '</h3>' +
        '<div class="tc-why">' + c.why + '</div>' +
        '<div class="tc-params">a=' + c.a.toPrecision(7) + ' &ensp; b=' + c.b.toPrecision(7) + ' &ensp; h=' + c.h.toFixed(6) + '</div>' +
        '<table>' + rows + '</table>';

      grid.appendChild(card);
    }
  } catch(e) {
    grid.innerHTML = '<p style="color:var(--red)">Failed to load tough cases: ' + e.message + '</p>';
  }
}

// ─── Init ───
window.addEventListener('load', async () => {
  await initChart();
  compare();
  loadToughCases();
});
</script>

</body>
</html>"""


def main():
    import uvicorn
    print("=" * 60)
    print("  Ellipse Perimeter World Record - Enhanced Visualizer")
    print("  Open http://localhost:8000 in your browser")
    print("=" * 60)
    uvicorn.run(app, host="0.0.0.0", port=8000)


if __name__ == "__main__":
    main()
