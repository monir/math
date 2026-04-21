#!/usr/bin/env python3
"""
ELLIPSE PERIMETER — Interactive Web Demo
==========================================
Launches a local web server showing the focal certainty–uncertainty duality
and the world-record ellipse perimeter formula interactively.

Usage:
    python ellipse_web_demo.py [--port 8080]
    Then open http://localhost:8080 in your browser.

Cross-platform: works on Linux and macOS. No external dependencies beyond
Python 3 standard library + mpmath.

Source code and paper:
    https://github.com/gutmogutmam/ellipse

License: MIT
"""
import http.server
import json
import math
import os
import socketserver
import sys
import threading
import webbrowser
from urllib.parse import urlparse, parse_qs

# Add directory to path for formulas import
_demo_dir = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _demo_dir)
sys.path.insert(0, os.path.join(_demo_dir, '..', 'src'))

from formulas import (ramanujan_ii, cantrell, ayala_raggi_r2_2exp,
                       r2_3exp_gated, r2_3exp_gated_pi, r2_3exp_gated_h2,
                       r2_3exp_v23_champion, exact_perimeter,
                       r3_15exp_champion,
                       r4_20exp_champion, r5_varpro_champion,
                       r6_varpro_champion, r6_scor_champion,
                       tower_perimeter, TOWER_INFO)

# Try mpmath for high precision, fall back to math
try:
    import mpmath
    mpmath.mp.dps = 30
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False

PORT = 8080

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
KAPPA = 2 / math.pi


def ramanujan1(a, b):
    """Ramanujan's first approximation (1914)."""
    a, b = max(a, b), min(a, b)
    return math.pi * (3 * (a + b) - math.sqrt((3 * a + b) * (a + 3 * b)))


def r2_2exp_beater(a, b):
    """Our 2-exp beater of Ayala-Raggi: 0.530 ppm, 4 params, multiplicative T-pinned."""
    a, b = max(a, b), min(a, b)
    h = ((a - b) / (a + b)) ** 2
    x = 1.0 - h
    A, B = 0.0000658824, 0.0003364551
    phi = A * math.exp(-40.127330 * x) + B * math.exp(-10.265288 * x)
    return ramanujan_ii(a, b) * (1.0 + h ** 0.01 * phi)


# Method registry: (display_name, function, is_ours)
# is_ours=True shows a star in the comparison table
METHODS = [
    ("Ramanujan I (1914)", ramanujan1, False),
    ("Ramanujan II (1914)", ramanujan_ii, False),
    ("Cantrell (2001)", cantrell, False),
    ("Ayala-Rendón R2/2exp (2025)", ayala_raggi_r2_2exp, False),
    ("Mamoun R2/2exp (0.530 ppm)", r2_2exp_beater, True),
    ("Mamoun R2/3exp (0.083 ppm)", r2_3exp_v23_champion, True),
    ("Mamoun R3+15exp (1.427 ppb)", r3_15exp_champion, True),
    ("Mamoun R4+20exp (0.492 ppb)", r4_20exp_champion, True),
    ("Mamoun R5+16exp (0.045 ppb)", r5_varpro_champion, True),
    ("Mamoun R6+16exp (0.018 ppb)", r6_varpro_champion, True),
    ("Mamoun R6+16exp+3log SCOR (0.007 ppb)", r6_scor_champion, True),
]


def compute_data(a, b):
    """Compute all quantities for given semi-axes a, b."""
    a, b = max(a, b), min(a, b)
    if a <= 0 or b <= 0:
        return None

    e = math.sqrt(1 - (b / a) ** 2) if a > b else 0.0
    h = ((a - b) / (a + b)) ** 2 if a > b else 0.0

    # Circle case
    if a == b or e == 0:
        P_exact_val = 2 * math.pi * a
        if HAS_MPMATH:
            P_exact_hp = mpmath.nstr(2 * mpmath.pi * mpmath.mpf(a), 30, strip_zeros=False)
        else:
            P_exact_hp = f"{P_exact_val:.16e}"
        methods_result = []
        for name, fn, is_champ in METHODS:
            P_approx = fn(a, b)
            methods_result.append({
                'name': name,
                'perimeter': P_approx,
                'perimeter_str': f"{P_approx:.15f}" if abs(P_approx) < 1e12 else f"{P_approx:.16e}",
                'error_ppm': abs(P_approx / P_exact_val - 1) * 1e6 if P_exact_val > 0 else 0,
                'is_champion': is_champ,
            })
        methods_result.sort(key=lambda m: m['error_ppm'])
        return {
            'e': 0.0, 'a': a, 'b': b, 'c': 0.0, 'h': 0.0,
            'ell': b, 'R': 0, 'U': 0, 'R_over_U': math.pi / 2,
            'pi_over_2': math.pi / 2, 'eta_max': 0,
            'sinh_2eta': 0, 'kappa': KAPPA,
            'P_exact': P_exact_val, 'P_exact_hp': P_exact_hp,
            'methods': methods_result,
            'angular_profile': [], 'chord_data': [],
            'rapidity_data': [],
            'I_f': 0, 'H_u': 0, 'info_surplus': 0,
            'CV2': math.pi ** 2 / 8 - 1,
            'CV': math.sqrt(math.pi ** 2 / 8 - 1),
        }

    if e >= 1:
        return None

    c = a * e
    ell = b ** 2 / a
    R = c / ell
    U = R * KAPPA
    eta_max = math.atanh(e)

    # Compute all methods
    P_exact_val = exact_perimeter(a, b)

    # High-precision exact perimeter string (30+ digits from mpmath)
    if HAS_MPMATH:
        P_exact_hp = mpmath.nstr(
            mpmath.mpf(4) * max(a, b) * mpmath.ellipe(mpmath.mpf(e) ** 2),
            30, strip_zeros=False)
    else:
        P_exact_hp = f"{P_exact_val:.16e}"

    methods_result = []
    for name, fn, is_champ in METHODS:
        try:
            P_approx = fn(a, b)
            err_ppm = abs(P_approx / P_exact_val - 1) * 1e6
        except Exception:
            P_approx = float('nan')
            err_ppm = float('nan')
        methods_result.append({
            'name': name,
            'perimeter': P_approx,
            'perimeter_str': f"{P_approx:.15f}" if abs(P_approx) < 1e12 else f"{P_approx:.16e}",
            'error_ppm': err_ppm,
            'is_champion': is_champ,
        })

    # Sort by error (ascending)
    methods_result.sort(
        key=lambda m: m['error_ppm'] if math.isfinite(m['error_ppm']) else float('inf'))

    # Angular profile: |MD(alpha)| / <|MD|> = (pi/2)|cos(alpha)|
    angles = [i * math.pi / 180 for i in range(361)]
    angular_profile = [(math.degrees(alpha), abs(math.cos(alpha)) * R,
                        abs(math.cos(alpha)) * math.pi / 2)
                       for alpha in angles]

    # Focal chord data
    chord_data = []
    for deg in range(0, 181, 5):
        alpha = deg * math.pi / 180
        rho1 = ell / (1 + e * math.cos(alpha)) if (1 + e * math.cos(alpha)) > 0 else 1e10
        rho2 = ell / (1 - e * math.cos(alpha)) if (1 - e * math.cos(alpha)) > 0 else 1e10
        hm = 2 * rho1 * rho2 / (rho1 + rho2) if (rho1 + rho2) > 0 else 0
        MD = (a ** 2 * e / b ** 2) * abs(math.cos(alpha))
        chord_data.append({
            'angle': deg, 'rho1': rho1, 'rho2': rho2,
            'harmonic_mean': hm, 'MD': MD
        })

    # Rapidity profile around the ellipse
    rapidity_data = []
    for deg in range(361):
        theta = deg * math.pi / 180
        cos_t = math.cos(theta)
        e_cos = e * cos_t
        if abs(e_cos) < 1:
            delta = (1 - e_cos) / (1 + e_cos)
            eta = math.atanh(e_cos) if abs(e_cos) < 0.9999 else (
                math.copysign(5, e_cos))
        else:
            delta = 0
            eta = 5 * (1 if e_cos > 0 else -1)
        rapidity_data.append({
            'theta': deg, 'delta': delta, 'eta': eta,
            'sqrt_delta': math.sqrt(max(delta, 0))
        })

    # Information surplus
    I_f = math.log2(R) if R > 0 else float('-inf')
    H_u = math.log2(U) if U > 0 else float('-inf')
    info_surplus = I_f - H_u

    return {
        'e': e, 'a': a, 'b': b, 'c': c, 'h': h,
        'ell': ell, 'R': R, 'U': U,
        'R_over_U': R / U if U > 0 else float('inf'),
        'pi_over_2': math.pi / 2,
        'eta_max': eta_max,
        'sinh_2eta': math.sinh(2 * eta_max),
        'kappa': KAPPA,
        'P_exact': P_exact_val,
        'P_exact_hp': P_exact_hp,
        'methods': methods_result,
        'angular_profile': angular_profile,
        'chord_data': chord_data,
        'rapidity_data': rapidity_data,
        'I_f': I_f, 'H_u': H_u,
        'info_surplus': info_surplus,
        'CV2': math.pi ** 2 / 8 - 1,
        'CV': math.sqrt(math.pi ** 2 / 8 - 1),
    }


def compute_sweep_over_eccentricities():
    """Compute R/U ratio across many eccentricities for the main plot."""
    data = []
    for i in range(1, 1000):
        e = i / 1000.0
        if e >= 1:
            break
        R_val = e / (1 - e ** 2)
        U_val = R_val * KAPPA
        ratio = R_val / U_val if U_val > 0 else 0
        data.append({
            'e': e, 'R': R_val, 'U': U_val,
            'ratio': ratio, 'eta': math.atanh(e)
        })
    return data


def compute_error_sweep():
    """Pre-compute error (ppm) vs eccentricity for ALL methods."""
    key_methods = [
        ("champion", r6_scor_champion),
        ("r6_varpro", r6_varpro_champion),
        ("r4_20exp", r4_20exp_champion),
        ("r5_varpro", r5_varpro_champion),
        ("r3_15exp", r3_15exp_champion),
        ("r2_3exp_v23", r2_3exp_v23_champion),
        ("r2_2exp_beater", r2_2exp_beater),
        ("ayala_raggi", ayala_raggi_r2_2exp),
        ("cantrell", cantrell),
        ("ramanujan_ii", ramanujan_ii),
        ("ramanujan_i", ramanujan1),
    ]
    data = []
    # Dense sampling: 500 points uniform + 200 extra in [0.9, 0.999]
    eccs = sorted(set(
        [i / 500.0 for i in range(1, 500)] +
        [0.9 + i * 0.0005 for i in range(200)]
    ))
    for e in eccs:
        if e <= 0 or e >= 1:
            continue
        a_val, b_val = 1.0, math.sqrt(1 - e ** 2)
        P_exact_val = exact_perimeter(a_val, b_val)
        point = {'e': e}
        for name, fn in key_methods:
            try:
                P_approx = fn(a_val, b_val)
                err = abs(P_approx / P_exact_val - 1) * 1e6
                if err < 1e-12:
                    err = 1e-12  # floor for log scale
            except Exception:
                err = float('nan')
            point[name] = err
        data.append(point)
    return data


def compute_signed_error_sweep():
    """Pre-compute SIGNED error (ppb) vs eccentricity for tower methods.

    This shows the equioscillation structure: the error alternates sign at
    N+1 points (Chebyshev theorem). Dense sampling (2000 points) is needed
    to resolve these oscillations.
    """
    tower_methods = [
        ("champion", r6_scor_champion),
        ("r6_varpro", r6_varpro_champion),
        ("r4_20exp", r4_20exp_champion),
        ("r5_varpro", r5_varpro_champion),
        ("r3_15exp", r3_15exp_champion),
        ("r2_3exp_v23", r2_3exp_v23_champion),
    ]
    data = []
    # Very dense: 2000 points, concentrated at high eccentricity where structure lives
    eccs = sorted(set(
        [i / 1000.0 for i in range(1, 1000)] +
        [0.9 + i * 0.0001 for i in range(1000)]
    ))
    for e in eccs:
        if e <= 0 or e >= 1:
            continue
        a_val, b_val = 1.0, math.sqrt(1 - e ** 2)
        P_exact_val = exact_perimeter(a_val, b_val)
        point = {'e': e}
        for name, fn in tower_methods:
            try:
                P_approx = fn(a_val, b_val)
                # SIGNED error in ppb (positive = overestimate, negative = underestimate)
                err_ppb = (P_approx / P_exact_val - 1) * 1e9
            except Exception:
                err_ppb = float('nan')
            point[name] = err_ppb
        data.append(point)
    return data


# Formula info for clickable display
FORMULA_INFO = {
    "Ramanujan I (1914)": """RAMANUJAN'S FIRST APPROXIMATION (1914)
=====================================

  P = pi * ( 3*(a + b) - sqrt( (3*a + b) * (a + 3*b) ) )

Variables:
  a = semi-major axis (the longer one)
  b = semi-minor axis (the shorter one)
  pi = 3.14159265358979323846...

No free parameters. Pure closed form.
Peak error: 1441 ppm at eccentricity e = 0.998.
Exact at e = 0 (circle: P = 2*pi*a).""",

    "Ramanujan II (1914)": """RAMANUJAN'S SECOND APPROXIMATION (1914)
=======================================

  h = ((a - b) / (a + b))^2

  P = pi * (a + b) * (1 + 3*h / (10 + sqrt(4 - 3*h)))

Variables:
  a = semi-major axis (the longer one)
  b = semi-minor axis (the shorter one)
  h = Ramanujan's eccentricity parameter, ranges from 0 (circle) to 1 (degenerate)
  pi = 3.14159265358979323846...

No free parameters. Pure closed form.
When b -> 0 (degenerate ellipse), evaluates R(1) = 22/7.
Peak error: 34.26 ppm at eccentricity e = 0.998.""",

    "Cantrell (2001)": """CANTRELL'S APPROXIMATION (2001)
================================

  h = ((a - b) / (a + b))^2
  delta = 4/pi - 14/11 = 0.0004025069685009...

  P = pi * (a + b) * (1 + 3*h / (10 + sqrt(4 - 3*h) + delta * h^1.5))

Variables:
  a = semi-major axis (the longer one)
  b = semi-minor axis (the shorter one)
  h = ((a-b)/(a+b))^2
  pi = 3.14159265358979323846...

1 parameter (delta). Closed form.
Corrects Ramanujan II's degenerate limit from 22/7 to 4/pi exactly.
Peak error: 39.57 ppm at eccentricity e = 0.998.""",

    "Ayala-Rendón R2/2exp (2025)": """AYALA-RENDÓN R2 + 2-EXPONENTIAL (2025)
======================================

  h = ((a - b) / (a + b))^2
  x = 1 - h

  R2(h) = pi * (a + b) * (1 + 3*h / (10 + sqrt(4 - 3*h)))

  A = 3.37528e-04
  B = 10.29662
  C = 6.48093e-05
  D = 40.89043

  P = R2(h) / (1 - A * exp(-B * x) - C * exp(-D * x))

Variables:
  a = semi-major axis
  b = semi-minor axis
  h = ((a-b)/(a+b))^2
  x = 1 - h  (ranges from 1 at circle to 0 at degenerate)
  exp = e^(...) where e = 2.71828...

4 free parameters (A, B, C, D).
The denominator correction is < 4e-4, making P very close to R2.
Peak error: 573.6 ppb.""",

    "Mamoun R2/3exp (0.083 ppm)": """R2 + 3-EXPONENTIAL, VERSION 23 (3-PARAMETER CHAMPION)
=====================================================

  h = ((a - b) / (a + b))^2
  x = 1 - h

  R2(h) = pi * (a + b) * (1 + 3*h / (10 + sqrt(4 - 3*h)))

  T    = 1 - 7*pi/22 = 0.00040250696850...   (the 22/7 - pi remainder)
  lam  = 6.8954698854899                       (decay scale)
  q    = 7/3 = 2.33333...                      (gate exponent, from CF of pi: 7/3)
  r1   = 1                                      (rate 1)
  r2   = 81/25 = 3.24                           (rate 2)
  r3   = 15                                     (rate 3)
  rho1 = 1.0                                    (ratio for term 1)
  rho2 = 0.3725797305793                        (ratio for term 2)
  rho3 = 0.0360560365885                        (ratio for term 3)
  S    = rho1 + rho2 + rho3 = 1.408635767168

  c1 = rho1 * T / S = 2.85784e-04
  c2 = rho2 * T / S = 1.06470e-04
  c3 = rho3 * T / S = 1.02987e-05

  phi(h) = c1 * exp(-r1 * lam * x)
         + c2 * exp(-r2 * lam * x)
         + c3 * exp(-r3 * lam * x)

  P = R2(h) / (1 - h^q * phi(h))

3 free parameters (lam, rho2, rho3). Rates and q fixed from pi structure.
Budget constraint: c1 + c2 + c3 = T = 4.025e-4 (exhausts the 22/7 remainder).
Peak error: 83.43 ppb (0.083 ppm).""",

    "Mamoun R4+20exp (0.492 ppb)": """R4 PADE TOWER + 20 EXPONENTIALS (0.492 ppb)
=============================================

  h = ((a - b) / (a + b))^2
  x = 1 - h
  k = (1 - sqrt(h)) / (1 + sqrt(h))   (nome-like parameter)

  BASE: P_R4(h) = pi * (1 + k) * R4(h)

  R4(h) = R2(h) + h^5  * N1(h)/D1(h)
                + h^10 * N2(h)/D2(h)

  where R2(h) = (1 + 3*h / (10 + sqrt(4 - 3*h)))

  Tower layer 1 (R3, pinned to 355/113):
    N1(h) = -5.7692e-05 + 2.0693e-04*h - 2.6893e-04*h^2 + 1.2660e-04*h^3
    D1(h) = 1.0 - 3.3333e+00*h + 2.8888e+00*h^2

  Tower layer 2 (R4, pinned to 103993/33102):
    N2(h) = 2.0577e-09 - 7.3830e-09*h + 9.5971e-09*h^2 - 4.5178e-09*h^3
    D2(h) = 1.0 - 3.3335e+00*h + 2.8891e+00*h^2

  CORRECTION: 20 exponential terms
  lam = 15.8023        (decay scale)
  q   = 2.5199         (gate exponent)
  T_4 = 1.84e-10       (budget: sum of all coefficients)

  Rate r_i   |   Coefficient c_i
  -----------|-----------------------
  1/3        |  (optimized, sum = T_4)
  3/7        |  ...
  3/4        |  ...
  1          |  ...
  7/6        |  ...
  7/3        |  ...
  3          |  ...
  81/25      |  ...
  292/63     |  ...
  5          |  ...
  7.56       |  ...
  9          |  ...
  12         |  ...
  15         |  ...
  17         |  ...
  25         |  ...
  30         |  ...
  35         |  ...
  45         |  ...
  70         |  ...

  phi(h) = sum_{i=1}^{20} c_i * exp(-r_i * lam * x)

  P = P_R4(h) / (1 - h^q * phi(h))

20 free parameters (18 ratios + lam + q). Rates fixed.
Peak error: 0.492 ppb at eccentricity e = 0.974.""",

    "Mamoun R5+16exp (0.045 ppb)": """R5 PADE TOWER + 20 EXPONENTIALS (0.508 ppb)
=============================================

  h = ((a - b) / (a + b))^2
  x = 1 - h
  k = (1 - sqrt(h)) / (1 + sqrt(h))

  BASE: P_R5(h) = pi * (1 + k) * R5(h)

  R5(h) = R2(h) + h^5  * N1(h)/D1(h)
                + h^10 * N2(h)/D2(h)
                + h^15 * N3(h)/D3(h)

  Tower layers 1-2: same as R4
  Tower layer 3 (R5, pinned to 104348/33215):
    N3, D3 computed from continued fraction convergent

  CORRECTION: 20 exponential terms
  lam = 15.2303        (decay scale)
  q   = 6.6769         (gate exponent)
  T_5 = 1.06e-10       (budget: sum of all coefficients)

  Rate r_i   |   Coefficient c_i
  -----------|-----------------------
  3/7        |  (optimized, sum = T_5)
  2/3        |  ...
  1          |  ...
  7/6        |  ...
  3/2        |  ...
  81/25      |  ...
  292/63     |  ...
  5          |  ...
  7          |  ...
  7.56       |  ...
  10         |  ...
  11         |  ...
  15         |  ...
  20         |  ...
  24         |  ...
  25         |  ...
  26         |  ...
  30         |  ...
  50         |  ...
  100        |  ...

  phi(h) = sum_{i=1}^{20} c_i * exp(-r_i * lam * x)

  P = P_R5(h) / (1 - h^q * phi(h))

20 free parameters (18 ratios + lam + q). Rates fixed.
Peak error: 0.508 ppb at eccentricity e = 0.996.""",

    "Mamoun R6+16exp (0.018 ppb)": """R6 PADE TOWER + 16 EXPONENTIALS — 0.018 ppb (Former Champion)
==================================================
0.018 ppb = 18 parts per trillion (March 2026)
Found via VARPRO coefficient-scale separation. Superseded by SCOR.

VARIABLES:
  a   = semi-major axis (the longer one)
  b   = semi-minor axis (the shorter one)
  h   = ((a - b) / (a + b))^2
  x   = 1 - h
  pi  = 3.14159265358979323846...
  exp = e^(...) where e = 2.71828182845904523536...

BASE TOWER: P_R6(h) = pi * (a + b) * R6(h)

  R6(h) = R2(h) + h^5  * N1(h)/D1(h)
                + h^10 * N2(h)/D2(h)
                + h^15 * N3(h)/D3(h)
                + h^20 * N4(h)/D4(h)

  R2(h) = 1 + 3*h / (10 + sqrt(4 - 3*h))

EXPONENTIAL CORRECTION (16 terms, VARPRO-optimized):
  lam     = 31.353           (global decay scale)
  q       = 11.818           (gate exponent)

Peak error: 0.018 ppb at eccentricity e ~ 0.97.""",

    "Mamoun R6+16exp+3log SCOR (0.007 ppb)": """R6 PADE TOWER + 16 EXPONENTIALS + 3 LOG TERMS — 0.007 ppb WORLD RECORD
=====================================================================
0.007 ppb = 7 parts per trillion (March 2026)
SCOR: Singularity-Conscious Optimal Reduction with Enrichment.

SCOR enriches the correction basis with x^k*ln(x) terms that directly
absorb the logarithmic singularity of E(m) at m=1 — the same singularity
that creates the BARF floor for purely analytic corrections.

VARIABLES:
  a   = semi-major axis (the longer one)
  b   = semi-minor axis (the shorter one)
  h   = ((a - b) / (a + b))^2
  x   = 1 - h
  pi  = 3.14159265358979323846...
  exp = e^(...) where e = 2.71828182845904523536...
  ln  = natural logarithm

BASE TOWER: P_R6(h) = pi * (a + b) * R6(h)

  R6(h) = R2(h) + h^5  * N1(h)/D1(h)
                + h^10 * N2(h)/D2(h)
                + h^15 * N3(h)/D3(h)
                + h^20 * N4(h)/D4(h)

  R2(h) = 1 + 3*h / (10 + sqrt(4 - 3*h))

  4 Pade layers pin R(1) to successive convergents of 4/pi:
    T_3 = 1 - 113*pi/355      = 8.49e-08
    T_4 = 1 - 33102*pi/103993 = 1.84e-10
    T_5 = 1 - 33215*pi/104348 = 1.06e-10
    T_6 = 1 - 66317*pi/208341 = 3.93e-11

MIXED SCOR CORRECTION (16 exp + 3 log terms):
  lam     = 31.552           (global decay scale)
  q       = 12.415           (gate exponent)

  EXPONENTIAL TERMS (16):
  i  |  Rate r_i     |  Coefficient c_i
  ---|--------------|--------------------
   1 |  0.01017     |  2.662e-04
   2 |  0.07777     | -8.682e-04
   3 |  0.19901     |  1.417e-03
   4 |  0.33804     | -1.523e-03
   5 |  0.49710     |  1.050e-03
   6 |  0.70707     | -5.408e-04
   7 |  0.87220     |  1.930e-04
   8 |  2.73148     |  3.535e-06
   9 |  4.74024     |  1.156e-06
  10 |  9.97044     |  6.182e-07
  11 | 14.93644     | -3.132e-07
  12 | 20.67302     |  3.990e-07
  13 | 29.72962     | -2.266e-07
  14 | 37.55442     |  1.279e-07
  15 | 125.32824    | -8.260e-09
  16 | 135.77786    |  1.099e-08

  LOGARITHMIC ENRICHMENT TERMS (3):
   d_1 * x * ln(x)     =  1.902e-06 * x * ln(x)
   d_2 * x^2 * ln(x)   = -4.374e-04 * x^2 * ln(x)
   d_3 * x^3 * ln(x)   =  1.178e-03 * x^3 * ln(x)

FINAL FORMULA:
  phi(h) = sum_i c_i * exp(-r_i * 31.552 * x)
         + d_1 * x*ln(x) + d_2 * x^2*ln(x) + d_3 * x^3*ln(x)

  P = P_R6(h) / (1 - h^12.415 * phi(h))

Peak error: 0.007 ppb at eccentricity e ~ 0.975.
Verified at 300 decimal digits.""",
}

# ---------------------------------------------------------------------------
# Rich HTML formulas — ONE equation, EVERY number literal, no shorthand
# ---------------------------------------------------------------------------

def _fmt_sci(v):
    """Format a float as '±M.NNNNNN × 10^E' HTML."""
    if v == 0:
        return '0'
    sign = '&minus;' if v < 0 else '+'
    av = abs(v)
    e = int(math.floor(math.log10(av)))
    m = av / 10**e
    return f'{sign}{m:.6f} &times; 10<sup>{e}</sup>'

def _fmt_sci_nosign(v):
    """Format without leading sign."""
    if v == 0:
        return '0'
    prefix = '&minus;' if v < 0 else ''
    av = abs(v)
    e = int(math.floor(math.log10(av)))
    m = av / 10**e
    return f'{prefix}{m:.6f} &times; 10<sup>{e}</sup>'

def _build_exp_terms_html(rates, coeffs, lam):
    """Build fully explicit exponential terms, every symbol shown."""
    lines = []
    for i, (r, c) in enumerate(zip(rates, coeffs)):
        decay = r * lam
        c_str = _fmt_sci_nosign(c) if i == 0 else _fmt_sci(c)
        prefix = '&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;' if i > 0 else ''
        lines.append(f'{prefix}{c_str} &middot; e<sup>&minus;{decay:.6f} &middot; (1&minus;h)</sup>')
    return '<br>\n        '.join(lines)

def _build_coeff_table(rates, coeffs, lam):
    """Build HTML table of all rates, decays, and coefficients."""
    rows = ''
    for i, (r, c) in enumerate(zip(rates, coeffs)):
        decay = r * lam
        # Format rate as fraction if possible
        if isinstance(r, float) and r == int(r):
            r_str = str(int(r))
        else:
            r_str = f'{r:.6g}'
        rows += (f'<tr><td style="text-align:center">{i+1}</td>'
                 f'<td>{r_str}</td>'
                 f'<td style="text-align:right">{decay:.6f}</td>'
                 f'<td style="text-align:right">{c:+.6e}</td></tr>\n          ')
    return rows

def _tower_formula_html(title, color, tower_level, n_layers_desc,
                        rates, coeffs, lam, q, peak_err_str, peak_e_str):
    """Generate rich HTML for any tower+exponential champion formula."""
    n = len(rates)
    terms = _build_exp_terms_html(rates, coeffs, lam)
    table = _build_coeff_table(rates, coeffs, lam)

    # Tower layer equations
    tower_eq = 'R<sub>2</sub>(h)'
    for k in range(1, int(tower_level) - 1):
        onset = 5 * k
        tower_eq += f'\n        + h<sup>{onset}</sup> &middot; N<sub>{k}</sub>(h)/D<sub>{k}</sub>(h)'

    return f'''<div class="theorem-box" style="border-color:{color};">
      <div class="title" style="color:{color}; font-size:18px;">{title}</div>

      <p style="margin:12px 0 8px; font-size:15px; color:var(--bright);">Given semi-axes a &ge; b &gt; 0, compute:</p>
      <div class="eq" style="font-size:18px; text-align:left; padding-left:40px;">
        h = ((a &minus; b) / (a + b))<sup>2</sup>
      </div>

      <p style="margin:12px 0 8px; font-size:15px; color:var(--bright);">Pad&eacute; tower base ({n_layers_desc}):</p>
      <div class="eq" style="font-size:16px; text-align:left; padding-left:40px;">
        R<sub>2</sub>(h) = 1 + 3h / (10 + &radic;(4 &minus; 3h))
      </div>
      <div class="eq" style="font-size:16px; text-align:left; padding-left:40px; margin-top:8px;">
        R<sub>{tower_level}</sub>(h) = {tower_eq}
      </div>

      <p style="margin:16px 0 8px; font-size:15px; color:var(--bright);">
        All {n} exponential correction terms, every one fully explicit
        (&lambda; = {lam}, q = {q}):</p>
      <div class="eq" style="font-size:15px; text-align:left; padding-left:20px; border:1px solid var(--border); border-radius:6px; padding:16px; overflow-x:auto;">
        &phi;(h) =<br>
        {terms}
      </div>

      <p style="margin:16px 0 8px; font-size:15px; color:var(--bright);">
        <strong style="font-size:18px; color:{color};">FINAL ANSWER:</strong></p>
      <div class="eq" style="font-size:22px; color:{color}; border:1px solid {color}; border-radius:6px; padding:16px; margin:8px 0;">
        P = &pi; &middot; (a + b) &middot; R<sub>{tower_level}</sub>(h) / (1 &minus; h<sup>{q}</sup> &middot; &phi;(h))
      </div>

      <p style="margin:16px 0 8px; font-size:15px; color:var(--bright);">Complete coefficient table (all {n} terms):</p>
      <table style="font-size:14px; width:auto; margin:0 auto;">
        <thead><tr>
          <th style="text-align:center; padding:4px 14px;">i</th>
          <th style="text-align:left; padding:4px 14px;">Rate r<sub>i</sub></th>
          <th style="text-align:right; padding:4px 14px;">Decay r<sub>i</sub>&middot;&lambda;</th>
          <th style="text-align:right; padding:4px 14px;">Coefficient c<sub>i</sub></th>
        </tr></thead>
        <tbody>
          {table}
        </tbody>
      </table>
      <p style="margin:12px 0; font-size:14px; color:#a0a8b8;">
        Peak error: {peak_err_str} at e = {peak_e_str}</p>
    </div>'''

# V23 coefficients for explicit display
_T_FLAT = 1.0 - 7.0 * math.pi / 22.0  # 22/7 remainder
_v23_c1 = _T_FLAT / (1.0 + 0.3725797305793 + 0.0360560365885)
_v23_c2 = 0.3725797305793 * _v23_c1
_v23_c3 = 0.0360560365885 * _v23_c1
_v23_lam = 6.8954698854899
_v23_d1 = _v23_lam * 1.0
_v23_d2 = _v23_lam * 3.24
_v23_d3 = _v23_lam * 15.0
_cantrell_delta = 4.0 / math.pi - 14.0 / 11.0

FORMULA_HTML = {
    "Ramanujan I (1914)": '''<div class="theorem-box">
      <div class="title" style="font-size:18px;">RAMANUJAN I (1914), 1441 ppm</div>
      <div class="eq" style="font-size:24px; color:var(--bright); border:1px solid var(--accent); border-radius:6px; padding:20px; margin:12px 0;">
        P &nbsp;=&nbsp; &pi; &middot; ( 3(a + b) &minus; &radic;( (3a + b)(a + 3b) ) )
      </div>
      <p style="margin:8px 0; font-size:14px; color:#a0a8b8;">
        a = semi-major axis, b = semi-minor axis. No free parameters.</p>
    </div>''',

    "Ramanujan II (1914)": '''<div class="theorem-box">
      <div class="title" style="font-size:18px;">RAMANUJAN II (1914), 34.26 ppm</div>
      <p style="margin:8px 0; font-size:14px; color:#a0a8b8;">h = ((a&minus;b)/(a+b))&sup2;</p>
      <div class="eq" style="font-size:24px; color:var(--bright); border:1px solid var(--accent); border-radius:6px; padding:20px; margin:12px 0;">
        P &nbsp;=&nbsp; &pi;(a + b)(1 + 3h / (10 + &radic;(4 &minus; 3h)))
      </div>
      <p style="margin:8px 0; font-size:14px; color:#a0a8b8;">
        No free parameters. When b&rarr;0: P = 2a&middot;22/7 (thinks &pi; = 22/7).</p>
    </div>''',

}

# ---------------------------------------------------------------------------
# LaTeX formulas for KaTeX rendering — ONE equation each, all numbers explicit
# ---------------------------------------------------------------------------

def _exp_terms_latex(rates, coeffs, lam):
    """Build LaTeX for sum of exponential terms with all decays computed."""
    parts = []
    for i, (r, c) in enumerate(zip(rates, coeffs)):
        d = r * lam
        sign = '+' if c >= 0 else '-'
        ac = abs(c)
        # Find mantissa and exponent
        import math as _m
        exp_val = int(_m.floor(_m.log10(ac))) if ac > 0 else 0
        mantissa = ac / 10**exp_val
        term = f'{mantissa:.4f} \\!\\times\\! 10^{{{exp_val}}} \\, e^{{-{d:.4f}\\,(1-h)}}'
        if i == 0:
            parts.append(f'{"-" if c < 0 else ""}{term}')
        else:
            parts.append(f'{sign} {term}')
    # Join with line breaks for readability
    return ' \\\\[4pt]\n    &\\quad '.join(parts)

# Build LaTeX for tower Padé base from actual coefficients
import sys as _sys
_sys.path.insert(0, os.path.join(_demo_dir, '..', 'src'))
from formulas import _TOWER

def _sci_latex(v):
    """Format a float as LaTeX scientific notation: ±M.MMMM × 10^{E}."""
    if v == 0:
        return '0'
    sign = '-' if v < 0 else '+'
    av = abs(v)
    e = int(math.floor(math.log10(av)))
    m = av / 10**e
    if e == 0:
        return f'{sign}{m:.4f}'
    elif e == 1:
        return f'{sign}{m:.4f} \\!\\times\\! 10'
    else:
        return f'{sign}{m:.4f} \\!\\times\\! 10^{{{e}}}'

def _tower_base_latex(n_layers):
    """Build LaTeX for tower base R_k(h) with all polynomial coefficients."""
    parts = ['1 + \\dfrac{3h}{10 + \\sqrt{4-3h}}']
    for i in range(n_layers):
        layer = _TOWER[i]
        N = layer['N']
        D = layer['D']
        onset = layer['onset']
        # Format numerator polynomial
        n_terms = []
        for j, coeff in enumerate(N):
            if abs(coeff) < 1e-30:
                continue
            c_str = _sci_latex(coeff)
            if j == 0:
                n_terms.append(c_str)
            elif j == 1:
                n_terms.append(f'{c_str} \\cdot h')
            else:
                n_terms.append(f'{c_str} \\cdot h^{j}')
        num = ' '.join(n_terms)
        # Format denominator polynomial
        d_terms = []
        for j, coeff in enumerate(D):
            if abs(coeff) < 1e-30:
                continue
            c_str = _sci_latex(coeff)
            if j == 0:
                d_terms.append(c_str)
            elif j == 1:
                d_terms.append(f'{c_str} \\cdot h')
            else:
                d_terms.append(f'{c_str} \\cdot h^{j}')
        den = ' '.join(d_terms)
        parts.append(f'h^{{{onset}}} \\cdot \\dfrac{{{num}}}{{{den}}}')
    # Use & alignment marks so it works inside \begin{aligned}
    lines = ['& ' + parts[0]]
    for p in parts[1:]:
        lines.append('& + ' + p)
    return ' \\\\[6pt]\n'.join(lines)

FORMULA_LATEX = {
    "Ramanujan I (1914)": {
        "title": "Ramanujan I (1914)",
        "subtitle": "No free parameters. Peak error: 1441 ppm.",
        "color": "#58a6ff",
        "latex": r"P \;=\; \pi \!\left(\, 3(a+b) \;-\; \sqrt{(3a+b)(a+3b)} \,\right)",
        "where": r"a = \text{semi-major axis},\; b = \text{semi-minor axis}",
    },
    "Ramanujan II (1914)": {
        "title": "Ramanujan II (1914)",
        "subtitle": "No free parameters. Peak error: 34.26 ppm.",
        "color": "#58a6ff",
        "latex": r"P \;=\; \pi(a+b)\!\left(1 + \frac{3h}{10 + \sqrt{4-3h}}\right)",
        "where": r"h = \left(\frac{a-b}{a+b}\right)^{\!2}",
    },
    "Cantrell (2001)": {
        "title": "Cantrell (2001)",
        "subtitle": "1 parameter. Peak error: 39.57 ppm.",
        "color": "#58a6ff",
        "latex": r"P \;=\; \pi(a+b)\!\left(1 + \frac{3h}{10 + \sqrt{4-3h} + 0.000512272 \cdot h^{3/2}}\right)",
        "where": r"h = \left(\frac{a-b}{a+b}\right)^{\!2}",
    },
    "Ayala-Rendón R2/2exp (2025)": {
        "title": "Ayala Raggi & Rendón Marín (2025)",
        "subtitle": "4 parameters. Peak error: 574 ppb. Previous state of the art.",
        "color": "#bc8cff",
        "latex": (r"P \;=\; \frac{\pi(a+b)\!\left(1 + \dfrac{3h}{10 + \sqrt{4-3h}}\right)}"
                  r"{1 \;-\; 3.37528\!\times\!10^{-4}\, e^{-10.29662\,(1-h)}"
                  r"\;-\; 6.48093\!\times\!10^{-5}\, e^{-40.89043\,(1-h)}}"),
        "where": r"h = \left(\frac{a-b}{a+b}\right)^{\!2}",
    },
    "Mamoun R2/2exp (0.530 ppm)": {
        "title": "Mamoun R₂/2exp (0.530 ppm)",
        "subtitle": "4 parameters. Beats Ayala-Rendón by 8%. Multiplicative form, T-pinned (A+B = 1 - 7pi/22).",
        "color": "#e8b4fe",
        "latex": (r"P \;=\; \pi(a+b)\!\left(1 + \frac{3h}{10 + \sqrt{4-3h}}\right)"
                  r"\!\left(1 + h^{0.01}\!\left("
                  r"6.5882\!\times\!10^{-5}\, e^{-40.1273\,(1-h)}"
                  r"\;+\; 3.3646\!\times\!10^{-4}\, e^{-10.2653\,(1-h)}"
                  r"\right)\right)"),
        "where": r"h = \left(\frac{a-b}{a+b}\right)^{\!2},\quad A+B = 1 - \tfrac{7\pi}{22} \approx 4.023\!\times\!10^{-4}",
    },
    "Mamoun R2/3exp (0.083 ppm)": {
        "title": "Mamoun R₂/3exp (0.083 ppm)",
        "subtitle": "1 free parameter. 6.9x improvement over Ayala-Rendón. Our simplest world record.",
        "color": "#58a6ff",
        "latex": (r"P \;=\; \frac{\pi(a+b)\!\left(1 + \dfrac{3h}{10 + \sqrt{4-3h}}\right)}"
                  r"{1 \;-\; h^{7/3}\!\left("
                  r"2.8562\!\times\!10^{-4}\, e^{-6.8955\,(1-h)}"
                  r"\;+\; 1.0642\!\times\!10^{-4}\, e^{-22.341\,(1-h)}"
                  r"\;+\; 1.0298\!\times\!10^{-5}\, e^{-103.43\,(1-h)}"
                  r"\right)}"),
        "where": r"h = \left(\frac{a-b}{a+b}\right)^{\!2}",
    },
}

# Tower methods — build from actual data
_r3_base = _tower_base_latex(1)
_r4_base = _tower_base_latex(2)
_r5_base = _tower_base_latex(3)
_r6_base = _tower_base_latex(4)

_r3_exp = _exp_terms_latex(
    [3/7, 2/3, 1, 7/6, 3/2, 53/25, 81/25, 162/25, 189/25, 13, 15, 292/15, 24, 30, 35],
    [1.0690331487437538e-06, -5.3446219367020315e-06, -4.0279727459249e-06,
     -5.069600273319092e-06, -5.344344263799115e-06, 3.8078085513734217e-06,
     9.539748048443633e-06, -3.4773795578775624e-06, 1.0344348076505942e-05,
     -3.937426561235638e-06, -3.3525450185435064e-06, 1.0593006595991767e-05,
     -3.0640908934958932e-06, -5.328578613384776e-06, 3.677529114762622e-06],
    14.563322134576083)

_r4_exp = _exp_terms_latex(
    [1/3, 3/7, 3/4, 1, 7/6, 7/3, 3, 81/25, 292/63, 5, 7.56, 9, 12, 15, 17, 25, 30, 35, 45, 70],
    [-1.5937722286313696e-06, 4.004676507772733e-06, -6.07781259758309e-06,
     -1.7887837164351737e-05, 7.004699361980741e-06, -1.534340458195682e-06,
     8.604354677488707e-06, -5.918840736648467e-07, 4.016298270455695e-06,
     2.308529236939859e-06, -4.070618365020088e-06, 6.387425123480058e-06,
     -4.4507260538806865e-07, -7.202231753854354e-06, 9.243836492981317e-06,
     -3.985839132116884e-06, -1.6398228803520656e-06, 5.453076591436378e-06,
     -2.3199601822721373e-06, 3.261112304827786e-07],
    15.802299362305348)

_r5_exp = _exp_terms_latex(
    [3/7, 2/3, 1, 7/6, 3/2, 81/25, 292/63, 5, 7, 7.56, 10, 11, 15, 20, 24, 25, 26, 30, 50, 100],
    [4.826487614666834e-06, -2.3995431024901575e-05, -1.3983149966928165e-05,
     3.610773363134473e-05, -2.0627570247922536e-05, 1.8361450410777854e-05,
     -3.036496371952144e-05, 2.986798101900685e-05, 6.102770545532203e-06,
     -2.1721342929309672e-05, 4.818843318153823e-05, -3.0029777963704074e-05,
     -1.8709454471278563e-05, 3.539671949510961e-05, 2.201634954838419e-05,
     -3.665046743365169e-05, -2.6884550639689826e-05, 2.3025674645330903e-05,
     -1.017872383950891e-06, 9.108624972732102e-08],
    15.230301669375985)

_r6_exp = _exp_terms_latex(
    [0.2770728913534926, 0.3765766461829889, 0.43518732502096386,
     0.6227919873574936, 0.7120771475689809, 0.9652822045811873,
     1.1225804496593386, 2.4505928930768612, 3.9272773944603014,
     8.553444360039164, 15.942147112122198, 16.918705322192356,
     29.708859382748724, 35.59586275256653, 120.40919165741495,
     149.61328333612892],
    [-7.477482549632848e-05, 8.480101043445639e-04, -1.374994156479528e-03,
     2.150905621364287e-03, -1.958123011624892e-03, 5.984415445829431e-04,
     -2.022984114091492e-04, 8.697909560225977e-06, 2.451640251690270e-06,
     1.740698079585359e-06, -5.234051452543231e-06, 5.452650342659784e-06,
     -8.112790710470234e-07, 5.347009897739028e-07, -2.118336446855793e-08,
     2.201043493782428e-08],
    23.39233408908156)

FORMULA_LATEX["Mamoun R3+15exp (1.427 ppb)"] = {
    "title": "Mamoun R\u2083 + 15 Exponentials (1.427 ppb)",
    "subtitle": "Pad\u00e9 tower pinned to 355/113. 15 correction terms.",
    "color": "#f0883e",
    "latex_num": (r"\pi(a+b)\!\left[\begin{aligned}" + "\n" +
                  _r3_base + r"\end{aligned}\right]"),
    "latex_den": (r"1 \;-\; h^{3.4164}\!\left(\begin{aligned}" + "\n    &" +
                  _r3_exp + r"\end{aligned}\right)"),
    "where": r"h = \left(\frac{a-b}{a+b}\right)^{\!2}",
}

FORMULA_LATEX["Mamoun R4+20exp (0.492 ppb)"] = {
    "title": "Mamoun R₄ + 20 Exponentials (0.492 ppb)",
    "subtitle": "Padé tower pinned to 103993/33102. 20 correction terms.",
    "color": "#e8a832",
    "latex_num": (r"\pi(a+b)\!\left[\begin{aligned}" + "\n" +
                  _r4_base + r"\end{aligned}\right]"),
    "latex_den": (r"1 \;-\; h^{2.5199}\!\left(\begin{aligned}" + "\n    &" +
                  _r4_exp + r"\end{aligned}\right)"),
    "where": r"h = \left(\frac{a-b}{a+b}\right)^{\!2}",
}

FORMULA_LATEX["Mamoun R5+16exp (0.045 ppb)"] = {
    "title": "Mamoun R₅ + 20 Exponentials (0.508 ppb)",
    "subtitle": "Padé tower pinned to 104348/33215. 20 correction terms.",
    "color": "#bc8cff",
    "latex_num": (r"\pi(a+b)\!\left[\begin{aligned}" + "\n" +
                  _r5_base + r"\end{aligned}\right]"),
    "latex_den": (r"1 \;-\; h^{6.6769}\!\left(\begin{aligned}" + "\n    &" +
                  _r5_exp + r"\end{aligned}\right)"),
    "where": r"h = \left(\frac{a-b}{a+b}\right)^{\!2}",
}

FORMULA_LATEX["Mamoun R6+16exp (0.018 ppb)"] = {
    "title": "Mamoun R₆ + 16 Exponentials (0.018 ppb)",
    "subtitle": "Former champion. VARPRO + L-BFGS-B continuous rate refinement. Padé tower pinned to 208341/66317.",
    "color": "#3fb950",
    "latex_num": (r"\pi(a+b)\!\left[\begin{aligned}" + "\n" +
                  _r6_base + r"\end{aligned}\right]"),
    "latex_den": (r"1 \;-\; h^{7.687}\!\left(\begin{aligned}" + "\n    &" +
                  _r6_exp + r"\end{aligned}\right)"),
    "where": r"h = \left(\frac{a-b}{a+b}\right)^{\!2}",
}

# SCOR champion — build LaTeX for the mixed exp + log basis
_r6_scor_exp = _exp_terms_latex(
    [0.010166999187513546, 0.07776780092888144, 0.19901003723401806,
     0.338043080886615, 0.4971009768543303, 0.7070725423114185,
     0.8722016136238608, 2.7314795971348453, 4.740243707070392,
     9.970442852904373, 14.936436441424814, 20.673019711422043,
     29.729616427543093, 37.55442387982917, 125.32824271647245,
     135.77785701559],
    [0.00026618116484864926, -0.0008681885839445673, 0.0014174476376588706,
     -0.0015231308488015433, 0.0010502084585483412, -0.000540825515736969,
     0.00019300900837453404, 3.5348485318019746e-06, 1.1557743338413409e-06,
     6.181548524889021e-07, -3.1316471711835696e-07, 3.989652643111546e-07,
     -2.2656409450964743e-07, 1.2789922739378625e-07, -8.259915063897185e-09,
     1.098662224931808e-08],
    31.55228058803741)

# Add log terms to the SCOR LaTeX
_r6_scor_log = (r"+ 1.9018 \!\times\! 10^{-6} \, x\ln x \\[4pt]"
                "\n    &\\quad "
                r"- 4.3741 \!\times\! 10^{-4} \, x^2\ln x \\[4pt]"
                "\n    &\\quad "
                r"+ 1.1782 \!\times\! 10^{-3} \, x^3\ln x")

FORMULA_LATEX["Mamoun R6+16exp+3log SCOR (0.007 ppb)"] = {
    "title": "Mamoun R₆ + 16exp + 3log SCOR (0.007 ppb)",
    "subtitle": "WORLD RECORD. SCOR enriches the basis with x^k ln(x) terms that absorb the logarithmic singularity. Padé tower pinned to 208341/66317. 2.5× below former champion.",
    "color": "#ffd700",
    "latex_num": (r"\pi(a+b)\!\left[\begin{aligned}" + "\n" +
                  _r6_base + r"\end{aligned}\right]"),
    "latex_den": (r"1 \;-\; h^{12.415}\!\left(\begin{aligned}" + "\n    &" +
                  _r6_scor_exp + r" \\[6pt]" + "\n    &\\quad " +
                  _r6_scor_log +
                  r"\end{aligned}\right)"),
    "where": r"h = \left(\frac{a-b}{a+b}\right)^{\!2}, \quad x = 1-h",
}

# Keep FORMULA_HTML as empty — we use FORMULA_LATEX + KaTeX now
FORMULA_HTML = {}

PUBLISHED_MAX_PPM = {
    "Ayala-Rendón R2/2exp (2025)": 0.5735751744673223,
    "Mamoun R2/2exp (0.530 ppm)": 0.5304962574781413,
    "Mamoun R2/3exp (0.083 ppm)": 0.08342607871192342,
    "Mamoun R3+15exp (1.427 ppb)": 0.0014268262127359321,
    "Mamoun R4+20exp (0.492 ppb)": 0.000491637397459499,
    "Mamoun R5+16exp (0.045 ppb)": 4.539094362333431e-05,
    "Mamoun R6+16exp (0.018 ppb)": 1.772e-05,
    "Mamoun R6+16exp+3log SCOR (0.007 ppb)": 6.978e-06,
}


def compute_max_errors():
    """Pre-compute the peak error and worst-case eccentricity for all methods."""
    max_errors = {}
    for name, fn, _ in METHODS:
        best_err = 0
        best_e = 0
        for i in range(1, 999):
            e = i / 1000.0
            a_val, b_val = 1.0, math.sqrt(1 - e * e)
            P_exact_val = exact_perimeter(a_val, b_val)
            try:
                P_approx = fn(a_val, b_val)
                err = abs(P_approx / P_exact_val - 1) * 1e6
            except Exception:
                err = 0
            if err > best_err:
                best_err = err
                best_e = e
        max_errors[name] = {'max_ppm': best_err, 'at_e': best_e}
        if name in PUBLISHED_MAX_PPM:
            max_errors[name]['max_ppm'] = PUBLISHED_MAX_PPM[name]
    return max_errors


def compute_winner_data_mpmath():
    """Pre-compute accurate winner/runner-up at each eccentricity using mpmath.

    Evaluates ALL formulas at 30-digit precision to eliminate float64 noise.
    Returns list of {e, winner, runner} where winner/runner are method keys.
    """
    import mpmath as mp
    mp.mp.dps = 30

    # Tower layers (from formulas.py _TOWER, already computed at import)
    from formulas import _TOWER

    def mp_exact_perimeter(a, b):
        return 4 * a * mp.ellipe(1 - (b/a)**2)

    def mp_ramanujan1(a, b):
        return mp.pi * (3*(a+b) - mp.sqrt((3*a+b)*(a+3*b)))

    def mp_ramanujan_ii(a, b):
        h = ((a-b)/(a+b))**2
        return mp.pi * (a+b) * (1 + 3*h / (10 + mp.sqrt(4 - 3*h)))

    def mp_cantrell(a, b):
        h = ((a-b)/(a+b))**2
        delta = 4/mp.pi - mp.mpf(14)/11
        return mp.pi * (a+b) * (1 + 3*h / (10 + mp.sqrt(4 - 3*h) + delta * h**mp.mpf('1.5')))

    def mp_tower_base(h, level):
        R = 1 + 3*h / (10 + mp.sqrt(4 - 3*h))
        for i in range(min(level, len(_TOWER))):
            layer = _TOWER[i]
            N = [mp.mpf(x) for x in layer['N']]
            D = [mp.mpf(x) for x in layer['D']]
            onset = layer['onset']
            Nv = N[0] + h*(N[1] + h*(N[2] + h*N[3]))
            Dv = D[0] + h*(D[1] + h*D[2])
            if abs(Dv) > 1e-30:
                R += h**onset * Nv / Dv
        return R

    def mp_tower_corrected(a, b, level, rates, coeffs, lam, q):
        h = ((a-b)/(a+b))**2
        x = 1 - h
        R = mp_tower_base(h, level)
        P_Rk = mp.pi * (a+b) * R
        phi = sum(mp.mpf(c) * mp.exp(-mp.mpf(r) * mp.mpf(lam) * x) for r, c in zip(rates, coeffs))
        denom = 1 - h**mp.mpf(q) * phi
        return P_Rk / denom

    def mp_tower_corrected_scor(a, b, level, rates, exp_coeffs, log_coeffs, lam, q):
        h = ((a-b)/(a+b))**2
        x = 1 - h
        R = mp_tower_base(h, level)
        P_Rk = mp.pi * (a+b) * R
        phi = sum(mp.mpf(c) * mp.exp(-mp.mpf(r) * mp.mpf(lam) * x) for r, c in zip(rates, exp_coeffs))
        if x > 0:
            lnx = mp.log(x)
            xk = x
            for d in log_coeffs:
                phi += mp.mpf(d) * xk * lnx
                xk *= x
        denom = 1 - h**mp.mpf(q) * phi
        return P_Rk / denom

    # Import formula constants
    from formulas import (_R3_15_RATES, _R3_15_COEFFS, _R3_15_LAM, _R3_15_Q,
                          _R4_20_RATES, _R4_20_COEFFS, _R4_20_LAM, _R4_20_Q,
                          _R5_VP_RATES, _R5_VP_COEFFS, _R5_VP_LAM, _R5_VP_Q,
                          _R6_VP_RATES, _R6_VP_COEFFS, _R6_VP_LAM, _R6_VP_Q,
                          _R6_SCOR_RATES, _R6_SCOR_EXP_COEFFS,
                          _R6_SCOR_LOG_COEFFS, _R6_SCOR_LAM, _R6_SCOR_Q)

    # Ayala-Raggi constants
    A2, B2, C2, D2 = mp.mpf('3.37528e-4'), mp.mpf('10.29662'), mp.mpf('6.48093e-5'), mp.mpf('40.89043')
    def mp_ayala(a, b):
        h = ((a-b)/(a+b))**2; x = 1 - h
        R2 = mp.pi * (a+b) * (1 + 3*h / (10 + mp.sqrt(4 - 3*h)))
        return R2 / (1 - A2*mp.exp(-B2*x) - C2*mp.exp(-D2*x))

    # R2/2exp beater
    def mp_r2_2exp(a, b):
        h = ((a-b)/(a+b))**2; x = 1 - h
        R2 = mp.pi * (a+b) * (1 + 3*h / (10 + mp.sqrt(4 - 3*h)))
        A, B = mp.mpf('0.0000658824'), mp.mpf('0.0003364551')
        phi = A * mp.exp(mp.mpf('-40.127330') * x) + B * mp.exp(mp.mpf('-10.265288') * x)
        return R2 * (1 + h**mp.mpf('0.01') * phi)

    # R2/3exp v23: rates [1, 81/25, 15], q=7/3
    from formulas import _LAM_V23, _A_V23, _B_V23, _C_V23, _Q_V23, _M_OPT, _N
    def mp_r2_3exp(a, b):
        h = ((a-b)/(a+b))**2; x = 1 - h
        R2 = mp.pi * (a+b) * (1 + 3*h / (10 + mp.sqrt(4 - 3*h)))
        lam = mp.mpf(_LAM_V23)
        phi = (mp.mpf(_A_V23) * mp.exp(-lam * x)
             + mp.mpf(_B_V23) * mp.exp(-mp.mpf(_M_OPT) * lam * x)
             + mp.mpf(_C_V23) * mp.exp(-mp.mpf(_N) * lam * x))
        return R2 / (1 - h**mp.mpf(_Q_V23) * phi)

    method_fns = [
        ('champion',        lambda a, b: mp_tower_corrected_scor(a, b, 4, _R6_SCOR_RATES, _R6_SCOR_EXP_COEFFS, _R6_SCOR_LOG_COEFFS, _R6_SCOR_LAM, _R6_SCOR_Q)),
        ('r6_varpro',       lambda a, b: mp_tower_corrected(a, b, 4, _R6_VP_RATES, _R6_VP_COEFFS, _R6_VP_LAM, _R6_VP_Q)),
        ('r4_20exp',        lambda a, b: mp_tower_corrected(a, b, 2, _R4_20_RATES, _R4_20_COEFFS, _R4_20_LAM, _R4_20_Q)),
        ('r5_varpro',       lambda a, b: mp_tower_corrected(a, b, 3, _R5_VP_RATES, _R5_VP_COEFFS, _R5_VP_LAM, _R5_VP_Q)),
        ('r3_15exp',        lambda a, b: mp_tower_corrected(a, b, 1, _R3_15_RATES, _R3_15_COEFFS, _R3_15_LAM, _R3_15_Q)),
        ('r2_3exp_v23',     mp_r2_3exp),
        ('r2_2exp_beater',  mp_r2_2exp),
        ('ayala_raggi',     mp_ayala),
        ('cantrell',        mp_cantrell),
        ('ramanujan_ii',    mp_ramanujan_ii),
        ('ramanujan_i',     mp_ramanujan1),
    ]

    # Sample at ~500 points across the log-e axis used by the winner band
    # xVal = -log10(1-e), range [0, 3.5], 500 steps
    data = []
    n_pts = 500
    for i in range(n_pts):
        xVal = i / n_pts * 3.5
        e_f = 1 - 10**(-xVal)
        if e_f <= 0 or e_f >= 1:
            continue
        e = mp.mpf(e_f)
        a = mp.mpf(1)
        b = mp.sqrt(1 - e**2)
        P_exact = mp_exact_perimeter(a, b)

        errs = {}
        for key, fn in method_fns:
            try:
                P_approx = fn(a, b)
                errs[key] = float(abs(P_approx / P_exact - 1) * 1e6)
            except Exception:
                errs[key] = float('inf')

        # Winner (all methods)
        winner = min(errs, key=lambda k: errs[k])
        # Runner-up (excluding champion)
        runner_errs = {k: v for k, v in errs.items() if k != 'champion'}
        runner = min(runner_errs, key=lambda k: runner_errs[k])

        data.append({'e': float(e_f), 'winner': winner, 'runner': runner,
                     'winErr': errs[winner], 'runErr': errs[runner]})

    return data


# Pre-compute data at startup
print("  Pre-computing sweep data...", end=" ", flush=True)
SWEEP_DATA = compute_sweep_over_eccentricities()
print("done.")
print("  Pre-computing error landscape...", end=" ", flush=True)
ERROR_SWEEP = compute_error_sweep()
print("done.")
print("  Pre-computing peak errors...", end=" ", flush=True)
MAX_ERRORS = compute_max_errors()
for name, info in MAX_ERRORS.items():
    if info['max_ppm'] < 1:
        print(f"\n    {name}: {info['max_ppm']*1000:.3f} ppb at e={info['at_e']:.3f}", end="")
print("\n  done.")
print("  Pre-computing signed error sweep (2000 pts)...", end=" ", flush=True)
SIGNED_SWEEP = compute_signed_error_sweep()
print("done.")
print("  Pre-computing accurate winner data (mpmath 30d)...", end=" ", flush=True)
WINNER_DATA = compute_winner_data_mpmath()
print("done.")


# ---------------------------------------------------------------------------
# HTML page (all-in-one: CSS + JS + HTML)
# ---------------------------------------------------------------------------
HTML_PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Ellipse Perimeter — Focal Certainty Demo</title>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.7/dist/chart.umd.min.js"></script>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css">
<script src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js"></script>
<style>
:root {
  --bg: #1a1f2e; --card: #232a3b; --border: #3a4258;
  --text: #e2e6ed; --bright: #ffffff; --accent: #6db3f8;
  --green: #5cd07a; --orange: #e8a832; --red: #f85149;
  --purple: #c4a0ff; --mono: 'SF Mono', 'Cascadia Mono', 'Fira Code', monospace;
}
* { box-sizing: border-box; margin: 0; padding: 0; }
body {
  font-family: var(--mono); background: var(--bg); color: var(--text);
  font-size: 15px; min-height: 100vh; padding: 0;
}
header {
  background: linear-gradient(135deg, #232a3b 0%, #1a1f2e 100%);
  border-bottom: 1px solid var(--border); padding: 20px 28px;
  display: flex; align-items: flex-start; gap: 20px;
}
header .header-left { flex-shrink: 0; }
header h1 { font-size: 24px; color: var(--bright); font-weight: 600; }
header .author { font-size: 14px; color: #a0a8b8; margin-top: 4px; }
header .header-links {
  margin-left: auto; display: flex; flex-direction: column; align-items: flex-end;
  gap: 5px; font-size: 13px;
}
header .header-links a {
  color: var(--accent); text-decoration: none; white-space: nowrap;
}
header .header-links a:hover { text-decoration: underline; }
header .header-links .link-label {
  color: #7a8396; font-size: 11px; text-transform: uppercase; letter-spacing: 0.5px;
  margin-right: 6px;
}

.container { max-width: 1600px; margin: 0 auto; padding: 24px; }

/* === FORMULA HERO (full width, above two-panel) === */
.formula-hero {
  max-width: 1600px; margin: 0 auto; padding: 0 24px 16px;
}
.formula-hero .theorem-box { margin-bottom: 0; }
@import url('https://fonts.googleapis.com/css2?family=Caveat:wght@400;600&display=swap');
.formula-hero-heading {
  font-family: 'Caveat', cursive; font-size: 22px; color: #eef1f5;
  line-height: 1.4; margin-bottom: 14px; padding-left: 4px;
}
.formula-btn-row {
  display: flex; flex-wrap: wrap; gap: 8px; padding: 0 0 6px 0;
  position: relative;
}
.formula-btn {
  background: #2d3548; border: 1px solid #4a5470; color: #e2e6ed;
  font-family: var(--mono); font-size: 12px; padding: 6px 14px;
  border-radius: 5px; cursor: pointer; transition: all 0.15s;
  white-space: nowrap; position: relative;
}
.formula-btn:hover { border-color: var(--accent); color: #fff; background: #3a4562; }
.formula-btn.active {
  border-color: #6db3f8; color: #fff; background: #2a3a55;
  box-shadow: 0 0 10px rgba(109,179,248,0.25);
}
.formula-btn .btn-star {
  color: #5cd07a; font-size: 15px; margin-right: 4px; vertical-align: -1px;
}
.formula-tip {
  position: absolute; font-family: 'Caveat', cursive; font-size: 16px;
  color: #f0883e; pointer-events: none; white-space: nowrap;
  text-shadow: 0 0 6px rgba(240,136,62,0.3);
}
.formula-tip svg {
  position: absolute; overflow: visible;
}

/* === TWO-PANEL LAYOUT === */
.two-panel {
  display: flex; gap: 24px; align-items: flex-start;
  max-width: 1600px; margin: 0 auto; padding: 0 24px;
}
.left-panel {
  width: 420px; min-width: 360px; max-width: 520px;
  position: sticky; top: 0;
  display: flex; flex-direction: column;
  padding: 16px 0;
}
.left-controls {
  padding-top: 0;
}
.right-panel { flex: 1; min-width: 0; max-width: calc(100% - 460px); padding: 16px 0; }

/* === INTRO BULLETS === */
.intro-bullets {
  list-style: none; padding: 0; margin: 0 0 16px 0;
}
.intro-bullets li {
  padding: 5px 0; color: #dde1e8; font-size: 13px;
  border-bottom: 1px solid #3a4258; line-height: 1.5;
}
.intro-bullets li::before { content: '\25b8'; color: var(--accent); margin-right: 8px; }
.intro-bullets li:last-child { border-bottom: none; }

/* === COMPACT CONTROLS (left panel) === */
.compact-controls { margin-bottom: 8px; }
.compact-controls .input-row { gap: 8px; margin-bottom: 8px; }
.compact-controls .input-row label { font-size: 14px; }
.compact-controls .input-row input[type=number] { font-size: 16px; padding: 5px 8px; width: 90px; }
.compact-controls .btn { font-size: 13px; padding: 5px 14px; }
.compact-controls .preset-row { gap: 5px; margin-bottom: 8px; }
.compact-controls .preset-btn { font-size: 11px; padding: 3px 8px; }
.compact-controls .slider-row label { font-size: 14px; min-width: 100px; }
.compact-controls .slider-row .val { font-size: 18px; min-width: 60px; }
.compact-controls .slider-row .h-val { font-size: 12px; min-width: 100px; }
.compact-summary {
  display: grid; grid-template-columns: repeat(3, 1fr); gap: 6px;
  background: #252d40; border: 1px solid var(--border); border-radius: 6px;
  padding: 8px; margin-top: 8px;
}
.compact-summary .si { text-align: center; }
.compact-summary .sl { font-size: 11px; color: #a0a8b8; text-transform: uppercase; }
.compact-summary .sv { font-size: 16px; color: var(--bright); font-weight: 600; font-variant-numeric: tabular-nums; }
.compact-summary .sv.sg { color: var(--green); }
.compact-summary .sv.sa { color: var(--accent); }
.input-hint { font-size: 11px; color: #8890a0; margin: 2px 0 6px 0; }

/* === METHOD LOCK/HOVER === */
tr.method-locked td { background: #2a3550 !important; border-left: 3px solid var(--accent); }

/* === CONTROLS === */
.controls {
  background: var(--card); border: 1px solid var(--border);
  border-radius: 8px; padding: 24px; margin-bottom: 20px;
}
.input-row {
  display: flex; align-items: center; gap: 16px; flex-wrap: wrap;
  margin-bottom: 14px;
}
.input-row label { color: var(--bright); font-size: 18px; }
.input-row input[type=number] {
  background: #1e2538; border: 1px solid var(--border); color: var(--bright);
  font-family: var(--mono); font-size: 20px; padding: 8px 12px;
  border-radius: 4px; width: 130px; text-align: right;
}
.input-row input[type=number]:focus { outline: none; border-color: var(--accent); }
.btn {
  background: var(--accent); color: var(--bg); border: none;
  font-family: var(--mono); font-size: 15px; font-weight: 600;
  padding: 8px 20px; border-radius: 4px; cursor: pointer;
}
.btn:hover { opacity: 0.85; }
.btn-sm {
  background: #2d3548; color: var(--accent); border: 1px solid var(--accent);
  font-family: var(--mono); font-size: 12px; font-weight: 600;
  padding: 3px 10px; border-radius: 3px; cursor: pointer;
}
.btn-sm:hover { background: #3a4562; }
.preset-row {
  display: flex; align-items: center; gap: 10px; flex-wrap: wrap;
  margin-bottom: 14px;
}
.preset-row .label { color: #a0a8b8; font-size: 14px; }
.preset-btn {
  background: #2d3548; border: 1px solid #4a5470; color: #e2e6ed;
  font-family: var(--mono); font-size: 14px; padding: 6px 14px;
  border-radius: 4px; cursor: pointer; transition: all 0.15s;
}
.preset-btn:hover { border-color: var(--accent); color: var(--bright); background: #3a4562; }
.preset-btn.active { border-color: var(--accent); color: var(--accent); background: #2a3a55; }
.preset-btn.worst-case { border-color: var(--red); color: #ff7b73; }
.preset-btn.worst-case:hover { background: #3a2525; }
.slider-row {
  display: flex; align-items: center; gap: 20px; flex-wrap: wrap;
}
.slider-row label { color: var(--bright); font-size: 18px; min-width: 160px; }
.slider-row input[type=range] { flex: 1; min-width: 250px; accent-color: var(--accent); height: 8px; }
.slider-row .val { font-size: 26px; color: var(--accent); min-width: 100px; text-align: right; }
.slider-row .h-val { font-size: 16px; color: #a0a8b8; min-width: 140px; }
.loading-dot { display: inline-block; width: 10px; height: 10px; border-radius: 50%;
  background: var(--accent); margin-left: 10px; opacity: 0; transition: opacity 0.2s; }
.loading-dot.active { opacity: 1; animation: pulse 0.6s infinite alternate; }
@keyframes pulse { from { opacity: 0.4; } to { opacity: 1; } }

/* === QUICK SUMMARY BAR === */
.summary-bar {
  background: #252d42; border: 1px solid var(--accent); border-radius: 8px;
  padding: 16px 24px; margin-bottom: 20px;
  display: flex; gap: 28px; flex-wrap: wrap; align-items: center;
  transition: background 0.3s;
}
.summary-bar.flash { background: #2a3f2e; }
.summary-item { text-align: center; }
.summary-item .sl { font-size: 13px; color: #a0a8b8; text-transform: uppercase; letter-spacing: 0.5px; }
.summary-item .sv { font-size: 22px; color: var(--bright); font-weight: 600; margin-top: 2px;
  font-variant-numeric: tabular-nums; }
.summary-item .sv.sg { color: var(--green); }
.summary-item .sv.sa { color: var(--accent); }
.summary-sep { width: 1px; height: 40px; background: var(--border); }

/* === GRID AND CARDS === */
.grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(450px, 1fr)); gap: 20px; }
.card {
  background: var(--card); border: 1px solid var(--border);
  border-radius: 8px; padding: 20px; overflow: hidden;
}
.card h2 {
  font-size: 16px; color: var(--accent); margin-bottom: 14px;
  text-transform: uppercase; letter-spacing: 1px;
}
.card h3 { font-size: 15px; color: var(--orange); margin: 10px 0 6px 0; }
.section-title {
  font-size: 18px; color: var(--accent); font-weight: 700;
  text-transform: uppercase; letter-spacing: 1px;
  padding: 12px 0; margin-top: 8px; border-bottom: 1px solid var(--border);
  margin-bottom: 16px;
}

.theorem-box {
  background: #252d42; border: 1px solid var(--accent);
  border-radius: 6px; padding: 20px; margin: 14px 0;
  font-size: 15px; line-height: 1.7;
}
.theorem-box .title { color: var(--accent); font-weight: 700; font-size: 16px; margin-bottom: 10px; }
.theorem-box .eq {
  text-align: center; font-size: 22px; color: var(--bright);
  padding: 10px 0; letter-spacing: 1px;
}

.stats-grid {
  display: grid; grid-template-columns: repeat(auto-fit, minmax(170px, 1fr));
  gap: 10px; margin: 14px 0;
}
.stat { background: #252d40; border-radius: 4px; padding: 12px; text-align: center; }
.stat .label { font-size: 13px; color: #a0a8b8; text-transform: uppercase; }
.stat .value { font-size: 20px; color: var(--bright); margin-top: 4px; }
.stat .unit { font-size: 12px; color: #a0a8b8; }

canvas { width: 100%; height: 300px; display: block; }

table { width: 100%; border-collapse: collapse; font-size: 15px; }
table th { color: var(--accent); text-align: left; padding: 8px 12px; border-bottom: 2px solid var(--border); font-size: 14px; }
table td { padding: 8px 12px; border-bottom: 1px solid #3a4258; color: #e2e6ed; }
table td.num { text-align: right; font-variant-numeric: tabular-nums; }
table td.mono-left { text-align: left; font-variant-numeric: tabular-nums; white-space: pre; }
tr:hover td { background: #2d3548; }
tr.clickable { cursor: pointer; }
tr.clickable:hover td { background: #303a50; }

.err-green { color: #5cd07a; }
.err-yellow { color: #e8a832; }
.err-orange { color: #f0c050; }
.err-red { color: #f85149; }
.champion-row td { background: #1e3828 !important; }
.ours-row td { background: #1e2e45 !important; }

.formula-display {
  background: #252d42; border: 1px solid var(--accent);
  border-radius: 6px; padding: 24px; font-size: 16px;
  line-height: 2.0; overflow-x: auto; color: var(--text);
}
.perimeter-header { font-size: 15px; color: #a0a8b8; margin-bottom: 10px; line-height: 1.5; }
.perimeter-header span { color: var(--bright); }
.perim-compare {
  background: rgba(30,36,52,0.7);
  border-radius: 8px; padding: 10px 12px;
}
.perim-entry {
  display: grid; grid-template-columns: 1fr; grid-template-rows: auto auto;
  padding: 6px 8px; border-radius: 5px; cursor: pointer;
  transition: background 0.15s; position: relative;
}
.perim-entry:hover { background: rgba(109,179,248,0.1); }
.perim-entry.active { background: rgba(109,179,248,0.15); }
.perim-entry .pe-row1 {
  display: flex; justify-content: space-between; align-items: baseline;
}
.perim-entry .pe-name { font-size: 13px; color: #8dc4ff; line-height: 1.4; }
.perim-entry .pe-row2 {
  display: flex; justify-content: space-between; align-items: baseline;
  margin-top: 1px;
}
.perim-entry .pe-val {
  font-family: var(--mono); font-size: 13px; text-align: right;
  line-height: 1.3; letter-spacing: 0.02em; padding-left: 4.5em;
}
.perim-entry .pe-err {
  font-family: var(--mono); font-size: 13px; font-variant-numeric: tabular-nums;
  text-align: left; padding-left: 8px; white-space: nowrap;
}
.perim-entry.pe-exact { border-top: 1px solid #4a5470; margin-top: 4px; padding-top: 8px; }
.perim-entry .pe-name.pe-ours { color: #7be090; }
.perim-entry .pe-name.pe-champ { color: #7be090; font-weight: 700; }

.legend-row { display: flex; gap: 20px; margin-top: 10px; font-size: 14px; flex-wrap: wrap; }
.legend-item { display: flex; align-items: center; gap: 6px; }
.legend-dot { width: 12px; height: 12px; border-radius: 50%; display: inline-block; }
.explainer { color: #b0b8c8; font-size: 14px; line-height: 1.6; margin-bottom: 14px; }

footer {
  margin-top: 40px; padding: 20px 0; border-top: 1px solid var(--border);
  text-align: center; font-size: 14px; color: #b0b8c8;
}
footer a { color: var(--accent); text-decoration: none; }
footer a:hover { text-decoration: underline; }

.highlight { color: var(--green); }
.warn { color: var(--orange); }
.err { color: var(--red); }

@media (max-width: 1100px) {
  .two-panel { flex-direction: column; }
  .left-panel { width: 100%; max-width: none; position: static; }
  .grid { grid-template-columns: 1fr; }
  .slider-row { flex-direction: column; align-items: stretch; }
  .input-row { flex-direction: column; align-items: stretch; }
  .summary-bar { gap: 14px; }
}
</style>
</head>
<body>

<header>
  <div class="header-left">
    <h1>Two Foci, One Curve</h1>
    <div class="author">by Gutmo Gutmam</div>
  </div>
  <div class="header-links">
    <div><span class="link-label">this demo</span><a href="https://gutmogutmam.github.io/ellipse/" target="_blank">gutmogutmam.github.io/ellipse</a></div>
    <div><span class="link-label">paper</span><a href="https://github.com/gutmogutmam/ellipse" target="_blank">Ellipse Perimeter &mdash; Two Foci, One Curve</a></div>
    <div><span class="link-label">paper</span><a href="https://github.com/gutmogutmam/sriracha" target="_blank">SRIRACHA Framework &mdash; 20 New Discoveries of 2026</a></div>
    <div><span class="link-label">paper</span><a href="https://github.com/gutmogutmam/cf-proofs" target="_blank">Dozens of CF Proofs of Open Conjectures</a></div>
    <div><span class="link-label">paper</span><a href="https://github.com/gutmogutmam/snow-crystal" target="_blank">Snow Crystal Mathematics Breakthrough</a></div>
  </div>
</header>

<!-- INTRO -->
<div class="container" style="padding-bottom:0;">
  <ul class="intro-bullets">
    <li>An <strong>ellipse</strong> is the set of all points whose distances to two foci sum to 2a (the major axis).</li>
    <li><strong>Eccentricity</strong> e measures elongation: e = 0 is a circle, e near 1 is nearly flat. Computed as e = sqrt(1 - b&sup2;/a&sup2;).</li>
    <li>Unlike circles (P = 2&pi;r), there is <strong>no closed-form formula</strong> for the perimeter of an ellipse. Only infinite series converge exactly.</li>
    <li>Our method builds a <a href="#pade-tower" style="color:var(--accent);">convergent Pad&eacute; tower</a> that pins the degenerate-ellipse value to successively deeper continued-fraction convergents of 4/&pi;, then exhausts the remaining error with optimized exponentials.</li>
    <li>This page compares 11 approximation formulas, from Ramanujan (1914, 34 ppm error) to our <strong>seven new world-record formulas</strong>, the best at <strong>0.007 ppb</strong> (7 parts per trillion) using SCOR enrichment with logarithmic singularity terms.</li>
  </ul>
</div>

<!-- FORMULA HERO (full width) -->
<div class="formula-hero">
  <div class="formula-hero-heading">
    New World Record Equation Examples
    (<span style="font-size:28px; color:#5cd07a; vertical-align:-2px;">&starf;</span>
    <span style="font-size:18px; color:#b0b8c8;">= new records</span>)
    using my newly described continued fraction pattern,
    and these examples are not well optimized yet.
  </div>
  <div id="formula-buttons" class="formula-btn-row"></div>
  <div style="display:flex; gap:20px; align-items:flex-start; flex-wrap:wrap;">
    <div style="flex:1; min-width:400px;">
      <div id="formula-rich" style="line-height:1.8; font-size:15px;">
        <p style="color:#a0a8b8; text-align:center; padding:30px 10px;">Loading formula...</p>
      </div>
      <div class="formula-display" id="formula-display" style="display:none;"></div>
    </div>
    <div style="min-width:340px; max-width:420px; flex-shrink:0;">
      <div class="slider-row" style="margin-bottom:6px; gap:6px;">
        <label style="font-size:14px; min-width:30px;">e =</label>
        <input type="range" id="e-slider-mini" min="0" max="999" value="700" step="1"
               style="flex:1; min-width:120px; accent-color:var(--accent); height:6px;">
        <span class="val" id="e-value-mini" style="font-size:16px; min-width:50px;">0.700</span>
      </div>
      <p style="color:#7a8498; font-size:12px; margin:0 0 6px 0; text-align:center;">
        Click any formula to see its full definition &darr;
      </p>
      <div class="perim-compare" id="perim-compare">
        <div class="perimeter-header" id="perimeter-header"></div>
        <div id="perimeter-table"></div>
      </div>
    </div>
  </div>
</div>

<!-- TWO-PANEL LAYOUT -->
<div class="two-panel">

<!-- ============ LEFT PANEL: CONTROLS + ELLIPSE ============ -->
<div class="left-panel">
  <div class="left-controls">
    <div class="compact-controls">
      <div class="input-row">
        <label>a =</label>
        <input type="number" id="input-a" value="1" step="any" min="0.001">
        <label>b =</label>
        <input type="number" id="input-b" value="0.714" step="any" min="0.001">
        <button class="btn" id="btn-apply">Apply</button>
        <span class="loading-dot" id="loading-dot"></span>
      </div>
      <div class="input-hint">a, b > 0. If b > a, auto-swapped. Try the presets below.</div>
      <div class="preset-row">
        <button class="preset-btn" data-a="1" data-b="1">Circle</button>
        <button class="preset-btn" data-a="2" data-b="1">2:1</button>
        <button class="preset-btn" data-a="1.618034" data-b="1">&phi;</button>
        <button class="preset-btn" data-a="5" data-b="3">5:3</button>
        <button class="preset-btn" data-a="10" data-b="1">10:1</button>
        <button class="preset-btn" data-a="100" data-b="1">100:1</button>
        <button class="preset-btn worst-case" data-a="1" data-b="0.2233">e=0.975</button>
      </div>
      <div class="slider-row">
        <label>e =</label>
        <input type="range" id="e-slider" min="0" max="999" value="700" step="1">
        <span class="val" id="e-value">0.700</span>
        <span class="h-val" id="h-value">h = 0.0156</span>
      </div>
    </div>
    <div class="compact-summary" id="summary-bar">
      <div class="si"><div class="sl">a</div><div class="sv" id="sum-a">1.0000</div></div>
      <div class="si"><div class="sl">b</div><div class="sv" id="sum-b">0.7140</div></div>
      <div class="si"><div class="sl">e</div><div class="sv sa" id="sum-e">0.7001</div></div>
      <div class="si"><div class="sl">h</div><div class="sv" id="sum-h">0.0278</div></div>
      <div class="si"><div class="sl">P exact</div><div class="sv" id="sum-p">5.4222</div></div>
      <div class="si"><div class="sl">Best err</div><div class="sv sg" id="sum-err">0.0001 ppm</div></div>
    </div>
    <!-- Mini ellipse animation -->
    <canvas id="canvas-ellipse" height="360" style="height:360px; margin-top:8px; border-radius:6px; background:#1a1f2e;"></canvas>
    <div class="stats-grid" id="stats-geom" style="margin-top:6px;"></div>
  </div>

</div>

<!-- ============ RIGHT PANEL: CHARTS + TABLES ============ -->
<div class="right-panel">

<!-- Perimeter Formula Comparison is now in the formula hero above -->

<!-- ERROR LANDSCAPE (log scale, all methods) -->
<div class="card" style="margin-bottom:16px;">
  <h2>Peak Error vs Eccentricity (log scale)</h2>
  <p class="explainer">Absolute error on a logarithmic scale from 0.1 ppb to 10,000 ppm.
  Ramanujan I reaches 1400 ppm while the SCOR champion stays below 0.01 ppb.</p>
  <div style="position:relative; height:400px;"><canvas id="chart-error-log"></canvas></div>
</div>

<!-- WINNER BY ECCENTRICITY BAND -->
<div class="card" style="margin-bottom:16px;">
  <h2>Best Formula by Eccentricity</h2>
  <p class="explainer"><strong>Top band</strong>: lowest error among all methods.
  <strong>Bottom band</strong>: best excluding R6 (shows the competition).
  At low eccentricity all errors are below 10<sup>&minus;12</sup> ppm, so the &ldquo;winner&rdquo; is just floating-point noise.</p>
  <canvas id="canvas-winner-band" height="440" style="height:220px;"></canvas>
  <div class="legend-row" id="winner-legend"></div>
</div>

<!-- ERROR METRICS: PEAK vs RMS vs MEAN -->
<div class="card" style="margin-bottom:16px;">
  <h2>Error Metrics Comparison</h2>
  <p class="explainer"><strong>Peak (max)</strong>: guaranteed worst-case bound.
  <strong>RMS</strong>: typical performance. <strong>Mean</strong>: average error.
  Optimized for peak error (minimax), so not optimal under other norms.</p>
  <div id="error-metrics-table"></div>
</div>

<!-- SIGNED ERROR: OVERVIEW -->
<div class="card" style="margin-bottom:16px;">
  <h2>Signed Error, All Corrected Formulas (ppb)</h2>
  <p class="explainer">Positive = overestimate, negative = underestimate.
  R2/3exp swings to &plusmn;83 ppb. Sub-ppb methods are invisible at this scale.</p>
  <div style="position:relative; height:350px;"><canvas id="chart-signed-overview"></canvas></div>
</div>

<!-- SIGNED ERROR: ZOOMED -->
<div class="card" style="margin-bottom:16px;">
  <h2>Sub-2 ppb Error Structure: R3, R4, R5, R6 (e &gt; 0.9)</h2>
  <p class="explainer">Y clamped to &plusmn;1.5 ppb. Error equioscillates at N+1 Chebyshev points.
  SCOR champion (gold) has the tightest band at &plusmn;0.007 ppb.</p>
  <div style="position:relative; height:450px;"><canvas id="chart-signed-zoom"></canvas></div>
</div>

<!-- PEAK ERROR COMPARISON -->
<div class="card" style="margin-bottom:16px;">
  <h2>Peak (Max) Error Comparison</h2>
  <p class="explainer">Each method is tested at 998 eccentricities from 0.001 to 0.998.
  The table shows the single worst error encountered anywhere (the L&infin; norm).
  This is the guaranteed accuracy bound. See the Error Metrics table above for RMS and mean.</p>
  <div id="peak-error-table"></div>
</div>

<!-- CONVERGENT TOWER -->
<div class="card" id="pade-tower" style="margin-bottom:16px;">
  <h2>The Convergent Pad&eacute; Tower</h2>
  <p class="explainer">The key idea: Ramanujan II&rsquo;s formula evaluates to 22/7 when the ellipse
  degenerates (b&rarr;0). We correct this by adding Pad&eacute; layers that pin the degenerate
  value to successively deeper rational approximations of 4/&pi; from its continued fraction
  [3; 7, 15, 1, 292, 1, 1, ...]. Each layer matches 5 more Taylor coefficients of the exact
  perimeter series. The remaining error (the &ldquo;budget&rdquo; T<sub>k</sub>) shrinks by orders of magnitude
  at each level, and is exhausted by a sum of exponentials.</p>
  <div class="theorem-box">
    <div class="title">CONVERGENT TOWER: R2 &rarr; R3 &rarr; R4 &rarr; R5 &rarr; R6</div>
    <p>Each tower level adds a [3/2] Pad&eacute; correction at h<sup>5k</sup>, matching 5 more
    Taylor coefficients and pinning the endpoint R(1) = P(a,0)/(&pi;&middot;2a) to a deeper
    convergent of 4/&pi; from the continued fraction of &pi; = [3; 7, 15, 1, 292, ...].</p>
    <div class="eq">P<sub>Rk</sub>(h) = &pi;(a+b) &middot; [R<sub>2</sub>(h) + &sum; h<sup>5k</sup> &middot; N<sub>k</sub>(h)/D<sub>k</sub>(h)]</div>
    <p style="margin-top:8px;">The exponential correction exhausts the tower remainder budget
    T<sub>k</sub> = 1 &minus; q<sub>k</sub>&pi;/p<sub>k</sub> across N basis functions.</p>
  </div>

  <h3 style="color:var(--accent); margin:16px 0 8px;">Tower Hierarchy</h3>
  <table>
    <thead><tr>
      <th>Level</th><th>Pinned to</th><th>T<sub>k</sub></th><th>Best n<sub>exp</sub></th><th>Best Error</th>
    </tr></thead>
    <tbody>
      <tr><td>R2</td><td>22/7</td><td>4.0 &times; 10<sup>&minus;4</sup></td><td>3</td><td>0.083 ppm</td></tr>
      <tr><td>R3</td><td>355/113</td><td>8.5 &times; 10<sup>&minus;8</sup></td><td>15</td><td>1.43 ppb</td></tr>
      <tr><td>R4</td><td>103993/33102</td><td>1.8 &times; 10<sup>&minus;10</sup></td><td>20</td><td>0.492 ppb</td></tr>
      <tr><td>R5</td><td>104348/33215</td><td>1.1 &times; 10<sup>&minus;10</sup></td><td>20</td><td>0.508 ppb</td></tr>
      <tr><td>R6</td><td>208341/66317</td><td>3.9 &times; 10<sup>&minus;11</sup></td><td>16</td><td style="color:#5cd07a;">0.018 ppb &star;</td></tr>
      <tr style="background:#332800"><td>R6 SCOR</td><td>208341/66317</td><td>3.9 &times; 10<sup>&minus;11</sup></td><td>16+3log</td><td style="color:#ffd700;font-weight:700">0.007 ppb &star;&star;</td></tr>
    </tbody>
  </table>

  <div class="theorem-box" style="margin-top:16px;">
    <div class="title">VARPRO COEFFICIENT-SCALE SEPARATION THEOREM</div>
    <p>For any fixed set of rates, the (N+2)-dimensional optimization over N coefficient
    ratios + &lambda; + q separates into:</p>
    <p style="margin:8px 0;">1. An <strong>inner linear Chebyshev problem</strong> in the N coefficients
    (solved exactly for each (&lambda;, q) via LP)</p>
    <p>2. An <strong>outer 2D search</strong> over (&lambda;, q)</p>
    <div class="eq" style="font-size:15px;">Linearization error: O(T<sub>k</sub><sup>2</sup>) &asymp; 10<sup>&minus;17</sup> &nbsp; (negligible)</div>
    <p style="margin-top:8px; color:#a0a8b8; font-size:13px;">This reduces the optimization
    from 17D to 2D, making exhaustive rate search over C(50,4) &asymp; 230K combinations feasible.</p>
  </div>
</div>

<!-- FOCAL CERTAINTY THEORY -->
<div class="card" style="margin-bottom:16px;">
  <h2>Focal Certainty-Uncertainty Duality</h2>
  <p class="explainer">Every ellipse has two foci. From any point on the curve, draw lines to both foci:
  their lengths r<sub>1</sub> and r<sub>2</sub> sum to 2a, but their RATIO varies around the ellipse.
  The &ldquo;certainty&rdquo; R = c/&ell; measures how sharply the foci resolve each other,
  while the &ldquo;uncertainty&rdquo; U averages the angular disagreement. Their ratio is ALWAYS &pi;/2,
  regardless of eccentricity. A universal geometric constant.</p>
  <div class="theorem-box">
    <div class="title">THEOREM (Max Unit Certainty of Inter-Focal Distance)</div>
    <p>For ANY ellipse with eccentricity e in (0, 1), foci at distance c = ae from center,
    and semi-latus rectum l = b&sup2;/a:</p>
    <div class="eq">R / U = &pi;/2 &nbsp;&nbsp; (UNIVERSAL)</div>
    <p>where R = c/l = e/(1-e&sup2;) is the <span class="highlight">focal resolution</span>
    and U = &langle;|M&middot;D|&rangle; = R&middot;&kappa; is the <span class="warn">sweep uncertainty</span>,
    with &kappa; = 2/&pi;.</p>
    <p style="margin-top:8px;">The ellipse's two foci pin each other's location to EXACTLY
    &pi;/2 natural units per unit of angular sweep disagreement.</p>
  </div>
  <div class="grid">
    <div class="card" style="border:none;padding:0;">
      <h2>R/U Ratio vs Eccentricity</h2>
      <canvas id="canvas-ratio" height="250"></canvas>
      <p style="font-size:13px; color:#a0a8b8; margin-top:8px;">
        The ratio R/U = &pi;/2 = 1.5708... is CONSTANT for all eccentricities.
        The red dot shows the current eccentricity.</p>
    </div>
    <div class="card" style="border:none;padding:0;">
      <h2>|M&middot;D(&alpha;)| - Angular Profile</h2>
      <canvas id="canvas-angular" height="250"></canvas>
      <p style="font-size:13px; color:#a0a8b8; margin-top:8px;">
        Maximum at &alpha;=0 (periapsis). Zero at &alpha;=90&deg; (latus rectum).
        Mean = R&middot;&kappa; = R&middot;(2/&pi;). Ceiling = c/l = R.</p>
    </div>
  </div>
</div>

<!-- RAPIDITY & INFORMATION -->
<div class="card" style="margin-bottom:16px;">
  <h2>Rapidity, Doppler &amp; Information Theory</h2>
  <p class="explainer">An ellipse can be thought of relativistically: the Doppler factor
  &Delta;(&theta;) = r<sub>2</sub>/r<sub>1</sub> at each point acts like a redshift/blueshift.
  The rapidity &eta; = atanh(e) is the hyperbolic &ldquo;speed&rdquo; of the ellipse.
  The information surplus I<sub>f</sub> &minus; H<sub>u</sub> = log<sub>2</sub>(&pi;/2) &asymp; 0.6514 bits
  is the irreducible geometric advantage of having two foci rather than one center.</p>
  <div class="grid">
    <div class="card" style="border:none;padding:0;">
      <h2>Rapidity &eta; and Doppler &Delta;</h2>
      <canvas id="canvas-rapidity" height="250"></canvas>
      <div class="stats-grid" id="stats-rapidity"></div>
    </div>
    <div class="card" style="border:none;padding:0;">
      <h2>Information Theory</h2>
      <div class="stats-grid" id="stats-info"></div>
      <div class="theorem-box" style="margin-top:12px;">
        <div class="title">Information Surplus</div>
        <div class="eq">I<sub>f</sub> &minus; H<sub>u</sub> = log<sub>2</sub>(&pi;/2) &asymp; 0.6514 bits</div>
        <p>The focal information ALWAYS exceeds the uncertainty entropy by
        exactly log<sub>2</sub>(&pi;/2) bits, the irreducible geometric advantage of
        having two foci.</p>
      </div>
    </div>
  </div>
</div>

<!-- REFERENCE TABLES -->
<div class="card" style="margin-bottom:16px;">
  <h2>Reference Tables (&kappa; Bridge, Focal Chords)</h2>
  <p class="explainer">The constant &kappa; = 2/&pi; appears in five independent contexts related to the ellipse.
  This is not a coincidence; all five are consequences of the R/U = &pi;/2 duality.</p>
  <div class="grid">
    <div class="card" style="border:none;padding:0;">
      <h2>The Shared Leg: &kappa; = 2/&pi;</h2>
      <table>
        <thead><tr><th>Context</th><th>Identity</th><th>&kappa; acts as</th></tr></thead>
        <tbody>
          <tr><td>Focal duality</td><td>U&middot;(l/c) = &kappa;</td><td>coupling</td></tr>
          <tr><td>Gauss connection</td><td>&Gamma;(1)&sup2;/(&Gamma;(3/2)&Gamma;(1/2))</td><td>amplitude</td></tr>
          <tr><td>Flat-limit deficiency</td><td>P(a,0)/(2&pi;a) = &kappa;</td><td>limit ratio</td></tr>
          <tr><td>MEPB coefficient</td><td>7&pi;/704 = 7/(352&kappa;)</td><td>scale factor</td></tr>
          <tr><td>Angular average</td><td>&langle;|cos&alpha;|&rangle; = &kappa;</td><td>mean value</td></tr>
        </tbody>
      </table>
      <p style="font-size:13px; color:#a0a8b8; margin-top:12px;">
        Unit closure: &kappa; &times; (R/U) = (2/&pi;)(&pi;/2) = 1.</p>
    </div>
    <div class="card" style="border:none;padding:0;">
      <h2>Focal Chord Data</h2>
      <div id="chord-table" style="max-height:300px; overflow-y:auto;"></div>
    </div>
  </div>
</div>

</div> <!-- end right-panel -->
</div> <!-- end two-panel -->

<footer>
  <a href="https://github.com/gutmogutmam/ellipse">gutmogutmam/ellipse</a>
  &nbsp;|&nbsp; Paper: "Two Foci, One Curve"
  &nbsp;|&nbsp; Best peak error: R6+16exp+3log SCOR at 0.007 ppb (7 parts per trillion)
  &nbsp;|&nbsp; &kappa; = 2/&pi;
</footer>

<script>
// =========================================================================
// State and Data
// =========================================================================
let currentData = null;
let currentA = 1.0;
let currentB = 0.714;
let fetchSeq = 0;          // sequence number to ignore stale responses
let debounceTimer = null;
let animAngle = 0;
let animFrameId = null;
let lockedFormula = 'Mamoun R2/3exp (0.083 ppm)';  // start locked to R2/3exp
let hoveredFormula = null;
const sweepData = SWEEP_DATA_PLACEHOLDER;
const errorSweep = ERROR_SWEEP_PLACEHOLDER;
const maxErrors = MAX_ERRORS_PLACEHOLDER;
const formulaInfo = FORMULA_INFO_PLACEHOLDER;
const signedSweep = SIGNED_SWEEP_PLACEHOLDER;
const formulaHTML = FORMULA_HTML_PLACEHOLDER;
const formulaLatex = FORMULA_LATEX_PLACEHOLDER;
const winnerData = WINNER_DATA_PLACEHOLDER;
const PI = Math.PI;
const KAPPA = 2 / PI;

const slider = document.getElementById('e-slider');
const sliderMini = document.getElementById('e-slider-mini');
const eValueMini = document.getElementById('e-value-mini');
const eValue = document.getElementById('e-value');
const hValue = document.getElementById('h-value');
const inputA = document.getElementById('input-a');
const inputB = document.getElementById('input-b');
const btnApply = document.getElementById('btn-apply');
const loadingDot = document.getElementById('loading-dot');
const summaryBar = document.getElementById('summary-bar');

// =========================================================================
// Helpers
// =========================================================================
function eFromAB(a, b) {
  if (a <= 0 || b <= 0) return 0;
  if (a < b) { const t = a; a = b; b = t; }
  if (a === b) return 0;
  return Math.sqrt(1 - (b / a) * (b / a));
}

function hFromAB(a, b) {
  if (a <= 0 || b <= 0) return 0;
  return ((a - b) / (a + b)) ** 2;
}

// =========================================================================
// Sync logic: a,b <-> slider (THREE input paths, all converge to doUpdate)
// =========================================================================

// Path 1: User changed a/b fields (typing, arrows, paste)
function onABChanged() {
  let a = parseFloat(inputA.value);
  let b = parseFloat(inputB.value);
  if (isNaN(a) || a <= 0) return;  // don't update on empty/invalid
  if (isNaN(b) || b <= 0) return;
  if (b > a) { const t = a; a = b; b = t; inputA.value = a; inputB.value = b; }
  currentA = a;
  currentB = b;
  const e = eFromAB(a, b);
  slider.value = Math.round(e * 1000);
  sliderMini.value = Math.round(e * 1000);
  eValue.textContent = e.toFixed(3);
  eValueMini.textContent = e.toFixed(3);
  hValue.textContent = 'h = ' + hFromAB(a, b).toFixed(6);
  debouncedFetch(a, b);
}

// Path 2: User moved slider (main or mini)
function onSliderChanged(src) {
  const val = (src === 'mini') ? sliderMini.value : slider.value;
  slider.value = val;
  sliderMini.value = val;
  const e = val / 1000;
  eValue.textContent = e.toFixed(3);
  eValueMini.textContent = e.toFixed(3);
  const a = currentA;
  const b = (e >= 1) ? 0.001 : a * Math.sqrt(1 - e * e);
  currentB = b;
  inputB.value = (Math.round(b * 10000) / 10000);
  hValue.textContent = 'h = ' + hFromAB(a, b).toFixed(6);
  debouncedFetch(a, b);
}

// Path 3: Preset button
function onPreset(a, b) {
  inputA.value = a;
  inputB.value = b;
  currentA = a;
  currentB = b;
  const e = eFromAB(a, b);
  slider.value = Math.round(e * 1000);
  sliderMini.value = Math.round(e * 1000);
  eValueMini.textContent = e.toFixed(3);
  eValue.textContent = e.toFixed(3);
  hValue.textContent = 'h = ' + hFromAB(a, b).toFixed(6);
  // highlight active preset
  document.querySelectorAll('.preset-btn').forEach(b => b.classList.remove('active'));
  event.currentTarget.classList.add('active');
  fetchAndRender(a, b);  // immediate for presets
}

// Debounced fetch (for typing / slider dragging)
function debouncedFetch(a, b) {
  clearTimeout(debounceTimer);
  debounceTimer = setTimeout(() => fetchAndRender(a, b), 120);
}

// Event listeners: number inputs
inputA.addEventListener('input', onABChanged);   // fires on every keystroke, arrow, paste
inputB.addEventListener('input', onABChanged);
inputA.addEventListener('change', onABChanged);   // fires on blur / commit
inputB.addEventListener('change', onABChanged);
btnApply.addEventListener('click', () => {
  onABChanged();
  clearTimeout(debounceTimer);
  fetchAndRender(currentA, currentB);
});

// Event listeners: sliders (main + mini, synced)
slider.addEventListener('input', function() { onSliderChanged('main'); });
sliderMini.addEventListener('input', function() { onSliderChanged('mini'); });

// Event listeners: presets
document.querySelectorAll('.preset-btn').forEach(btn => {
  btn.addEventListener('click', (event) => {
    onPreset(parseFloat(btn.dataset.a), parseFloat(btn.dataset.b));
  });
});

// =========================================================================
// API with loading indicator and sequence guarding
// =========================================================================
async function fetchAndRender(a, b) {
  const seq = ++fetchSeq;
  loadingDot.classList.add('active');
  try {
    const resp = await fetch(`/api/compute?a=${a}&b=${b}`);
    if (seq !== fetchSeq) return; // stale response, discard
    currentData = await resp.json();
    render(currentData);
    // flash summary bar
    summaryBar.classList.add('flash');
    setTimeout(() => summaryBar.classList.remove('flash'), 300);
  } catch (err) {
    console.error('Fetch error:', err);
  } finally {
    if (seq === fetchSeq) loadingDot.classList.remove('active');
  }
}

// =========================================================================
// Rendering
// =========================================================================
function render(d) {
  renderSummaryBar(d);
  renderEllipse(d);
  renderPerimeterTable(d);
  renderPeakErrorTable();
  renderErrorLandscape(d);
  renderWinnerBands();
  updateWinnerIndicator(d.e);
  renderErrorMetrics();
  renderSignedError(d);
  renderSignedErrorZoom(d);
  renderRatioPlot(d);
  renderAngular(d);
  renderRapidity(d);
  renderInfoStats(d);
  renderChordTable(d);
}

function renderSummaryBar(d) {
  const champ = d.methods.find(m => m.is_champion);
  document.getElementById('sum-a').textContent = d.a.toPrecision(8);
  document.getElementById('sum-b').textContent = d.b.toPrecision(8);
  document.getElementById('sum-e').textContent = d.e.toFixed(8);
  document.getElementById('sum-h').textContent = d.h.toFixed(10);
  document.getElementById('sum-p').textContent = d.P_exact.toPrecision(12);
  const errEl = document.getElementById('sum-err');
  if (champ) {
    errEl.textContent = fmtErr(champ.error_ppm);
    errEl.className = 'sv ' + (champ.error_ppm < 0.001 ? 'sg' : champ.error_ppm < 0.1 ? 'sa' : '');
  }
}

function onMethodHover(name) {
  if (lockedFormula) return;
  hoveredFormula = name;
  showFormula(name);
}
function onMethodUnhover() {
  if (lockedFormula) return;
  hoveredFormula = null;
  showFormula('Mamoun R2/3exp (0.083 ppm)');
}
function onMethodClick(name) {
  lockedFormula = name;
  showFormula(name);
  // Update formula buttons
  document.querySelectorAll('.formula-btn').forEach(b => {
    b.classList.toggle('active', b.dataset.method === name);
  });
  // Update table highlighting
  document.querySelectorAll('.method-locked').forEach(r => r.classList.remove('method-locked'));
  document.querySelectorAll('tr.clickable').forEach(row => {
    if (row.dataset.method === name) row.classList.add('method-locked');
  });
  document.querySelectorAll('.perim-entry').forEach(row => {
    row.classList.toggle('active', row.dataset.method === name);
  });
}

function showFormula(name) {
  const fmtDiv = document.getElementById('formula-display');
  const richDiv = document.getElementById('formula-rich');

  // KaTeX rendering (preferred)
  if (formulaLatex && formulaLatex[name]) {
    const f = formulaLatex[name];
    const kopts = {displayMode: true, throwOnError: false, maxSize: 500, maxExpand: 10000};
    const kInline = {displayMode: false, throwOnError: false, maxSize: 500, maxExpand: 10000};
    if (f.latex_num && f.latex_den) {
      // Giant fraction: heading + num/den as one visual block
      richDiv.innerHTML = '<div class="theorem-box" style="border-color:' + f.color + '">' +
        '<div class="title" style="color:' + f.color + '">' + f.title + '</div>' +
        '<p style="color:#a0a8b8; margin:8px 0">' + f.subtitle + '</p>' +
        '<div style="margin:16px 0 8px 10px;">' +
          '<div style="font-style:italic; color:#58a6ff; font-size:1.35em; text-shadow:0 0 14px rgba(88,166,255,0.45); letter-spacing:0.02em;">Perimeter Formula</div>' +
          '<div style="font-style:italic; color:#58a6ff; font-size:1.05em; text-shadow:0 0 10px rgba(88,166,255,0.3); margin-top:3px; letter-spacing:0.02em;">Fully Expanded Form</div>' +
        '</div>' +
        '<div style="padding:12px 10px; overflow-x:auto;">' +
          '<div style="display:inline-flex; flex-direction:column; align-items:center;">' +
            '<div id="katex-num" style="padding:8px 12px;"></div>' +
            '<div style="width:100%; height:2px; background:#a0a8b8;"></div>' +
            '<div id="katex-den" style="padding:8px 12px;"></div>' +
          '</div>' +
        '</div>' +
        '<p style="color:#a0a8b8; margin-top:12px; font-size:14px;">where <span id="katex-where"></span></p>' +
        '</div>';
      try {
        katex.render(f.latex_num, document.getElementById('katex-num'), kopts);
        katex.render(f.latex_den, document.getElementById('katex-den'), kopts);
        katex.render(f.where, document.getElementById('katex-where'), kInline);
      } catch(e) { console.error('KaTeX error:', e); }
    } else {
      // Simple formula: single render
      richDiv.innerHTML = '<div class="theorem-box" style="border-color:' + f.color + '">' +
        '<div class="title" style="color:' + f.color + '">' + f.title + '</div>' +
        '<p style="color:#a0a8b8; margin:8px 0">' + f.subtitle + '</p>' +
        '<div id="katex-main" style="padding:20px 10px; overflow-x:auto;"></div>' +
        '<p style="color:#a0a8b8; margin-top:12px; font-size:14px;">where <span id="katex-where"></span></p>' +
        '</div>';
      try {
        katex.render(f.latex, document.getElementById('katex-main'), kopts);
        katex.render(f.where, document.getElementById('katex-where'), kInline);
      } catch(e) { console.error('KaTeX error:', e); }
    }
    richDiv.style.display = '';
    fmtDiv.style.display = 'none';
  } else if (formulaInfo[name]) {
    // Fallback to plain text
    richDiv.style.display = 'none';
    fmtDiv.style.display = '';
    fmtDiv.innerHTML = formulaInfo[name].replace(/\n/g, '<br>');
  } else {
    richDiv.style.display = 'none';
    fmtDiv.style.display = '';
    fmtDiv.innerHTML = 'No detailed formula available for: ' + name;
  }
  // Formula is in sticky left panel, no scrolling needed
}

function renderPeakErrorTable() {
  const div = document.getElementById('peak-error-table');
  if (!maxErrors) { div.innerHTML = '<p>Loading...</p>'; return; }
  const entries = Object.entries(maxErrors).sort((a, b) => a[1].max_ppm - b[1].max_ppm);
  let html = '<table><thead><tr><th>#</th><th>Method</th><th style="text-align:right">Peak Error</th><th style="text-align:right">Worst e</th></tr></thead><tbody>';
  let rank = 1;
  for (const [name, info] of entries) {
    const ppm = info.max_ppm;
    let colorClass = 'err-red';
    if (ppm < 0.001) colorClass = 'err-green';
    else if (ppm < 0.1) colorClass = 'err-yellow';
    else if (ppm < 10) colorClass = 'err-orange';
    const isBest = (rank === 1);
    const rowClass = isBest ? ' class="champion-row clickable"' : ' class="clickable"';
    const eName = name.replace(/'/g, "\\'");
    html += '<tr' + rowClass + ' data-method="' + name + '" onmouseover="onMethodHover(\'' + eName + '\')" onmouseout="onMethodUnhover()" onclick="onMethodClick(\'' + eName + '\')">' +
      '<td>' + rank + '</td>' +
      '<td>' + name + '</td>' +
      '<td class="num ' + colorClass + '">' + fmtErr(ppm) + '</td>' +
      '<td class="num">' + info.at_e.toFixed(3) + '</td>' +
      '</tr>';
    rank++;
  }
  html += '</tbody></table>';
  div.innerHTML = html;
}

function renderEllipse(d) {
  // Cancel previous animation
  if (animFrameId) { cancelAnimationFrame(animFrameId); animFrameId = null; }
  animAngle = 0;
  drawEllipseFrame(d);
  function animLoop() {
    animAngle += 0.012;
    if (animAngle > 2 * PI) animAngle -= 2 * PI;
    drawEllipseFrame(d);
    animFrameId = requestAnimationFrame(animLoop);
  }
  animFrameId = requestAnimationFrame(animLoop);
}

function drawEllipseFrame(d) {
  const canvas = document.getElementById('canvas-ellipse');
  const ctx = canvas.getContext('2d');
  const W = canvas.width = canvas.offsetWidth * 2;
  const H = canvas.height = 800;
  ctx.clearRect(0, 0, W, H);

  const cx = W / 2, cy = H / 2 - 20;
  const maxDim = Math.max(d.a, d.b);
  const scale = Math.min(W * 0.36, H * 0.34);
  const a_px = scale * d.a / maxDim;
  const b_px = scale * d.b / maxDim;

  // Fill ellipse (subtle)
  ctx.fillStyle = '#58a6ff10';
  ctx.beginPath();
  ctx.ellipse(cx, cy, a_px, b_px, 0, 0, 2 * PI);
  ctx.fill();

  // Draw ellipse curve
  ctx.strokeStyle = '#58a6ff';
  ctx.lineWidth = 3;
  ctx.beginPath();
  ctx.ellipse(cx, cy, a_px, b_px, 0, 0, 2 * PI);
  ctx.stroke();

  // Draw axes (dashed)
  ctx.strokeStyle = '#30363d';
  ctx.lineWidth = 1;
  ctx.setLineDash([6, 4]);
  ctx.beginPath();
  ctx.moveTo(cx - a_px - 30, cy); ctx.lineTo(cx + a_px + 30, cy);
  ctx.moveTo(cx, cy - b_px - 30); ctx.lineTo(cx, cy + b_px + 30);
  ctx.stroke();
  ctx.setLineDash([]);

  // Semi-major axis line (solid, labeled)
  ctx.strokeStyle = '#58a6ff88';
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.moveTo(cx, cy); ctx.lineTo(cx + a_px, cy);
  ctx.stroke();
  ctx.fillStyle = '#58a6ff';
  ctx.font = 'bold 28px monospace';
  ctx.textAlign = 'center';
  ctx.fillText('a=' + d.a.toFixed(3), cx + a_px / 2, cy - 10);

  // Semi-minor axis line (solid, labeled)
  ctx.strokeStyle = '#58a6ff88';
  ctx.beginPath();
  ctx.moveTo(cx, cy); ctx.lineTo(cx, cy - b_px);
  ctx.stroke();
  ctx.fillStyle = '#58a6ff';
  ctx.font = 'bold 28px monospace';
  ctx.textAlign = 'left';
  ctx.fillText('b=' + d.b.toFixed(3), cx + 8, cy - b_px / 2);

  // Draw foci
  const fc = scale * d.c / maxDim;
  ctx.fillStyle = '#f85149';
  ctx.beginPath(); ctx.arc(cx - fc, cy, 5, 0, 2 * PI); ctx.fill();
  ctx.beginPath(); ctx.arc(cx + fc, cy, 5, 0, 2 * PI); ctx.fill();

  // Label foci
  ctx.fillStyle = '#f85149';
  ctx.font = 'bold 34px monospace';
  ctx.textAlign = 'center';
  ctx.fillText('F\u2081', cx - fc, cy + 24);
  ctx.fillText('F\u2082', cx + fc, cy + 24);

  // Draw semi-latus rectum (ℓ = b²/a, measured at focus)
  if (d.e > 0.01) {
    const ell_px = scale * d.ell / maxDim;
    ctx.strokeStyle = '#3fb950';
    ctx.lineWidth = 3;
    ctx.setLineDash([8, 4]);
    ctx.beginPath();
    ctx.moveTo(cx - fc, cy - ell_px); ctx.lineTo(cx - fc, cy + ell_px);
    ctx.stroke();
    ctx.setLineDash([]);
    ctx.fillStyle = '#3fb950';
    ctx.font = 'bold 24px monospace';
    ctx.textAlign = 'left';
    ctx.fillText('\u2113=' + d.ell.toFixed(3), cx - fc + 8, cy - ell_px - 4);
  }

  // Draw center
  ctx.fillStyle = '#d29922';
  ctx.beginPath(); ctx.arc(cx, cy, 4, 0, 2 * PI); ctx.fill();

  // Inter-focal distance bar
  if (d.e > 0.01) {
    const barY = cy + 36;
    ctx.strokeStyle = '#bc8cff';
    ctx.lineWidth = 3;
    ctx.beginPath();
    ctx.moveTo(cx - fc, barY); ctx.lineTo(cx + fc, barY);
    ctx.stroke();
    // Endcaps
    ctx.beginPath();
    ctx.moveTo(cx - fc, barY - 8); ctx.lineTo(cx - fc, barY + 8);
    ctx.moveTo(cx + fc, barY - 8); ctx.lineTo(cx + fc, barY + 8);
    ctx.stroke();
    ctx.fillStyle = '#bc8cff';
    ctx.font = '20px monospace';
    ctx.textAlign = 'center';
    ctx.fillText('2c=' + (2 * d.c).toFixed(3), cx, barY + 20);
  }

  // Eccentricity label
  ctx.fillStyle = '#d29922';
  ctx.font = 'bold 24px monospace';
  ctx.textAlign = 'left';
  ctx.fillText('e=' + d.e.toFixed(4), 8, 20);
  ctx.fillStyle = '#a0a8b8';
  ctx.font = '20px monospace';
  ctx.fillText('h=' + d.h.toFixed(6), 8, 38);

  // Perimeter label (bottom center, large)
  ctx.fillStyle = '#3fb950';
  ctx.font = 'bold 34px monospace';
  ctx.textAlign = 'center';
  ctx.fillText('P = ' + d.P_exact.toPrecision(10), cx, H - 16);

  // Animated tracing point
  if (d.e > 0.001) {
    const theta = animAngle;
    const px = cx + a_px * Math.cos(theta);
    const py = cy - b_px * Math.sin(theta);
    const f1x = cx - fc, f2x = cx + fc;
    // Distance lines to foci
    ctx.strokeStyle = '#f8514966'; ctx.lineWidth = 1.5; ctx.setLineDash([4, 3]);
    ctx.beginPath(); ctx.moveTo(f1x, cy); ctx.lineTo(px, py); ctx.stroke();
    ctx.strokeStyle = '#d2992266';
    ctx.beginPath(); ctx.moveTo(f2x, cy); ctx.lineTo(px, py); ctx.stroke();
    ctx.setLineDash([]);
    // r1+r2=2a label
    const r1 = Math.sqrt((px-f1x)**2 + (py-cy)**2);
    const r2 = Math.sqrt((px-f2x)**2 + (py-cy)**2);
    ctx.fillStyle = '#a0a8b8'; ctx.font = '16px monospace'; ctx.textAlign = 'left';
    const lx = Math.min(px + 14, W - 180), ly = Math.max(py - 10, 20);
    ctx.fillText('r\u2081+r\u2082 = ' + ((r1+r2)*maxDim/scale).toFixed(4), lx, ly);
    // Dot
    ctx.fillStyle = '#f0f6fc'; ctx.beginPath(); ctx.arc(px, py, 6, 0, 2*PI); ctx.fill();
    ctx.fillStyle = '#58a6ff'; ctx.beginPath(); ctx.arc(px, py, 4, 0, 2*PI); ctx.fill();
  }

  // Compact stats for left panel
  const statsDiv = document.getElementById('stats-geom');
  statsDiv.innerHTML = `
    <div class="stat"><div class="label">R = c/\u2113</div><div class="value highlight">${d.R.toFixed(6)}</div><div class="unit">certainty</div></div>
    <div class="stat"><div class="label">U = \u03baR</div><div class="value warn">${d.U.toFixed(6)}</div><div class="unit">uncertainty</div></div>
    <div class="stat"><div class="label">R/U</div><div class="value" style="color:#3fb950">${d.R_over_U.toFixed(6)}</div><div class="unit">\u2192 \u03c0/2</div></div>
  `;
}

function renderRatioPlot(d) {
  const canvas = document.getElementById('canvas-ratio');
  const ctx = canvas.getContext('2d');
  const W = canvas.width = canvas.offsetWidth * 2;
  const H = canvas.height = 500;
  ctx.clearRect(0, 0, W, H);

  const pad = { l: 80, r: 40, t: 40, b: 60 };
  const pw = W - pad.l - pad.r;
  const ph = H - pad.t - pad.b;

  const yMin = 1.0, yMax = 2.0;
  const xMin = 0, xMax = 1;

  function mapX(e) { return pad.l + (e - xMin) / (xMax - xMin) * pw; }
  function mapY(v) { return pad.t + (yMax - v) / (yMax - yMin) * ph; }

  // Grid
  ctx.strokeStyle = '#3a4258';
  ctx.lineWidth = 1;
  for (let y = 1.0; y <= 2.01; y += 0.25) {
    ctx.beginPath();
    ctx.moveTo(pad.l, mapY(y)); ctx.lineTo(W - pad.r, mapY(y));
    ctx.stroke();
    ctx.fillStyle = '#a0a8b8'; ctx.font = '20px monospace';
    ctx.textAlign = 'right';
    ctx.fillText(y.toFixed(2), pad.l - 8, mapY(y) + 5);
  }
  for (let x = 0; x <= 1.01; x += 0.2) {
    ctx.beginPath();
    ctx.moveTo(mapX(x), pad.t); ctx.lineTo(mapX(x), H - pad.b);
    ctx.stroke();
    ctx.fillStyle = '#a0a8b8'; ctx.font = '20px monospace';
    ctx.textAlign = 'center';
    ctx.fillText(x.toFixed(1), mapX(x), H - pad.b + 24);
  }

  // pi/2 line
  ctx.strokeStyle = '#3fb950';
  ctx.lineWidth = 3;
  ctx.setLineDash([8, 4]);
  ctx.beginPath();
  ctx.moveTo(pad.l, mapY(PI / 2));
  ctx.lineTo(W - pad.r, mapY(PI / 2));
  ctx.stroke();
  ctx.setLineDash([]);
  ctx.fillStyle = '#3fb950'; ctx.font = '22px monospace';
  ctx.textAlign = 'left';
  ctx.fillText('\u03c0/2 = 1.5708...', W - pad.r - 240, mapY(PI / 2) - 10);

  // Data line
  ctx.strokeStyle = '#58a6ff';
  ctx.lineWidth = 2;
  ctx.beginPath();
  let first = true;
  for (const pt of sweepData) {
    const x = mapX(pt.e), y = mapY(pt.ratio);
    if (first) { ctx.moveTo(x, y); first = false; }
    else ctx.lineTo(x, y);
  }
  ctx.stroke();

  // Current point
  ctx.fillStyle = '#f85149';
  ctx.beginPath();
  ctx.arc(mapX(d.e), mapY(d.R_over_U), 8, 0, 2 * PI);
  ctx.fill();

  // Labels
  ctx.fillStyle = '#c9d1d9'; ctx.font = '22px monospace';
  ctx.textAlign = 'center';
  ctx.fillText('Eccentricity e', W / 2, H - 8);
  ctx.save();
  ctx.translate(16, H / 2);
  ctx.rotate(-PI / 2);
  ctx.fillText('R / U', 0, 0);
  ctx.restore();
}

function renderAngular(d) {
  const canvas = document.getElementById('canvas-angular');
  const ctx = canvas.getContext('2d');
  const W = canvas.width = canvas.offsetWidth * 2;
  const H = canvas.height = 500;
  ctx.clearRect(0, 0, W, H);

  if (!d.angular_profile || d.angular_profile.length === 0) {
    ctx.fillStyle = '#a0a8b8'; ctx.font = '20px monospace'; ctx.textAlign = 'center';
    ctx.fillText('(Circle: no angular variation)', W / 2, H / 2);
    return;
  }

  const pad = { l: 80, r: 40, t: 40, b: 60 };
  const pw = W - pad.l - pad.r;
  const ph = H - pad.t - pad.b;

  const maxMD = d.R * 1.1;
  function mapX(deg) { return pad.l + deg / 360 * pw; }
  function mapY(v) { return pad.t + (maxMD - v) / maxMD * ph; }

  // Grid
  ctx.strokeStyle = '#3a4258'; ctx.lineWidth = 1;
  for (let deg = 0; deg <= 360; deg += 90) {
    ctx.beginPath();
    ctx.moveTo(mapX(deg), pad.t); ctx.lineTo(mapX(deg), H - pad.b);
    ctx.stroke();
    ctx.fillStyle = '#a0a8b8'; ctx.font = '20px monospace'; ctx.textAlign = 'center';
    ctx.fillText(deg + '\u00b0', mapX(deg), H - pad.b + 24);
  }

  // Ceiling line (R = c/l)
  ctx.strokeStyle = '#f85149'; ctx.lineWidth = 2;
  ctx.setLineDash([6, 4]);
  ctx.beginPath();
  ctx.moveTo(pad.l, mapY(d.R)); ctx.lineTo(W - pad.r, mapY(d.R));
  ctx.stroke();
  ctx.setLineDash([]);
  ctx.fillStyle = '#f85149'; ctx.font = '18px monospace';
  ctx.textAlign = 'right';
  ctx.fillText('ceiling = c/\u2113 = ' + d.R.toFixed(2), W - pad.r - 4, mapY(d.R) - 6);

  // Mean line (U = R*kappa)
  ctx.strokeStyle = '#d29922'; ctx.lineWidth = 2;
  ctx.setLineDash([4, 4]);
  ctx.beginPath();
  ctx.moveTo(pad.l, mapY(d.U)); ctx.lineTo(W - pad.r, mapY(d.U));
  ctx.stroke();
  ctx.setLineDash([]);
  ctx.fillStyle = '#d29922'; ctx.font = '18px monospace';
  ctx.fillText('mean = R\u00b7\u03ba = ' + d.U.toFixed(2), W - pad.r - 4, mapY(d.U) + 18);

  // |MD(alpha)| curve
  ctx.strokeStyle = '#58a6ff'; ctx.lineWidth = 2;
  ctx.beginPath();
  let first = true;
  for (const [deg, md, _] of d.angular_profile) {
    const x = mapX(deg), y = mapY(md);
    if (first) { ctx.moveTo(x, y); first = false; }
    else ctx.lineTo(x, y);
  }
  ctx.stroke();

  // Labels
  ctx.fillStyle = '#c9d1d9'; ctx.font = '22px monospace'; ctx.textAlign = 'center';
  ctx.fillText('Focal chord angle \u03b1', W / 2, H - 8);
  ctx.save(); ctx.translate(16, H / 2); ctx.rotate(-PI / 2);
  ctx.fillText('|M\u00b7D(\u03b1)|', 0, 0); ctx.restore();
}

function renderRapidity(d) {
  const canvas = document.getElementById('canvas-rapidity');
  const ctx = canvas.getContext('2d');
  const W = canvas.width = canvas.offsetWidth * 2;
  const H = canvas.height = 500;
  ctx.clearRect(0, 0, W, H);

  if (!d.rapidity_data || d.rapidity_data.length === 0) {
    ctx.fillStyle = '#a0a8b8'; ctx.font = '20px monospace'; ctx.textAlign = 'center';
    ctx.fillText('(Circle: \u0394 = 1 everywhere)', W / 2, H / 2);
    return;
  }

  const pad = { l: 80, r: 40, t: 40, b: 60 };
  const pw = W - pad.l - pad.r;
  const ph = H - pad.t - pad.b;

  const deltas = d.rapidity_data.map(p => p.delta);
  const maxDelta = Math.max(...deltas) * 1.1;
  function mapX(deg) { return pad.l + deg / 360 * pw; }
  function mapY(v) { return pad.t + (maxDelta - v) / maxDelta * ph; }

  // Grid
  ctx.strokeStyle = '#3a4258'; ctx.lineWidth = 1;
  for (let deg = 0; deg <= 360; deg += 90) {
    ctx.beginPath();
    ctx.moveTo(mapX(deg), pad.t); ctx.lineTo(mapX(deg), H - pad.b);
    ctx.stroke();
    ctx.fillStyle = '#a0a8b8'; ctx.font = '20px monospace'; ctx.textAlign = 'center';
    ctx.fillText(deg + '\u00b0', mapX(deg), H - pad.b + 24);
  }

  // delta = 1 line
  if (1 <= maxDelta) {
    ctx.strokeStyle = '#3fb950'; ctx.lineWidth = 1;
    ctx.setLineDash([4, 4]);
    ctx.beginPath();
    ctx.moveTo(pad.l, mapY(1)); ctx.lineTo(W - pad.r, mapY(1));
    ctx.stroke();
    ctx.setLineDash([]);
    ctx.fillStyle = '#3fb950'; ctx.font = '16px monospace';
    ctx.textAlign = 'left';
    ctx.fillText('\u0394=1 (circle)', pad.l + 4, mapY(1) - 4);
  }

  // delta(theta) curve
  ctx.strokeStyle = '#bc8cff'; ctx.lineWidth = 2;
  ctx.beginPath();
  let first = true;
  for (const pt of d.rapidity_data) {
    const x = mapX(pt.theta), y = mapY(pt.delta);
    if (first) { ctx.moveTo(x, y); first = false; }
    else ctx.lineTo(x, y);
  }
  ctx.stroke();

  // sqrt(delta) curve
  ctx.strokeStyle = '#d29922'; ctx.lineWidth = 1.5;
  ctx.setLineDash([4, 2]);
  ctx.beginPath();
  first = true;
  for (const pt of d.rapidity_data) {
    const x = mapX(pt.theta), y = mapY(pt.sqrt_delta);
    if (first) { ctx.moveTo(x, y); first = false; }
    else ctx.lineTo(x, y);
  }
  ctx.stroke();
  ctx.setLineDash([]);

  // Labels
  ctx.fillStyle = '#c9d1d9'; ctx.font = '22px monospace'; ctx.textAlign = 'center';
  ctx.fillText('\u03b8 (ellipse parameter angle)', W / 2, H - 8);
  ctx.save(); ctx.translate(16, H / 2); ctx.rotate(-PI / 2);
  ctx.fillText('\u0394(\u03b8) = r\u2082/r\u2081', 0, 0); ctx.restore();

  // Legend
  ctx.fillStyle = '#bc8cff'; ctx.fillText('\u0394(\u03b8)', W - pad.r - 120, pad.t + 20);
  ctx.fillStyle = '#d29922'; ctx.fillText('\u221a\u0394(\u03b8)', W - pad.r - 120, pad.t + 44);

  // Stats
  const statsDiv = document.getElementById('stats-rapidity');
  statsDiv.innerHTML = `
    <div class="stat"><div class="label">\u03b7_max</div><div class="value">${d.eta_max.toFixed(4)}</div></div>
    <div class="stat"><div class="label">sinh(2\u03b7)</div><div class="value">${d.sinh_2eta.toFixed(4)}</div></div>
    <div class="stat"><div class="label">R = \u00bdsinh(2\u03b7)</div><div class="value highlight">${(d.sinh_2eta/2).toFixed(4)}</div></div>
    <div class="stat"><div class="label">\u0394_max/\u0394_min</div><div class="value warn">${((1+d.e)/(1-d.e)).toFixed(2)}\u00b2</div></div>
  `;
}

function fmtErr(ppm) {
  // Adaptive precision with ppb/ppm units — NEVER show bare "0"
  if (!isFinite(ppm)) return 'NaN';
  if (ppm === 0) return '<0.001 ppb';
  const ppb = ppm * 1000;
  if (ppm < 0.0000001) return '<0.001 ppb';
  if (ppm < 0.001) return ppb.toFixed(4) + ' ppb';
  if (ppm < 1) return ppb.toFixed(3) + ' ppb';
  if (ppm < 100) return ppm.toFixed(4) + ' ppm';
  return ppm.toFixed(2) + ' ppm';
}

function boldMatch(padded, exactStr) {
  // Compare digit-by-digit: bold all leading chars that match exact value,
  // dim the rest (those are the wrong digits)
  const pClean = padded.replace(/[\u00a0 ]/g, '');
  const eClean = exactStr.replace(/[\u00a0 ]/g, '');
  let matchLen = 0;
  for (let i = 0; i < Math.min(pClean.length, eClean.length); i++) {
    if (pClean[i] === eClean[i]) matchLen = i + 1;
    else break;
  }
  if (matchLen <= 0) return '<span style="color:#7a8498">' + padded + '</span>';
  // Walk padded, bold first matchLen non-space chars, dim the rest
  let result = '';
  let count = 0;
  let inBold = true;
  result += '<strong style="color:var(--bright)">';
  for (const ch of padded) {
    if (ch === '\u00a0') {
      result += ch;
    } else {
      count++;
      if (count <= matchLen) {
        result += ch;
      } else {
        if (inBold) { result += '</strong><span style="color:#7a8498">'; inBold = false; }
        result += ch;
      }
    }
  }
  if (inBold) result += '</strong>';
  else result += '</span>';
  return result;
}

function renderPerimeterTable(d) {
  // Header
  const headerDiv = document.getElementById('perimeter-header');
  headerDiv.innerHTML = `<span style="color:#58a6ff; font-size:13px; text-transform:uppercase; letter-spacing:1px;">Perimeter Comparison</span>` +
    `<span style="margin-left:12px;">a = <span>${d.a.toPrecision(10)}</span>, b = <span>${d.b.toPrecision(10)}</span></span>`;

  const div = document.getElementById('perimeter-table');

  // Uniform decimal formatting: find max decimal places needed, use fixed notation
  // All values formatted to 15 decimal places for alignment
  const exactStr = d.P_exact_hp || d.P_exact.toPrecision(16);
  const FIXED_DP = 15;

  // Format all perimeter values to same fixed decimal places
  function fmtPerim(val) {
    if (!isFinite(val)) return 'NaN';
    return val.toFixed(FIXED_DP);
  }

  let html = '';
  for (let i = 0; i < d.methods.length; i++) {
    const m = d.methods[i];
    const ppm = m.error_ppm;
    let errColor = '#f85149';
    if (ppm < 0.001) errColor = '#5cd07a';
    else if (ppm < 0.1) errColor = '#e8a832';
    else if (ppm < 10) errColor = '#f0c050';
    const isR6 = m.name.includes('R6+16exp');
    const nameClass = isR6 ? 'pe-name pe-champ' : (m.is_champion ? 'pe-name pe-ours' : 'pe-name');
    const pStr = fmtPerim(m.perimeter);
    const boldStr = boldMatch(pStr, fmtPerim(d.P_exact));
    const escapedName = m.name.replace(/'/g, "\\'");
    // Extract error rating from name (e.g. "0.083 ppm" or "0.018 ppb") and append "max"
    const errMatch = m.name.match(/\(([^)]+)\)/);
    const nameWithMax = errMatch ? m.name.replace(errMatch[0], '(' + errMatch[1] + ' max)') : m.name;
    html += `<div class="perim-entry" data-method="${m.name}" onmouseover="onMethodHover('${escapedName}')" onmouseout="onMethodUnhover()" onclick="onMethodClick('${escapedName}')">` +
      `<div class="pe-row1">` +
        `<div class="${nameClass}">${nameWithMax}</div>` +
      `</div>` +
      `<div class="pe-row2">` +
        `<div class="pe-val">${boldStr}</div>` +
        `<div class="pe-err" style="color:${errColor}">${fmtErr(ppm)}</div>` +
      `</div>` +
    `</div>`;
  }

  // Exact row
  const exactFmt = fmtPerim(d.P_exact);
  html += `<div class="perim-entry pe-exact">` +
    `<div class="pe-row1">` +
      `<div class="pe-name" style="color:var(--accent)">Exact (E(m) via AGM)</div>` +
    `</div>` +
    `<div class="pe-row2">` +
      `<div class="pe-val" style="color:var(--bright)"><strong>${exactFmt}</strong></div>` +
      `<div class="pe-err" style="color:#a0a8b8">\u2014</div>` +
    `</div>` +
  `</div>`;

  div.innerHTML = html;
}

// =========================================================================
// Chart.js — Error Charts (proper rendering, interactive tooltips)
// =========================================================================
let chartErrorLog = null;
let chartSignedOverview = null;
let chartSignedZoom = null;

const chartjsDefaults = {
  color: '#e2e6ed',
  borderColor: '#3a4258',
  font: { family: "'SF Mono', 'Cascadia Mono', 'Fira Code', monospace", size: 13 },
};
if (typeof Chart !== 'undefined') {
  Chart.defaults.color = chartjsDefaults.color;
  Chart.defaults.borderColor = chartjsDefaults.borderColor;
  Chart.defaults.font.family = chartjsDefaults.font.family;
  Chart.defaults.font.size = chartjsDefaults.font.size;
}

function renderErrorLandscape(d) {
  // Build datasets from errorSweep
  const logMethods = [
    { key: 'champion', color: '#ffd700', label: 'Mamoun R6+16exp+3log SCOR (0.007 ppb)', width: 3 },
    { key: 'r4_20exp', color: '#e8a832', label: 'R4+20exp (0.492 ppb)', width: 2 },
    { key: 'r5_varpro', color: '#bc8cff', label: 'R5+16exp (0.045 ppb)', width: 2 },
    { key: 'r3_15exp', color: '#f0883e', label: 'R3+15exp (1.43 ppb)', width: 2 },
    { key: 'r2_3exp_v23', color: '#58a6ff', label: 'Mamoun R2/3exp (83.4 ppb)', width: 2 },
    { key: 'r2_2exp_beater', color: '#79c0ff', label: 'Mamoun R2/2exp (530.5 ppb)', width: 1.5 },
    { key: 'ayala_raggi', color: '#ff7eb6', label: 'Ayala-Rendón (573.6 ppb)', width: 1.5 },
    { key: 'ramanujan_ii', color: '#d29922', label: 'Ramanujan II', width: 1.5 },
    { key: 'ramanujan_i', color: '#f85149', label: 'Ramanujan I', width: 1.5 },
  ];
  // Transform X: use -log10(1-e) to stretch high eccentricities
  // e=0 -> 0, e=0.9 -> 1, e=0.99 -> 2, e=0.999 -> 3
  function xTransform(e) { return -Math.log10(Math.max(1e-6, 1 - e)); }

  const datasets = logMethods.map(m => ({
    label: m.label,
    data: errorSweep.filter(pt => pt[m.key] > 0 && isFinite(pt[m.key]))
                     .map(pt => ({ x: xTransform(pt.e), y: pt[m.key] })),
    borderColor: m.color,
    backgroundColor: m.color + '20',
    borderWidth: m.width,
    pointRadius: 0,
    tension: 0.2,
    fill: false,
  }));

  if (chartErrorLog) chartErrorLog.destroy();
  chartErrorLog = new Chart(document.getElementById('chart-error-log'), {
    type: 'scatter',
    data: { datasets },
    options: {
      responsive: true, maintainAspectRatio: false,
      showLine: true,
      plugins: {
        tooltip: {
          mode: 'nearest', intersect: false,
          callbacks: {
            label: function(ctx) {
              const ppm = ctx.parsed.y;
              return ctx.dataset.label + ': ' + (ppm < 1 ? (ppm*1000).toFixed(3) + ' ppb' : ppm.toFixed(3) + ' ppm');
            }
          }
        },
        legend: { position: 'bottom', labels: { usePointStyle: true, pointStyle: 'line', padding: 16, font: { size: 13 } } },
        annotation: d.e > 0 ? {
          annotations: {
            currentE: {
              type: 'line', xMin: xTransform(d.e), xMax: xTransform(d.e),
              borderColor: '#f0f6fc88', borderWidth: 1, borderDash: [4, 4],
              label: { display: true, content: 'e=' + d.e.toFixed(3), position: 'start', color: '#f0f6fc', font: { size: 12 } }
            }
          }
        } : {}
      },
      scales: {
        x: {
          type: 'linear', min: 0, max: 3.5,
          title: { display: true, text: 'Eccentricity e  (stretched: -log\u2081\u2080(1-e))', font: { size: 15 } },
          grid: { color: '#3a4258' },
          ticks: {
            callback: function(v) {
              const e = 1 - Math.pow(10, -v);
              if (v <= 0.01) return '0';
              if (Math.abs(v - 0.3) < 0.05) return '0.5';
              if (Math.abs(v - 1) < 0.05) return '0.9';
              if (Math.abs(v - 1.3) < 0.05) return '0.95';
              if (Math.abs(v - 2) < 0.05) return '0.99';
              if (Math.abs(v - 2.3) < 0.05) return '0.995';
              if (Math.abs(v - 3) < 0.05) return '0.999';
              return '';
            },
            stepSize: 0.1,
            maxTicksLimit: 20,
          }
        },
        y: {
          type: 'logarithmic', min: 1e-7, max: 10000,
          title: { display: true, text: 'Error (ppm, log scale)', font: { size: 15 } },
          grid: { color: '#3a4258' },
          afterBuildTicks: function(axis) {
            // Only show clean powers of 10
            axis.ticks = [];
            for (let exp = -7; exp <= 4; exp++) {
              axis.ticks.push({ value: Math.pow(10, exp) });
            }
          },
          ticks: {
            callback: function(v) {
              const log = Math.log10(v);
              if (Math.abs(log - Math.round(log)) > 0.01) return '';
              if (v >= 1) return v.toFixed(0) + ' ppm';
              if (v >= 0.001) return (v*1000).toFixed(0) + ' ppb';
              if (v >= 0.000001) return (v*1e6).toFixed(0) + ' ppt';
              return v.toExponential(0) + ' ppm';
            },
            maxTicksLimit: 12,
          }
        }
      },
      interaction: { mode: 'nearest', axis: 'x', intersect: false },
    }
  });
}

function renderSignedError(d) {
  // Log-eccentricity transform: -log10(1-e) stretches high eccentricities
  function eToLogX(e) { return -Math.log10(Math.max(1e-6, 1 - e)); }
  function logXToE(v) { return 1 - Math.pow(10, -v); }

  const overviewMethods = [
    { key: 'r2_3exp_v23', color: '#58a6ff', label: 'R2/3exp V23 (83 ppb)', width: 2 },
    { key: 'r3_15exp', color: '#f0883e', label: 'R3+15exp (1.43 ppb)', width: 1.5 },
    { key: 'champion', color: '#ffd700', label: 'Mamoun R6+16exp+3log SCOR (0.007 ppb)', width: 2.5 },
    { key: 'r4_20exp', color: '#e8a832', label: 'R4+20exp', width: 1.5 },
    { key: 'r5_varpro', color: '#bc8cff', label: 'R5+16exp', width: 1.5 },
  ];
  const datasets = overviewMethods.map(m => ({
    label: m.label,
    data: signedSweep.filter(pt => pt[m.key] !== undefined && isFinite(pt[m.key]))
                      .map(pt => ({ x: eToLogX(pt.e), y: pt[m.key] })),
    borderColor: m.color,
    borderWidth: m.width,
    pointRadius: 0,
    tension: 0.15,
    fill: false,
  }));

  if (chartSignedOverview) chartSignedOverview.destroy();
  chartSignedOverview = new Chart(document.getElementById('chart-signed-overview'), {
    type: 'scatter',
    data: { datasets },
    options: {
      responsive: true, maintainAspectRatio: false,
      showLine: true,
      plugins: {
        tooltip: {
          mode: 'nearest', intersect: false,
          callbacks: {
            label: function(ctx) {
              var e = logXToE(ctx.parsed.x);
              return ctx.dataset.label + ': ' + ctx.parsed.y.toFixed(3) + ' ppb at e=' + e.toFixed(4);
            }
          }
        },
        legend: { position: 'bottom', labels: { usePointStyle: true, pointStyle: 'line', padding: 16 } },
      },
      scales: {
        x: {
          type: 'linear', min: 0, max: 3.5,
          title: { display: true, text: 'Eccentricity e (log scale)', font: { size: 15 } },
          grid: { color: '#3a4258' },
          ticks: {
            callback: function(v) {
              var map = {0:'0', 0.301:'0.5', 1:'0.9', 1.301:'0.95', 2:'0.99', 2.301:'0.995', 3:'0.999'};
              for (var k in map) { if (Math.abs(v - parseFloat(k)) < 0.05) return map[k]; }
              return '';
            },
            autoSkip: false,
            stepSize: 0.301,
          }
        },
        y: {
          type: 'linear',
          title: { display: true, text: 'Signed error (ppb) — positive = overestimate', font: { size: 14 } },
          grid: { color: '#3a4258' },
          ticks: { callback: v => v.toFixed(0) + ' ppb' }
        }
      },
      interaction: { mode: 'nearest', axis: 'x', intersect: false },
    }
  });
}

function renderSignedErrorZoom(d) {
  // Filter to e > 0.9, sub-2ppb methods
  const zoomMethods = [
    { key: 'champion', color: '#ffd700', label: 'Mamoun R6+16exp+3log SCOR (0.007 ppb)', width: 3 },
    { key: 'r4_20exp', color: '#e8a832', label: 'R4+20exp (0.492 ppb)', width: 2 },
    { key: 'r5_varpro', color: '#bc8cff', label: 'R5+16exp (0.045 ppb)', width: 2 },
    { key: 'r3_15exp', color: '#f0883e', label: 'R3+15exp (1.43 ppb)', width: 1.5 },
  ];
  const datasets = zoomMethods.map(m => ({
    label: m.label,
    data: signedSweep.filter(pt => pt.e >= 0.9 && pt[m.key] !== undefined && isFinite(pt[m.key]))
                      .map(pt => ({ x: pt.e, y: Math.max(-1.5, Math.min(1.5, pt[m.key])) })),
    borderColor: m.color,
    borderWidth: m.width,
    pointRadius: 0,
    tension: 0.1,
    fill: false,
  }));
  // Add champion envelope band as a filled dataset
  datasets.unshift({
    label: '\u00b10.007 ppb envelope',
    data: [{x: 0.9, y: 0.018}, {x: 1.0, y: 0.018}],
    borderColor: '#3fb95044',
    backgroundColor: '#3fb95015',
    borderWidth: 1,
    borderDash: [6, 4],
    pointRadius: 0,
    fill: false,
  });
  datasets.unshift({
    label: '',
    data: [{x: 0.9, y: -0.049}, {x: 1.0, y: -0.049}],
    borderColor: '#3fb95044',
    borderWidth: 1,
    borderDash: [6, 4],
    pointRadius: 0,
    fill: false,
    showLine: true,
  });

  if (chartSignedZoom) chartSignedZoom.destroy();
  chartSignedZoom = new Chart(document.getElementById('chart-signed-zoom'), {
    type: 'scatter',
    data: { datasets },
    options: {
      responsive: true, maintainAspectRatio: false,
      showLine: true,
      plugins: {
        tooltip: {
          mode: 'nearest', intersect: false,
          filter: function(item) { return item.datasetIndex >= 2; },
          callbacks: {
            label: function(ctx) {
              return ctx.dataset.label + ': ' + ctx.parsed.y.toFixed(4) + ' ppb at e=' + ctx.parsed.x.toFixed(4);
            }
          }
        },
        legend: {
          position: 'bottom',
          labels: {
            usePointStyle: true, pointStyle: 'line', padding: 16,
            filter: function(item) { return item.text && item.text.length > 0 && !item.text.startsWith('\u00b1'); }
          }
        },
      },
      scales: {
        x: {
          type: 'linear', min: 0.9, max: 1.0,
          title: { display: true, text: 'Eccentricity e (zoomed: 0.9 \u2013 1.0)', font: { size: 15 } },
          grid: { color: '#3a4258' },
          ticks: { stepSize: 0.01, callback: v => v.toFixed(2) }
        },
        y: {
          type: 'linear', min: -0.6, max: 0.6,
          title: { display: true, text: 'Signed error (ppb)', font: { size: 15 } },
          grid: { color: '#3a4258' },
          ticks: { stepSize: 0.1, callback: v => v.toFixed(1) }
        }
      },
      interaction: { mode: 'nearest', axis: 'x', intersect: false },
    }
  });
}


function renderInfoStats(d) {
  const div = document.getElementById('stats-info');
  div.innerHTML = `
    <div class="stat"><div class="label">I_f = log\u2082(R)</div><div class="value highlight">${d.I_f.toFixed(4)}</div><div class="unit">bits</div></div>
    <div class="stat"><div class="label">H_u = log\u2082(U)</div><div class="value warn">${d.H_u.toFixed(4)}</div><div class="unit">bits</div></div>
    <div class="stat"><div class="label">I_f - H_u</div><div class="value" style="color:#3fb950">${d.info_surplus.toFixed(6)}</div><div class="unit">bits</div></div>
    <div class="stat"><div class="label">log\u2082(\u03c0/2)</div><div class="value" style="color:#3fb950">${Math.log2(PI/2).toFixed(6)}</div><div class="unit">bits</div></div>
    <div class="stat"><div class="label">CV\u00b2 = \u03c0\u00b2/8-1</div><div class="value">${d.CV2.toFixed(6)}</div></div>
    <div class="stat"><div class="label">CV</div><div class="value">${d.CV.toFixed(6)}</div></div>
  `;
}

function renderChordTable(d) {
  const div = document.getElementById('chord-table');
  if (!d.chord_data || d.chord_data.length === 0) {
    div.innerHTML = '<p style="color:#a0a8b8; font-size:12px;">(Circle: all chords identical)</p>';
    return;
  }
  let html = `<table><thead><tr>
    <th>\u03b1 (\u00b0)</th><th>\u03c1\u2081</th><th>\u03c1\u2082</th><th>HM</th><th>|M\u00b7D|</th>
  </tr></thead><tbody>`;
  for (const ch of d.chord_data) {
    html += `<tr>
      <td class="num">${ch.angle}</td>
      <td class="num">${ch.rho1.toFixed(6)}</td>
      <td class="num">${ch.rho2.toFixed(6)}</td>
      <td class="num" style="color:#3fb950">${ch.harmonic_mean.toFixed(6)}</td>
      <td class="num">${ch.MD.toFixed(6)}</td>
    </tr>`;
  }
  html += '</tbody></table>';
  div.innerHTML = html;
}

// =========================================================================
// Winner-by-eccentricity band (canvas, logarithmic x-axis)
// =========================================================================
function renderWinnerBands() {
  const canvas = document.getElementById('canvas-winner-band');
  if (!canvas) return;
  const ctx = canvas.getContext('2d');
  // Proper 2x retina: CSS height from attribute, internal = 2x
  const cssH = 220;
  const W = canvas.width = canvas.offsetWidth * 2;
  const H = canvas.height = cssH * 2;
  canvas.style.height = cssH + 'px';
  ctx.clearRect(0, 0, W, H);

  const pad = { l: 180, r: 60, t: 36, b: 80 };
  const pw = W - pad.l - pad.r;

  // Two stacked bands: "Best overall" + "Best excluding champion"
  const winH = 40;
  const gap = 16;
  const runH = 140;
  const runTop = pad.t + winH + gap;
  const totalH = winH + gap + runH;

  // 10 colors at 36° hue spacing on HSL wheel (S≈80%, L≈58%), maximally distinct
  const methods = [
    { key: 'champion',        color: '#ffd700', label: 'R6+16exp+3log SCOR (0.007 ppb)' },   // gold
    { key: 'r4_20exp',        color: '#3BB8B8', label: 'R4+20exp (0.492 ppb)' },   // H=180° cyan
    { key: 'r5_varpro',        color: '#7E65D6', label: 'R5+16exp (0.045 ppb)' },   // H=252° indigo
    { key: 'r3_15exp',        color: '#3B8AEB', label: 'R3+15exp (1.43 ppb)' },    // H=216° blue
    { key: 'r2_3exp_v23',     color: '#C157D6', label: 'R2/3exp (83 ppb)' },       // H=288° magenta
    { key: 'r2_2exp_beater',  color: '#D65797', label: 'R2/2exp (530 ppb)' },      // H=324° pink
    { key: 'ayala_raggi',     color: '#F04848', label: 'Ayala-Rendón (574 ppb)' },  // H=0°   red
    { key: 'cantrell',        color: '#EB9E14', label: 'Cantrell (2001)' },         // H=36°  amber
    { key: 'ramanujan_ii',    color: '#A8C824', label: 'Ramanujan II (1914)' },     // H=72°  lime
    { key: 'ramanujan_i',     color: '#3BB87A', label: 'Ramanujan I (1914)' },      // H=144° teal
  ];
  const runnerMethods = methods.filter(m => m.key !== 'champion');

  // x transform: -log10(1-e), range [0, 3.5]
  const xMin = 0, xMax = 3.5;
  function xT(e) { return -Math.log10(Math.max(1e-6, 1 - e)); }

  // Use precomputed mpmath-accurate winner data (30 digits, no float64 noise)
  const winnerByPx = new Array(pw);
  for (let px = 0; px < pw; px++) {
    const xVal = xMin + (px / pw) * (xMax - xMin);
    const e = 1 - Math.pow(10, -xVal);

    // Find nearest precomputed point
    let bestIdx = 0;
    for (let i = 0; i < winnerData.length; i++) {
      if (Math.abs(winnerData[i].e - e) < Math.abs(winnerData[bestIdx].e - e)) bestIdx = i;
    }
    const wd = winnerData[bestIdx];

    // Look up winner/runner-up colors from precomputed keys
    const winM = methods.find(mm => mm.key === wd.winner) || methods[0];
    const runM = runnerMethods.find(mm => mm.key === wd.runner) || runnerMethods[0];

    ctx.fillStyle = winM.color;
    ctx.fillRect(pad.l + px, pad.t, 1, winH);
    ctx.fillStyle = runM.color;
    ctx.fillRect(pad.l + px, runTop, 1, runH);

    winnerByPx[px] = { winner: winM, runner: runM, e: e,
                        winErr: wd.winErr, runErr: wd.runErr };
  }

  // Borders
  ctx.strokeStyle = '#484f5e';
  ctx.lineWidth = 2;
  ctx.strokeRect(pad.l, pad.t, pw, winH);
  ctx.strokeRect(pad.l, runTop, pw, runH);

  // Row labels (left of bands)
  ctx.textAlign = 'right';
  ctx.fillStyle = '#c9d1d9';
  ctx.font = 'bold 24px -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif';
  ctx.fillText('Best overall', pad.l - 14, pad.t + winH / 2 + 8);
  ctx.fillText('Runner-up', pad.l - 14, runTop + runH / 2 + 8);

  // X axis ticks
  ctx.textAlign = 'center';
  ctx.font = '22px -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif';
  ctx.fillStyle = '#a0a8b8';
  const ticks = [
    [0, '0'], [0.3, '0.5'], [1, '0.9'], [1.3, '0.95'],
    [2, '0.99'], [2.3, '0.995'], [3, '0.999']
  ];
  for (const [v, label] of ticks) {
    const x = pad.l + (v - xMin) / (xMax - xMin) * pw;
    ctx.beginPath();
    ctx.moveTo(x, runTop + runH);
    ctx.lineTo(x, runTop + runH + 10);
    ctx.strokeStyle = '#a0a8b8';
    ctx.lineWidth = 1;
    ctx.stroke();
    ctx.fillText(label, x, runTop + runH + 32);
  }
  ctx.fillStyle = '#c9d1d9';
  ctx.font = '22px -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif';
  ctx.fillText('Eccentricity e', W / 2, runTop + runH + 58);

  // Legend via HTML (much crisper than canvas text)
  const legendDiv = document.getElementById('winner-legend');
  if (legendDiv) {
    legendDiv.innerHTML = methods.map(m =>
      '<div class="legend-item"><span class="legend-dot" style="background:' + m.color + '"></span> ' + m.label + '</div>'
    ).join('');
  }

  // Mouseover tooltip
  let tooltip = document.getElementById('winner-tooltip');
  if (!tooltip) {
    tooltip = document.createElement('div');
    tooltip.id = 'winner-tooltip';
    tooltip.style.cssText = 'position:absolute;background:#161b22;border:1px solid #30363d;' +
      'color:#c9d1d9;padding:6px 10px;border-radius:6px;font-size:13px;pointer-events:none;' +
      'display:none;z-index:100;white-space:nowrap;box-shadow:0 4px 12px rgba(0,0,0,0.4);';
    canvas.parentElement.style.position = 'relative';
    canvas.parentElement.appendChild(tooltip);
  }
  canvas.style.cursor = 'crosshair';
  canvas.onmousemove = function(evt) {
    const rect = canvas.getBoundingClientRect();
    const scaleX = W / rect.width;
    const scaleY = H / rect.height;
    const cx = (evt.clientX - rect.left) * scaleX;
    const cy = (evt.clientY - rect.top) * scaleY;
    const px = Math.round(cx - pad.l);
    if (px >= 0 && px < pw) {
      const w = winnerByPx[px];
      const eStr = w.e < 0.01 ? w.e.toExponential(1) : w.e.toFixed(4);
      const inRunner = (cy >= runTop && cy <= runTop + runH);
      const m = inRunner ? w.runner : w.winner;
      const err = inRunner ? w.runErr : w.winErr;
      const errStr = err < 0.001 ? (err * 1000).toFixed(2) + ' ppb' : err.toFixed(3) + ' ppm';
      const bandLabel = inRunner ? '(runner-up)' : '(best)';
      tooltip.innerHTML = '<span style="color:' + m.color + '">\u25CF</span> ' +
        '<strong>' + m.label + '</strong> ' + bandLabel + '<br>e = ' + eStr + ', error = ' + errStr;
      tooltip.style.display = 'block';
      tooltip.style.left = (evt.clientX - rect.left + 12) + 'px';
      tooltip.style.top = (evt.clientY - rect.top - 40) + 'px';
    } else {
      tooltip.style.display = 'none';
    }
  };
  canvas.onmouseleave = function() { tooltip.style.display = 'none'; };

  // Save state for eccentricity indicator overlay
  _winnerBandState = {
    canvas: canvas, padL: pad.l, padT: pad.t, pw: pw, bandH: totalH,
    xMin: xMin, xMax: xMax,
    imgData: ctx.getImageData(0, 0, W, H)
  };
}

// Winner band: overlay a vertical indicator at current eccentricity
// Stores canvas params so the indicator can be updated without full redraw.
var _winnerBandState = null;
function updateWinnerIndicator(e) {
  if (!_winnerBandState) return;
  var s = _winnerBandState;
  var canvas = s.canvas, ctx = canvas.getContext('2d');
  // Redraw from saved image
  if (s.imgData) ctx.putImageData(s.imgData, 0, 0);
  // Draw vertical line at current e
  var xVal = -Math.log10(Math.max(1e-6, 1 - e));
  var x = s.padL + (xVal - s.xMin) / (s.xMax - s.xMin) * s.pw;
  if (x >= s.padL && x <= s.padL + s.pw) {
    ctx.save();
    ctx.strokeStyle = '#ffffff';
    ctx.lineWidth = 3;
    ctx.setLineDash([]);
    ctx.beginPath();
    ctx.moveTo(x, s.padT);
    ctx.lineTo(x, s.padT + s.bandH);
    ctx.stroke();
    // Label
    ctx.fillStyle = '#ffffff';
    ctx.font = 'bold 18px monospace';
    ctx.textAlign = 'center';
    ctx.fillText('e=' + e.toFixed(3), x, s.padT - 4);
    ctx.restore();
  }
}

// =========================================================================
// Error Metrics: Peak, RMS, Mean (computed from errorSweep in JS)
// =========================================================================
function renderErrorMetrics() {
  const div = document.getElementById('error-metrics-table');
  if (!div || !errorSweep || errorSweep.length === 0) return;

  const methods = [
    { key: 'champion', name: '\u2605 Mamoun R6+16exp+3log SCOR (0.007 ppb)' },
    { key: 'r4_20exp', name: '\u2606 Mamoun R4+20exp (0.492 ppb)' },
    { key: 'r5_varpro', name: '\u2606 Mamoun R5+16exp (0.045 ppb)' },
    { key: 'r3_15exp', name: '\u2606 Mamoun R3+15exp (1.43 ppb)' },
    { key: 'r2_3exp_v23', name: '\u2606 Mamoun R2/3exp (0.083 ppm)' },
    { key: 'r2_2exp_beater', name: '\u2606 Mamoun R2/2exp (0.530 ppm)' },
    { key: 'ayala_raggi', name: 'Ayala-Rendón R2/2exp (2025)' },
    { key: 'cantrell', name: 'Cantrell (2001)' },
    { key: 'ramanujan_ii', name: 'Ramanujan II (1914)' },
    { key: 'ramanujan_i', name: 'Ramanujan I (1914)' },
  ];

  const metrics = methods.map(m => {
    const vals = errorSweep.map(pt => pt[m.key]).filter(v => v !== undefined && isFinite(v) && v > 0);
    const n = vals.length;
    const peak = Math.max(...vals);
    const mean = vals.reduce((a, b) => a + b, 0) / n;
    const rms = Math.sqrt(vals.reduce((a, b) => a + b * b, 0) / n);
    const sorted = [...vals].sort((a, b) => a - b);
    const median = sorted[Math.floor(n / 2)];
    return { ...m, peak, mean, rms, median };
  });

  // Sort by peak error
  metrics.sort((a, b) => a.peak - b.peak);

  let html = '<table><thead><tr>' +
    '<th>#</th><th>Method</th>' +
    '<th style="text-align:right">Peak (max)</th>' +
    '<th style="text-align:right">RMS</th>' +
    '<th style="text-align:right">Mean</th>' +
    '<th style="text-align:right">Median</th>' +
    '</tr></thead><tbody>';

  let rank = 1;
  for (const m of metrics) {
    const isBest = (rank === 1);
    const rc = isBest ? ' class="champion-row"' : '';
    html += '<tr' + rc + '>' +
      '<td>' + rank + '</td>' +
      '<td>' + m.name + '</td>' +
      '<td class="num" style="color:#f85149">' + fmtErr(m.peak) + '</td>' +
      '<td class="num" style="color:#d29922">' + fmtErr(m.rms) + '</td>' +
      '<td class="num" style="color:#58a6ff">' + fmtErr(m.mean) + '</td>' +
      '<td class="num" style="color:#a0a8b8">' + fmtErr(m.median) + '</td>' +
      '</tr>';
    rank++;
  }
  html += '</tbody></table>';
  div.innerHTML = html;
}

// Initial render
fetchAndRender(1.0, 0.714);

// Build formula buttons with green stars and tip words
setTimeout(function() {
  var btnRow = document.getElementById('formula-buttons');
  if (!btnRow || !formulaLatex) return;

  // Tip words for "ours" buttons — keyed by substring match
  var tipMap = [
    { match: 'Mamoun R2/2exp', tip: 'simplest' },
    { match: 'Mamoun R2/3exp', tip: 'handiest' },
    { match: 'R3+15exp', tip: 'elegant' },
    { match: 'R4+20exp', tip: 'deep' },
    { match: 'R5+16exp', tip: 'precise' },
    { match: 'R6+16exp', tip: 'champion' },
  ];
  // "Ours" names contain "Mamoun"
  var isOurs = function(n) { return n.indexOf('Mamoun') >= 0; };

  var names = Object.keys(formulaLatex);
  var btnEls = [];
  names.forEach(function(name) {
    var btn = document.createElement('button');
    btn.className = 'formula-btn' + (name === lockedFormula ? ' active' : '');
    btn.dataset.method = name;
    if (isOurs(name)) {
      btn.innerHTML = '<span class="btn-star">\u2605</span>' + name;
    } else {
      btn.textContent = name;
    }
    btn.onclick = function() { onMethodClick(name); };
    btnRow.appendChild(btn);
    btnEls.push({ el: btn, name: name });
  });

  // Add tip annotations after layout settles
  setTimeout(function() {
    btnEls.forEach(function(b) {
      var tipWord = null;
      tipMap.forEach(function(t) { if (b.name.indexOf(t.match) >= 0) tipWord = t.tip; });
      if (!tipWord) return;

      var wrapper = document.createElement('div');
      wrapper.style.position = 'relative';
      wrapper.style.display = 'inline-block';
      b.el.parentNode.insertBefore(wrapper, b.el);
      wrapper.appendChild(b.el);

      var tip = document.createElement('span');
      tip.className = 'formula-tip';
      tip.style.bottom = '100%';
      tip.style.left = '50%';
      tip.style.marginBottom = '2px';
      // Cocky angle: alternate tilt directions
      var angles = { simplest: -12, handiest: 8, elegant: -10, deep: 14, precise: -8, champion: 6 };
      var angle = angles[tipWord] || 0;
      tip.style.transform = 'translateX(-50%) rotate(' + angle + 'deg)';
      // Curved arrow SVG pointing down to button
      tip.innerHTML = tipWord +
        '<svg width="20" height="14" style="bottom:-12px;left:50%;transform:translateX(-50%)">' +
        '<path d="M10 0 Q 6 8 10 13" stroke="#f0883e" fill="none" stroke-width="1.5"/>' +
        '<path d="M7 10 L10 14 L12 9" stroke="#f0883e" fill="none" stroke-width="1.2"/>' +
        '</svg>';
      wrapper.appendChild(tip);
    });
  }, 100);

  showFormula(lockedFormula);
}, 500);
</script>
</body>
</html>"""


class EllipseHandler(http.server.SimpleHTTPRequestHandler):
    """Custom handler for the ellipse demo server."""

    def do_GET(self):
        parsed = urlparse(self.path)

        if parsed.path == '/' or parsed.path == '/index.html':
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.end_headers()
            # Inject sweep data into the HTML
            page = HTML_PAGE.replace(
                'SWEEP_DATA_PLACEHOLDER',
                json.dumps(SWEEP_DATA)
            ).replace(
                'ERROR_SWEEP_PLACEHOLDER',
                json.dumps(ERROR_SWEEP)
            ).replace(
                'MAX_ERRORS_PLACEHOLDER',
                json.dumps(MAX_ERRORS)
            ).replace(
                'FORMULA_INFO_PLACEHOLDER',
                json.dumps(FORMULA_INFO)
            ).replace(
                'SIGNED_SWEEP_PLACEHOLDER',
                json.dumps(SIGNED_SWEEP)
            ).replace(
                'FORMULA_HTML_PLACEHOLDER',
                json.dumps(FORMULA_HTML)
            ).replace(
                'FORMULA_LATEX_PLACEHOLDER',
                json.dumps(FORMULA_LATEX)
            ).replace(
                'WINNER_DATA_PLACEHOLDER',
                json.dumps(WINNER_DATA)
            )
            self.wfile.write(page.encode('utf-8'))

        elif parsed.path == '/api/compute':
            params = parse_qs(parsed.query)
            # Accept a,b params (preferred) or fall back to e with a=1
            if 'a' in params and 'b' in params:
                a = float(params['a'][0])
                b = float(params['b'][0])
            else:
                e = float(params.get('e', [0.5])[0])
                e = max(0.001, min(e, 0.999))
                a = 1.0
                b = a * math.sqrt(1 - e ** 2)
            data = compute_data(a, b)
            if data is None:
                data = {'error': 'Invalid parameters'}
            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Access-Control-Allow-Origin', '*')
            self.end_headers()
            self.wfile.write(json.dumps(data).encode('utf-8'))

        else:
            self.send_error(404)

    def log_message(self, format, *args):
        """Suppress default logging for cleaner output."""
        pass


def main():
    global PORT
    if '--port' in sys.argv:
        idx = sys.argv.index('--port')
        if idx + 1 < len(sys.argv):
            PORT = int(sys.argv[idx + 1])

    # Try to find an available port
    for attempt_port in range(PORT, PORT + 20):
        try:
            socketserver.TCPServer.allow_reuse_address = True
            with socketserver.TCPServer(("", attempt_port), EllipseHandler) as httpd:
                PORT = attempt_port
                url = f"http://localhost:{PORT}"
                print()
                print("=" * 60)
                print("  ELLIPSE PERIMETER — Interactive Web Demo")
                print("=" * 60)
                print()
                print(f"  Server running at: {url}")
                print(f"  Press Ctrl+C to stop.")
                print()
                print("  Features:")
                print("    - 11-method perimeter comparison (R2 through R6+16exp+3log SCOR)")
                print("    - Convergent Pade Tower hierarchy")
                print("    - Error landscape (log scale)")
                print("    - Focal certainty-uncertainty duality")
                print("    - VARPRO coefficient separation theorem")
                print()
                print("  Best peak error: R6+16exp+3log SCOR at 0.007 ppb (7 ppt)")
                print("  Paper: 'Two Foci, One Curve'")
                print("  Source: https://github.com/gutmogutmam/ellipse")
                print()
                print("=" * 60)

                # Open browser in a separate thread
                threading.Timer(0.5, lambda: webbrowser.open(url)).start()

                try:
                    httpd.serve_forever()
                except KeyboardInterrupt:
                    print("\n  Server stopped.")
        except OSError:
            continue
        break
    else:
        print(f"  ERROR: Could not find an available port in range {PORT}-{PORT+19}")
        sys.exit(1)


if __name__ == '__main__':
    main()
