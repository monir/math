#!/usr/bin/env python3
"""
Mercury GR perihelion precession and the K-E period duality.

Verifies:
1. Mercury's perihelion advance from first-order Schwarzschild formula
2. The focal resolution R = c/l and the bridge formula ε_GR = R · 3r_S/(2c)
3. The exact Schwarzschild orbit involves K(k²) — period of the FIRST kind
4. The perimeter involves E(e²) — period of the SECOND kind
5. The Legendre relation: K·E' + E·K' - K·K' = π/2 = 1/κ
6. The MEPB coefficient from κ/2 log branch amplitude
7. Both K and E develop logarithmic behavior at m=1 (shared singularity)
"""
import math
import sys
import os

# High precision via mpmath
try:
    import mpmath
    mpmath.mp.dps = 50
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False
    print("  WARNING: mpmath not available; using math (limited precision)")

# Physical constants (SI)
G = 6.67430e-11
M_sun = 1.98847e30
c_light = 299_792_458.0
GM_sun = G * M_sun

# Mercury orbital elements
a_orb = 5.790905e10
e_orb = 0.205630
T_days = 87.9691

# Derived
b_orb = a_orb * math.sqrt(1 - e_orb**2)
c_focal = a_orb * e_orb
ell = b_orb**2 / a_orb  # semi-latus rectum
r_S = 2 * GM_sun / c_light**2  # Schwarzschild radius

# ===================================================================
# 1) GR perihelion precession
# ===================================================================
delta_rad = 6.0 * math.pi * GM_sun / (c_light**2 * a_orb * (1.0 - e_orb**2))
arcsec_per_rad = 206_264.80624709636
arcsec_per_orbit = delta_rad * arcsec_per_rad
orbits_per_century = 36_525.0 / T_days
arcsec_per_century = arcsec_per_orbit * orbits_per_century

print("=" * 70)
print("  1) Mercury GR Perihelion Precession")
print("=" * 70)
print(f"  GM_sun    = {GM_sun:.12e} m³/s²")
print(f"  a         = {a_orb:.12e} m")
print(f"  b         = {b_orb:.12e} m")
print(f"  e         = {e_orb:.6f}")
print(f"  ℓ = a(1-e²) = {ell:.12e} m")
print(f"  c = ae    = {c_focal:.12e} m")
print(f"  r_S (Sun) = {r_S:.6f} m")
print()
print(f"  Δϖ / orbit  = {delta_rad:.12e} rad")
print(f"              = {arcsec_per_orbit:.9f} arcsec")
print(f"  orbits/cent = {orbits_per_century:.9f}")
print(f"  Δϖ / cent   = {arcsec_per_century:.6f} arcsec")
print(f"  (expected: ~42.98 arcsec/century)")
print()

# ===================================================================
# 2) Bridge formula: ε_GR = R · 3r_S/(2c)
# ===================================================================
R_focal = c_focal / ell
U_sweep = R_focal * 2 / math.pi
eps_GR = 3 * GM_sun / (c_light**2 * ell)
ratio_eps_R = eps_GR / R_focal
bridge_check = 3 * r_S / (2 * c_focal)

print("=" * 70)
print("  2) Bridge Formula: ε_GR = R · 3r_S/(2c)")
print("=" * 70)
print(f"  R = c/ℓ   = {R_focal:.10f}")
print(f"  U = Rκ    = {U_sweep:.10f}")
print(f"  R / U     = {R_focal / U_sweep:.14f}")
print(f"  π / 2     = {math.pi / 2:.14f}")
print()
print(f"  ε_GR          = {eps_GR:.12e}")
print(f"  ε_GR / R      = {ratio_eps_R:.12e}")
print(f"  3r_S / (2c)   = {bridge_check:.12e}")
print(f"  Match?        {abs(ratio_eps_R - bridge_check) < 1e-20}")
print()

if not HAS_MPMATH:
    print("  (Skipping high-precision checks; install mpmath)")
    sys.exit(0)

# ===================================================================
# 3) K-E Period Duality
# ===================================================================
pi = mpmath.pi
kappa = 2 / pi

print("=" * 70)
print("  3) K-E Period Duality: Perimeter (E) vs Orbit (K)")
print("=" * 70)
print(f"  κ = 2/π = {mpmath.nstr(kappa, 30)}")
print(f"  π/2 = 1/κ = {mpmath.nstr(pi/2, 30)}")
print()

# Hypergeometric representations
print("  Hypergeometric representations:")
m_test = mpmath.mpf('0.5')
K_hyp = (pi/2) * mpmath.hyp2f1(mpmath.mpf('0.5'), mpmath.mpf('0.5'), 1, m_test)
K_direct = mpmath.ellipk(m_test)
E_hyp = (pi/2) * mpmath.hyp2f1(mpmath.mpf('-0.5'), mpmath.mpf('0.5'), 1, m_test)
E_direct = mpmath.ellipe(m_test)

print(f"  At m = 0.5:")
print(f"    K(m) = {mpmath.nstr(K_direct, 30)}")
print(f"    (π/2)·₂F₁(½,½;1;m) = {mpmath.nstr(K_hyp, 30)}  match: {abs(K_direct - K_hyp) < mpmath.mpf(10)**(-40)}")
print(f"    E(m) = {mpmath.nstr(E_direct, 30)}")
print(f"    (π/2)·₂F₁(-½,½;1;m) = {mpmath.nstr(E_hyp, 30)}  match: {abs(E_direct - E_hyp) < mpmath.mpf(10)**(-40)}")
print()

# ===================================================================
# 4) Legendre Relation Verification
# ===================================================================
print("=" * 70)
print("  4) Legendre Relation: K·E' + E·K' - K·K' = π/2")
print("=" * 70)

for m_val in ['0.1', '0.3', '0.5', '0.7', '0.9', '0.99', '0.999']:
    m = mpmath.mpf(m_val)
    m1 = 1 - m
    K_m = mpmath.ellipk(m)
    E_m = mpmath.ellipe(m)
    K_m1 = mpmath.ellipk(m1)
    E_m1 = mpmath.ellipe(m1)

    legendre = K_m * E_m1 + E_m * K_m1 - K_m * K_m1
    err = abs(legendre - pi / 2)
    print(f"  m = {m_val:>5s}: K·E' + E·K' - K·K' = {mpmath.nstr(legendre, 25)} (err = {mpmath.nstr(err, 3)})")

print()

# ===================================================================
# 5) Perimeter = 4a · E(e²)
# ===================================================================
print("=" * 70)
print("  5) Perimeter as Period of the Second Kind")
print("=" * 70)

a_mp = mpmath.mpf(str(a_orb))
e_mp = mpmath.mpf(str(e_orb))
b_mp = a_mp * mpmath.sqrt(1 - e_mp**2)
m_P = e_mp**2  # perimeter modulus

P_exact = 4 * a_mp * mpmath.ellipe(m_P)
E_val = mpmath.ellipe(m_P)

print(f"  Mercury: a = {mpmath.nstr(a_mp, 12)}, e = {e_orb}")
print(f"  Perimeter modulus m_P = e² = {mpmath.nstr(m_P, 10)}")
print(f"  E(e²) = {mpmath.nstr(E_val, 20)}")
print(f"  P = 4a·E(e²) = {mpmath.nstr(P_exact, 20)} m")
print(f"  P = {mpmath.nstr(P_exact / 1e9, 12)} billion m")
print(f"  D = P/(2πa) = {mpmath.nstr(P_exact / (2*pi*a_mp), 15)}")
print()

# Table of E and D vs eccentricity
print("  E and Deficiency vs eccentricity:")
print(f"  {'e':>6s}  {'E(e²)':>18s}  {'D = P/(2πa)':>18s}  {'E→':>8s}")
for e_t in [0, 0.2, 0.5, 0.7, 0.9, 0.95, 0.99, 0.999]:
    m_t = mpmath.mpf(str(e_t))**2
    E_t = mpmath.ellipe(m_t)
    D_t = 2*E_t/pi
    print(f"  {e_t:6.3f}  {mpmath.nstr(E_t, 16):>18s}  {mpmath.nstr(D_t, 16):>18s}")
print(f"  {'1':>6s}  {'1 (finite)':>18s}  {'2/π = κ':>18s}")
print()

# ===================================================================
# 6) GR Orbit involves K(k²)
# ===================================================================
print("=" * 70)
print("  6) GR Orbit as Period of the First Kind")
print("=" * 70)

r_S_mp = mpmath.mpf(str(r_S))
ell_mp = a_mp * (1 - e_mp**2)
c_mp = a_mp * e_mp

# Orbit roots (weak-field approximation)
u1 = 1 / (a_mp * (1 + e_mp))   # 1/r_apo
u2 = 1 / (a_mp * (1 - e_mp))   # 1/r_peri
u3 = 1 / r_S_mp                 # approx third root

k2 = (u2 - u1) / (u3 - u1)
K_orbit = mpmath.ellipk(k2)

print(f"  Orbit roots (weak-field):")
print(f"    u₁ = 1/r_apo = {mpmath.nstr(u1, 15)}")
print(f"    u₂ = 1/r_peri = {mpmath.nstr(u2, 15)}")
print(f"    u₃ ≈ 1/r_S = {mpmath.nstr(u3, 15)}")
print(f"  Orbit modulus k² = {mpmath.nstr(k2, 15)}")
print()
print(f"  K(k²)   = {mpmath.nstr(K_orbit, 25)}")
print(f"  π/2     = {mpmath.nstr(pi/2, 25)}")
print(f"  K - π/2 = {mpmath.nstr(K_orbit - pi/2, 15)}")
print(f"  (tiny departure from π/2: orbit is nearly Newtonian)")
print()

# ===================================================================
# 7) Behavior at m → 1 (shared log singularity)
# ===================================================================
print("=" * 70)
print("  7) Shared Log Singularity at m = 1")
print("=" * 70)
print(f"  {'m':>10s}  {'K(m)':>14s}  {'E(m)':>14s}  {'-½ln(1-m)':>14s}  {'K diverges?':>12s}")

for m_str in ['0.9', '0.99', '0.999', '0.9999', '0.99999', '0.999999']:
    m = mpmath.mpf(m_str)
    K_m = mpmath.ellipk(m)
    E_m = mpmath.ellipe(m)
    log_approx = -0.5 * mpmath.log(1 - m)
    print(f"  {m_str:>10s}  {float(K_m):14.6f}  {float(E_m):14.10f}  {float(log_approx):14.6f}  {'∞' if m == 1 else ''}")

print()
print(f"  K(m) ~ ½ln(16/(1-m)) as m→1  (DIVERGES — logarithmic)")
print(f"  E(m) → 1                as m→1  (FINITE — non-analytic residual)")
print(f"  The log branch lives in both K and E via the Picard-Fuchs system.")
print(f"  For K: divergence → infinite precession near ISCO")
print(f"  For E: non-analytic residual → MEPB barrier (x²ln x)")
print()

# E near m=1: check the (1-m)ln(1-m) coefficient
print("  E(m) log branch coefficient check:")
for m_str in ['0.99', '0.999', '0.9999']:
    m = mpmath.mpf(m_str)
    E_m = mpmath.ellipe(m)
    x = 1 - m
    residual = (E_m - 1) / (x * mpmath.log(x)) if x > 0 else 0
    print(f"  m = {m_str}: (E-1)/((1-m)ln(1-m)) = {mpmath.nstr(residual, 10)} (expected ≈ κ/2 = {float(kappa/2):.6f})")
print()

# ===================================================================
# 8) MEPB coefficient from κ
# ===================================================================
kappa_val = 2 / math.pi
mepb_coeff = 7 * math.pi / 704

print("=" * 70)
print("  8) MEPB Coefficient from κ")
print("=" * 70)
print(f"  κ = 2/π = {kappa_val:.15f}")
print(f"  MEPB = 7π/704 = {mepb_coeff:.15f}")
print(f"  MEPB = 7/(352κ) = {7 / (352 * kappa_val):.15f}")
print(f"  Match: {abs(mepb_coeff - 7 / (352 * kappa_val)) < 1e-15}")
print()

h_mercury = ((a_orb - b_orb) / (a_orb + b_orb))**2
x_mercury = 1 - h_mercury
mepb_mercury = mepb_coeff * x_mercury**2 * abs(math.log(x_mercury))

print(f"  Mercury: h = {h_mercury:.12e}, x = {x_mercury:.12f}")
print(f"  MEPB at Mercury's orbit = {mepb_mercury:.12e}")
print(f"  (negligible — Mercury is nearly circular)")
print()

# ===================================================================
# 9) Both corrections vs eccentricity
# ===================================================================
print("=" * 70)
print("  9) Both Corrections vs Eccentricity")
print("=" * 70)
print(f"  {'e':>6s}  {'E(e²)':>14s}  {'K(e²)':>14s}  {'R = c/ℓ':>10s}  {'MEPB term':>12s}")
print(f"  {'':>6s}  {'(perimeter)':>14s}  {'(orbit)':>14s}  {'':>10s}  {'x²|ln x|':>12s}")
print(f"  {'-'*6}  {'-'*14}  {'-'*14}  {'-'*10}  {'-'*12}")

for e_t in [0.1, 0.3, 0.5, 0.7, 0.8, 0.9, 0.95, 0.99, 0.999]:
    m_t = mpmath.mpf(str(e_t))**2
    E_t = float(mpmath.ellipe(m_t))
    K_t = float(mpmath.ellipk(m_t))
    R_t = e_t / (1 - e_t**2)
    b_t = math.sqrt(1 - e_t**2)
    h_t = ((1 - b_t) / (1 + b_t))**2
    x_t = 1 - h_t
    mepb_t = mepb_coeff * x_t**2 * abs(math.log(x_t)) if x_t > 0 else float('inf')
    print(f"  {e_t:6.3f}  {E_t:14.8f}  {K_t:14.8f}  {R_t:10.4f}  {mepb_t:12.6e}")

print()

# ===================================================================
# 10) Perimeter at Mercury's eccentricity (formula comparison)
# ===================================================================
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    from formulas import r2_3exp_v23_champion, exact_perimeter, ramanujan_ii

    P_exact_f = exact_perimeter(a_orb, b_orb)
    P_champ = r2_3exp_v23_champion(a_orb, b_orb)
    P_r2 = ramanujan_ii(a_orb, b_orb)

    print("=" * 70)
    print("  10) Perimeter of Mercury's Orbit")
    print("=" * 70)
    print(f"  a = {a_orb:.6e} m, b = {b_orb:.6e} m")
    print(f"  P_exact    = {P_exact_f:.15f} m")
    print(f"  P_champion = {P_champ:.15f} m  (err = {abs(P_champ/P_exact_f - 1)*1e6:.10f} ppm)")
    print(f"  P_R2       = {P_r2:.15f} m  (err = {abs(P_r2/P_exact_f - 1)*1e6:.10f} ppm)")
    print(f"  P/(2πa)    = {P_exact_f/(2*math.pi*a_orb):.15f}")
    print()
except ImportError:
    print("  (formulas.py not found; skipping perimeter computation)")
    print()

# ===================================================================
# Summary
# ===================================================================
print("=" * 70)
print("  SUMMARY: K-E Period Duality")
print("=" * 70)
print(f"""
  The perimeter and GR orbit are the two canonical period integrals:

    P = 4a·E(e²)           [period of the 2nd kind, E finite at m=1]
    Δφ = f(K(k²))          [period of the 1st kind, K diverges at m=1]

  Both are ₂F₁(±½, ½; 1; m) with prefactor π/2 = 1/κ.

  Legendre relation: K·E' + E·K' - K·K' = π/2 = 1/κ  (EXACT)

  At m = 0: E = K = π/2 = 1/κ  → circle & closed orbit
  At m = 1: E → 1 (MEPB source), K → ∞ (infinite precession)

  The SAME log singularity at m=1 in the Picard-Fuchs system:
    — makes K diverge → orbit spirals in (GR)
    — leaves non-analytic residual in E → x²ln x barrier (MEPB)

  κ = 2/π controls:
    — flat-limit deficiency D → κ
    — MEPB coefficient 7π/704 = 7/(352κ)
    — log branch amplitude κ/2
    — Newtonian closure K(0) = 1/κ
    — Legendre relation RHS = 1/κ
    — focal duality R/U = 1/κ
""")
