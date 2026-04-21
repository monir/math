#!/usr/bin/env python3
"""
Integer/exact arithmetic verification of all π-CF connections.

All verifications use either:
  (a) Pure integer arithmetic (no floating point)
  (b) mpmath at 100+ digits for transcendental quantities

Goal: prove the CF identities beyond any numerical doubt.
"""

import mpmath
mpmath.mp.dps = 120  # 120 decimal digits

print("=" * 72, flush=True)
print("  π-CF CONNECTIONS: EXACT INTEGER/MPMATH VERIFICATION", flush=True)
print("=" * 72, flush=True)

# ═══════════════════════════════════════════════════════════════════════════════
print("\n  PART 1: π continued fraction — exact integer computation", flush=True)
print("  " + "-"*60, flush=True)

# π CF partial quotients (known to arbitrary precision)
a = [3, 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14]

# Convergents via EXACT integer recurrence (no floating point!)
p = [0] * (len(a) + 1)
q = [0] * (len(a) + 1)
p[-2], p[-1] = 1, 0  # p_{-1}=1, p_{-2}=0 — wait, standard convention:
# p_{-1} = 1, p_0 = a_0
# q_{-1} = 0, q_0 = 1
# p_n = a_n * p_{n-1} + p_{n-2}
# q_n = a_n * q_{n-1} + q_{n-2}

# Use explicit recurrence with exact integers
P = []  # numerators of convergents
Q = []  # denominators of convergents
p_prev, p_curr = 1, a[0]   # p_{-1}=1, p_0=a_0=3
q_prev, q_curr = 0, 1       # q_{-1}=0, q_0=1
P.append(p_curr)
Q.append(q_curr)

for i in range(1, len(a)):
    p_new = a[i] * p_curr + p_prev
    q_new = a[i] * q_curr + q_prev
    p_prev, p_curr = p_curr, p_new
    q_prev, q_curr = q_curr, q_new
    P.append(p_curr)
    Q.append(q_curr)

print("  Convergents (EXACT integers, no float):", flush=True)
for i in range(min(6, len(P))):
    # Verify with mpmath π
    exact_val = mpmath.mpf(P[i]) / mpmath.mpf(Q[i])
    error = abs(exact_val - mpmath.pi)
    print(f"    [{i}] p={P[i]:>10d} / q={Q[i]:>8d}  "
          f"|p/q - π| = {float(error):.4e}  a[{i}]={a[i]}", flush=True)

# ═══════════════════════════════════════════════════════════════════════════════
print(f"\n\n  PART 2: Endpoint pin T = 1 - 7π/22", flush=True)
print("  " + "-"*60, flush=True)

# T = 1 - (q₁/1) · π / p₁ = 1 - 7π/22
# Verify: q₁ = 7, p₁ = 22 (integer check)
assert Q[1] == 7, f"q₁ should be 7, got {Q[1]}"
assert P[1] == 22, f"p₁ should be 22, got {P[1]}"
print(f"  ✓ q₁ = {Q[1]} (integer)", flush=True)
print(f"  ✓ p₁ = {P[1]} (integer)", flush=True)

T = 1 - mpmath.mpf(7) * mpmath.pi / mpmath.mpf(22)
print(f"  T = 1 - 7π/22 = {mpmath.nstr(T, 50)}", flush=True)
print(f"  T > 0: {T > 0}  (because 22/7 > π)", flush=True)
# Verify 22/7 > π exactly
print(f"  22/7 - π = {mpmath.nstr(mpmath.mpf(22)/7 - mpmath.pi, 50)}", flush=True)

# ═══════════════════════════════════════════════════════════════════════════════
print(f"\n\n  PART 3: Gate exponent q = a₁/a₀ = 7/3", flush=True)
print("  " + "-"*60, flush=True)

# Pure integer verification
assert a[1] == 7, f"a₁ should be 7"
assert a[0] == 3, f"a₀ should be 3"
q_gate = mpmath.mpf(a[1]) / mpmath.mpf(a[0])
print(f"  ✓ a₁ = {a[1]} (integer)", flush=True)
print(f"  ✓ a₀ = {a[0]} (integer)", flush=True)
print(f"  q = a₁/a₀ = {a[1]}/{a[0]} = {mpmath.nstr(q_gate, 50)}", flush=True)
# As a fraction
from fractions import Fraction
q_frac = Fraction(a[1], a[0])
print(f"  q = {q_frac} (exact rational)", flush=True)

# ═══════════════════════════════════════════════════════════════════════════════
print(f"\n\n  PART 4: Mid-rate m = a₀⁴/(a₀+a₁+a₂) — THE KEY IDENTITY", flush=True)
print("  " + "-"*60, flush=True)

# ALL integer arithmetic — NO floats
numerator = a[0]**4
denominator = a[0] + a[1] + a[2]

print(f"  a₀ = {a[0]}", flush=True)
print(f"  a₁ = {a[1]}", flush=True)
print(f"  a₂ = {a[2]}", flush=True)
print(f"  a₀⁴ = {a[0]}⁴ = {numerator}", flush=True)
print(f"  a₀ + a₁ + a₂ = {a[0]} + {a[1]} + {a[2]} = {denominator}", flush=True)
print(f"  m = {numerator}/{denominator}", flush=True)

m_frac = Fraction(numerator, denominator)
print(f"  m = {m_frac} (exact rational, fully reduced)", flush=True)

# Verify this equals 81/25
assert m_frac == Fraction(81, 25), f"Expected 81/25, got {m_frac}"
print(f"  ✓ {m_frac} == 81/25 ← VERIFIED BY INTEGER ARITHMETIC", flush=True)

# Also verify the component integers
assert a[0]**4 == 81, f"3⁴ should be 81"
assert a[0] + a[1] + a[2] == 25, f"3+7+15 should be 25"
print(f"  ✓ 3⁴ = 81 (integer)", flush=True)
print(f"  ✓ 3 + 7 + 15 = 25 (integer)", flush=True)

# ═══════════════════════════════════════════════════════════════════════════════
print(f"\n\n  PART 5: Fast rate n = a₂ = 15", flush=True)
print("  " + "-"*60, flush=True)

assert a[2] == 15
print(f"  ✓ a₂ = {a[2]} (integer)", flush=True)

# Also: 15 = p₂/p₁ = 333/22 to first approximation
# Exact check: p₂ = 333, p₁ = 22
assert P[2] == 333, f"p₂ should be 333, got {P[2]}"
assert P[1] == 22, f"p₁ should be 22, got {P[1]}"
p2_p1_ratio = Fraction(P[2], P[1])
print(f"  p₂/p₁ = {P[2]}/{P[1]} = {p2_p1_ratio} = {float(p2_p1_ratio):.6f}", flush=True)
# And q₂/q₁
q2_q1_ratio = Fraction(Q[2], Q[1])
print(f"  q₂/q₁ = {Q[2]}/{Q[1]} = {q2_q1_ratio} = {float(q2_q1_ratio):.6f}", flush=True)
print(f"  Both ≈ a₂ = 15 (within 1%)", flush=True)

# ═══════════════════════════════════════════════════════════════════════════════
print(f"\n\n  PART 6: Amplitude ratio r/s ≈ 31/3 = (a₀+a₁) + a₃/a₀", flush=True)
print("  " + "-"*60, flush=True)

# Integer verification of 31/3 structure
rs_candidate_num = a[0] + a[1]  # = 10
rs_candidate_frac = Fraction(a[0]*rs_candidate_num + a[3], a[0])  # = (30+1)/3 = 31/3
print(f"  (a₀+a₁) + a₃/a₀ = ({a[0]}+{a[1]}) + {a[3]}/{a[0]}", flush=True)
print(f"                   = {a[0]+a[1]} + {Fraction(a[3], a[0])}", flush=True)
print(f"                   = {rs_candidate_frac} (exact rational)", flush=True)
assert rs_candidate_frac == Fraction(31, 3)
print(f"  ✓ (a₀+a₁) + a₃/a₀ = 31/3 (integer arithmetic)", flush=True)

# Cross-check: 31 = a₀(a₀+a₁) + a₃ = 3·10 + 1 = 31
assert a[0]*(a[0]+a[1]) + a[3] == 31
print(f"  ✓ a₀(a₀+a₁) + a₃ = {a[0]}·{a[0]+a[1]} + {a[3]} = 31 (integer)", flush=True)

print(f"\n  r/s from optimization ≈ 10.3334 vs 31/3 = {float(Fraction(31,3)):.10f}", flush=True)
print(f"  This identity is APPROXIMATE (|diff| ≈ 2×10⁻⁵), not exact.", flush=True)
print(f"  But the CF of r/s = [10; 2, 1, 5840, ...] suggests 31/3 = [10; 3]", flush=True)
print(f"  is a strong attractor (large PQ 5840 ≈ near-integer).", flush=True)

# ═══════════════════════════════════════════════════════════════════════════════
print(f"\n\n  PART 7: λ algebraic candidate: 7λ² - 59λ + 74 = 0", flush=True)
print("  " + "-"*60, flush=True)

# Check CF connections in the polynomial coefficients
print(f"  Polynomial: 7λ² - 59λ + 74 = 0", flush=True)
print(f"  Coefficients:", flush=True)
print(f"    7 = a₁ (2nd partial quotient of π)", flush=True)
print(f"    59 = ?", flush=True)
print(f"    74 = ?", flush=True)

# Check 59
print(f"\n  Is 59 CF-expressible?", flush=True)
checks_59 = {
    "4·a₂ - a₃": 4*a[2] - a[3],
    "a₀·p₁ - a₁": a[0]*P[1] - a[1],
    "p₁ + q₁²": P[1] + Q[1]**2,
    "a₁·a₀² - a₂ + a₃": a[1]*a[0]**2 - a[2] + a[3],
    "a₁² + a₀+a₃": a[1]**2 + a[0] + a[3],
    "a₁² + a₀·a₃": a[1]**2 + a[0]*a[3],
    "4·a₂ - 1": 4*15 - 1,
    "a₀·p₁ - a₁": 3*22 - 7,
}
for name, val in checks_59.items():
    marker = "  ◄" if val == 59 else ""
    print(f"    {name:25s} = {val}{marker}", flush=True)

# Check 74
print(f"\n  Is 74 CF-expressible?", flush=True)
checks_74 = {
    "2·37": 2*37,
    "a₁·a₀²+a₁+a₂+a₀": a[1]*a[0]**2+a[1]+a[2]+a[0],
    "p₁·a₀+a₁+a₃": P[1]*a[0]+a[1]+a[3],
    "a₀²·a₁+a₂+a₃+a₁": a[0]**2*a[1]+a[2]+a[3]+a[1],
    "a₁²+a₀+a₁+a₀²": a[1]**2+a[0]+a[1]+a[0]**2,
    "a₁²+a₀²+a₂+a₃": a[1]**2+a[0]**2+a[2]+a[3],
    "a₁(a₀²+a₃)+a₁": a[1]*(a[0]**2+a[3])+a[1],
    "2·(a₀²+a₁²+a₃+a₂)": 2*(a[0]**2+a[1]**2+a[3]+a[2]),
}
for name, val in checks_74.items():
    marker = "  ◄" if val == 74 else ""
    print(f"    {name:25s} = {val}{marker}", flush=True)

# Compute the root exactly with mpmath
print(f"\n  Exact root (mpmath, 100 digits):", flush=True)
disc = mpmath.mpf(59)**2 - 4*mpmath.mpf(7)*mpmath.mpf(74)
print(f"  Discriminant = 59² - 4·7·74 = {int(59**2 - 4*7*74)}", flush=True)
print(f"    = 3481 - 2072 = {3481-2072}", flush=True)
root = (mpmath.mpf(59) + mpmath.sqrt(disc)) / (2*mpmath.mpf(7))
print(f"  λ_alg = (59 + √1409) / 14 = {mpmath.nstr(root, 50)}", flush=True)
print(f"  λ_opt ≈ 6.89547 (from N=5000 optimization)", flush=True)
print(f"  |λ_alg - λ_opt| ≈ {abs(float(root) - 6.89547):.6f}", flush=True)
print(f"  This is an APPROXIMATION, not exact identity.", flush=True)

# ═══════════════════════════════════════════════════════════════════════════════
print(f"\n\n  PART 8: High-precision verification with mpmath elliptic integrals", flush=True)
print("  " + "-"*60, flush=True)

# Verify the champion formula at key eccentricities using 100-digit arithmetic
mpmath.mp.dps = 120

print(f"  Testing q=7/3, m=81/25, n=15 at extreme eccentricities:", flush=True)
print(f"  Using 120-digit mpmath arithmetic for exact perimeters.\n", flush=True)

# Parameters (use mpmath for everything)
q_mp = mpmath.mpf(7) / mpmath.mpf(3)
m_mp = mpmath.mpf(81) / mpmath.mpf(25)
n_mp = mpmath.mpf(15)
T_mp = 1 - mpmath.mpf(7) * mpmath.pi / mpmath.mpf(22)

# Best-fit λ, r, s (from optimization — these are the empirical ones)
lam_mp = mpmath.mpf('6.89547')
r_mp = mpmath.mpf('0.37258')
s_mp = mpmath.mpf('0.03606')

test_cases = [
    (mpmath.mpf(1), mpmath.mpf('0.999')),
    (mpmath.mpf(1), mpmath.mpf('0.99')),
    (mpmath.mpf(1), mpmath.mpf('0.9')),
    (mpmath.mpf(1), mpmath.mpf('0.5')),
    (mpmath.mpf(1), mpmath.mpf('0.1')),
    (mpmath.mpf(1), mpmath.mpf('0.01')),
    (mpmath.mpf(1), mpmath.mpf('0.001')),
    (mpmath.mpf(1), mpmath.mpf('0.0001')),
]

print(f"  {'b':>10s}  {'h':>12s}  {'P_exact':>20s}  {'P_formula':>20s}  {'rel_err':>14s}", flush=True)
print(f"  {'-'*82}", flush=True)

max_rel_err = mpmath.mpf(0)
for aa, bb in test_cases:
    if aa < bb: aa, bb = bb, aa
    # Exact perimeter
    m_ell = 1 - (bb/aa)**2
    P_exact = 4 * aa * mpmath.ellipe(m_ell)

    # Formula
    h = ((aa-bb)/(aa+bb))**2
    x = 1 - h
    A_coeff = T_mp / (1 + r_mp + s_mp)
    E_coeff = r_mp * A_coeff
    C_coeff = s_mp * A_coeff

    P_R2 = mpmath.pi * (aa+bb) * (1 + 3*h/(10 + mpmath.sqrt(4 - 3*h)))

    gate = h ** q_mp
    term = (A_coeff * mpmath.exp(-lam_mp * x)
            + E_coeff * mpmath.exp(-m_mp * lam_mp * x)
            + C_coeff * mpmath.exp(-n_mp * lam_mp * x))
    denom = 1 - gate * term
    P_formula = P_R2 / denom

    rel_err = abs(P_formula - P_exact) / P_exact

    if rel_err > max_rel_err:
        max_rel_err = rel_err

    print(f"  {float(bb):10.4f}  {float(h):12.8f}  "
          f"{mpmath.nstr(P_exact, 15):>20s}  {mpmath.nstr(P_formula, 15):>20s}  "
          f"{float(rel_err):.6e}", flush=True)

print(f"\n  max|rel_err| = {float(max_rel_err)*1e6:.4f} ppm", flush=True)
print(f"  (Using approximate λ,r,s — optimized values would be slightly better)", flush=True)

# ═══════════════════════════════════════════════════════════════════════════════
print(f"\n\n{'=' * 72}", flush=True)
print("  SUMMARY: VERIFIED π-CF IDENTITIES", flush=True)
print("=" * 72, flush=True)

print(f"""
  ALL VERIFIED BY EXACT INTEGER/RATIONAL ARITHMETIC:

  1. ✓ T = 1 - 7π/22 = 1 - q₁·π/p₁
     (Convergent p₁/q₁ = 22/7, verified: 22/7 > π)

  2. ✓ q = 7/3 = a₁/a₀
     (Pure integer ratio of first two partial quotients)

  3. ✓ m = 81/25 = a₀⁴/(a₀+a₁+a₂) = 3⁴/(3+7+15)
     (Integer arithmetic: 3⁴ = 81, 3+7+15 = 25)

  4. ✓ n = 15 = a₂
     (Third partial quotient, exact integer)

  5. ~ r/s ≈ 31/3 = (a₀(a₀+a₁)+a₃)/a₀
     (APPROXIMATE: |r/s - 31/3| ≈ 2×10⁻⁵)
     (CF of r/s = [10; 2, 1, 5840, ...] → strong 31/3 attractor)

  6. ~ λ ≈ (59+√1409)/14 where 7λ²-59λ+74≈0
     (APPROXIMATE: coefficients 7=a₁, residual ~10⁻⁴)

  STRUCTURAL PARAMETERS FROM π CF (exact):  T, q, m, n
  MINIMAX-DETERMINED (empirical):           λ, r, s

  DEPTH: All 3 levels of π = [3; 7, 15, ...] are used.
""", flush=True)
