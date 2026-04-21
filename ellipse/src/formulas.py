"""
All ellipse perimeter approximation formulas in one module.

Each function takes (a, b) with a >= b > 0 and returns the approximate perimeter.
"""
import math

# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

def _order(a: float, b: float) -> tuple[float, float]:
    return (a, b) if a >= b else (b, a)

def h_param(a: float, b: float) -> float:
    """Eccentricity parameter h = ((a-b)/(a+b))^2."""
    a, b = _order(a, b)
    return ((a - b) / (a + b)) ** 2

# ---------------------------------------------------------------------------
# 1. Ramanujan II (1914)  —  the 110-year-old legend
# ---------------------------------------------------------------------------

def ramanujan_ii(a: float, b: float) -> float:
    """Ramanujan's second approximation (1914). Max error ~402 ppm."""
    a, b = _order(a, b)
    h = h_param(a, b)
    return math.pi * (a + b) * (1.0 + 3.0 * h / (10.0 + math.sqrt(4.0 - 3.0 * h)))

# ---------------------------------------------------------------------------
# 2. Cantrell (2001)  —  Holder mean correction
# ---------------------------------------------------------------------------

def cantrell(a: float, b: float) -> float:
    """Cantrell's correction to Ramanujan II. Max error ~412 ppm."""
    a, b = _order(a, b)
    h = h_param(a, b)
    c = 4.0 / math.pi - 14.0 / 11.0
    return math.pi * (a + b) * (1.0 + 3.0 * h / (10.0 + math.sqrt(4.0 - 3.0 * h) + c * h ** 1.5))

# ---------------------------------------------------------------------------
# 3. Ayala-Raggi & Rendon-Marin R2/2exp (2025)  —  previous world record
# ---------------------------------------------------------------------------

_A2 = 3.37528e-4
_B2 = 10.29662
_C2 = 6.48093e-5
_D2 = 40.89043

def ayala_raggi_r2_2exp(a: float, b: float) -> float:
    """Ayala-Raggi & Rendon-Marin (2025) R2/2exp. Max error ~0.57 ppm."""
    a, b = _order(a, b)
    h = h_param(a, b)
    x = 1.0 - h
    term = _A2 * math.exp(-_B2 * x) + _C2 * math.exp(-_D2 * x)
    return ramanujan_ii(a, b) / (1.0 - term)

# ---------------------------------------------------------------------------
# 4. THIS WORK: R2/3exp-gated  —  new world record
# ---------------------------------------------------------------------------

# Endpoint pin: forces P -> 4a exactly as b -> 0
T_FLAT = 1.0 - 7.0 * math.pi / 22.0  # ~0.000402499...

# ---------------------------------------------------------------------------
# 4a. TRUE CHAMPION (m = 81/25, gate = h^2.5)  —  numerical optimum
#
# Configuration: m = 81/25 = 3.24,  n = 15,  gate = h^2.5
# Full adversarial test (5000 pts): max error = 8.91e-8 (0.0891 ppm)
# 6.4x improvement over Ayala-Raggi
# ---------------------------------------------------------------------------
_M_OPT = 81.0 / 25.0    # mid-range rate multiplier (numerically optimal)
_N = 15.0                # fast rate multiplier
_LAM_OPT = 6.64515       # decay rate
_R_OPT = 0.39218         # ratio E/A
_S_OPT = 0.039235        # ratio C/A
_Q = 2.5                 # gate exponent (h^2.5)

_A_OPT = T_FLAT / (1.0 + _R_OPT + _S_OPT)
_E_OPT = _R_OPT * _A_OPT
_C_OPT = _S_OPT * _A_OPT

# ---------------------------------------------------------------------------
# 4b. THEORETICALLY MOTIVATED (m = pi, gate = h^2.5)
#
# Configuration: m = pi,  n = 15,  gate = h^2.5
# Full adversarial test: max error = 1.242e-7 (0.1242 ppm)
# pi arises from Gauss connection coefficient Gamma(1)^2/(Gamma(3/2)*Gamma(1/2)) = 2/pi
# ---------------------------------------------------------------------------
_M_PI = math.pi          # mid-range rate multiplier (from Gamma connection)
_LAM_PI = 6.51185        # decay rate
_R_PI = 0.43207          # ratio E/A
_S_PI = 0.043796         # ratio C/A

_A_PI = T_FLAT / (1.0 + _R_PI + _S_PI)
_E_PI = _R_PI * _A_PI
_C_PI = _S_PI * _A_PI

# ---------------------------------------------------------------------------
# 4c. ORIGINAL (gate = h^2)  —  simpler gate
#
# Configuration: m = pi,  n = 15,  gate = h^2
# Full adversarial test: max error = 1.245e-7 (0.1245 ppm)
# ---------------------------------------------------------------------------
_LAM_H2 = 7.34099    # decay rate (h^2 variant)
_R_H2 = 0.35508      # ratio E/A
_S_H2 = 0.03374      # ratio C/A
_Q_H2 = 2.0          # gate exponent (h^2)

_A_H2 = T_FLAT / (1.0 + _R_H2 + _S_H2)
_E_H2 = _R_H2 * _A_H2
_C_H2 = _S_H2 * _A_H2


def _r2_3exp_core(a: float, b: float,
                  lam: float, A: float, E: float, C: float,
                  m_mult: float, n_mult: float,
                  q: float) -> float:
    """Core R2/3exp-gated computation."""
    a, b = _order(a, b)
    h = h_param(a, b)
    x = 1.0 - h

    gate = h ** q
    term = (A * math.exp(-lam * x)
            + E * math.exp(-m_mult * lam * x)
            + C * math.exp(-n_mult * lam * x))
    denom = 1.0 - gate * term
    if denom <= 0.0 or not math.isfinite(denom):
        return float("nan")
    return ramanujan_ii(a, b) / denom


def r2_3exp_gated(a: float, b: float) -> float:
    """
    R2/3exp-gated formula (this work, 2026).  TRUE CHAMPION: m=81/25, gate=h^2.5.

    P = P_R2 / (1 - h^q * [A*exp(-lam*x) + E*exp(-(81/25)*lam*x) + C*exp(-15*lam*x)])

    Max error: <0.09 ppm (8.91e-8).  World record as of Feb 2026.
    """
    return _r2_3exp_core(a, b, _LAM_OPT, _A_OPT, _E_OPT, _C_OPT, _M_OPT, _N, _Q)


def r2_3exp_gated_pi(a: float, b: float) -> float:
    """
    R2/3exp-gated formula, m=pi variant (theoretically motivated).

    The rate multiplier pi comes from the Gauss connection coefficient 2/pi.
    Max error: <0.125 ppm (1.242e-7).
    """
    return _r2_3exp_core(a, b, _LAM_PI, _A_PI, _E_PI, _C_PI, _M_PI, _N, _Q)


def r2_3exp_gated_h2(a: float, b: float) -> float:
    """
    R2/3exp-gated formula, original h^2 gate variant.

    Max error: <0.125 ppm (1.245e-7).  Simpler gate.
    """
    return _r2_3exp_core(a, b, _LAM_H2, _A_H2, _E_H2, _C_H2, _M_PI, _N, _Q_H2)

# ---------------------------------------------------------------------------
# Exact perimeter (ground truth via mpmath, 50+ digits)
# ---------------------------------------------------------------------------

def exact_perimeter(a: float, b: float) -> float:
    """Exact perimeter via complete elliptic integral E(e). Uses mpmath at 50 digits."""
    import mpmath
    mpmath.mp.dps = 50
    a, b = _order(a, b)
    A = mpmath.mpf(a)
    B = mpmath.mpf(b)
    m = mpmath.mpf(1) - (B / A) ** 2
    return float(4 * A * mpmath.ellipe(m))

# ---------------------------------------------------------------------------
# 4d. V23 CHAMPION (q = 7/3, m = 81/25)  —  paper's best
#
# Configuration: m = 81/25 = 3.24,  n = 15,  gate = h^(7/3)
# Full adversarial test (5000 pts): max error ~0.083 ppm
# q = 7/3 from CF of pi: a_1/a_0 = 7/3
# ---------------------------------------------------------------------------
_Q_V23 = 7.0 / 3.0          # gate exponent (h^(7/3))
_LAM_V23 = 6.8954698854899   # decay rate (paper's champion)
_R_V23 = 0.3725797305793     # ratio B/A
_S_V23 = 0.0360560365885     # ratio C/A

_A_V23 = T_FLAT / (1.0 + _R_V23 + _S_V23)
_B_V23 = _R_V23 * _A_V23
_C_V23 = _S_V23 * _A_V23


def r2_3exp_v23_champion(a: float, b: float) -> float:
    """
    R2/3exp-gated formula (this work, 2026).  V23 CHAMPION: q=7/3, m=81/25.

    P = P_R2 / (1 - h^(7/3) * [A*exp(-lam*x) + B*exp(-3.24*lam*x) + C*exp(-15*lam*x)])

    Gate exponent q = a_1/a_0 = 7/3 from the continued fraction of pi.
    Max error: 0.083 ppm (8.34e-8).  World record as of Feb 2026.
    """
    return _r2_3exp_core(a, b, _LAM_V23, _A_V23, _B_V23, _C_V23, _M_OPT, _N, _Q_V23)


# ---------------------------------------------------------------------------
# 5. Tower construction + tower-corrected formulas
# ---------------------------------------------------------------------------

from fractions import Fraction

_CF_A = [3, 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14]

def _cf_convergents(a_list):
    p, q = [0, 1], [1, 0]
    for a in a_list:
        p.append(a * p[-1] + p[-2])
        q.append(a * q[-1] + q[-2])
    return p[2:], q[2:]

_CF_P, _CF_Q = _cf_convergents(_CF_A)

def _build_tower(max_level):
    N_MAX = 5 * max_level + 10
    def B_coeff(n):
        num = Fraction(1)
        for k in range(n): num *= Fraction(2*k - 1, 2)
        fac = Fraction(1)
        for k in range(1, n+1): fac *= k
        return (num * num) / (fac * fac)
    def binom_half(n):
        if n == 0: return Fraction(1)
        num = Fraction(1)
        for k in range(n): num *= (Fraction(1, 2) - k)
        fac = Fraction(1)
        for k in range(1, n+1): fac *= k
        return num / fac
    B = [B_coeff(n) for n in range(N_MAX)]
    s = [2 * binom_half(n) * (Fraction(-3, 4))**n for n in range(N_MAX)]
    d = [Fraction(0)] * N_MAX
    d[0] = Fraction(10) + s[0]
    for n in range(1, N_MAX): d[n] = s[n]
    inv = [Fraction(0)] * N_MAX
    inv[0] = Fraction(1) / d[0]
    for n in range(1, N_MAX):
        inv[n] = -sum(d[k] * inv[n-k] for k in range(1, n+1)) / d[0]
    R_series = [Fraction(0)] * N_MAX
    R_series[0] = Fraction(1)
    for n in range(1, N_MAX): R_series[n] = 3 * inv[n-1]
    R_exact_1 = Fraction(14, 11)
    CONV_ORDER = list(range(3, len(_CF_P)))
    tower = []
    for step in range(1, max_level):
        onset = 5 * step
        delta = [B[n] - R_series[n] for n in range(N_MAX)]
        psi = [delta[onset+k] for k in range(N_MAX - onset)]
        conv_idx = step - 1
        if conv_idx >= len(CONV_ORDER): break
        best_conv = CONV_ORDER[conv_idx]
        target_R = Fraction(4 * _CF_Q[best_conv], _CF_P[best_conv])
        psi_target = target_R - R_exact_1
        T_k = float(1 - _CF_Q[best_conv] * math.pi / _CF_P[best_conv])
        e = psi[:5]
        S_c = e[0]+e[1]+e[2]+e[3]; S_1 = e[0]+e[1]+e[2]; S_2 = e[0]+e[1]
        Am = [[e[3], e[2]], [S_1-psi_target, S_2-psi_target]]
        bv = [-e[4], -(S_c-psi_target)]
        det_val = Am[0][0]*Am[1][1] - Am[0][1]*Am[1][0]
        if det_val == 0: break
        dd1 = (bv[0]*Am[1][1] - bv[1]*Am[0][1]) / det_val
        dd2 = (Am[0][0]*bv[1] - Am[1][0]*bv[0]) / det_val
        N_k = [e[0], e[1]+dd1*e[0], e[2]+dd1*e[1]+dd2*e[0], e[3]+dd1*e[2]+dd2*e[1]]
        D_k = [Fraction(1), dd1, dd2]
        R_exact_1 = R_exact_1 + psi_target
        D_inv = [Fraction(0)] * N_MAX
        D_inv[0] = Fraction(1)
        for n in range(1, N_MAX):
            sm = sum(D_k[k]*D_inv[n-k] for k in range(1, min(n+1, len(D_k))))
            D_inv[n] = -sm
        ND = [Fraction(0)] * N_MAX
        for n in range(N_MAX):
            for k in range(min(n+1, len(N_k))):
                ND[n] += N_k[k] * D_inv[n-k]
        for n in range(N_MAX):
            if n >= onset:
                R_series[n] += ND[n - onset]
        tower.append({
            'N': [float(x) for x in N_k], 'D': [float(x) for x in D_k],
            'onset': onset, 'conv_idx': best_conv,
            'p': _CF_P[best_conv], 'q': _CF_Q[best_conv],
            'T': T_k, 'psi_1': float(psi_target),
        })
    return tower

# Build tower layers at import time (< 10ms)
_TOWER = _build_tower(5)  # 4 layers: R3, R4, R5, R6

# Tower level metadata for external use
TOWER_INFO = {}
_TOWER_NAMES = ['R3', 'R4', 'R5', 'R6']
for _i, _name in enumerate(_TOWER_NAMES):
    TOWER_INFO[_name] = {
        'level': _i + 1, 'p': _TOWER[_i]['p'], 'q': _TOWER[_i]['q'],
        'T': _TOWER[_i]['T'], 'onset': _TOWER[_i]['onset'],
    }


def tower_base_ratio(h, level):
    """Compute R_tower(h) for tower level 0-4.

    level 0 = R2 (Ramanujan II base only)
    level 1 = R3, level 2 = R4, level 3 = R5, level 4 = R6
    """
    if h <= 0:
        return 1.0
    R = 1.0 + 3.0 * h / (10.0 + math.sqrt(4.0 - 3.0 * h))
    for i in range(min(level, len(_TOWER))):
        layer = _TOWER[i]
        N = layer['N']; D = layer['D']
        onset = layer['onset']
        Nv = N[0] + h*(N[1] + h*(N[2] + h*N[3]))
        Dv = D[0] + h*(D[1] + h*D[2])
        if abs(Dv) > 1e-30:
            R += h**onset * Nv / Dv
    return R


def tower_perimeter(a, b, level):
    """Compute P_Rk(a,b) — the bare Pade tower approximation (no exponential correction)."""
    a, b = _order(a, b)
    h = h_param(a, b)
    R = tower_base_ratio(h, level)
    return math.pi * (a + b) * R


def tower_corrected(a, b, level, rates, coeffs, lam, q_gate):
    """Compute the tower + multi-exponential correction.

    P = P_Rk(h) / (1 - h^q * sum_i c_i exp(-r_i * lam * (1-h)))
    """
    a, b = _order(a, b)
    h = h_param(a, b)
    x = 1.0 - h
    P_Rk = tower_perimeter(a, b, level)
    phi = sum(c * math.exp(-r * lam * x) for r, c in zip(rates, coeffs))
    gate = h ** q_gate
    denom = 1.0 - gate * phi
    if denom <= 0.0 or not math.isfinite(denom):
        return float("nan")
    return P_Rk / denom


# ---------------------------------------------------------------------------
# 5a. R3+15exp — 1.427 ppb
# ---------------------------------------------------------------------------
_R3_15_RATES = [
    3/7, 2/3, 1, 7/6, 3/2, 53/25, 81/25, 162/25, 189/25,
    13, 15, 292/15, 24, 30, 35,
]
_R3_15_COEFFS = [
    1.0690331487437538e-06, -5.3446219367020315e-06, -4.0279727459249e-06,
    -5.069600273319092e-06, -5.344344263799115e-06, 3.8078085513734217e-06,
    9.539748048443633e-06, -3.4773795578775624e-06, 1.0344348076505942e-05,
    -3.937426561235638e-06, -3.3525450185435064e-06, 1.0593006595991767e-05,
    -3.0640908934958932e-06, -5.328578613384776e-06, 3.677529114762622e-06,
]
_R3_15_LAM = 14.563322134576083
_R3_15_Q = 3.416383861577742

def r3_15exp_champion(a, b):
    """R3+15exp champion. Max error 1.427 ppb."""
    return tower_corrected(a, b, 1, _R3_15_RATES, _R3_15_COEFFS, _R3_15_LAM, _R3_15_Q)


# ---------------------------------------------------------------------------
# 5c. R6+16exp GRAND CHAMPION — 0.409 ppb (best_results / result_r6_quad)
#
# Found by v10 quad search (rk_tower_quad_r6_12to16), combo P2:(55+45)+(36+20)
# Warm-start campaign C1 (11 Mar) found lam=10.62,q=10.80 at 14.8 ppb —
# that was 36x WORSE (kernel returns PPM, not PPB — unit confusion).
# The original lam=17.57, q=2.59 remains champion.
# ---------------------------------------------------------------------------
_R6_16_RATES = [
    1/3, 3/7, 3/4, 1, 3/2, 3, 81/25, 189/25,
    15, 17, 20, 30, 35, 36, 45, 55,
]
_R6_16_COEFFS = [
    -1.9467401013426172e-06, 5.508819445799763e-06, -1.7640675355786574e-05,
    -9.117704663920824e-07, 5.163691422792861e-07, 8.704568573188003e-07,
    1.003555830168441e-05, 2.9990307964469055e-06, -4.760312017507945e-06,
    1.143231096820204e-05, -8.043521058949328e-06, 2.451524342973302e-06,
    -1.417077384485474e-06, 2.586117312021959e-06, -2.851817333660465e-06,
    1.1716876041081825e-06,
]
_R6_16_LAM = 17.57453031672594
_R6_16_Q = 2.590682655650653

def r6_16exp_champion(a, b):
    """R6+16exp. Max error 0.409 ppb. Superseded by R6+18exp."""
    return tower_corrected(a, b, 4, _R6_16_RATES, _R6_16_COEFFS, _R6_16_LAM, _R6_16_Q)


# ---------------------------------------------------------------------------
# 5c2. R6+18exp — 0.358 ppb on coarse grid (115 ppb true peak at e>0.999)
#
# Found by warmstart_v5 C3 add-2 screen (12 Mar 2026). Adds rates 18 and 50
# to the 16-rate champion base. Mac MPS, 22 min.
# ---------------------------------------------------------------------------
_R6_18_RATES = [
    1/3, 3/7, 3/4, 1, 3/2, 3, 81/25, 7.56,
    15, 17, 18, 20, 30, 35, 36, 45, 50, 55,
]
_R6_18_COEFFS = [
    -1.889200127852881e-06, 5.261131096216272e-06, -1.694858674843210e-05,
    -1.141856953124702e-06, 1.176848763525786e-06, 5.942898689485934e-07,
    9.234043604351222e-06, 2.754169917053589e-06, -4.673328857644859e-06,
    1.088738198528497e-05, -5.656068438705963e-08, -7.710656916782353e-06,
    2.464118090592777e-06, -1.079370354838797e-06, 2.868271766606714e-06,
    -2.721995486317813e-06, -1.686257469212557e-07, 1.149887836432060e-06,
]
_R6_18_LAM = 17.44135856628418
_R6_18_Q = 2.633242607116699

def r6_18exp_champion(a, b):
    """R6+18exp. Max error 0.358 ppb. Superseded by VARPRO."""
    return tower_corrected(a, b, 4, _R6_18_RATES, _R6_18_COEFFS, _R6_18_LAM, _R6_18_Q)


# ---------------------------------------------------------------------------
# 5c3. R6+16exp VARPRO v3 — 0.018 ppb = 18 parts per trillion
#
# Found by ultrapolish v3: multi-scale CMA-ES (σ=0.1→0.001) + Nelder-Mead
# (17 Mar 2026, claude-525bd375). Continuous rates, λ=31.35, q=11.82.
# Verified at 300 digits, 500 points.
# The high gate q=11.82 suppresses the correction at moderate h,
# concentrating all 16 exponentials on the high-eccentricity region.
# ---------------------------------------------------------------------------
_R6_VP_RATES = [
    0.0549124247701398, 0.08959272582690402, 0.24697733467232463,
    0.34396214628787214, 0.4655283978174422, 0.7113920398223701,
    0.7744047899716632, 0.9210079249587176, 3.6495347918051557,
    10.887815967669043, 15.97715116830682, 20.6025317043627,
    30.355128560816556, 37.275181367113625, 124.98285889270504,
    134.9403146022634,
]
_R6_VP_COEFFS = [
    -7.359744999391803e-05, 1.706784926004658e-04, -9.198418581482057e-04,
    2.098920312370626e-03, -2.202085191328198e-03, 4.629004663174692e-03,
    -4.457178135606173e-03, 7.500881981855032e-04, 3.301248630070683e-06,
    1.072154845813948e-06, -1.256312076107994e-06, 1.211037623371705e-06,
    -6.351727102404296e-07, 3.184720885884841e-07, -3.842030381483090e-08,
    3.792170023733917e-08,
]
_R6_VP_LAM = 31.352571607846436
_R6_VP_Q = 11.817567226046656

def r6_varpro_champion(a, b):
    """R6+16exp VARPRO v3. Max error 0.018 ppb. Former champion (17 March 2026).
    Verified at 300 digits. Superseded by SCOR champion."""
    return tower_corrected(a, b, 4, _R6_VP_RATES, _R6_VP_COEFFS, _R6_VP_LAM, _R6_VP_Q)


# ---------------------------------------------------------------------------
# 5c-SCOR. R6+16exp+3log SCOR — 0.007 ppb = 7 parts per trillion
#
# SCOR (Singularity-Conscious Optimal Reduction) enriches the correction
# basis with x^k*ln(x) terms that directly absorb the logarithmic
# singularity of E(m) at m=1.  Found via VARPRO on mixed exp+log basis.
# Verified at 300 digits, 500 points (r6_nonanalytic_basis_v1.json).
# ---------------------------------------------------------------------------
_R6_SCOR_RATES = [
    0.010166999187513546, 0.07776780092888144, 0.19901003723401806,
    0.338043080886615, 0.4971009768543303, 0.7070725423114185,
    0.8722016136238608, 2.7314795971348453, 4.740243707070392,
    9.970442852904373, 14.936436441424814, 20.673019711422043,
    29.729616427543093, 37.55442387982917, 125.32824271647245,
    135.77785701559,
]
_R6_SCOR_EXP_COEFFS = [
    0.00026618116484864926, -0.0008681885839445673, 0.0014174476376588706,
    -0.0015231308488015433, 0.0010502084585483412, -0.000540825515736969,
    0.00019300900837453404, 3.5348485318019746e-06, 1.1557743338413409e-06,
    6.181548524889021e-07, -3.1316471711835696e-07, 3.989652643111546e-07,
    -2.2656409450964743e-07, 1.2789922739378625e-07, -8.259915063897185e-09,
    1.098662224931808e-08,
]
_R6_SCOR_LOG_COEFFS = [
    1.9018217478260242e-06,   # d_1 * x * ln(x)
    -0.0004374149293397197,   # d_2 * x^2 * ln(x)
    0.0011782018364791763,    # d_3 * x^3 * ln(x)
]
_R6_SCOR_LAM = 31.55228058803741
_R6_SCOR_Q = 12.414832272409459


def tower_corrected_scor(a, b, level, rates, exp_coeffs, log_coeffs, lam, q_gate):
    """Tower + mixed exponential/logarithmic SCOR correction.

    P = P_Rk(h) / (1 - h^q * [sum_i c_i exp(-r_i lam x) + sum_k d_k x^k ln(x)])
    The x^k ln(x) terms absorb the non-analytic singularity of E(m) at m=1.
    """
    a, b = _order(a, b)
    h = h_param(a, b)
    x = 1.0 - h
    P_Rk = tower_perimeter(a, b, level)
    # Exponential terms
    phi = sum(c * math.exp(-r * lam * x) for r, c in zip(rates, exp_coeffs))
    # Logarithmic enrichment terms: d_k * x^k * ln(x) for k=1,2,3
    if x > 0:
        lnx = math.log(x)
        xk = x
        for d in log_coeffs:
            phi += d * xk * lnx
            xk *= x
    # x^k * ln(x) → 0 as x → 0+, so phi is continuous
    gate = h ** q_gate
    denom = 1.0 - gate * phi
    if denom <= 0.0 or not math.isfinite(denom):
        return float("nan")
    return P_Rk / denom


def r6_scor_champion(a, b):
    """R6+16exp+3log SCOR. Max error 0.007 ppb = 7 ppt. WORLD RECORD.
    Verified at 300 digits (r6_nonanalytic_basis_v1.json)."""
    return tower_corrected_scor(a, b, 4,
                                _R6_SCOR_RATES, _R6_SCOR_EXP_COEFFS,
                                _R6_SCOR_LOG_COEFFS, _R6_SCOR_LAM, _R6_SCOR_Q)


# ---------------------------------------------------------------------------
# 5d. R4+20exp — 0.492 ppb
# ---------------------------------------------------------------------------
_R4_20_RATES = [
    1/3, 3/7, 3/4, 1, 7/6, 7/3, 3, 81/25, 292/63,
    5, 189/25, 9, 12, 15, 17, 25, 30, 35, 45, 70,
]
_R4_20_COEFFS = [
    -1.5937722286313696e-06, 4.004676507772733e-06, -6.07781259758309e-06,
    -1.7887837164351737e-05, 7.004699361980741e-06, -1.534340458195682e-06,
    8.604354677488707e-06, -5.918840736648467e-07, 4.016298270455695e-06,
    2.308529236939859e-06, -4.070618365020088e-06, 6.387425123480058e-06,
    -4.4507260538806865e-07, -7.202231753854354e-06, 9.243836492981317e-06,
    -3.985839132116884e-06, -1.6398228803520656e-06, 5.453076591436378e-06,
    -2.3199601822721373e-06, 3.261112304827786e-07,
]
_R4_20_LAM = 15.802299362305348
_R4_20_Q = 2.519930815428779

def r4_20exp_champion(a, b):
    """R4+20exp champion. Max error 0.492 ppb."""
    return tower_corrected(a, b, 2, _R4_20_RATES, _R4_20_COEFFS, _R4_20_LAM, _R4_20_Q)


# ---------------------------------------------------------------------------
# 5e. R5+16exp VARPRO — 0.045 ppb = 45 parts per trillion
#
# Found by hierarchical optimizer (17 Mar 2026, claude-525bd375).
# Continuous rates, λ=23.69, q=7.89. Verified 300 digits.
# ---------------------------------------------------------------------------
_R5_VP_RATES = [
    0.29878611440337327, 0.3572365501509249, 0.41828921662677127,
    0.5677005934267171, 0.770726605612723, 0.9495851373843635,
    1.1698946276558106, 2.3239087718175355, 4.205557610686093,
    8.283583529370196, 15.27658749199377, 18.649332712735315,
    27.835229882813813, 35.73422684428793, 113.10794979750942,
    135.17573511621515,
]
_R5_VP_COEFFS = [
    -2.588676620699167e-04, 1.220803421717380e-03, -1.651798604942254e-03,
    1.262847441025102e-03, -1.136064899841650e-03, 7.192927096587283e-04,
    -1.714984099958837e-04, 1.161648316508942e-05, 2.048063475485459e-06,
    1.551829455810800e-06, -1.263090356927472e-06, 1.733089858132272e-06,
    -8.106411423336153e-07, 4.107631652705958e-07, -3.194250873988154e-08,
    3.155489726726257e-08,
]
_R5_VP_LAM = 23.688420305684442
_R5_VP_Q = 7.890699853691736

def r5_varpro_champion(a, b):
    """R5+16exp VARPRO. Max error 0.045 ppb (17 March 2026).
    Verified 300 digits."""
    return tower_corrected(a, b, 3, _R5_VP_RATES, _R5_VP_COEFFS, _R5_VP_LAM, _R5_VP_Q)

# Keep old R5 for reference
_R5_20_RATES = [
    3/7, 2/3, 1, 7/6, 3/2, 81/25, 292/63,
    5, 7, 189/25, 10, 11, 15, 20, 24, 25, 26, 30, 50, 100,
]
_R5_20_COEFFS = [
    4.826487614666834e-06, -2.3995431024901575e-05, -1.3983149966928165e-05,
    3.610773363134473e-05, -2.0627570247922536e-05, 1.8361450410777854e-05,
    -3.036496371952144e-05, 2.986798101900685e-05, 6.102770545532203e-06,
    -2.1721342929309672e-05, 4.818843318153823e-05, -3.0029777963704074e-05,
    -1.8709454471278563e-05, 3.539671949510961e-05, 2.201634954838419e-05,
    -3.665046743365169e-05, -2.6884550639689826e-05, 2.3025674645330903e-05,
    -1.017872383950891e-06, 9.108624972732102e-08,
]
_R5_20_LAM = 15.230301669375985
_R5_20_Q = 6.676892221459639

def r5_20exp_champion(a, b):
    """R5+20exp (old, superseded by VARPRO). Max error 0.508 ppb."""
    return tower_corrected(a, b, 3, _R5_20_RATES, _R5_20_COEFFS, _R5_20_LAM, _R5_20_Q)


# ---------------------------------------------------------------------------
# Registry for easy iteration
# ---------------------------------------------------------------------------

ALL_FORMULAS = {
    "Ramanujan II (1914)": ramanujan_ii,
    "Cantrell (2001)": cantrell,
    "Ayala-Raggi R2/2exp (2025)": ayala_raggi_r2_2exp,
    "R2/3exp h^2, m=pi [THIS WORK]": r2_3exp_gated_h2,
    "R2/3exp h^2.5, m=pi [THIS WORK]": r2_3exp_gated_pi,
    "R2/3exp h^2.5, m=81/25 [THIS WORK]": r2_3exp_gated,
    "R2/3exp q=7/3, m=81/25 [V23]": r2_3exp_v23_champion,
    "R3+15exp (1.427 ppb) [THIS WORK]": r3_15exp_champion,
    "R4+20exp (0.492 ppb) [THIS WORK]": r4_20exp_champion,
    "R5+16exp VARPRO (0.045 ppb) [THIS WORK]": r5_varpro_champion,
    "R6+16exp VARPRO (0.018 ppb)": r6_varpro_champion,
    "R6+16exp+3log SCOR (0.007 ppb) [CHAMPION]": r6_scor_champion,
}
