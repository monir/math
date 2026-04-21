"""zbu_multiphase_solver_v2.py
Multi-phase ZBU solver: phase field + equipotential surfaces + phonon
transfer across boundaries.

Key data structures:
  PHASE_DATA[phase]: structural + elastic + free-energy data
  CLAUSIUS_CLAPEYRON: pairwise phase-coexistence curves (T, P)
  phase_at(T, P, history): returns dominant + metastable-allowed phase
  phonon_transfer(phonon, interface): transmission coefficient
"""

import math

# =====================================================================
# Constants
# =====================================================================
T_M_K = 273.15       # melting point
K_B = 8.617333262e-5
E_HB_meV = 241
R_RES = 2 * math.pi * math.sqrt(3)


# =====================================================================
# Phase data — densities, sound speeds, proton-order Tₒ
# =====================================================================
PHASE_DATA = {
    "Ih":    {"rho_g_cm3": 0.917, "c_sound_m_s": 3840, "ordered": False,
              "T_o": 72,  "irreps": ["A_1","A_2","B_1","B_2","E_1","E_2"],
              "stable_T_K": (72, 273.15), "stable_P_MPa": (0, 210)},
    "Ic":    {"rho_g_cm3": 0.938, "c_sound_m_s": 3800, "ordered": False,
              "T_o": 200, "irreps": ["A_1g","T_2u","T_1u","E_g"],
              "stable_T_K": (140, 200), "stable_P_MPa": (0, 100)},
    "II":    {"rho_g_cm3": 1.170, "c_sound_m_s": 4500, "ordered": True,
              "T_o": 118, "irreps": ["A_1","A_2","E"],
              "stable_T_K": (200, 250), "stable_P_MPa": (300, 500)},
    "III":   {"rho_g_cm3": 1.135, "c_sound_m_s": 4400, "ordered": True,
              "T_o": 164, "irreps": ["A_1","A_2","B_1","B_2","E"],
              "stable_T_K": (210, 250), "stable_P_MPa": (200, 350)},
    "V":     {"rho_g_cm3": 1.234, "c_sound_m_s": 4300, "ordered": True,
              "T_o": 122, "irreps": ["A","B"],
              "stable_T_K": (235, 272), "stable_P_MPa": (400, 600)},
    "VI":    {"rho_g_cm3": 1.310, "c_sound_m_s": 4400, "ordered": True,
              "T_o": 108, "irreps": ["A_1","A_2","B_1","B_2","E"],
              "stable_T_K": (250, 273), "stable_P_MPa": (620, 850)},
    "VII":   {"rho_g_cm3": 1.465, "c_sound_m_s": 4800, "ordered": False,
              "T_o": 258, "irreps": ["A_1g","T_2u","T_1u"],
              "stable_T_K": (273, 400), "stable_P_MPa": (2000, 40000)},
    "VIII":  {"rho_g_cm3": 1.454, "c_sound_m_s": 4800, "ordered": True,
              "T_o": None, "irreps": ["A_1g","T_1u"],
              "stable_T_K": (50, 258), "stable_P_MPa": (2000, 2500)},
    "IX":    {"rho_g_cm3": 0.991, "c_sound_m_s": 4200, "ordered": True,
              "T_o": None, "irreps": ["A_1","A_2","B_1","B_2","E"],
              "stable_T_K": (140, 165), "stable_P_MPa": (200, 400)},
    "X":     {"rho_g_cm3": 1.530, "c_sound_m_s": 5200, "ordered": True,
              "T_o": None, "irreps": ["A_1g","E_g","T_1u"],
              "stable_T_K": (70, 350), "stable_P_MPa": (40000, 100000)},
    "XI":    {"rho_g_cm3": 0.917, "c_sound_m_s": 3850, "ordered": True,
              "T_o": None, "irreps": ["A_1","B_1"],
              "stable_T_K": (0, 72), "stable_P_MPa": (0, 200)},
    "XII":   {"rho_g_cm3": 1.280, "c_sound_m_s": 4500, "ordered": True,
              "T_o": None, "irreps": ["A_1","A_2","B_1","B_2","E"],
              "stable_T_K": (240, 269), "stable_P_MPa": (500, 700)},
    "XIII":  {"rho_g_cm3": 1.235, "c_sound_m_s": 4400, "ordered": True,
              "T_o": None, "irreps": ["A","B"],
              "stable_T_K": (260, 273), "stable_P_MPa": (600, 650)},
    "XIV":   {"rho_g_cm3": 1.291, "c_sound_m_s": 4450, "ordered": True,
              "T_o": None, "irreps": ["A_g","B_g","A_u","B_u"],
              "stable_T_K": (260, 273), "stable_P_MPa": (650, 850)},
    "XV":    {"rho_g_cm3": 1.235, "c_sound_m_s": 4400, "ordered": True,
              "T_o": None, "irreps": ["A_g","B_g","A_u","B_u"],
              "stable_T_K": (240, 273), "stable_P_MPa": (350, 600)},
    "XVI":   {"rho_g_cm3": 1.263, "c_sound_m_s": 4400, "ordered": True,
              "T_o": None, "irreps": ["A_1","A_2","E"],
              "stable_T_K": (160, 248), "stable_P_MPa": (4000, 5500)},
    "XVII":  {"rho_g_cm3": 0.943, "c_sound_m_s": 3900, "ordered": False,
              "T_o": None, "irreps": ["A_g","B_u","A_u","B_g"],
              "stable_T_K": (273, 330), "stable_P_MPa": (600, 800)},
    "XVIII": {"rho_g_cm3": 0.964, "c_sound_m_s": 3950, "ordered": False,
              "T_o": None, "irreps": ["A_g","B_u","A_u","B_g"],
              "stable_T_K": (240, 265), "stable_P_MPa": (500, 650)},
    "XIX":   {"rho_g_cm3": 1.161, "c_sound_m_s": 4400, "ordered": True,
              "T_o": None, "irreps": ["A_1","A_2","B_1","B_2","E"],
              "stable_T_K": (260, 273), "stable_P_MPa": (200, 300)},
    "XX":    {"rho_g_cm3": 1.480, "c_sound_m_s": 5000, "ordered": None,
              "T_o": None, "irreps": ["(superionic dynamic)"],
              "stable_T_K": (500, 3000), "stable_P_MPa": (40000, 100000)},
}


# =====================================================================
# Clausius-Clapeyron boundaries (Petrenko-Whitworth 1999)
# =====================================================================
CC_BOUNDARIES = [
    ("Ih",     "liquid", 273.15, 0.1),
    ("Ih",     "II",     200.0,  210.0),
    ("Ih",     "III",    251.0,  210.0),
    ("II",     "III",    238.0,  340.0),
    ("III",    "V",      256.0,  346.0),
    ("II",     "V",      248.0,  500.0),
    ("V",      "VI",     272.0,  632.0),
    ("VI",     "VII",    355.0,  2216.0),
    ("VI",     "liquid", 354.0,  2216.0),
    ("VII",    "VIII",   258.0,  2200.0),
    ("VII",    "X",      350.0, 40000.0),
    ("Ih",     "XI",      72.0,    0.1),  # proton order
    ("III",    "IX",     164.0,  200.0),
    ("V",      "XII",    122.0,  550.0),
    ("VI",     "XV",     108.0,  700.0),
    ("VI",     "XIX",    260.0,  250.0),
]


# =====================================================================
# Phase classifier: given (T, P), return candidate phases
# =====================================================================
def phase_candidates(T_K: float, P_MPa: float):
    """Return all phases whose stability region contains (T, P)."""
    result = []
    for name, d in PHASE_DATA.items():
        T_lo, T_hi = d["stable_T_K"]
        P_lo, P_hi = d["stable_P_MPa"]
        if T_lo <= T_K <= T_hi and P_lo <= P_MPa <= P_hi:
            result.append(name)
    return result


# =====================================================================
# Acoustic impedance mismatch between two phases
# =====================================================================
def acoustic_impedance(phase: str) -> float:
    """Z = ρ · c_sound (SI: kg/m²s)."""
    d = PHASE_DATA[phase]
    return d["rho_g_cm3"] * 1000 * d["c_sound_m_s"]  # kg/m³ × m/s


def phonon_transmission(phase_1: str, phase_2: str) -> dict:
    """Transmission coefficient for acoustic phonons across
    phase_1 → phase_2 interface (normal incidence).
    t_elastic = 2 Z_1 / (Z_1 + Z_2).
    Reflection r = (Z_2 - Z_1)/(Z_2 + Z_1); |r|² + |t|²·(Z_1/Z_2) = 1.
    """
    Z1 = acoustic_impedance(phase_1)
    Z2 = acoustic_impedance(phase_2)
    t = 2 * Z1 / (Z1 + Z2)
    r = (Z2 - Z1) / (Z1 + Z2)
    # Check energy conservation |r|² + (Z1/Z2) |t|² = 1
    energy_check = r*r + (Z1/Z2) * t*t
    return {
        "phase_1": phase_1, "phase_2": phase_2,
        "Z_1": Z1, "Z_2": Z2,
        "t_amplitude": t, "r_amplitude": r,
        "t_energy_fraction": t*t * (Z1/Z2),
        "r_energy_fraction": r*r,
        "energy_conservation": energy_check,
    }


def irrep_overlap(phase_1: str, phase_2: str) -> float:
    """Number of shared irrep labels / sqrt(n1 × n2).
    Crude proxy for symmetry allowance of phonon transfer."""
    i1 = set(PHASE_DATA[phase_1]["irreps"])
    i2 = set(PHASE_DATA[phase_2]["irreps"])
    shared = i1.intersection(i2)
    n1 = len(i1)
    n2 = len(i2)
    if n1 * n2 == 0:
        return 0.0
    return len(shared) / math.sqrt(n1 * n2)


# =====================================================================
# Effective pressure from geometric confinement
# =====================================================================
def P_effective(P_ambient_MPa: float, r_confine_nm: float,
                gamma_N_per_m: float = 0.1) -> float:
    """Laplace-like effective pressure in confined ice.
    ΔP = 2γ/r in Pa × 1e-6 for MPa.
    """
    dP_Pa = 2 * gamma_N_per_m / (r_confine_nm * 1e-9)
    return P_ambient_MPa + dP_Pa * 1e-6


# =====================================================================
# Generate cross-phase transmission table
# =====================================================================
def generate_transmission_table():
    phases = ["Ih", "II", "III", "V", "VI", "VII", "VIII", "X", "XI"]
    print(f"\n{'Phase 1':>6} → {'Phase 2':>6}  "
          f"{'Z_1':>10} {'Z_2':>10} {'t_amp':>8} {'t_energy':>8} {'sym':>6}")
    for p1 in phases:
        for p2 in phases:
            if p1 >= p2: continue
            t = phonon_transmission(p1, p2)
            s = irrep_overlap(p1, p2)
            print(f"{p1:>6} → {p2:>6}  "
                  f"{t['Z_1']:>10.2e} {t['Z_2']:>10.2e} "
                  f"{t['t_amplitude']:>8.4f} {t['t_energy_fraction']:>8.4f} "
                  f"{s:>6.3f}")


# =====================================================================
# Main
# =====================================================================
def main():
    print("=" * 72)
    print("ZBU MULTI-PHASE SOLVER v2 — cross-phase tables")
    print("=" * 72)

    # 1. Phase candidates at various (T, P) points
    print("\n--- Phase candidates at (T, P) ---")
    test_points = [(250, 0.1), (250, 300), (250, 700),
                   (278, 2500), (100, 0.1), (60, 0.1)]
    for T, P in test_points:
        cands = phase_candidates(T, P)
        print(f"  T={T} K, P={P} MPa  candidates={cands}")

    # 2. Phonon transmission table
    print("\n--- Phonon transmission coefficients (normal incidence) ---")
    generate_transmission_table()

    # 3. Irrep overlaps for key pairs
    print("\n--- Irrep overlap (symmetry allowance) ---")
    pairs = [("Ih", "Ic"), ("Ih", "XI"), ("Ih", "II"),
             ("II", "V"), ("V", "VI"), ("VI", "VII"),
             ("VII", "VIII"), ("VII", "X")]
    for p1, p2 in pairs:
        print(f"  {p1} ↔ {p2}: "
              f"irrep_overlap = {irrep_overlap(p1, p2):.3f}, "
              f"|t_amp|² = {phonon_transmission(p1, p2)['t_amplitude']**2:.4f}")

    # 4. Effective pressure from confinement
    print("\n--- Effective P from nano-confinement (γ = 0.1 N/m) ---")
    for r_nm in (0.5, 1.0, 5.0, 50.0):
        P_eff = P_effective(0.1, r_nm)
        print(f"  r={r_nm:5.1f} nm  →  P_eff={P_eff:10.2f} MPa")

    # 5. Clausius-Clapeyron boundaries
    print("\n--- Published phase boundaries (CC curves) ---")
    for (p1, p2, T, P) in CC_BOUNDARIES:
        print(f"  {p1:>6} ↔ {p2:<6}  T={T:7.2f} K  P={P:10.2f} MPa")


if __name__ == "__main__":
    main()
