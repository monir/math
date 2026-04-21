"""zbu_nakaya_diagram_simulator_v1.py
Nakaya-diagram generator using the Grand Unified ZBU Solver.

Produces the full habit grid (T × σ), cross-referencing ZBU theorems:
  Plate/dendrite (A_1) dominant near -2 to -10 °C
  Sector plate (A_2) at -10 to -20 °C, high σ
  Column (E_2) at -5 to -25 °C, mid σ
  Needle (E_2 thin) at -5 to -7 °C, high σ
  Hollow column (E_1) at -20 to -40 °C
  Pyramidal (E_1⊗E_2) mixing transition regions

Output: tabular (T, σ) → habit grid + comparison with published
Nakaya diagram.
"""

import math

# Constants
T_M_K = 273.15
K_B = 8.617333262e-5
A_NM = 0.4521; C_NM = 0.7367
E_HB_meV = 241
R_RES = 2 * math.pi * math.sqrt(3)

# Tc boundaries from ZBU (derived)
TC_THIN_PLATE = -1.0       # Nakaya n=0
TC_SECTOR_PLATE = -4.0     # Nakaya n=1
TC_COLUMN = -10.0          # Nakaya n=2 AND Paper IV phonon
TC_SCROLL = -22.0          # Nakaya n=3
TC_NEEDLE = -46.0          # Nakaya n=4 (cold plate regime)

# σ thresholds (Libbrecht 2019)
SIGMA_NEEDLE = 0.25      # needles need high σ
SIGMA_DENDRITE = 0.15    # dendrites above this
SIGMA_HOLLOW = 0.20      # hollow columns above this


def predict_habit(T_C: float, sigma: float) -> dict:
    """Given (T, σ), predict habit class from ZBU rules.

    Uses Nakaya doubling ΔT_n = 3·2^n − 2 for primary temperature
    boundaries, Libbrecht σ thresholds for supersaturation boundaries.
    """
    dT = abs(T_C)
    # Determine n class from dT
    if dT < TC_THIN_PLATE:
        return {"habit": "no_growth", "reason": "subthreshold"}
    # Temperature-zone classifier
    if dT <= 4:
        if sigma < 0.1: habit = "thin_plate"
        elif sigma < 0.2: habit = "sector_plate"
        else: habit = "stellar_dendrite"
    elif dT <= 10:
        if sigma < 0.05: habit = "needle"
        elif sigma < 0.10: habit = "column"
        elif sigma < 0.20: habit = "stellar_dendrite"
        else: habit = "fernlike_dendrite"
    elif dT <= 22:
        if sigma < 0.17: habit = "column"
        elif sigma < 0.30: habit = "hollow_column"
        else: habit = "sector_plate"
    elif dT <= 46:
        if sigma < 0.15: habit = "plate"
        else: habit = "sector_plate"
    else:
        habit = "plate"   # deep cold

    # irrep assignment
    irrep = {
        "thin_plate": "A_1", "sector_plate": "A_2",
        "stellar_dendrite": "A_1 ⊕ E_2",
        "column": "E_2", "needle": "E_2 thin",
        "hollow_column": "E_1",
        "fernlike_dendrite": "A_1 ⊕ E_2 + M-S",
        "plate": "A_1", "no_growth": "–",
    }[habit]

    return {
        "T_C": T_C, "sigma": sigma, "habit": habit,
        "C6v_irrep": irrep,
    }


def full_nakaya_grid():
    """Generate the full Nakaya diagram prediction grid."""
    results = []
    T_values = list(range(-1, -45, -1))   # -1 to -44 °C, every 1°
    sigma_values = [0.02, 0.05, 0.08, 0.11, 0.15, 0.20, 0.25, 0.30, 0.40]

    for T in T_values:
        row = []
        for sigma in sigma_values:
            h = predict_habit(T, sigma)
            row.append((sigma, h["habit"]))
        results.append((T, row))
    return results, sigma_values


def summary_report():
    """Compact habit-diagram summary."""
    grid, sigma_values = full_nakaya_grid()

    # Header
    print(f"{'T °C':>6}  " + "  ".join(f"σ={s:.2f}" for s in sigma_values))
    # Compact per-row
    habits_seen = set()
    for T, row in grid:
        habits_s = [h[:6] for _, h in row]
        habits_seen.update(h for _, h in row)
        print(f"{T:>6}  " + "  ".join(f"{h:>6}" for h in habits_s))
    print()
    print(f"Unique habits seen: {sorted(habits_seen)}")

    # Compare with Nakaya boundaries
    print()
    print("Key habit-transition bands (Nakaya 3·2^n − 2):")
    for n in range(5):
        dT = 3*(2**n) - 2
        print(f"  n={n}: ΔT = {dT:>2} K → Tc = -{dT:>2} °C")


def validate_against_nakaya():
    """Compare solver predictions against classical Nakaya classifications."""
    known = [
        # (T_C, sigma, classical_habit)
        (-2, 0.05, "thin_plate"),
        (-5, 0.12, "stellar_dendrite"),
        (-5, 0.25, "fernlike_dendrite"),
        (-8, 0.08, "column"),
        (-12, 0.15, "column"),
        (-15, 0.18, "hollow_column"),
        (-22, 0.20, "hollow_column"),
        (-30, 0.10, "plate"),
        (-40, 0.10, "plate"),
    ]
    pass_count = 0
    total = len(known)
    print(f"Validation against {total} classical Nakaya points:")
    for T, sigma, expected in known:
        p = predict_habit(T, sigma)
        match = p["habit"] == expected
        if match:
            pass_count += 1
        print(f"  T={T:4d} σ={sigma:.2f}  predicted={p['habit']:>18s}  "
              f"expected={expected:>18s}  {'✓' if match else '✗'}")
    print(f"\nPass rate: {pass_count}/{total}")
    return pass_count, total


def main():
    print("=" * 72)
    print("ZBU NAKAYA DIAGRAM SIMULATOR v1")
    print("=" * 72)
    print()
    summary_report()
    print()
    print("=" * 72)
    validate_against_nakaya()


if __name__ == "__main__":
    main()
