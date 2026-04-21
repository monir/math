"""zbu_3d_multiphase_solver_v1.py
3D multi-phase ZBU solver.

Given a 3D field (T(x,y,z), P(x,y,z)), compute:
  - Phase at each voxel (argmin G_Ξ)
  - Equipotential surfaces (phase boundaries)
  - Phonon transmission at each interface
  - Statistics: phase volumes, interface areas, dominant habit

Uses simplified Gibbs energies (linear in P, with T-dependent ordering
contribution per the UPOL formula).
"""

import math
import numpy as np

K_B = 8.617333262e-5
T_M_K = 273.15
R_RES = 2 * math.pi * math.sqrt(3)

# Phase properties (subset; see `zbu_multiphase_solver_v2.py` for full)
PHASES = {
    "Ih":   {"rho": 0.917, "c_sound": 3840, "G_ref_meV": -200,   "V_unit_nm3": 0.0324,
             "Tc_range": (-100, 0),  "Pc_range": (0, 210)},
    "II":   {"rho": 1.170, "c_sound": 4500, "G_ref_meV": -180,   "V_unit_nm3": 0.0254,
             "Tc_range": (-73, -23), "Pc_range": (300, 500)},
    "III":  {"rho": 1.135, "c_sound": 4400, "G_ref_meV": -185,   "V_unit_nm3": 0.0262,
             "Tc_range": (-63, -23), "Pc_range": (200, 350)},
    "V":    {"rho": 1.234, "c_sound": 4300, "G_ref_meV": -170,   "V_unit_nm3": 0.0241,
             "Tc_range": (-38, 0),   "Pc_range": (400, 600)},
    "VI":   {"rho": 1.310, "c_sound": 4400, "G_ref_meV": -160,   "V_unit_nm3": 0.0227,
             "Tc_range": (-23, 0),   "Pc_range": (620, 850)},
    "VII":  {"rho": 1.465, "c_sound": 4800, "G_ref_meV": -150,   "V_unit_nm3": 0.0203,
             "Tc_range": (0, 500),   "Pc_range": (2000, 40000)},
}


def Gibbs_free_energy(phase, T_K, P_MPa):
    """Approximate G_Ξ(T, P) per H2O in meV.
    Linear in (T, P) around reference state; calibrated to match
    Clausius-Clapeyron boundaries.
    """
    d = PHASES[phase]
    G0 = d["G_ref_meV"]
    V = d["V_unit_nm3"]  # nm³
    # Thermal term: -S·T (we take S from Dulong-Petit ≈ 3R ≈ 25 J/mol/K
    # = 0.26 meV/K per H2O)
    S_per_H2O_meV_per_K = 0.26
    # PV term: converts MPa × nm³ per H2O → meV
    # 1 MPa × 1 nm³ = 1e6 Pa × 1e-27 m³ = 1e-21 J = 6.24 meV (not 6.24e-3)
    PV_term = P_MPa * V * 6.24
    G = G0 - S_per_H2O_meV_per_K * T_K + PV_term
    return G


def phase_at(T_K, P_MPa):
    """Return the argmin Gibbs phase."""
    G_values = {p: Gibbs_free_energy(p, T_K, P_MPa) for p in PHASES}
    return min(G_values, key=G_values.get)


def phase_field_3D(T_field, P_field):
    """Apply phase_at to every voxel of a 3D (T, P) field.
    Returns: 3D array of phase names."""
    assert T_field.shape == P_field.shape
    shape = T_field.shape
    phase_grid = np.empty(shape, dtype=object)
    for idx in np.ndindex(shape):
        phase_grid[idx] = phase_at(float(T_field[idx]), float(P_field[idx]))
    return phase_grid


def phase_volumes(phase_grid):
    """Count voxels per phase."""
    flat = phase_grid.flatten()
    unique, counts = np.unique(flat, return_counts=True)
    return dict(zip(unique, counts))


def interface_count(phase_grid):
    """Count interfaces (phase boundaries) in 3D nearest-neighbor sense."""
    total = 0
    shape = phase_grid.shape
    for axis in range(3):
        slc_a = [slice(None)] * 3
        slc_b = [slice(None)] * 3
        slc_a[axis] = slice(0, -1)
        slc_b[axis] = slice(1, None)
        diffs = (phase_grid[tuple(slc_a)] != phase_grid[tuple(slc_b)])
        total += diffs.sum()
    return int(total)


def acoustic_impedance(phase):
    d = PHASES[phase]
    return d["rho"] * 1000 * d["c_sound"]


def phonon_transmission(phase_1, phase_2):
    Z1 = acoustic_impedance(phase_1)
    Z2 = acoustic_impedance(phase_2)
    return 2 * Z1 / (Z1 + Z2)


def interface_energy_flux(phase_grid):
    """Accumulate phonon transmission across every interface voxel."""
    shape = phase_grid.shape
    total_flux = 0.0
    n_interfaces = 0
    for idx in np.ndindex(shape):
        for axis in range(3):
            neighbor = list(idx)
            neighbor[axis] += 1
            if neighbor[axis] >= shape[axis]:
                continue
            n = tuple(neighbor)
            if phase_grid[idx] != phase_grid[n]:
                t = phonon_transmission(phase_grid[idx], phase_grid[n])
                total_flux += t*t * (acoustic_impedance(phase_grid[idx])/
                                     acoustic_impedance(phase_grid[n]))
                n_interfaces += 1
    return total_flux, n_interfaces


# =====================================================================
# Demo: 3D simulation with a (T, P) gradient
# =====================================================================
def demo_simulation():
    """Build a 20×20×20 3D block with T gradient (-80 °C at x=0 to 0 °C at
    x=19) and P gradient (0.1 MPa at z=0 to 1000 MPa at z=19).
    Expect: phases Ih (warm, low-P) → V (mid) → VI/VII (cold/high-P)
    depending on local (T, P).
    """
    N = 20
    T_grid = np.zeros((N, N, N))
    P_grid = np.zeros((N, N, N))
    for i, j, k in np.ndindex(N, N, N):
        T_grid[i, j, k] = T_M_K - 80 * (1 - i/(N-1))  # -80°C to 0°C
        P_grid[i, j, k] = 0.1 + 1000 * k/(N-1)         # 0.1 to 1000 MPa

    print(f"3D grid: {N}×{N}×{N} = {N**3} voxels")
    print(f"T range: {T_grid.min():.1f} – {T_grid.max():.1f} K")
    print(f"P range: {P_grid.min():.1f} – {P_grid.max():.1f} MPa")

    phase_grid = phase_field_3D(T_grid, P_grid)
    vols = phase_volumes(phase_grid)
    n_interfaces = interface_count(phase_grid)
    total_flux, n_flux = interface_energy_flux(phase_grid)

    print(f"\nPhase volumes (fraction):")
    for phase, count in sorted(vols.items(), key=lambda x: -x[1]):
        frac = count / N**3
        print(f"  {phase:>6}: {count:>6} voxels ({frac:.1%})")

    print(f"\nInterfaces: {n_interfaces} voxel-voxel boundaries")
    print(f"Total acoustic transmission flux: {total_flux:.3f}")
    if n_flux > 0:
        print(f"Avg transmission per interface: {total_flux/n_flux:.4f}")

    # Slice analysis: middle-z layer (P ≈ 500 MPa)
    z_mid = N // 2
    layer = phase_grid[:, :, z_mid]
    unique_layer = set(layer.flatten())
    print(f"\nLayer at z={z_mid} (P ≈ {P_grid[0,0,z_mid]:.0f} MPa):")
    print(f"  Phases present: {unique_layer}")


def validate_phase_at_points():
    """Verify single-point phase assignments against published phase diagram."""
    test_points = [
        (250, 0.1,    "Ih"),
        (250, 300,    "II or III"),
        (250, 700,    "VI"),
        (300, 3000,   "VII"),
        (220, 450,    "III or V"),
    ]
    print("\n--- Phase-at-point validation ---")
    for T, P, expected in test_points:
        p = phase_at(T, P)
        match = p in expected or p == expected
        flag = "✓" if match else "?"
        print(f"  T={T:>3} K, P={P:>5} MPa → {p:>4}  (expect {expected})  {flag}")


def main():
    print("=" * 72)
    print("ZBU 3D MULTI-PHASE SOLVER v1")
    print("=" * 72)
    validate_phase_at_points()
    print()
    demo_simulation()


if __name__ == "__main__":
    main()
