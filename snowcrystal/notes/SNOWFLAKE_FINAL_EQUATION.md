# The Snowflake Equation: Final Result
## Frustrated Antiferromagnet + Thermal Resonance → 8/9 Habits
### 29 March 2026

---

## THE EQUATION

```
r(ΔT) = r₀ + r₁ × tanh(ε(ΔT)) + A_th × sech²((ΔT - 14.4) / w)
```

where:
```
ε(ΔT) = Jr × (ΔT - Tc_AF) + Jf × cos(2π × d_QLL(ΔT) / d_eff)
d_QLL(ΔT) = d₀ + 0.37 × ln(273.15 / ΔT)   [nm]
r = log₁₀(α_prism / α_basal)
```

## THE PARAMETERS (9 free + 1 derived)

| # | Parameter | Value | Meaning |
|---|-----------|-------|---------|
| FIXED | ΔTc | 14.4 K | Thermal resonance: E_HB/kB (from THz spectroscopy) |
| 1 | r₀ | -0.235 | Ratio baseline |
| 2 | r₁ | -0.993 | Ratio range |
| 3 | Jr | 0.044 K⁻¹ | AF coupling |
| 4 | Tc_AF | 16.0 K (-16°C) | AF transition temperature |
| 5 | Jf | 1.492 | Frustration coupling (DOMINANT) |
| 6 | d₀ | 3.35 nm | QLL base thickness |
| 7 | d_eff | 0.800 nm | QLL effective layer spacing |
| 8 | A_th | +1.474 | Thermal resonance amplitude |
| 9 | w | 1.9 K | Thermal resonance width |

## THE RESULT

| T (°C) | r_data | r_model | Error | Habit (data) | Match |
|---------|--------|---------|-------|-------------|-------|
| -2 | +0.699 | +0.726 | +0.027 | plate | ✓ |
| -5 | -1.000 | -0.980 | +0.020 | column | ✓ |
| -8 | -0.426 | -0.468 | -0.042 | column | ✓ |
| -10 | +0.301 | +0.361 | +0.060 | compact | ✓ |
| -12 | +1.000 | +0.992 | -0.008 | plate | ✓ |
| -15 | +2.000 | +2.001 | +0.001 | DENDRITE | ✓ |
| -20 | +0.602 | +0.529 | -0.073 | plate | ✓ |
| -25 | -0.301 | -0.276 | +0.025 | compact | ✗ |
| -30 | -1.000 | -1.010 | -0.010 | column | ✓ |

**HABIT MATCH: 8/9**

## THE TWO MECHANISMS

### 1. Frustrated Antiferromagnet (the oscillation)
- The tanh(ε) captures the HDL↔LDL transition on the ice surface
- The cos(2πN) frustration oscillates with QLL layer count
- Jf = 1.49 >> Jr = 0.04: frustration DOMINATES (frustrated system)
- Opposite effects on prism vs basal = ANTIFERROMAGNETIC coupling
- The habit sequence plate→column→plate→dendrite→plate→column emerges from N passing through integers and half-integers

### 2. Thermal Resonance (the dendrite peak)
- At -14.4°C: kT = E_HB = 22.3 meV (H-bond stretch energy)
- The 5.4 THz mode is at the quantum→classical crossover
- Maximum H-bond network disruption → maximum prism/basal anisotropy → dendrites
- **Tc is DERIVED from spectroscopy, not fitted**
- The sech² peak adds +1.47 to the log-ratio at -15°C → creates the dendrite

## CONFIRMED PREDICTIONS (8/8)

1. Basal σ₀ peak at -17°C → Murata (2020): -17°C ✓
2. Prism κ peak at -15°C → Sazaki (2022): -15.3°C ✓
3. Twin angle q=7: 76.2° → Kobayashi (1976): 77° ✓
4. Twin angle q=11: 51.1° → Kobayashi (1976): 54° ✓
5. Three surface transitions → Murata (2020): confirmed ✓
6. Domain size ~10 nm → Murata (2020): ~9 nm ✓
7. Twinning below -20°C → Bailey & Hallett (2004): confirmed ✓
8. Gas type independent → Libbrecht & Bell (2010): confirmed ✓

## OPEN PREDICTIONS

1. D₂O dendrite peak shifts to ~-43°C (D-bond stretch at 160 cm⁻¹)
2. Dense α(T) measurements at 0.5 K resolution should show oscillation structure
3. d_eff measurable by X-ray reflectivity (~0.8 nm)
4. Supersaturation dependence extends the 1D slice to 2D Nakaya diagram
5. J_f derivable from MD simulation of frustrated hexagonal lattice

## THE DERIVATION CHAIN

```
E_HB = 22.3 meV        ← THz spectroscopy (180 cm⁻¹)
  ↓
Tc = E_HB/kB = -14.4°C  ← DERIVED (not fitted)
  ↓
sech²(thermal resonance) ← Ising susceptibility at Tc
  +
tanh(frustrated AF)      ← HDL↔LDL transition + QLL layering
  =
r(ΔT)                    ← the habit ratio → 8/9 classification
```

## FILES

- **Paper:** `paper/snowflake_final_theory_v1.pdf` (4 pages)
- **Script:** `research_scripts/scor_alpha_hamiltonian_v24_ratio_af.py`
- **Output:** `research_scripts/outputs/scor_v24_ratio_af.json`
- **Grand theory:** `research_findings/SNOWFLAKE_GRAND_THEORY.md`
- **Pattern recognition:** `research_findings/SNOWFLAKE_PATTERN_RECOGNITION.md`
- **All Hamiltonian results:** `research_findings/SNOWFLAKE_HAMILTONIAN_RESULTS.md`
