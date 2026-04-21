# ZBU Phase-Field + Logatomic Bridge

**Date:** 2026-04-17
**Status:** Design document for Approach 3 — the full phase-field treatment of
crystallization, cast in ZBU + logatomic form, with careful treatment of the
equipotential-shell singularity at small scales and the analyticity radius
that separates algebraic from analytic regimes.
**Depends on:** ZBU_3D_VAPOR_HEAT_U_DESIGN, ZBU_3D_FIELD_PHYSICS_ADDENDUM,
ZBU_NUCLEATION_SYMMETRY_DYNAMICS, logatomic.sty LA1–LA5.

---

## Why Approach 3 (phase-field) — as you said, it "saves complexity"

At first glance a continuous phase-field (Cahn-Hilliard with order parameter
ξ and orientation ν) looks heavier than a masking approach. But:

1. **ξ(x) is exactly the UNDERWOOD U field's magnitude** — it's log(density of
   ice Ih) / log(density_eq). So it already lives in the ZBU algebra.
2. **Nucleation, growth, and phase transition are one equation**, not a
   special crystallization case + a separate growth case.
3. **Equipotential shells naturally become level sets of ξ** — r_k := {x :
   ξ(x) = ξ_k} for ξ_k ∈ (0,1). Foliation is implicit, not a separate
   geometric construction.
4. **2D manifold nucleation is the logatomic `bump` operator emerging from ξ**
   — no special detection code needed.

So Approach 3 doesn't ADD complexity; it REMOVES the bookkeeping that
separate {amorphous coating, crystallization phase, growth phase} would
impose.

---

## The one-equation form

```
   phase field:           ξ : R³ → [0,1]        (0 = vapor, 1 = ice Ih)
   orientation:           ν : R³ → C_6v irrep simplex (6-component, sums to 1)
   vapor:                 c : R³ → R₊           (as before)
   temperature:           T : R³ → R            (as before)
```

Cahn-Hilliard for ξ with a Landau free energy F(ξ) that has a double-well
(vapor at ξ=0, ice at ξ=1) and a hydration barrier between:

```
   ∂ξ/∂t = M_ξ ∇²(f'(ξ) − κ_ξ ∇²ξ)        Cahn-Hilliard

where  f(ξ) = a · ξ²(1−ξ)² − b(T, c) · ξ         double-well tilted by supersat
       κ_ξ  = surface-tension-related width parameter
       b(T, c) = k_B T · (ln(c) − L_sub/(k_B T) + ln(c_sat(T)))       driving force
```

Orientation ν evolves only where ξ is large (ice present):

```
   ∂ν_a/∂t = ξ · [M_ν ∇²ν_a + Γ_a(ν)]           per-irrep Allen-Cahn

where Γ_a(ν) = local irrep-alignment potential (gradient of B_dual from ZBU)
```

UNDERWOOD U from the earlier design **becomes** ν here — no separate bookkeeping.

---

## The logatomic reformulation

Every phase-field operation has a logatomic form. The user's intuition was
right: expressing in logatomic saves complexity because the algebra is
self-consistent.

### Vapor deposition = sink-source pair

```
                                          source{water_vapor}  ▹  sink{ice_lattice}
```
This is a `paired` element (LA convention: paired = sink-source in contact,
net flow zero). Deposition flux is the strength of the directed composition `▹`.

### Phase transition = bump creation

A 2D island forming on a flat face is the creation of a new 2D submanifold
embedded in the existing 2D surface:

```
   ∇_x · ∇_y = bump                  (LA3 exactly — two orthogonal lattice gradients coupled)
```

So **LA3 IS nucleation**. A flat face has zero bumps; a face with a 2D island
has one bump. The bump's boundary is the island's edge (a 1D oriented curve
ΓA ring on the surface).

### Phase-transition thermodynamics = bump accounting

Across the entire closed crystal surface M:

```
   ∮_M bump dA = 0                    (LA5 — Gauss-Bonnet in logatomic form)
```

This conservation is automatic, not enforced. It means **every new island
on the top creates an "anti-island" topologically** — e.g., an indent that
forms elsewhere. Real snow crystals DO have dimples and bumps that pair up;
this is the LA5 constraint in action.

### Crystallization step = irrep anchor creation

At nucleation, a single fresh irrep anchor appears — a specific irrep at a
specific point. In logatomic:

```
   amorphous_void  →  anchor_A1  @ (x₀)
```

The anchor has a type (A1, A2, E1, E2, B1, B2) which IS the c-axis orientation
choice. `anchor_A1` = basal-face-normal aligned with lab z-axis.

### Growth around the anchor = directed composition

```
   anchor_A1  ▹  sink_{N}  ▹  sink_{M}  ▹ ...
```
(LA1: sinks in series add orders — the accumulated water count.)

### Symmetry projection = B·U intertwining

Our original ZBU intertwining identity `U·Z = B·U` IS the symmetry projection:
U starts arbitrary; B projects onto C_6v eigenstates; the crystallization
process iterates U ↦ B·U·Z⁻¹ until convergence.

Logatomic: `U ▹ (Z ⋈ B)` = the growth chain's rule of composition.

### The full crystallization-to-growth chain in logatomic

```
   source{amorph}   ▹   source{0}·anchor_{A1}   ▹   bump  ⋈ latder{x}·latder{y}
                     (nucleation)                     (2D island on face)

                    ▹   sink_{6}·(C_6 rotation)   (growth along 6 equivalent prisms)

                    ▹   loopop_{perimeter}        (closure; Gauss-Bonnet satisfied)
```

Six glyphs. Six layers of snow-crystal physics. No extra machinery.

---

## The equipotential-shell singularity at small scales

This is your precise concern. Let me state it sharply.

### The problem

The scale-adaptive foliation uses shells r_k = r₀ · exp(k·Δ), log-spaced.
As k → −∞:
- r_k → 0
- r_k − r_{k−1} = r_k(1 − e^{−Δ}) → 0

The shells **crowd toward zero**. Near the center, the shell spacing
becomes smaller than a water molecule diameter (≈ 3 Å). At that scale:

- Multiple shells lie within a single water molecule's extent.
- The foliation is no longer a real geometric structure; it's **a dense set
  whose shells are all "in the same place."**
- Equivalently, the shells become a **space-filling covering set** (in the
  measure-theoretic sense): every point is in infinitely many shells.

### Why this matters physically

At r < r_a (analyticity radius, ≈ 1-2 nm), the continuum description breaks
down. You can't solve ∇²ξ = 0 meaningfully because there are no smooth
derivatives at the scale of individual molecules. The PDE becomes
ill-conditioned.

### The fix: matched algebraic/analytic zones with an UNDERWOOD bridge

```
   r < r_a  :  ALGEBRAIC ZONE
              integer counts of water molecules per voxel
              logatomic operators: source, sink, anchor, bump
              irrep weights from discrete C_6v table
              no continuous ξ; ξ ≡ 1 inside, 0 outside binary
              no equipotential shells (shells undefined below r_a)

   r = r_a  :  UNDERWOOD BRIDGE
              log-ladder matches inner integer state to outer ξ
              ξ_outer(r_a) = log(n_inner(r_a)) / log(n_crit)
              ν_outer(r_a) = projection of anchor irreps onto eigenstates

   r > r_a  :  ANALYTIC ZONE
              continuous ξ(x), ν(x), c(x), T(x)
              Cahn-Hilliard PDE solve
              equipotential shells r_k = r_a · exp(k·Δ) well-defined
              foliation geodesic + conformal invariants live here
```

r_a is the CUTOFF where the foliation starts — not at the origin. This
eliminates the singularity cleanly.

### r_a depends on the problem

- For crystallization from vapor (our case): r_a = 2 nm (a few water shells).
- For dendritic tip: r_a = tip radius ≈ 50 nm.
- For bulk ice: r_a = correlation length ≈ 1 nm.

The scenario YAML exposes r_a as a parameter:

```yaml
solver:
  analyticity_radius_nm: 2.0       # inner algebraic zone extends to here
  shell_base_um: 0.002              # r_0 = 2 nm
  shell_log_step: 0.2               # Δ log r
```

### Why this also saves compute

- Inner zone is a SMALL number of voxels (few nm) — cheap to do Monte Carlo
  on water-molecule clusters.
- Outer zone is large but coarse — cheap Laplace solve.
- The expensive interior near the molecular scale is replaced by a discrete
  graph.
- UNDERWOOD bridge is an O(1) matching condition.

Total compute scales as O(N_voxels_outer + N_clusters_inner) ≪ O(N_voxels_fine)
if we had to resolve the small scale as a continuum.

---

## The physical phase transition — careful treatment

A first-order phase transition (vapor ↔ ice) is **non-analytic** at σ = 0.
The free energy f(ξ) has a cusp where the two wells have equal depth.

### Consequence for ξ near the critical point

```
   f'(ξ, σ=0)  is discontinuous at ξ = ξ*
   ξ(x, t) satisfies a PDE with a non-differentiable source term near σ = 0
```

Numerically this causes Cahn-Hilliard to develop shock-like fronts. Standard
treatment: regularize with a finite-width double-well, accept that the front
has width ≈ √(κ_ξ / a).

### Consequence for analyticity radius

r_a is **at least** the front width: r_a ≥ √(κ_ξ / a) ≈ 0.5 - 2 nm for ice
at near-0 °C. This pins the minimum scale at which the phase field can resolve
the transition.

### Consequence for nucleation barrier

Classical nucleation theory:
```
   ΔG*(σ, T)  =  π γ_edge²(T) / (k_B T · ln(1+σ))
   r_critical  =  γ_edge(T) · Ω / (k_B T · ln(1+σ))
```

For σ → 0, r_critical → ∞ — **no nucleation possible**. This is also
non-analytic at σ = 0 (an essential singularity, ∼ exp(−const/σ²)).

**Implication**: the UNDERWOOD log-ladder must handle this essential
singularity. That's exactly what UNDERWOOD was designed to do in the ZBU
framework — it's the "singularity-handling connector" operator.

### Logatomic form of the phase transition

```
   source{0}_amorph   ▹   anchor_A1                   at σ > σ_crit
                                                       (else no transition)

   σ_crit(T) = σ*(T)  is implemented as a T-dependent threshold
   for the nucleation source term
```

The conditional `at σ > σ_crit` IS the non-analyticity. Below σ*, the
logatomic rule simply doesn't fire. Above, it fires exponentially fast.
UNDERWOOD's log-ladder regularizes the exponential: the rate is
exp(−const/σ²), which UNDERWOOD turns into a finite-radius-of-convergence
power series around σ = σ*.

---

## Radius of analyticity in the ZBU framework

Recall from ZBU: we have Gödel ω-consistency with analyticity radius r_a.
Below r_a, statements are algebraic (integer/rational counts of things);
above r_a, the theory is analytic (smooth functions of real variables).

Here r_a plays a triple role:

1. **Geometric cutoff**: equipotential shells start at r_a.
2. **Numerical cutoff**: continuous PDEs only make sense for r > r_a.
3. **Thermodynamic cutoff**: phase-transition front width is O(r_a).

These three should be CONSISTENT — if they disagree, something is wrong.
In our parametrization:

```
   r_a = max(
           √(κ_ξ / a),              front width
           water molecule radius,    molecular cutoff
           3 Å,                      absolute floor
           correlation length        thermal cutoff
         )
```

For practical ice at -15 °C: r_a ≈ 1.5 nm. All three definitions converge
on this value (within a factor of 2).

---

## The 2D manifold nucleation — the actual physics

"2D manifold nucleation that grows and keeps growing" is the user's key phrase.
Let me spell out exactly what happens:

### Phase 1: pre-nucleation
- Flat ice face exposed to supersaturated vapor.
- Adatoms (single water molecules) bounce on the face, diffusing with D_s.
- Adatom density n(x) is in local equilibrium: n ≈ n_∞ · exp(−E_ads/kT).
- Logatomic: `source{adatoms} ⋈ latder{face}` — a 2D gradient of free adatoms.
- No new manifold yet.

### Phase 2: critical fluctuation
- By random encounter, k adatoms cluster into a 2D island.
- For k < k_crit: island is thermodynamically unstable, dissolves back.
- For k = k_crit: probability of growing vs dissolving is 50-50.
- For k > k_crit: island grows.

Critical size:
```
   k_crit(σ, T) = (π γ_edge² Ω) / (k_B T · ln(1+σ))² · (1/a²)
               ≈ 10-100 molecules at moderate σ
```

### Phase 3: post-critical 2D growth
- Island grows by adatom attachment at its edge (perimeter).
- Edge velocity v_step = β_edge · (n − n_sat) at the step.
- The island sweeps across the face at v_step.
- Island size r(t) ∝ t until r = R_face (whole face covered).

### Phase 4: new layer complete
- Face advanced by one lattice spacing (3.68 Å for basal).
- Back to Phase 1 for the next layer.

### Logatomic representation of the full cycle

```
Phase 1:  source{N_adatoms}
Phase 2:  source{N_adatoms}  ⊗  latder{x}⋈latder{y} = bump_small(k_crit)
              (LA3: 2D-gradient-coupling creates the embryonic bump)
Phase 3:  bump_small ▹ bump_large(R_face)
              (LA1: sinks in series add — the bump accumulates adatoms)
Phase 4:  bump_large(R_face) = sink_layer
              (the completed 2D island = one full layer)
```

Each full cycle advances the face by one lattice spacing.

### The PDE form

All of the above can also be written as a stochastic PDE:

```
   ∂n/∂t = D_s ∇²n + j_deposit − k_step · (island edge terms)
   ∂ξ/∂t = Heaviside(n − n_crit) · C_island   + Cahn-Hilliard terms
```

And the stochastic part (phase 2) is a Poisson process with rate

```
   k_nuc = A · exp(−ΔG*/kT) · σ^p
```

fired at each surface voxel each timestep.

---

## Two-scale implementation sketch

```
class TwoScaleSolver {
  constructor({
    r_a_nm = 1.5,               // analyticity radius
    inner_voxel_nm = 0.3,       // water-molecule scale
    outer_voxel_um = 0.01,      // phase-field voxel (10 nm)
    grid_outer = 48,
  }) {
    this.inner = new InnerAlgebraicZone(r_a_nm, inner_voxel_nm);
    this.outer = new OuterPhaseFieldZone(grid_outer, outer_voxel_um);
    this.bridge = new UnderwoodBridge(this.inner, this.outer);
  }

  step(dt_s, env) {
    // 1. Inner: stochastic logatomic rules (~100 molecules)
    this.inner.stepLogatomic(dt_s, env);

    // 2. Outer: Cahn-Hilliard + vapor + heat + U
    this.outer.stepPhaseField(dt_s, env);

    // 3. Bridge: log-ladder matching
    this.bridge.match();
  }
}

class InnerAlgebraicZone {
  // A small graph of water-molecule sites with integer states.
  // Each site ∈ { vapor, amorph, ice_Ih_angle_θ }
  // Rules:
  //   source{vapor} ⋈ site → site.state := amorph with rate k_deposit
  //   amorph → ice_Ih_angle with rate k_cryst · alignment_score
  //   Nucleation event: emit anchor(θ) to bridge
  //
  // Implementation: ~1000 sites, Gillespie stochastic simulation.
}

class OuterPhaseFieldZone {
  // Cahn-Hilliard on 48³ grid for ξ, orientation ν, vapor c, temperature T.
  // ξ evolves per standard Cahn-Hilliard.
  // ν evolves per Allen-Cahn where ξ > 0.5.
  // Coupled to vapor and heat via boundary conditions at ξ-fronts.
}

class UnderwoodBridge {
  // Matching: ξ_outer(r_a) ↔ log(n_inner_at_shell) / log(n_crit)
  //          ν_outer(r_a) ↔ irrep-projection of inner anchors
  // Implements U · Z = B · U consistently across the interface.
  match() { ... }
}
```

---

## What a scenario with all this looks like

```yaml
zbu_schema: "1.2"                          # NEW minor version for phase-field
title: "Full phase-field growth from a bacterial nucleus"
starred: true
description: |
  Uses the two-scale solver: inner algebraic zone with stochastic
  logatomic rules for nucleation on a P.syringae INP surface, outer
  Cahn-Hilliard phase-field for growth. Watch the c-axis emerge in the
  first 5 ms (imperceptibly fast at 1× playback; set speed to 0.01× to see).

solver:
  mode: "two_scale"
  analyticity_radius_nm: 1.5
  inner:
    n_sites: 500                            # water molecule graph size
    gillespie_rate_scale: 1.0
  outer:
    mode: "phase_field"
    grid: 48
    world_box_um: 600
    ch_interface_width_nm: 1.5              # ≥ r_a
    M_xi: 1e-6                              # Cahn-Hilliard mobility
    kappa_xi: 1e-15                         # gradient energy
    M_nu: 5e-7
  vapor: {enabled: true, jacobi_iters: 2}
  heat:  {enabled: true, jacobi_iters: 2}
  underwood: {enabled: true}

nucleus:
  type: M6                                  # P.syringae INP
  initial:
    inner_sites: "random_blob"              # irregular seed
    n_sites: 20
```

---

## Priority for implementation

Given the user's directive "start with #3":

1. **[ ] Design doc** — this one. **DONE.**
2. **[ ] OuterPhaseFieldZone** — Cahn-Hilliard for ξ on 48³ grid.
   Relatively standard. ~200 lines.
3. **[ ] InnerAlgebraicZone** — Gillespie stochastic simulation of a water-site
   graph. ~150 lines.
4. **[ ] UnderwoodBridge** — matching conditions. ~80 lines.
5. **[ ] Logatomic operator module** — encode LA1-LA5 + anchor, source, sink,
   bump, loopop, latder. ~120 lines.
6. **[ ] TwoScaleSolver** — top-level orchestrator. ~50 lines.
7. **[ ] Scenario schema v1.2** — parser updates. ~30 lines.
8. **[ ] Rendering** — visualize ξ iso-surface at ξ=0.5 (the effective "ice
   surface"); draw U-runner streamlines in the outer zone. ~150 lines.

Total ≈ 780 lines of new code + doc. Call it 2-3 focused sessions of work.

**Biggest risk**: numerical stability of Cahn-Hilliard with sharp interfaces.
Standard mitigation is an ADI (alternating-direction implicit) time-step or
semi-implicit Crank-Nicolson. Both doable but add code. Could start with
explicit Euler at small dt for proof-of-concept.

---

## Summary — what I've locked in conceptually

| Concern (yours) | Resolution |
|---|---|
| Start with #3 (full phase-field) | Yes — ξ + ν + c + T as the 4-field core |
| Fits in ZBU | Yes — ξ is log-of-density = UNDERWOOD magnitude; ν IS the UNDERWOOD irrep vector; coupling is the intertwining U·Z = B·U |
| Fits in logatomic | Yes — nucleation = LA3 (∇x⋈∇y = bump), growth = LA1 (sinks add), conservation = LA5 (∮ bump = 0) |
| Equipotential-shell singularity at small scale | Solved by analyticity-radius cutoff r_a ≈ 1.5 nm; shells only exist for r > r_a; inner zone is algebraic/discrete |
| Fully space-filling covering below r_a | Accepted as physical — use logatomic discrete operators inside, continuum outside, UNDERWOOD bridges |
| 2D manifold nucleation that grows | Modeled as bump operator creation + LA1 accumulation + LA5 conservation; physically as adatom Gillespie + Cahn-Hilliard |
| Radius of analyticity | r_a = max(ξ-front-width, molecular size, correlation length) ≈ 1.5 nm; pinned as a scenario parameter |
| Non-analytic phase transition | UNDERWOOD handles the essential singularity at σ=0 via log-ladder regularization — this is its defining role in ZBU |

The physics is now mappable one-to-one to ZBU's existing machinery. No new
operators needed — just careful use of the ones we already proved.

## Next step

Build OuterPhaseFieldZone (Cahn-Hilliard for ξ) as the first concrete piece.
It's the only one that has real numerical subtleties; once it works the rest
is plumbing. Want me to go?
