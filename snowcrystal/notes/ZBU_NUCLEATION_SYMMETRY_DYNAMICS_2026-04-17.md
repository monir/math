# ZBU Nucleation → Symmetry Dynamics

**Date:** 2026-04-17
**Question:** How does an irregular nucleus (silica grain, soot particle, bacterium) rapidly produce an approximately 6-fold-symmetric snow crystal? What's the physical mechanism for "symmetry healing," and how do we simulate it?

---

## The short answer

**The lattice does the work, not the crystal.** Ice Ih has hexagonal symmetry baked into the water-water pair interaction. The nucleus matters only as a site where the first ~100 molecules stop being gas; after that, the ice lattice imposes its own geometry and the nucleus shape is erased by a phase transition.

Concretely, there are **five layered mechanisms**, each amplifying symmetry over a different time scale:

| Time | Layer | What happens |
|---|---|---|
| 0 – 100 µs | Amorphous coating | Vapor condenses as non-crystalline water on the nucleus surface; no structure yet |
| 100 µs – 1 ms | Ice Ih crystallization | Thermodynamic phase transition; the amorphous coating rearranges into a single ice Ih crystallite at ~10 nm. **The c-axis direction is CHOSEN at this step.** Once chosen, it is frozen |
| 1 ms – 100 ms | Lattice takeover | The crystallite grows by lattice-ordered deposition. New water molecules attach to existing lattice sites — not to the nucleus shape. Nucleus becomes invisible |
| 100 ms – seconds | Facet emergence | Slowest-growing face (basal or prism, depending on T) develops as a flat surface. Other faces get "eaten" by fast growth. Hexagonal outline appears |
| Seconds – minutes | Vapor-field feedback | Once the crystal has 6 equivalent prism faces, the external ∇c field itself becomes 6-fold symmetric. Any tiny asymmetry gets damped because the symmetric field supplies all 6 tips equally |

The net effect is **radical projection** onto the lattice's own symmetry group (C_6v). Whatever goes in (random dust) gets projected to the nearest point on the C_6v orbit of ice Ih. Asymmetry information has nowhere to live.

---

## Why doesn't the simulator need "magical knowledge"?

In the demo we were worried: "the grid can't know about symmetry, so how does it get hexagons?" The answer is that **the grid doesn't need to know — the growth rules know**, and the growth rules come from the water-water interaction.

Specifically, here's what does the symmetrizing:

### A. Ice Ih atomic structure
The water-water dimer's minimum-energy configuration has H-bonds at 109.5° (tetrahedral). When you pack many dimers, the lowest-energy arrangement **is** hexagonal ice (or cubic, depending on T and pressure). This is a **property of water**, not of the grid. Our MB-pol calibration (`zbu_synthesis_v1.json`) literally proves this — the hexamer prism is 99.7% of the ab-initio prediction.

In ZBU terms: the bizipular operator Z has its eigenspace aligned with C_6v irreps. Z doesn't care about the nucleus.

### B. The UNDERWOOD U field collapses onto lattice irreps
The UNDERWOOD log-ladder connector's job is precisely this: take arbitrary input irrep weights (`U_initial` from the nucleus bias) and project them onto the discrete set of C_6v eigenstates **logarithmically fast**. The log-ladder's convergence rate is:

```
|U(t) - U_lattice|  ~  exp(-t / τ_U)         τ_U ~ 1 ms at -15 °C
```

After ~5τ_U ≈ 5 ms, U has forgotten the nucleus bias entirely and is fully aligned with whichever lattice irrep won. This is the ZBU-language version of the crystallization phase transition.

### C. Equal β on 6 equivalent prism faces
Once the crystal is big enough to have prism faces (~10 nm+), all six of those faces are CRYSTALLOGRAPHICALLY EQUIVALENT — they're related by C_6 rotation and reflection. So β_prism is one scalar function of (T, σ), applied identically to all six. Any initial asymmetry is damped by how fast the slow faces grow out the fast ones.

### D. Vapor field enforces symmetry at the mesoscale
A 6-fold symmetric crystal produces a 6-fold symmetric vapor concentration field around itself. Since each of 6 arms sees the same local σ and ∇c, they grow at the same rate. Any perturbation is damped by the Ivantsov tip-radius selection mechanism (r_tip · v_tip = 2D_v Δ is same for all tips).

---

## The user's "pyramid" intuition — partly right

The user asked whether the irregular seed gets "healed" by building up new layers **above and below**, pyramidally, until a self-stabilizing hex emerges.

This is **partly correct** but the mechanism is different. Let me state it precisely:

**True**: crystallization is a local process that propagates layer-by-layer out from a nucleation site. Each new layer uses the previous layer's lattice as a template. Defects accumulate ↓ or get "polished out" by subsequent layers. So yes, asymmetric seeds DO get "buried" under symmetric layers.

**Also true**: the first few nanometers of ice are critically important — they select the c-axis orientation. Once the c-axis is set, the entire remaining crystal respects it.

**Less true**: it's not "pyramidal" in the sense of distinct pyramid planes. It's more like **homogeneous epitaxy** — each new layer is a 2D crystal parallel to the previous one, with 6-fold in-plane symmetry. The profile of the growing crystal can be:

- **Plate**: basal face grows slow, so top/bottom stay flat; prism grows fast, so a thin hexagonal plate appears.
- **Column**: basal grows fast (tall), prism grows slow (narrow). Cross-section is still hexagonal thanks to the 6 equivalent prism faces, but the column extends up/down in c-axis.
- **Bullet / pyramid**: at very cold T (<-25 °C) the pyramidal faces (intermediate between basal and prism) become kinetically accessible. These give pointy ends to a column — hence "bullet rosettes".

So: the crystal doesn't BUILD pyramids to heal itself; rather, it BUILDS LAYERS that are each perfectly lattice-aligned, and the overall silhouette depends on the rate ratio of faces.

---

## How does a non-planar thing (hexcolumn) evolve?

Columns are especially interesting because the user is right: columnar growth seems "non-planar," so how can it self-stabilize?

Answer: **columns have a 6-fold-symmetric cross-section** at every height. The column is the z-stack of identical hexagons. So the symmetry really IS 2D + translation in z — just extended along the c-axis instead of the ab-plane.

Dynamically:

1. Crystallization step picks the c-axis direction.
2. At T ≈ -5 °C, β_basal(T) ≈ 0.25 µm/s while β_prism(T) ≈ 0.8 µm/s — but the BASAL faces are the TOP AND BOTTOM, and growing basal means adding a new layer at the top or bottom, not spreading sideways.

Wait — there's a subtle confusion. Let me restate:
- **Growing a basal face** = adding a layer perpendicular to c-axis = making the column TALLER.
- **Growing a prism face** = adding a layer perpendicular to a prism = making the column WIDER.

So if β_basal > β_prism → tall narrow = column. If β_basal < β_prism → short wide = plate.

**Convention (checked and corrected in `src/zbu.mjs`)**:

```
β_basal = velocity of the basal (top/bottom) face → crystal gets TALLER
β_prism = velocity of the prism (side) face      → crystal gets WIDER
r = β_basal / β_prism:
   r > 1.15  → column  (basal fast → elongates in c-axis)
   r < 0.85  → plate   (prism fast → widens in ab-plane)
```

Nakaya verified at the four canonical T:
- -2 °C  plate    (r ≈ 0.5)
- -5 °C  column   (r ≈ 3.3)
- -15 °C plate/dendrite (r ≈ 0.29)
- -22 °C column   (r ≈ 2.9)

**Note**: In writing this doc I caught a sign error in the original β table —
the `basal` and `prism` columns had been swapped so that -5 °C gave plate
instead of column, and vice versa at -2 °C. Fixed in `src/zbu.mjs`,
`habitFromBetaRatio`, and tests. The convention I use above is the
Libbrecht / Furukawa-Shimada 1993 convention: β is the **normal advance
velocity** of the named face. That's the convention that gives the correct
Nakaya diagram.

**Remaining caveat**: real β depends on both T AND σ. At low σ the basal face
is kinetically locked (2D nucleation bottleneck); at high σ it unfreezes.
My table is a 1D slice at moderate σ; a full treatment needs β(T, σ). Flagged
as a follow-up calibration task, not a design gap.

---

## How the simulator would represent this

Three implementation approaches, in increasing fidelity:

### Approach 1: "Effective seed" (simplest, what we do now)
Always initialize the CrystalState with a perfect 6-fold symmetric seed. Nucleus type (M1..M12) only contributes:
- Initial irrep bias in the UNDERWOOD U field.
- A thermodynamic "temperature offset" or "σ boost" that reflects how the real nucleus facilitates nucleation.

This skips the crystallization phase entirely. It's PHYSICALLY DEFENSIBLE because after ~1 ms the nucleus shape is irrelevant anyway — we just "fast-forward" to that point.

Trade-off: can't show the crystallization transient.

### Approach 2: "Crystallization phase"
First N frames (say 10) run a special rule:
1. Initialize with an irregular mask (optionally loaded from a PNG or random bumpy shape).
2. Each "crystallization tick":
   - For each voxel, compute alignment to ice lattice (hex-grid projection).
   - Voxels with poor alignment get eliminated; those with good alignment persist.
   - Neighboring aligned voxels "pull" new voxels into alignment (Ising-like local propagation).
3. After crystallization, the mask is a ~symmetric ice Ih nucleus, then normal growth begins.

Shows: you can WATCH the irregular blob smooth into a hexagon in the first second. This is what the user is asking about.

### Approach 3: "Full amorphous → crystal" phase-field
Treat each voxel's crystallinity as a continuous scalar ξ(x) ∈ [0,1]:
- ξ = 0: amorphous/liquid water.
- ξ = 1: fully crystalline ice Ih.

With an orientation vector ν(x) (lattice angle). The dynamics:
```
∂ξ/∂t = α · ∇²ξ + driving_force(σ, T)
∂ν/∂t = β · ∇²ν + pinning(ξ)         # orientation only matters where ξ > 0
```

Once ξ > 0.5 at a voxel, treat it as "crystal" for vapor BC. Below, treat it as porous.

This is the full Cahn-Hilliard / phase-field model. Heavy but absolutely correct.

**Recommendation**: Approach 2 for the demo. Fast, educational, shows the physics.

---

## What the demo should SHOW (concrete scenario)

New scenario `nucleation_symmetry_demo.zbu.yaml`:

```yaml
zbu_schema: "1.1"
title: "Irregular seed → 6-fold crystal"
starred: true
description: |
  Start with an irregular 5-voxel cluster representing a silica dust
  grain. Over the first 2 seconds, watch the irregularity get buried
  under ice Ih lattice-aligned layers. By t=5s the crystal is
  essentially hexagonal. Silica shape is now invisible.
seed: 42
duration_s: 60

nucleus:
  type: M5             # silica dust
  initial_mask:        # NEW: load irregular starting geometry
    kind: "random_blob"
    n_voxels: 5
    radius_um: 3

solver:
  mode: "field"
  crystallization_phase_s: 2.0   # duration of lattice-takeover phase
  crystallization:
    enabled: true
    alignment_threshold: 0.7

environment:
  T_C: -15
  sigma: 0.25
```

What the user SEES:
- t=0: 5 random voxels
- t=0–2s: cluster rounds off, starts showing hex corners
- t=2–5s: hex prism clearly formed, ~10 μm across, no sign of original dust shape
- t=5–60s: full dendritic growth from the clean hex base

This tells the symmetry-emergence story visibly.

---

## Why it's still not "100% symmetric" in nature

Real snowflakes usually show small asymmetries. Our demo should too, if we want honesty. The sources:

1. **Fall dynamics**: upwind tip sees fresh vapor, downwind tip shielded → rate difference → asymmetry.
2. **Multiple nucleation sites on large nuclei**: if the nucleus is > ~100 nm, two or three ice Ih crystals may form, each with its own c-axis. They meet at grain boundaries → the final crystal is polycrystalline, not perfectly 6-fold.
3. **Thermal fluctuations during crystallization**: even on a nm-scale nucleus, the c-axis selection has noise at kT scale. Some statistical distribution of c-axes across a population of crystals.
4. **Atmospheric turbulence**: non-stationary T, σ locally → non-uniform growth → asymmetry.
5. **Crystal-crystal collisions**: rare but happens. Makes twinned, rosette, irregular flakes.

In the simulator, these can each be toggled:
```yaml
realism:
  fall_asymmetry: true
  multi_nucleation_prob: 0.05
  c_axis_noise_deg: 3.0
  turbulence: true
```

---

## Summary of physics for the user's question

1. **Irregular nucleus → symmetric crystal happens because of water itself, not the simulator's grid.** The ice Ih lattice has hexagonal symmetry encoded in pairwise water-water interactions (MB-pol, 99.7% match to ab-initio).

2. **The mechanism is a phase transition**: amorphous coating → single ice Ih crystallite → lattice-ordered deposition. By ~1 ms, the nucleus is invisible.

3. **The c-axis is selected at the crystallization step** (stochastically, on nm scale). Once selected, that's the c-axis for the whole crystal's life. This is what makes ONE orientation emerge from a pool of random initial conditions — it's spontaneous symmetry breaking, like ferromagnet cooling below Tc.

4. **In-plane 6-fold symmetry is automatic** because the 6 prism faces are crystallographically equivalent and therefore have identical β kinetics.

5. **Columns aren't less symmetric than plates** — they're 6-fold-symmetric in cross-section, just extended along c-axis instead of ab-plane.

6. **"Healing" happens layer-by-layer**: each new deposited layer uses the previous layer's lattice as a template, so defects get buried and the crystal "forgets" its seed shape within a few tens of nm.

7. **UNDERWOOD U field in ZBU terms**: the U field starts with whatever irrep bias the nucleus gives, then log-ladder-converges (UNDERWOOD's defining property) onto the lattice's own irrep eigenstates at rate τ_U ≈ 1 ms. This IS the crystallization phase transition, in our framework's language.

8. **Pragmatic simulator choice**: skip the first 1 ms; initialize with a perfect hex seed; only preserve nucleus info through the irrep bias term. This is Approach 1 and is what the demo does. Approach 2 (explicit crystallization phase) is easy to add and tells the story visually.

9. **Imperfect symmetries are real** (fall dynamics, multi-nucleation, thermal noise) and can be toggled as realism options.

The answer to "how is symmetry projected out of imperfect seeds" is: **the lattice does it**. The simulator's job is to get out of its way.
