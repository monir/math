# Snow Crystal 3D Defect Solver v2 Notes

Date: 2026-04-17

## Main Problems in v1

The old v1 solver had seven hard limitations:

1. Temperature structure was partly hand-shaped through explicit warm/cold
   shoulder functions.
2. The defect field was static geometry, not dislocation mechanics.
3. Transport was a single depletion field, not separate supersaturation and
   thermal transport.
4. Orientation physics was only a basal/prism blend.
5. Benchmark success depended partly on a kinetics-assisted classifier.
6. Numerics still used a toy periodic stencil and low-resolution defaults.
7. Validation focused mostly on habit labels.

## What v2 Changes

The v2 solver in `snow_crystal_phase_field_3d_defects_v2.py` replaces those
pieces with:

- a registry / roughening / resonance free-energy landscape for face kinetics
- dynamic dislocation lines with Burgers vectors and Peach-Koehler-like motion
- separate supersaturation `sigma(x,t)` and thermal `temp(x,t)` fields
- orientation weights over basal, prism, and pyramidal families
- morphology-only habit classification
- non-periodic stencils plus grid / timestep / transport / defect-motion checks

## Honest Status

v2 is more physical than v1 by construction, but it is still not the final
continuum truth of snow-crystal growth.

Current runtime artifact status from `snow_crystal_phase_field_3d_defects_v2.json`:

- training benchmark: `5/9`
- held-out benchmark: `4/5`
- validation tests: passing

That is worse on labels than the tuned v1 benchmark path, and that is the
expected tradeoff: v2 removed several benchmark-shaped hacks and replaced them
with more physical closures. It should be read as a better physics base, not as
the new best benchmark scorer.

What is better:

- no hand-inserted warm/cold shoulder functions in the face kinetics
- no static fake defect mask
- no periodic `np.roll` stencil
- no classifier using basal/prism kinetic ratio as an input
- broader validation than simple label matching

What is still not perfect:

- dislocation motion is still a reduced Peach-Koehler-like closure, not full
  crystal elasticity
- the phase-field still uses an Allen-Cahn-like interface update rather than a
  fully derived sharp-interface Stefan formulation
- orientation anisotropy is family-resolved, not a fully ab initio
  `gamma(n)` surface over the sphere
- transport is better than v1 but still reduced compared with a full
  vapor-flow + heat-flow + attachment-kinetics solver
- experimental validation remains far narrower than a true production model

## Sharp Summary

v1 was a strong prototype with obvious surrogate seams.

v2 is a materially more physical 3D solver:

- dynamic defects
- dual transport fields
- richer orientation physics
- morphology-first validation logic

It should be treated as the new base for future snow-crystal work, but not yet
as the final word on real snow-crystal dynamics.
