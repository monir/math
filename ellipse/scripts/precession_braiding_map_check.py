#!/usr/bin/env python3
"""Numerical check of the precession-braiding normal-form mapping."""

import math

# Ellipse-barrier coefficients
R0 = 7.0 * math.pi / 22.0
C = 7.0 * math.pi / 704.0

# Mercury constants/elements
G = 6.67430e-11
M_sun = 1.98847e30
c = 299_792_458.0
GM = G * M_sun
a = 5.790905e10
e = 0.205630
p = a * (1.0 - e * e)

# GR small parameter and exact 1PN precession formula
# eps_GR = 3GM/(c^2 p), Delta = 2*pi*eps_GR/(1-eps_GR)
eps_gr = 3.0 * GM / (c * c * p)
delta_gr = 2.0 * math.pi * eps_gr / (1.0 - eps_gr)

print("Precession-Braiding Map Check")
print("-----------------------------")
print(f"R0 = 7*pi/22               = {R0:.16e}")
print(f"C  = 7*pi/704              = {C:.16e}")
print(f"C/R0                       = {C/R0:.16e} (should be 1/32)")
print(f"1/32                       = {1/32:.16e}")
print()
print(f"eps_GR (Mercury)           = {eps_gr:.16e}")
print(f"Delta_GR per orbit (rad)   = {delta_gr:.16e}")
print(f"Delta_GR per orbit (arcsec)= {delta_gr*206264.80624709636:.12f}")
print()

# Equivalent braid depth x_eq via eps_B=x^2/32 = eps_GR
x_eq = math.sqrt(32.0 * eps_gr)
eps_b_eq = x_eq * x_eq / 32.0
delta_b_eq = 2.0 * math.pi * eps_b_eq

print(f"x_eq from eps_B=eps_GR     = {x_eq:.16e}")
print(f"eps_B(x_eq)                = {eps_b_eq:.16e}")
print(f"Delta_B at x_eq (rad)      = {delta_b_eq:.16e}")
print(f"Delta_B/Delta_GR           = {delta_b_eq/delta_gr:.16e}")
print()

print("Sample braid-side phase slips:")
print(f"{'x':>10} {'eps_B=x^2/32':>18} {'Delta_B=2pi eps_B (rad)':>26}")
for x in [1e-4, 5e-4, 1e-3, 2e-3, 1e-2]:
    eps_b = x * x / 32.0
    delta_b = 2.0 * math.pi * eps_b
    print(f"{x:10.4e} {eps_b:18.10e} {delta_b:26.10e}")
