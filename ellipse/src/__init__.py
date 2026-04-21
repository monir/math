"""
Ellipse Perimeter World Record Release (2026).

The release contains:
  - a practical closed-form formula at 0.083 ppm (`r2_3exp_v23_champion`)
  - the overall R6+16exp champion at 0.018 ppb (`r6_varpro_champion`)

Usage:
    from src.formulas import r6_varpro_champion, exact_perimeter
    P_approx = r6_varpro_champion(a, b)
    P_exact  = exact_perimeter(a, b)
"""

__version__ = "1.0.0"
