#!/usr/bin/env python3
"""
zipularity_crystal_scan_v2.py — Fixed scan with proper polynomial handling
==========================================================================

v1 found individual zipularity classification but failed on Hadamards due
to fraction field issue. v2 fixes by re-guessing the Hadamard from the
computed sequence (guarantees polynomial coefficients).

Key findings from v1:
- Gold S₁: Q(√5), growth φ⁵ ≈ 11.09
- Silver S₂: Q(√2), growth (1+√2)⁴ ≈ 33.97
- Franel Σ C³: Q (rational!), growth 8, roots {8, -1}
- Calkin Σ C⁴: Q (rational!), growth 16, roots {16, -4}
- Bronze Σ C·C: Q(√2), growth 3+2√2 ≈ 5.83, roots {3+2√2, 3-2√2}

PREDICTIONS (from DNA model):
- Gold ⊗ Silver: needs Q(√5)·Q(√2) = Q(√5, √2) → already proved irreducible
- Bronze ⊗ Silver: BOTH in Q(√2) → compositum is Q(√2), char poly stays in Q(√2)!
  → This pair may unwind (DNA unwinds within Q(√2))
- Franel ⊗ Silver: Franel is rational, Silver is Q(√2) → compositum is Q(√2)
  → Hadamard char poly is in Q(√2); may factor nicely
- Franel ⊗ Calkin: BOTH rational → Hadamard eigenvalues all in Q
  → Char poly factors over Q; operator may factor over Q directly!

Author: GUT Research, 13 Apr 2026
"""
import time
t0 = time.time()

from sage.all import (QQ, ZZ, NumberField, binomial, PolynomialRing, factor,
                       QQbar, prod, squarefree_part)
from ore_algebra import OreAlgebra, guess

print("=" * 70)
print("ZIPULARITY CRYSTAL SCAN v2 — focus on Bronze×Silver, Franel×Calkin")
print("=" * 70, flush=True)

N_TERMS = 120

def gold_sum(n):
    return sum(binomial(n,k)**2 * binomial(n+k,k) for k in range(n+1))
def silver_sum(n):
    return sum(binomial(n,k)**2 * binomial(n+k,k)**2 for k in range(n+1))
def franel_sum(n):
    return sum(binomial(n,k)**3 for k in range(n+1))
def calkin_sum(n):
    return sum(binomial(n,k)**4 for k in range(n+1))
def bronze_sum(n):
    return sum(binomial(n,k) * binomial(n+k,k) for k in range(n+1))

candidates = [
    ("Gold", gold_sum),
    ("Silver", silver_sum),
    ("Franel", franel_sum),
    ("Calkin", calkin_sum),
    ("Bronze", bronze_sum),
]

Rn = PolynomialRing(QQ, 'n')
n_var = Rn.gen()
A_qq = OreAlgebra(Rn, 'Sn')
Sn_qq = A_qq.gen()

# ── Precompute sequences ──
print("\n--- Computing sequences ---", flush=True)
seqs = {}
for name, fn in candidates:
    seqs[name] = [QQ(fn(n)) for n in range(N_TERMS)]
    print(f"  {name}: {N_TERMS} terms computed")

# ── Test KEY PAIRS ──
print("\n--- Testing Hadamard products ---", flush=True)

key_pairs = [
    ("Bronze", "Silver"),    # both Q(√2)
    ("Franel", "Silver"),    # Q, Q(√2) → Q(√2)
    ("Franel", "Calkin"),    # both Q → Q
    ("Gold", "Silver"),      # Q(√5), Q(√2) → already proved irreducible
    ("Bronze", "Gold"),      # Q(√2), Q(√5) → Q(√10) likely
    ("Franel", "Gold"),      # Q, Q(√5) → Q(√5)
    ("Calkin", "Silver"),    # Q, Q(√2) → Q(√2)
    ("Bronze", "Bronze"),    # both Q(√2) — narcissistic
]

def analyze_hadamard(nameA, nameB, seqA, seqB):
    print(f"\n═══ {nameA} ⊗ {nameB} ═══")
    had_seq = [seqA[n] * seqB[n] for n in range(N_TERMS)]

    # Try to guess operator at various orders
    L_had = None
    for ord in [2, 3, 4, 5]:
        try:
            L_try = guess(had_seq, A_qq, order=ord)
            if L_try.order() == ord:
                # Verify
                coeffs = [L_try[j] for j in range(ord + 1)]
                errs = 0
                for nn in range(1, min(N_TERMS - ord - 3, 80)):
                    val = sum(coeffs[j](n=nn) * had_seq[nn+j] for j in range(ord+1))
                    if val != 0:
                        errs += 1
                if errs == 0:
                    L_had = L_try
                    break
        except Exception as e:
            continue

    if L_had is None:
        print(f"  Could not find operator")
        return None

    ord_h = L_had.order()
    deg_h = L_had.degree()
    print(f"  L: order {ord_h}, degree {deg_h}")

    # Char poly
    coeffs = [L_had[j] for j in range(ord_h + 1)]
    leads = [c.leading_coefficient() for c in coeffs]

    Rx = PolynomialRing(QQ, 'x')
    x = Rx.gen()
    char_poly = sum(leads[j] * x**j for j in range(ord_h + 1))

    # Factor over QQ
    char_fact_Q = char_poly.factor()
    print(f"  Char(L): {char_poly}")
    print(f"  Factored over Q: {char_fact_Q}")

    # If already factors over Q, check operator factoring
    if all(f.degree() <= ord_h // 2 for f, m in char_fact_Q):
        print(f"  → Char poly splits over Q; test operator factoring")

        # Test right_factors()
        try:
            rf = L_had.right_factors()
            print(f"  L.right_factors() over QQ: found {len(rf)} factor(s)")
            for i, r in enumerate(rf):
                print(f"    Factor {i+1}: order {r.order()}")
                print(f"    {r}")
        except Exception as e:
            print(f"  right_factors over QQ: {type(e).__name__}: {e}")

    # Find splitting field
    Rx_ext = PolynomialRing(QQ, 'xx')
    xx = Rx_ext.gen()

    best_field = None
    best_fact = None
    for d in [2, 3, 5, 6, 7, 10, 11, 13, 15]:
        try:
            K = NumberField(xx**2 - d, 'sd')
            char_K = char_poly.change_ring(K)
            fact_K = char_K.factor()
            max_deg = max(f.degree() for f, m in fact_K) if fact_K else 999
            if max_deg <= ord_h // 2:
                # char poly fully splits into degree ≤ ord/2 pieces
                best_field = d
                best_fact = fact_K
                break
        except:
            continue

    if best_field is not None:
        print(f"  Splits over Q(√{best_field}): {best_fact}")

        # Test polynomial factoring of L₄ and L₀ over Q(√d)
        K = NumberField(xx**2 - best_field, 'sd')
        L4 = coeffs[ord_h].change_ring(K)
        L0 = coeffs[0].change_ring(K)

        L4_fact = L4.factor()
        L0_fact = L0.factor()
        print(f"  L_leading (deg {L4.degree()}) factored: {L4_fact}")
        print(f"  L_trailing (deg {L0.degree()}) factored: {L0_fact}")

        max_L4_irred = max(f.degree() for f, m in L4_fact) if L4_fact else 0
        max_L0_irred = max(f.degree() for f, m in L0_fact) if L0_fact else 0

        if max_L4_irred <= ord_h // 2 and max_L0_irred <= ord_h // 2:
            print(f"  ★ POTENTIAL UNWIND: all L₄, L₀ factors have degree ≤ {ord_h // 2}")
            return (nameA, nameB, 'unwind_candidate', best_field)
        else:
            print(f"  ✗ Blocked: irreducible deg {max(max_L4_irred, max_L0_irred)} factor")
            return (nameA, nameB, 'blocked_leading_coeff', best_field)
    else:
        print(f"  ✗ Char poly doesn't split over tested quadratics")
        return (nameA, nameB, 'char_unsplit', None)

results = []
for nameA, nameB in key_pairs:
    try:
        r = analyze_hadamard(nameA, nameB, seqs[nameA], seqs[nameB])
        if r:
            results.append(r)
    except Exception as e:
        print(f"\n  {nameA} ⊗ {nameB}: failed — {type(e).__name__}: {e}")
        import traceback; traceback.print_exc()

# Summary
print("\n\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
unwinds = [r for r in results if r[2] == 'unwind_candidate']
print(f"\nUnwind candidates: {len(unwinds)}")
for r in unwinds:
    print(f"  ★ {r[0]} ⊗ {r[1]}  unwinds over Q(√{r[3]})")

blocked = [r for r in results if r[2] == 'blocked_leading_coeff']
print(f"\nBlocked (leading coeff has irreducible factor): {len(blocked)}")
for r in blocked:
    print(f"  {r[0]} ⊗ {r[1]}  char splits over Q(√{r[3]}), but operator blocked")

unsplit = [r for r in results if r[2] == 'char_unsplit']
print(f"\nChar poly doesn't split over tested quadratics: {len(unsplit)}")
for r in unsplit:
    print(f"  {r[0]} ⊗ {r[1]}")

elapsed = time.time() - t0
print(f"\nDONE [{elapsed:.1f}s]")
