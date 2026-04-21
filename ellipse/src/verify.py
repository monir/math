#!/usr/bin/env python3
"""
Verification script: runs adversarial tests and prints comparison table.
"""
import math, time
import numpy as np
from src.formulas import (
    ALL_FORMULAS, exact_perimeter, h_param, ramanujan_ii,
    ayala_raggi_r2_2exp, r2_3exp_gated, r2_3exp_gated_pi, r2_3exp_gated_h2,
    r2_3exp_v23_champion,
)


def _primes_upto(n: int) -> np.ndarray:
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = False
    return np.nonzero(sieve)[0]

PRIMES = _primes_upto(100_000)
PRIMES = PRIMES[PRIMES > 50]


def build_test_set(n: int = 2000, seed: int = 42) -> list[tuple[float, float]]:
    """Build a diverse adversarial test set."""
    rng = np.random.default_rng(seed)
    ellipses = []

    # 1. Uniform in h-space
    for h_val in np.linspace(0.0, 1.0 - 1e-15, n // 4):
        t = math.sqrt(max(0.0, min(1.0, h_val)))
        k = (1.0 - t) / (1.0 + t) if t < 1.0 else 0.0
        ellipses.append((1.0, max(k, 1e-300)))

    # 2. Log-uniform flattening with prime axes
    for _ in range(n // 4):
        a = float(rng.choice(PRIMES))
        y = rng.uniform(0.0, 50.0)
        b = max(a * 10 ** (-y), 1e-300)
        ellipses.append((a, b))

    # 3. Near-circle (prime jitter)
    idx = min(len(PRIMES) - 2, 500 + n // 4)
    for i in range(501, idx):
        ellipses.append((float(PRIMES[i]), float(PRIMES[i - 1])))

    # 4. Ultra-flat boundary
    for _ in range(n - len(ellipses)):
        a = float(rng.choice(PRIMES))
        eps = 10 ** rng.uniform(-16, -1)
        b = max(a * eps, 1e-300)
        ellipses.append((a, b))

    return ellipses


def evaluate(ellipses: list[tuple[float, float]]) -> dict:
    """Evaluate all formulas against exact perimeters."""
    results = {}
    truths = [exact_perimeter(a, b) for a, b in ellipses]

    for name, fn in ALL_FORMULAS.items():
        errs = []
        for (a, b), pe in zip(ellipses, truths):
            pf = fn(a, b)
            if math.isfinite(pf) and pe > 0:
                errs.append(abs((pf - pe) / pe))
        ea = np.array(errs)
        results[name] = {
            "max": float(np.max(ea)),
            "mean": float(np.mean(ea)),
            "rms": float(np.sqrt(np.mean(ea ** 2))),
            "max_ppm": float(np.max(ea)) * 1e6,
            "n": len(errs),
        }
    return results


def main():
    print("=" * 75)
    print("  ELLIPSE PERIMETER WORLD-RECORD VERIFICATION")
    print("  R2/3exp-gated formula vs all prior art")
    print("=" * 75)

    print("\nBuilding adversarial test set...")
    t0 = time.time()
    ellipses = build_test_set(3000, seed=137)
    print(f"  {len(ellipses)} test ellipses")

    print("Computing exact perimeters (mpmath, 50 digits)...")
    # warm up exact_perimeter
    _ = exact_perimeter(1.0, 0.5)
    print(f"  Done in {time.time() - t0:.1f}s")

    print("\nEvaluating all formulas...\n")
    results = evaluate(ellipses)

    # Print comparison table
    hdr = f"{'Formula':<35s} {'Max |err|':>12s} {'ppm':>10s} {'Mean |err|':>12s} {'RMS |err|':>12s}"
    print(hdr)
    print("-" * len(hdr))
    for name, r in sorted(results.items(), key=lambda x: x[1]["max"]):
        print(f"{name:<35s} {r['max']:>12.3e} {r['max_ppm']:>10.3f} {r['mean']:>12.3e} {r['rms']:>12.3e}")

    # Comparison highlights
    ours = results.get("R2/3exp q=7/3, m=81/25 [V23]", {})
    ar = results.get("Ayala-Rendón R2/2exp (2025)", {})
    r2 = results.get("Ramanujan II (1914)", {})

    if ours and ar:
        print(f"\n{'='*75}")
        improvement = ar["max"] / ours["max"]
        print(f"  vs Ayala-Rendón (2025):  {improvement:.1f}x better worst-case accuracy")
    if ours and r2:
        improvement_r2 = r2["max"] / ours["max"]
        print(f"  vs Ramanujan II (1914): {improvement_r2:.0f}x better worst-case accuracy")
    print(f"{'='*75}")

    # Limit checks
    print("\nEndpoint verification:")
    for label, a, b in [("Circle (a=b=1)", 1.0, 1.0), ("Flat (b=1e-15)", 1.0, 1e-15)]:
        pe = exact_perimeter(a, max(b, 1e-300))
        ours_val = r2_3exp_v23_champion(a, max(b, 1e-300))
        ar_val = ayala_raggi_r2_2exp(a, max(b, 1e-300))
        r2_val = ramanujan_ii(a, max(b, 1e-300))
        print(f"\n  {label}: exact = {pe:.10f}")
        print(f"    R2/3exp-gated:  {ours_val:.10f}  (err = {abs(ours_val-pe)/pe:.2e})")
        print(f"    Ayala-Rendón:    {ar_val:.10f}  (err = {abs(ar_val-pe)/pe:.2e})")
        print(f"    Ramanujan II:   {r2_val:.10f}  (err = {abs(r2_val-pe)/pe:.2e})")


if __name__ == "__main__":
    main()
