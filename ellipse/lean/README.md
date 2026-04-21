# Lean 4 Proofs for the Ellipse Perimeter World Record

Machine-verified proofs of key identities and bounds using Lean 4 + Mathlib.

## Prerequisites

1. Install [elan](https://github.com/leanprover/elan) (the Lean version manager):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```
2. Lean 4 v4.28.0 will be installed automatically from `lean-toolchain`.

## Building

```bash
cd lean/
lake build
```

First build downloads Mathlib (~2 GB cache) and takes 5-15 minutes.
Subsequent builds are fast (seconds).

## Module Guide

### Sorry-Free (fully machine-verified)

| Module | Theorems | What it proves |
|--------|----------|---------------|
| **Basic.lean** | 26 | All continued-fraction identities (`q = 7/3`, `m = 81/25`, `n = 15`, `T = 1 - 7pi/22`), variable-chain equalities (`h`, `n_euler`, `z`, `phi`), fold identity, Gauss connection coefficient `kappa = 2/pi`, endpoint pin, budget constraint, MEPB coefficient `7/352` |
| **PiBounds.lean** | 4 | `22/7 > pi` (Niven bound), endpoint pin positivity and bounds |
| **GammaConnection.lean** | 2 | `Gamma(3/2) = sqrt(pi)/2`, Gauss summation value `Gamma(1)^2 / (Gamma(3/2) * Gamma(1/2)) = 2/pi` |

**Total: 32 theorems, 0 sorry.**

### Skeleton (in progress)

| Module | Theorems | Sorry count | What's missing |
|--------|----------|-------------|---------------|
| **Monotonicity.lean** | 10 | 7 | Leibniz integral rule, dominated convergence, MVT for strict convexity |
| **NonAnalyticBound.lean** | 6 | 6 | Analyticity class preservation, function-space boundedness arguments |

**Total: 16 theorems, 13 sorry.** These are standard analysis results available in Mathlib but require non-trivial plumbing to connect.

## What the Proofs Cover

The sorry-free modules verify the **algebraic backbone** of the paper:

- Every continued-fraction parameter (`q`, `m`, `n`, `T`) is derived from `pi`'s CF `[3; 7, 15, 1, 292, ...]`
- The variable chain `e -> h -> n_euler -> z -> phi` is exact (integer arithmetic)
- The MEPB coefficient `7*pi/704 = (7*pi/22) * 2^(-5)` factors as claimed
- The Gauss connection formula gives `kappa = 2/pi` exactly
- The endpoint pin `T = 1 - 7*pi/22 > 0` (using the Niven bound `22/7 > pi`)

The skeleton modules contain the **analytic core** — monotonicity of the elliptic integral and the non-analytic barrier bound. These are stated precisely but their proofs require Mathlib's integration and differentiation infrastructure.

## File Dependency Graph

```
EllipseProofs.lean
  +-- Basic.lean           (standalone, uses Mathlib.Analysis.SpecialFunctions.*)
  +-- PiBounds.lean        (imports Basic)
  +-- GammaConnection.lean (standalone, uses Mathlib.Analysis.SpecialFunctions.Gamma.*)
  +-- Monotonicity.lean    (imports Basic, skeleton)
  +-- NonAnalyticBound.lean (imports Basic, skeleton)
```
