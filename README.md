# monir/math — central distribution point for Monir Mamoun's mathematical research

> *Hard, classical problems — solved with explicit formulas, every coefficient written out, every proof checkable, every number reproducible.*

This repository is the public umbrella for **Monir Mamoun**'s
mathematical-research output.  It is laid out as **one folder per
mega-topic**; each folder is self-contained (its own paper, code,
scripts, Lean modules) and links back here.  The umbrella site at
[monir.github.io/math](https://monir.github.io/math) is the visitor's-eye
view; this README is the contributor's-eye view.

---

## Recent updates

> [!TIP]
> **2026-04-27 — [NEW] Top-level README is now data-driven; first dated changelog at the top**
>
> The top-level README is now generated from a single master YAML data
> file (`infra/publishing/sources/monir_math_repo.yaml` in the upstream
> master) by a renderer (`render_monir_math_readme.py`).  Future README
> updates are made by prepending entries to that file's `update_log`,
> bumping the topics table, and prepending to the papers directory; old
> entries stay verbatim, so this section reads newest-at-top with full
> history preserved.  The same publish mechanism that handles paper
> releases now also drift-audits all declared downstream copies (e.g.,
> a Zenodo deposit bundle) after every publish and refuses to silently
> overwrite drifted files.
>
> Commits: [`b77f053`](https://github.com/monir/math/commit/b77f053) (data-driven README first publish) · [`82573e88`](https://github.com/gitscratch/ellipse/commit/82573e88) (renderer + master YAML) · [`50f3551d`](https://github.com/gitscratch/ellipse/commit/50f3551d) (drift check on downstream copies)

> [!NOTE]
> **2026-04-27 — [UPDATE] rev4 abstract aligned with the deposited Logatoms slice**
>
> The rev4 abstract's description of the companion Lean Logatoms
> package now matches the slice deposited with the paper:
> 5 modules, 37 named declarations, sorry-free and axiom-free against
> Mathlib v4.28.0, covering the logatom primitives, the Odrzywołek-EML
> grammar with its Catalan-number tree count, the Gram-matrix structure
> of the augmented basis, the master Gamma-moment identity, and the
> depth-stratified multidepth ladder.  The Φ-bijection and the
> Heisenberg-commutator [T, D] = -I modules are described as forthcoming
> in an integrated logatom library.
>
> Commits: [`414389b`](https://github.com/monir/math/commit/414389b) (rev4 abstract update)

> [!TIP]
> **2026-04-27 — [NEW] First publication of UNDERWOOD rev4 + Snow-Crystal Paper V to monir/math**
>
> Two-commit publication of (1) UNDERWOOD ellipse-perimeter rev4 (the
> Definitive Second Breakthrough, 136 pp) to ellipse/, and (2) Snow-
> Crystal Paper V Unified Theory v2 (14 April 2026, 25 pp) to
> snowcrystal/.  Top-level README added.  Manifest-driven publishing
> mechanism live at gitscratch/ellipse:infra/publishing/.
>
> Commits: [`4a9ca89`](https://github.com/monir/math/commit/4a9ca89) (UNDERWOOD rev4 (initial publication)) · [`da68918`](https://github.com/monir/math/commit/da68918) (Snow Crystal Series Paper V) · [`bf36e9f`](https://github.com/monir/math/commit/bf36e9f) (Top-level README first publication)

---

## At a glance — the active research areas

| Topic | Folder | Latest publication | Headline |
|---|---|---|---|
| **Ellipse perimeter** | [`ellipse/`](./ellipse/) | rev4, 27 April 2026 (136 pp) | **UNDERWOOD — the Definitive Second Breakthrough in Closed-Form Approximator Models.** **3.3 parts-per-trillion at 13 stored constants** (F3); 2.1 × 10⁻¹³ relative error at 14 (F4 + Remez). Beats SRIRACHA by **2×** and the Ramanujan / Cantrell / Ayala–Raggi / AAA lines by **10⁴–10⁸×** at every matched parameter budget. **147,000×** better than AAA on the L-shaped corner singularity. Walsh–Bernstein **separation theorem**: the gap vs any rational method grows without bound. |
| **Snow-crystal physics** | [`snowcrystal/`](./snowcrystal/) | Paper V (Unified Theory v2), 14 April 2026 (25 pp) | **First-principles unified theory of snow-crystal formation**, MB-pol(2023) quantum chemistry through Kobayashi 1993 phase-field PDE. Predicts ice-face splitting Δ_split = 8.94 ± 0.46 cm⁻¹ vs THz-measured 8.80 (**0.30σ**). Recovers the Mason 1:2:3 cyclotomic ratio at −4 / −10 / −22 °C. Lean-verified hexagonal factor R_hex = 4/(4+√3) = (16−4√3)/13 exact. **7/8** historical predictions confirmed (Murata 2020, Sazaki 2012, Bailey-Hallett 2004, Kobayashi 1976). 6 new falsifiable predictions. Spans 10 orders of magnitude in length, 30 in time. |

---

## Biggest results, by area

### Ellipse perimeter — ellipse/

**UNDERWOOD — the Definitive Second Breakthrough in Closed-Form Approximator Models.**
**3.3 parts-per-trillion at 13 stored constants** (F3); 2.1 × 10⁻¹³ relative error at 14 (F4 + Remez).
Beats SRIRACHA by **2×** and the Ramanujan / Cantrell / Ayala–Raggi / AAA lines by **10⁴–10⁸×**
at every matched parameter budget.  **147,000×** better than AAA on the L-shaped corner singularity.
Walsh–Bernstein **separation theorem**: the gap vs any rational method grows without bound.

**Interactive demo:** <https://monir.github.io/math/ellipse/>

The ellipse perimeter has a **logarithmic branch point** at the
degeneracy limit `b → 0` (the ellipse collapses to a segment).
For 2500 years every compact-formula approximator has been fitting
a *smooth* function to this *non-smooth* target.  UNDERWOOD writes
the log modes explicitly: three named log companions
`ξ^{2+j}·log(1/ξ)` added to a Chebyshev basis, a QR solve, done.
The residual becomes analytic; Chebyshev handles it at geometric
rate; the floor falls.

Mathematical contribution beyond the number:
(i) the **logatom** primitive `M^j_α(ξ) = ξ^α (log(1/ξ))^j`,
with closed-form Gamma moment `j!/(α+1)^{j+1}` and minimality
under the Heisenberg ladder;
(ii) the **Odrzywołek-EML** substrate (Sheffer stroke for elementary
functions, arXiv:2603.21852);
(iii) the **Walsh-Bernstein separation theorem** ruling out
super-geometric rational approximation of any non-removably-singular
target.

Lean: the deposited Logatoms slice is **5 modules, sorry-free and
axiom-free against Mathlib v4.28.0**; full library forthcoming.

### Snow-crystal physics — snowcrystal/

**First-principles unified theory of snow-crystal formation**, MB-pol(2023)
quantum chemistry through Kobayashi 1993 phase-field PDE.
Predicts ice-face splitting Δ_split = 8.94 ± 0.46 cm⁻¹ vs THz-measured 8.80 (**0.30σ**).
Recovers the Mason 1:2:3 cyclotomic ratio at −4 / −10 / −22 °C.
Lean-verified hexagonal factor R_hex = 4/(4+√3) = (16−4√3)/13 exact.
**7/8** historical predictions confirmed (Murata 2020, Sazaki 2012, Bailey-Hallett 2004, Kobayashi 1976).
6 new falsifiable predictions.  Spans 10 orders of magnitude in length, 30 in time.

The series comprises five papers (I-V), with **Paper V** as the
canonical headline that combines and supersedes the rest:
  - Paper I: THz Spectroscopy of Ice Faces
  - Paper II: Phonon Dispersion of Ice I_h
  - Paper III: The Snowflake Equation (current iterate: snow_crystal_equation_v6)
  - Paper IV: Snow-Crystal Splitting Equation
  - **Paper V (★)** Unified Theory — twinning, Hamiltonian hierarchy,
    phase-field morphology, 6 falsifiable predictions.
Companion: Crystal-Math θ-means series (parts 1, 2, 3 + UNDERWOOD addendum).

---

## Reproduce the headline numbers

```bash
git clone https://github.com/monir/math
cd math

# UNDERWOOD ellipse paper -- 20-test verification suite
cd ellipse
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
python3 scripts/verify_all_claims_v2.py
# Expected: 20/20 PASS in <8 seconds

# (Optional) Build the Lean Logatoms package
cd lean
lake build
```

---

## Publishing workflow

This repo's `main` branch is updated **only** through the author's
manifest-driven publishing pipeline (in the upstream master at
`gitscratch/ellipse:infra/publishing/`):

1. **Manifest preparation** — a YAML manifest under `infra/publishing/manifests/`
   declares one or more git commits, each targeted at a registered repo + branch,
   with explicit `{src, dst}` file mappings. Subtree guards in `registry.yaml`
   block writes outside the topic folders declared for each target.
2. **Validation + preview** — `publish.py validate` checks every source file
   exists; `publish.py preview` shows the human-readable plan.
3. **Approval gate** — `publish.py approve` flips status `prepared` → `approved`.
   Nothing copies, commits, or pushes until this gate passes.
4. **Execute** — `publish.py execute` performs the file copies, makes the
   listed git commits, pushes the target's `main`, archives the manifest
   with the resulting commit SHAs, and commits the archive back to
   `gitscratch/ellipse:main` for permanent audit trail.

The top-level README itself is now data-driven: edit
`infra/publishing/sources/monir_math_repo.yaml`, run
`render_monir_math_readme.py`, then publish through a manifest.

---

## Directory of papers, by date

| Date | Paper | Location |
|---|---|---|
| 2026-04-27 | UNDERWOOD ellipse perimeter — rev4 abstract update (136 pp) — *current; abstract describes deposited Logatoms slice* | [`ellipse/paper/two_foci_one_cup_ellipse_perimeter_mamoun_rev4.pdf`](./ellipse/paper/two_foci_one_cup_ellipse_perimeter_mamoun_rev4.pdf) |
| 2026-04-23 | UNDERWOOD ellipse perimeter — v6 (88 pp) — *legacy; superseded by rev4* | [`ellipse/paper/paper_mamoun_ellipse_underwood_two_foci_one_cup_v6_23-April-2026.pdf`](./ellipse/paper/paper_mamoun_ellipse_underwood_two_foci_one_cup_v6_23-April-2026.pdf) |
| 2026-04-19 | UNDERWOOD ellipse perimeter — v1 original release — *legacy* | [`ellipse/paper/paper_mamoun_ellipse_underwood_two_foci_one_cup_v1_19-April-2026.pdf`](./ellipse/paper/paper_mamoun_ellipse_underwood_two_foci_one_cup_v1_19-April-2026.pdf) |
| 2026-04-14 | Snow-Crystal Paper V Unified Theory v2 (canonical headline) (25 pp) | [`snowcrystal/papers/paper_mamoun_snow_crystal_theory_unified_v2_14-April-2026.pdf`](./snowcrystal/papers/paper_mamoun_snow_crystal_theory_unified_v2_14-April-2026.pdf) |
| 2026-04-14 | Snow-Crystal Paper IV — Splitting Equation | [`snowcrystal/papers/snow_crystal_splitting_v2.pdf`](./snowcrystal/papers/snow_crystal_splitting_v2.pdf) |
| 2026-04-14 | Snow-Crystal Paper III — Snowflake Equation (v6 current) | [`snowcrystal/papers/snow_crystal_equation_v6.pdf`](./snowcrystal/papers/snow_crystal_equation_v6.pdf) |
| 2026-03-30 | SRIRACHA ellipse perimeter (R6+16exp+3log SCOR, 7 ppt) — *legacy standalone repo; superseded by UNDERWOOD* | [https://github.com/monir/ellipse](https://github.com/monir/ellipse) |

---

## License and citation

Code: **MIT** · Papers and figures: **CC BY 4.0** · see [`LICENSE`](./LICENSE).

If you use any result from this repository in your work, please cite the
relevant paper directly.

## Contact

GitHub: [@monir](https://github.com/monir) · Issues:
[github.com/monir/math/issues](https://github.com/monir/math/issues)
