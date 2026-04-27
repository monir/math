# `monir/math` &mdash; central distribution point for Monir Mamoun's mathematical research

> *Hard, classical problems &mdash; solved with explicit formulas, every coefficient
> written out, every proof checkable, every number reproducible.*

This repository is the **public umbrella** for **Monir Mamoun**'s
mathematical-research output. It is laid out as **one folder per
mega-topic**; each folder is self-contained (its own paper, code, scripts,
Lean modules) and links back here.

The umbrella site at **[monir.github.io/math](https://monir.github.io/math)**
is the visitor's-eye view; this README is the contributor's-eye view.

---

## At a glance &mdash; the active research areas

| Topic | Folder | Latest publication | Headline result |
|-------|--------|--------------------|-----------------|
| **Ellipse perimeter** | [`ellipse/`](./ellipse) | **`rev4`, 27 April 2026 (136 pp)** | **UNDERWOOD &mdash; the Definitive Second Breakthrough in Closed-Form Approximator Models.** **3.3 parts-per-trillion at 13 stored constants** (F3); $3\times 10^{-13}$ relative error at 14 (F4 + Remez). Beats SRIRACHA by **2&times;** and the Ramanujan / Cantrell / Ayala&ndash;Raggi / AAA lines by **$10^{4}$&ndash;$10^{8}$&times;** at every matched parameter budget. **147,000&times;** better than AAA on the L-shaped corner singularity. Walsh&ndash;Bernstein **separation theorem**: gap vs any rational method grows without bound. |
| **Snow-crystal physics** | [`snowcrystal/`](./snowcrystal) | **Paper V (Unified Theory v2), 14 April 2026 (25 pp)** | **First-principles unified theory of snow-crystal formation**, MB-pol(2023) quantum chemistry through Kobayashi 1993 phase-field PDE. Predicts ice-face splitting $\Delta_{\rm split} = 8.94 \pm 0.46\ {\rm cm}^{-1}$ vs THz-measured 8.80 (**0.30&sigma;**). Recovers Mason 1:2:3 cyclotomic ratio at $-4$/$-10$/$-22$ &deg;C. Lean-verified hexagonal factor $R_{\rm hex} = 4/(4+\sqrt{3}) = (16-4\sqrt{3})/13$ exact. **7/8** historical predictions confirmed (Murata 2020, Sazaki 2012, Bailey&ndash;Hallett 2004, Kobayashi 1976). 6 new falsifiable predictions. Spans 10 orders of magnitude in length, 30 in time. |
| **&lambda;-ladder + logatoms (cross-cutting)** | inside both topics' `lean/` &mdash; package name **`Logatoms`** | sorry-free against Mathlib v4.28.0 | **Logatom analytical framework**: canonical primitive $M^{j}_{\alpha}(\xi) = \xi^{\alpha}\bigl(\log(1/\xi)\bigr)^{j}$ with closed-form Gamma moment $j!/(\alpha+1)^{j+1}$ and Heisenberg ladder commutator $[T, D] = -I$. Sits inside Odrzywo&#322;ek's **EML** grammar (`eml(x, y) := exp(x) - log(y)`, Sheffer stroke for elementary functions; arXiv:2603.21852). Bijection $\Phi(\alpha, j) = j!/(\alpha+1)^{j+1}$ gives a syntax-free equality test on the logatom algebra. |
| **Convergent reduction / NS / $\zeta(5)$** | private working tree (results migrate here as they harden) | Internal | NS Grand Solution (conditional on Lemma 11; Lemma 11 closed in Lean via `Logatoms.ExtNSAlgebra`). $\zeta(5) \notin \mathbb{Q}$ effective irrationality measure $\mu_{\rm eff}(\zeta(5)) \le 7.233$ (conditional on CDT 2025 + Andr&eacute; 1989). |

---

## The unifying thread

> *One algebra. Many depths. The same number $1/4$ everywhere.*

Read top-to-bottom, the active topics look like four separate research
programs (ellipse-perimeter approximation, snow-crystal physics,
Navier&ndash;Stokes regularity, $\zeta(5)$ irrationality). They are not.
**They are the same algebra at different depths.** That algebra is the
*iterated logatom subspace*

$$\bigoplus_{\alpha,\,p}\, \mathbb{R}\cdot \xi^{\alpha}\log^{p}(1/\xi)$$

closed under truncated $\partial_{\xi}$, with integer Galois-equivariant
structure constants &mdash; the same algebra that `Logatoms.MultiDepth` and
`Logatoms.ExtNSAlgebra` formalise in Lean 4 and that the NS Grand Solution
paper rests on.

The depth-stratification:

| Depth $p$ | Where it appears | Damping ratio | Verified at |
|----------:|------------------|---------------|-------------|
| **0** (analytic) | Outer Euler flow in NS; analytic remainder of every UNDERWOOD fit | (Bernstein, geometric) | UNDERWOOD Theorem 1 (rev4, &sect;3) |
| **1** (single log) | UNDERWOOD F1&ndash;F2 ellipse formulas; **NS law of the wall** $u^{+} = (1/\kappa)\log(y^{+}) + B$; first Lipowsky term in ice | $1/\kappa$ (NS); leading Lipowsky $\xi$ (ice) | $\kappa$ recovered to $3.3\times 10^{-51}$ (`ns_law_of_the_wall_underwood_v2.py`) |
| **2** (squared log) | **UNDERWOOD F3&ndash;F4 logatoms $\xi^{2+j}\log(1/\xi)$** (record); NS triple-deck; second Walsh&ndash;Bernstein rung in ice | $\delta/\xi = 1/4$ EXACT (Lipowsky, Lean-proved) | rev4 Lemma 12, full inline derivation |
| **3** (cubed log) | **Ice QLL** in production: $d_{\rm QLL}(\Delta T) = \sum_{p=0}^{3}\xi_{p}\log^{p}(T_{m}/\Delta T)$ | $\delta/\xi = 1/4$, factorial $1/p!$ damping | $T_{c,\,{\rm basal}} = -5.16007$ &deg;C round-trip to $10^{-46}$ K |
| **4&ndash;9** (deep ladder) | $\widetilde{V}_{\rm NS}$ 100-dim algebra closing **NS Lemma 11**; $\zeta(5)$ channel substrate | truncated $\partial_{\xi}$ has integer structure constants $\in \{-9,\ldots,9\}$ | `Logatoms.ExtNSAlgebra.Lemma11_Galois_stability` (sorry-free) |

**The same number $1/4$ appears as: (i) the leading Villarino coefficient
$a_{0}$ of the elliptic integral, (ii) the Lipowsky pucker quantum
$\delta/\xi$ in ice Ih, and (iii) the Walsh&ndash;Bernstein damping ratio
recovered from a fit on the ice QLL profile.** Three independent
derivations from three different physical settings, all matching exactly.

---

## Layout

```
monir/math/
&#9500;&#9472;&#9472; ellipse/              &#9733; ACTIVE   UNDERWOOD ellipse perimeter
&#9474;   &#9500;&#9472;&#9472; paper/            Latest manuscript (rev4, 27 April 2026, 136 pp)
&#9474;   &#9500;&#9472;&#9472; scripts/          Verification suite, figure regen, certificate gen
&#9474;   &#9500;&#9472;&#9472; src/              Importable Python: augmented_basis, formulas, verify
&#9474;   &#9500;&#9472;&#9472; lean/             Lean 4 modules; Logatoms package sorry-free
&#9474;   &#9500;&#9472;&#9472; docs/             Stand-alone web demo
&#9474;   &#9492;&#9472;&#9472; README.md         Topic-specific entry point
&#9500;&#9472;&#9472; snowcrystal/          &#9733; ACTIVE   Unified snow-crystal theory
&#9474;   &#9500;&#9472;&#9472; papers/           5+ papers (Paper V Unified Theory canonical, plus I&ndash;IV)
&#9474;   &#9500;&#9472;&#9472; lean/             Hexagonal-factor Lean proofs, MultiDepth module
&#9474;   &#9500;&#9472;&#9472; notes/            Working notes
&#9474;   &#9500;&#9472;&#9472; scripts/          ZBU operator + 26 unit tests
&#9474;   &#9492;&#9472;&#9472; README.md
&#9492;&#9472;&#9472; docs/                 GitHub Pages umbrella site
    &#9500;&#9472;&#9472; index.html         monir.github.io/math/
    &#9500;&#9472;&#9472; ellipse/index.html monir.github.io/math/ellipse/
    &#9492;&#9472;&#9472; README.md
```

---

## Biggest results, by area

### Ellipse perimeter &mdash; UNDERWOOD

The ellipse perimeter has a **logarithmic branch point** at the
degeneracy limit $b \to 0$ (the ellipse collapses to a segment). For 2500
years every compact-formula approximator has been fitting a *smooth*
function to this *non-smooth* target. **UNDERWOOD writes the log modes
explicitly**: three named log companions $\xi^{2+j}\log(1/\xi)$ added to
a Chebyshev basis, a QR solve, done. The residual becomes analytic;
Chebyshev handles it at geometric rate; the floor falls.

| Metric | Value |
|---|---|
| Peak relative error (F3, 13 constants) | $3.3 \times 10^{-12}$ |
| Peak relative error (F4 + Remez, 14 constants) | $2.1 \times 10^{-13}$ |
| Improvement over Ayala&ndash;Raggi 2025 | $\sim 10^{5}$&times; |
| Improvement over AAA at L-corner | $\sim 1.47 \times 10^{5}$&times; |
| Improvement over SRIRACHA (author's own prior 30 March 2026) | $2$&times; on half the parameter budget |
| Verification | 50-digit `mpmath`, zero float64 |
| Reproduces in | $< 5$ seconds (20-test suite) |
| Lean formalisation | `Logatoms` package, sorry-free against Mathlib v4.28.0 |

**The mathematical contribution beyond the number:**

1. **The logatom analytical framework** &mdash; named primitive
   $M^{j}_{\alpha}(\xi) = \xi^{\alpha}\bigl(\log(1/\xi)\bigr)^{j}$ with
   closed-form Gamma moment $j!/(\alpha+1)^{j+1}$ and Heisenberg ladder
   $[T, D] = -I$; minimal basis for the log-branch class.

2. **The Odrzywo&#322;ek&ndash;EML substrate** &mdash; logatoms inhabit Odrzywo&#322;ek's
   recent 2026 result that the single binary operation $\mathrm{eml}(x,y) =
   \exp(x) - \log(y)$ together with the constant 1 is a Sheffer stroke
   for the elementary functions (every elementary function is a finite
   EML tree). The bijection $\Phi$ from logatom indices to Gamma-moment
   signatures gives a *syntax-free* equality test.

3. **The Walsh&ndash;Bernstein separation theorem** &mdash; rational approximation
   has a *polynomial* convergence floor against logarithmic-branch
   targets. UNDERWOOD's basis converges *geometrically*. The gap
   $(P/\rho)^{P/2} \to \infty$ is unbounded as parameters grow; no
   rational method, however cleverly its poles are placed, can close
   the gap.

**Read first:**

| You want | Go to |
|---|---|
| The shortest accurate ellipse-perimeter formula to copy into a CAD tool | [`ellipse/README.md`](./ellipse/README.md) (F4 copy-paste Python block) |
| The full 136-page paper with every proof line-by-line | [`ellipse/paper/two_foci_one_cup_ellipse_perimeter_mamoun_rev4.pdf`](./ellipse/paper/two_foci_one_cup_ellipse_perimeter_mamoun_rev4.pdf) |
| One-page press handout | [`ellipse/paper/underwood_press_handout_v2.pdf`](./ellipse/paper/underwood_press_handout_v2.pdf) |
| The Lean 4 logatoms package | [`ellipse/lean/`](./ellipse/lean) (and the cross-cutting `Logatoms` package shipped under `snowcrystal/lean`) |

### Snow-crystal physics &mdash; the unified theory

A first-principles framework for snow-crystal formation, derived from
**MB-pol(2023)** quantum chemistry through the **Kobayashi 1993** 2D
phase-field PDE simulation. **Paper V** (the canonical headline,
14 April 2026, 25 pp) combines and supersedes Papers I&ndash;IV.

| Result | Value |
|---|---|
| Predicted ice-face splitting $\Delta_{\rm split}$ | $8.94 \pm 0.46\ {\rm cm}^{-1}$ |
| Measured (THz spectroscopy) | $8.80\ {\rm cm}^{-1}$ |
| Significance | **0.30&sigma;** |
| Hexagonal factor (Lean-proven exact) | $R_{\rm hex} = 4/(4+\sqrt{3}) = (16-4\sqrt{3})/13 \approx 7/10$ |
| Twin angles | $76.2$&deg; ($q=7$) vs measured $77$&deg;; $51.1$&deg; ($q=11$) vs measured $54$&deg; |
| Mason cyclotomic transitions | $-4$ / $-10$ / $-22$ &deg;C in 1:2:3 ratio (matches $\varphi(6,12,18)$) |
| Historical-prediction confirmation | **7/8** (Murata 2020, Sazaki 2012, Bailey&ndash;Hallett 2004, Kobayashi 1976) |
| New falsifiable predictions | 6 (D&#8322;O splitting, HDO satellite, $d\Delta/dT$, humidity, twin reduction, chiral phonons) |
| Length scales spanned | 10 orders of magnitude (&Aring; &rarr; km) |
| Time scales spanned | 30 orders of magnitude (fs &rarr; hours) |

**Series structure:**

| Paper | Title | Status |
|---|---|---|
| Paper I | THz Spectroscopy of Ice Faces | Companion submission |
| Paper II | Phonon Dispersion of Ice I$_{\rm h}$ | Companion submission |
| Paper III | The Snowflake Equation &mdash; Frustrated AF + Thermal Resonance | [`snow_crystal_equation_v6.pdf`](./snowcrystal/papers/snow_crystal_equation_v6.pdf) |
| Paper IV | Snow Crystal Splitting Equation | [`snow_crystal_splitting_v2.pdf`](./snowcrystal/papers/snow_crystal_splitting_v2.pdf) |
| **Paper V** &#9733; | **Unified Theory** (combines I&ndash;IV plus twinning, Hamiltonian hierarchy, phase-field morphology) | [`paper_mamoun_snow_crystal_theory_unified_v2_14-April-2026.pdf`](./snowcrystal/papers/paper_mamoun_snow_crystal_theory_unified_v2_14-April-2026.pdf) |
| Habit summary | Snow-Crystal Habit Unified | [`snow_crystal_habit_unified_v2.pdf`](./snowcrystal/papers/snow_crystal_habit_unified_v2.pdf) |
| $\theta$-means series | Crystal-Math $\theta$-Means parts 1&ndash;3 + UNDERWOOD addendum | [`crystal_math_theta_means_*`](./snowcrystal/papers) |

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
`gitscratch/ellipse:infra/publishing/`). The pipeline:

1. **Manifest preparation** &mdash; a YAML manifest under
   `infra/publishing/manifests/` declares one or more git commits, each
   targeted at a registered repo + branch, with explicit `{src, dst}`
   file mappings. Subtree guards in `registry.yaml` block writes outside
   the topic folders declared for each target.
2. **Validation + preview** &mdash; `publish.py validate` checks every
   source file exists and every destination is within an allowed
   subtree. `publish.py preview` shows the human-readable plan
   (subjects, bodies, file sizes, target paths).
3. **Approval gate** &mdash; `publish.py approve` flips the manifest's
   `status: prepared` &rarr; `status: approved`. Nothing copies, commits, or
   pushes until this gate is passed.
4. **Execute** &mdash; `publish.py execute` performs the file copies, makes
   the listed git commits in the target's working copy, pushes the
   target's `main`, archives the manifest with the resulting commit
   SHAs and push timestamps, and commits the archive back to
   `gitscratch/ellipse:main` for permanent audit trail.

Every executed manifest leaves a trail under
`gitscratch/ellipse:infra/publishing/manifests/archive/` &mdash; a record of
*what was published when, to where, and exactly which files*. **Never
push directly to this repo's `main` branch &mdash; always go through a
manifest.**

---

## Directory of papers, by date

| Date | Paper | Folder |
|------|-------|--------|
| **27 Apr 2026** | UNDERWOOD ellipse perimeter (rev4, 136 pp, Definitive Second Breakthrough &mdash; logatom + EML substrate) | [`ellipse/paper/two_foci_one_cup_ellipse_perimeter_mamoun_rev4.pdf`](./ellipse/paper/two_foci_one_cup_ellipse_perimeter_mamoun_rev4.pdf) |
| 23 Apr 2026 | UNDERWOOD ellipse perimeter (v6, 88 pp) | [`ellipse/paper/paper_mamoun_ellipse_underwood_two_foci_one_cup_v6_23-April-2026.pdf`](./ellipse/paper/paper_mamoun_ellipse_underwood_two_foci_one_cup_v6_23-April-2026.pdf) (legacy; superseded by rev4) |
| 19 Apr 2026 | UNDERWOOD ellipse perimeter (v1, original release) | [`ellipse/paper/paper_mamoun_ellipse_underwood_two_foci_one_cup_v1_19-April-2026.pdf`](./ellipse/paper/paper_mamoun_ellipse_underwood_two_foci_one_cup_v1_19-April-2026.pdf) (legacy) |
| **14 Apr 2026** | Snow Crystal Paper V Unified Theory (canonical headline) | [`snowcrystal/papers/paper_mamoun_snow_crystal_theory_unified_v2_14-April-2026.pdf`](./snowcrystal/papers/paper_mamoun_snow_crystal_theory_unified_v2_14-April-2026.pdf) |
| Apr 2026 | Snow Crystal Paper IV (Splitting Equation) | [`snowcrystal/papers/snow_crystal_splitting_v2.pdf`](./snowcrystal/papers/snow_crystal_splitting_v2.pdf) |
| Apr 2026 | Snow Crystal Paper III (Snowflake Equation, v6 current) | [`snowcrystal/papers/snow_crystal_equation_v6.pdf`](./snowcrystal/papers/snow_crystal_equation_v6.pdf) |
| Apr 2026 | Crystal-Math $\theta$-means (parts 1, 2, 3 + UNDERWOOD addendum) | [`snowcrystal/papers/`](./snowcrystal/papers) |
| 30 Mar 2026 | SRIRACHA ellipse perimeter (R6+16exp+3log SCOR, 7 ppt; **superseded by UNDERWOOD**) | [`github.com/monir/ellipse`](https://github.com/monir/ellipse) (legacy standalone repo) |

---

## License and citation

Code: **MIT** &middot; Papers and figures: **CC BY 4.0** &middot; see [`LICENSE`](./LICENSE).

If you use any result from this repository in your work, please cite the
relevant paper directly. For UNDERWOOD ellipse-perimeter, see the
citation block in [`ellipse/README.md`](./ellipse/README.md).

---

## Contact

GitHub: [@monir](https://github.com/monir) &middot;
Issues: [github.com/monir/math/issues](https://github.com/monir/math/issues) &middot;
Pull requests welcome on the public side.
