# `monir/math` &mdash; GitHub Pages source

This folder is the source for the umbrella site served at
**https://monir.github.io/math/**.

```
docs/
├── _config.yml              # Jekyll: theme:null + include ellipse/, snowcrystal/
├── index.html               # umbrella landing page (this site's root)
├── ellipse/
│   └── index.html           # https://monir.github.io/math/ellipse/
├── snowcrystal/
│   └── index.html           # https://monir.github.io/math/snowcrystal/
└── README.md                # this file
```

## What lives where

| URL | Source file | Audience |
|-----|-------------|----------|
| `monir.github.io/math/`             | `docs/index.html`             | All visitors &mdash; brief intro to the umbrella research repo, links to each mega-topic, featured UNDERWOOD rev4 record card, snow-crystal Paper V card. |
| `monir.github.io/math/ellipse/`     | `docs/ellipse/index.html`     | Readers who want the ellipse-perimeter result specifically: the formula ladder, the comparison table, the rev4 paper, the one-page summary, reproduce-in-5-seconds. |
| `monir.github.io/math/snowcrystal/` | `docs/snowcrystal/index.html` | Readers who want the snow-crystal result specifically: the Unified Theory Paper&nbsp;V, the THz match, the Lean-proven hexagonal factor, the five-paper series, the Crystal Math and Theta Means companion. |

## What is **not** here

* The **legacy interactive demo** with sliders, KaTeX, and live error
  charts lives in the older standalone repo at
  https://monir.github.io/ellipse/ . Both URLs remain valid; new work
  goes to the umbrella.
* The **research scripts**, **paper TeX sources**, and **Lean modules**
  live in their topic folders (`ellipse/`, `snowcrystal/`, &hellip;) at
  the repo root, not under `docs/`. The site links out to GitHub for
  those.

## Edit the site

The two pages are self-contained static HTML &mdash; no build step.
Edit, commit, push: GitHub Pages rebuilds in ~30 seconds.

If you change the **Underwood F4 coefficients** (or any number cited
on either page), regenerate the matching paper fragments first
(`scripts/underwood/formula_renderer_dual_v1.py`,
`scripts/underwood/intro_formula_ladder_v1.py`) so the paper, the site,
and the running code never drift apart.
